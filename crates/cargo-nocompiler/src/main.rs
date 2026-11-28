mod build;
mod chc;
#[allow(dead_code)] // This module also supplies the encoder used by the embedded rustc driver.
mod contract_ir;
mod contracts;
mod flow;
mod heap;
mod llvm;
mod llvm_ir;
mod loops;
mod memory;
mod scope;

use clap::{Parser, Subcommand};
use nocompiler_typed::asm;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    process::{Command, ExitCode},
};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
type TextMap = BTreeMap<String, String>;

#[derive(Parser)]
#[command(
    name = "cargo nocompiler",
    about = "Generate and verify NoCompiler contracts for Rust binaries"
)]
struct Cli {
    #[command(subcommand)]
    command: Action,
}
#[derive(Subcommand)]
enum Action {
    Check(Args),
}
#[derive(clap::Args)]
struct Args {
    #[arg(long, default_value = "Cargo.toml")]
    manifest_path: PathBuf,
    #[arg(long)]
    package: Option<String>,
    #[arg(long, value_delimiter = ',')]
    features: Vec<String>,
    #[arg(long)]
    no_default_features: bool,
    #[arg(long)]
    all_features: bool,
    #[arg(long)]
    locked: bool,
    #[arg(long, default_value = "release")]
    profile: String,
    #[arg(long, default_value = "llvm-symbolizer")]
    symbolizer: PathBuf,
    #[arg(long)]
    no_source_trace: bool,
    #[arg(long)]
    invariants: Option<PathBuf>,
    #[arg(long)]
    allocator_contracts: Option<PathBuf>,
    #[arg(long, default_value_t = 4096)]
    global_allocator_stack: u64,
    #[arg(long)]
    allow_assumptions: bool,
    /// Require the generated contracts for these public entries to match a reviewed JSON file.
    #[arg(long)]
    entry_contracts: Option<PathBuf>,
    /// Require an existing deployment ELF to match the bytes given to the checker.
    #[arg(long)]
    deployment_elf: Option<PathBuf>,
    #[arg(long)]
    no_infer_loops: bool,
    /// Report MIR candidates without using them to generate annotations.
    #[arg(long)]
    no_mir_hints: bool,
    /// Use a Z3-compatible executable for bounded Horn reachability refinement.
    #[arg(long)]
    chc_solver: Option<PathBuf>,
    /// Generate additional candidates from optimized LLVM IR and post-allocation Machine IR.
    #[arg(long)]
    llvm_hints: bool,
    #[arg(long)]
    bin: String,
    #[arg(long, required = true)]
    function: Vec<String>,
    #[arg(long)]
    artifacts: Option<PathBuf>,
    #[arg(long)]
    checker: Option<PathBuf>,
    #[arg(long)]
    lean_dir: Option<PathBuf>,
}

fn metadata(dir: &Path) -> Result<(TextMap, BTreeMap<String, contracts::Layout>)> {
    let mut targets = TextMap::new();
    let mut layouts = BTreeMap::new();
    for line in fs::read_to_string(dir.join("abi.tsv"))?.lines() {
        let row: Vec<_> = line.split('\t').collect();
        let [name, symbol, output, args, safety] = row.as_slice() else {
            return Err("malformed ABI record".into());
        };
        let is_unsafe = match *safety {
            "safe" => false,
            "unsafe" => true,
            _ => return Err("invalid function safety in ABI record".into()),
        };
        targets.insert((*name).into(), (*symbol).into());
        let args = if args.is_empty() {
            vec![]
        } else {
            args.split(',').map(str::to_owned).collect()
        };
        if layouts
            .insert(
                (*symbol).into(),
                contracts::Layout {
                    output: (*output).into(),
                    args,
                    is_unsafe,
                },
            )
            .is_some()
        {
            return Err(
                "compiler capture did not uniquely identify the requested functions".into(),
            );
        }
    }
    Ok((targets, layouts))
}
fn tsv(path: &Path) -> Result<Vec<(String, String)>> {
    fs::read_to_string(path)?
        .lines()
        .map(|line| {
            let (a, b) = line.split_once('\t').ok_or("malformed compiler capture")?;
            Ok((a.into(), b.into()))
        })
        .collect()
}
fn callees(path: &Path) -> Result<BTreeMap<String, Vec<String>>> {
    let mut groups = BTreeMap::<String, Vec<String>>::new();
    for (caller, callee) in tsv(path)? {
        groups.entry(caller).or_default().push(callee);
    }
    Ok(groups)
}

fn directive<'a>(line: &'a str, name: &str) -> Option<&'a str> {
    let rest = line.trim().strip_prefix(name)?;
    rest.starts_with(char::is_whitespace).then(|| rest.trim())
}
fn symbol_kind(line: &str) -> Option<(&str, &str)> {
    let (symbol, kind) = directive(line, ".type")?.split_once(',')?;
    Some((symbol.trim(), kind.trim()))
}
fn select(source: &str, selected: &BTreeSet<String>) -> (String, BTreeSet<String>) {
    let mut body = String::new();
    let mut found = BTreeSet::new();
    let mut keep = true;
    let mut debug = false;
    for line in source.split_inclusive('\n') {
        if let Some(section) = directive(line, ".section") {
            debug = section.starts_with(".debug") || section.starts_with("\".debug");
        } else if matches!(line.trim(), ".text" | ".data" | ".bss") {
            debug = false;
        }
        if debug {
            continue;
        }
        if let Some((name, "@function")) = symbol_kind(line) {
            keep = selected.contains(name);
            if keep {
                found.insert(name.into());
            }
        }
        if keep {
            body.push_str(line)
        }
        if directive(line, ".size").is_some() {
            keep = true;
        }
    }
    (body, found)
}
fn parse(source: &str) -> Result<asm::Program> {
    asm::parse(source).map_err(|err| format!("assembly line {}: {}", err.line, err.msg).into())
}
fn write_json(path: &Path, value: &Value) -> Result<()> {
    fs::write(path, format!("{}\n", serde_json::to_string_pretty(value)?))?;
    Ok(())
}

fn elf_digest(path: &Path) -> Result<String> {
    use std::io;
    let mut digest = Sha256::new();
    io::copy(&mut fs::File::open(path)?, &mut digest)?;
    Ok(format!("{:x}", digest.finalize()))
}

fn run(args: &Args, dir: &Path) -> Result<u8> {
    let reviewed: Option<TextMap> = args
        .entry_contracts
        .as_ref()
        .map(|path| -> Result<_> { Ok(serde_json::from_slice(&fs::read(path)?)?) })
        .transpose()?;
    if let Some(reviewed) = &reviewed
        && (reviewed.is_empty() || reviewed.keys().any(|name| !args.function.contains(name)))
    {
        return Err("reviewed entry contracts must name at least one selected function".into());
    }
    let build_started = std::time::Instant::now();
    let image = build::compile(args, dir)?;
    let build_ms = build_started.elapsed().as_millis();
    let elf_sha256 = elf_digest(&image.image)?;
    if let Some(path) = &args.deployment_elf
        && elf_digest(path)? != elf_sha256
    {
        return Err(format!(
            "deployment ELF differs from the proof input: {}",
            path.display()
        )
        .into());
    }
    let (targets, layouts) = metadata(dir)?;
    let mir = contract_ir::Summary::decode(&fs::read_to_string(dir.join("mir-contracts.tsv"))?)
        .ok_or("malformed MIR contract record")?;
    let unsupported: TextMap = tsv(&dir.join("unsupported.tsv"))?.into_iter().collect();
    if targets.keys().any(|key| unsupported.contains_key(key))
        || targets.len() + unsupported.len() != args.function.len()
        || args
            .function
            .iter()
            .any(|name| !targets.contains_key(name) && !unsupported.contains_key(name))
    {
        return Err("compiler capture did not uniquely identify the requested functions".into());
    }
    let trace = if args.no_source_trace {
        json!({})
    } else {
        build::trace(&args.symbolizer, &image.image, &image.symbols, &targets)?
    };
    let global: BTreeSet<_> = image
        .assembly
        .lines()
        .filter_map(|line| directive(line, ".globl"))
        .collect();
    let selected: BTreeSet<_> = targets
        .values()
        .filter(|name| image.symbols.contains_key(*name) && global.contains(name.as_str()))
        .cloned()
        .collect();
    let (body, found) = select(&image.assembly, &selected);
    if found != selected {
        return Err(format!(
            "no assembly body for {}",
            selected
                .difference(&found)
                .cloned()
                .collect::<Vec<_>>()
                .join(", ")
        )
        .into());
    }
    let funcs = if selected.is_empty() {
        vec![]
    } else {
        // The checker owns parse diagnostics and includes them in the report.
        // A malformed or unsupported body simply receives no analysis hints.
        parse(&body)
            .map(|program| program.funcs)
            .unwrap_or_default()
            .into_iter()
            .filter(|f| selected.contains(&f.name))
            .collect()
    };
    let raw: BTreeMap<_, _> = selected
        .iter()
        .map(|name| (name.clone(), contracts::pointers(&layouts[name])))
        .collect();
    let (requirements, chc_refinement) =
        memory::requirements(&funcs, &raw, args.chc_solver.as_deref());
    let shims: BTreeSet<_> = image
        .symbols
        .keys()
        .filter(|name| heap::operation(name).is_some())
        .cloned()
        .collect();
    // Parse shims independently. An unselected allocator body may use instructions
    // outside the checker profile, and only transparent forwarding is relevant here.
    let shims: Vec<_> = shims
        .iter()
        .filter_map(|shim| {
            let marker = image
                .assembly
                .lines()
                .position(|line| symbol_kind(line) == Some((shim.as_str(), "@function")))?;
            let body = image
                .assembly
                .lines()
                .skip(marker)
                .take_while(|line| directive(line, ".size").is_none())
                .collect::<Vec<_>>()
                .join("\n");
            parse(&body)
                .ok()?
                .funcs
                .into_iter()
                .find(|func| func.name == *shim)
        })
        .collect();
    let mut specs = heap::discover(
        &funcs,
        &shims,
        image.symbols.keys(),
        args.global_allocator_stack,
    );
    if let Some(path) = &args.allocator_contracts {
        let overrides: heap::Specs = serde_json::from_str(&fs::read_to_string(path)?)?;
        specs.extend(overrides);
    }
    let heap::AllocatorContracts {
        annotations: external,
        budgets,
    } = heap::contracts(&specs, &image.symbols, &selected)?;
    let mut heap_users: BTreeSet<_> = external
        .keys()
        .filter(|name| specs[*name]["operation"] != "rust_no_alloc_shim_is_unstable_v2")
        .cloned()
        .collect();
    heap_users.extend(
        selected
            .iter()
            .filter(|name| contracts::owned(&layouts[*name]))
            .cloned(),
    );
    let heap_users = heap::propagate(&funcs, heap_users);
    let declared: contracts::Rules = if let Some(path) = &args.invariants {
        serde_json::from_str(&fs::read_to_string(path)?)?
    } else {
        BTreeMap::new()
    };
    let inferred_report = contracts::discover(&funcs, &layouts);
    let symbolic = memory::symbolic_requirements(&funcs, &layouts);
    let stack = memory::stack(&funcs, &requirements, budgets);
    let mut signatures = TextMap::new();
    let mut llvm_fallbacks = TextMap::new();
    let mut llvm_result_fallbacks = BTreeMap::new();
    let mut annotations = BTreeMap::new();
    let mut source_contracts = BTreeMap::new();
    for name in args.function.iter().filter_map(|path| targets.get(path)) {
        let layout = &layouts[name];
        let summary = mir.get(name);
        let empty = contract_ir::Summary::default();
        let candidate = contracts::infer_source(layout, summary.unwrap_or(&empty));
        let mut source = contracts::source_report(layout, summary, &candidate);
        let machine_ir = contracts::infer_source(layout, symbolic.get(name).unwrap_or(&empty));
        let ir = candidate.with_machine_raw(machine_ir, !args.no_mir_hints);
        let llvm_trips = image
            .llvm_hints
            .trips
            .get(name)
            .map(Vec::as_slice)
            .unwrap_or_default();
        let llvm_range = image.llvm_hints.ranges.get(name).copied();
        let llvm_result = image.llvm_hints.affine_results.get(name).filter(|_| {
            layout
                .args
                .iter()
                .all(|arg| matches!(arg.as_str(), "word" | "uword"))
        });
        let build_contract = |llvm| {
            contracts::build(
                name,
                layout,
                requirements.get(name),
                Some(&ir),
                llvm,
                &declared,
                heap_users.contains(name) || contracts::owned(layout),
            )
        };
        let mut contract = build_contract((llvm_range, llvm_result))?;
        if (llvm_range.is_some() || llvm_result.is_some()) && selected.contains(name) {
            let baseline = build_contract((None, None))?;
            if baseline.text != contract.text {
                let mut reviews = reviewed
                    .iter()
                    .flat_map(|entries| entries.iter())
                    .filter(|(path, _)| targets.get(*path) == Some(name))
                    .map(|(_, signature)| signature.as_str())
                    .peekable();
                if reviews.peek().is_none() {
                    llvm_fallbacks.insert(name.clone(), baseline.text);
                } else if reviews.all(|signature| {
                    baseline.text.strip_prefix(&format!("#: fn {name} ")) == Some(signature)
                }) {
                    contract = baseline;
                }
            }
        }
        signatures.insert(name.clone(), contract.text.clone());

        if let Some(value) = llvm_result {
            source["llvm_affine_result"] =
                json!({"register": "a0", "expression": value.render(contracts::input_name)});
        }
        if let Some(range) = llvm_range {
            source["llvm_result_range"] =
                json!({"register": "a0", "lower": range.lower, "upper_exclusive": range.upper});
        }
        if !llvm_trips.is_empty() {
            let candidates: Vec<_> = llvm_trips
                .iter()
                .map(|trip| {
                    json!({
                        "iterations": trip.iterations.map(|n| n.to_string()),
                        "latch_operands": [trip.left.name(), trip.right.name()],
                        "count_arg_register": trip.count_arg.map(|reg| reg.name()),
                    })
                })
                .collect();
            source["llvm_loop_trip"] = candidates[0].clone();
            source["llvm_loop_trips"] = json!(candidates);
        }
        if let Some(frame) = image.llvm_hints.frames.get(name) {
            source["llvm_stack"] = json!({"frame_size": frame.size as u64, "slots":
                frame.slots.iter().map(|&(a, b)| [a as u64, b as u64]).collect::<Vec<_>>()});
        }
        if let Some(values) = image.llvm_hints.affine_values.get(name)
            && let Some(func) = funcs.iter().find(|f| f.name == *name)
        {
            source["llvm_affine_locations"] =
                json!(llvm::affine_locations(func, &contract.state, values));
        }
        if let Some(summary) = summary {
            source["mir_resolved_callees"] = json!(summary.callees);
        }
        source_contracts.insert(name.clone(), source);
        if selected.contains(name)
            && !args.no_infer_loops
            && let Some(func) = funcs.iter().find(|f| f.name == *name)
        {
            annotations.extend(loops::annotate(
                func,
                &contract.state,
                &mut contract.names,
                &contract.slices,
            ));
        }
    }
    let render_contracts = |selected_only: bool, signatures: &TextMap| -> String {
        let mut text = String::new();
        for name in args.function.iter().filter_map(|path| targets.get(path)) {
            if !selected_only || selected.contains(name) {
                let frame = stack.get(name).map(String::as_str).unwrap_or("stack 0");
                text.push_str(&format!("{} {frame}\n", signatures[name]));
            }
        }
        text.extend(external.values().map(String::as_str));
        text
    };
    let get_entries = |signatures: &TextMap| -> Result<TextMap> {
        targets
            .iter()
            .map(|(path, name)| {
                let signature = signatures[name]
                    .strip_prefix(&format!("#: fn {name} "))
                    .ok_or("generated contract has an unexpected signature")?;
                Ok((path.clone(), signature.trim().to_owned()))
            })
            .collect()
    };
    let entry_contracts = get_entries(&signatures)?;
    let changed: BTreeSet<_> = reviewed
        .iter()
        .flat_map(|entries| entries.iter())
        .filter(|(name, signature)| entry_contracts.get(*name) != Some(*signature))
        .map(|(name, _)| name.as_str())
        .collect();
    let ledger = dir.join("ledger.json");
    let mut report = json!({"checker":null,"functions":[],"global_errors":[]});
    let mut status = 0;
    let mut checker_attempts_ms = Vec::new();
    if changed.is_empty() && !selected.is_empty() {
        let mut annotated_body = String::new();
        for (index, line) in body.split_inclusive('\n').enumerate() {
            if let Some(annotation) = annotations.get(&(index + 1)) {
                annotated_body.push_str(annotation);
            }
            annotated_body.push_str(line);
        }
        let annotated = dir.join("annotated.s");
        let checker = args
            .checker
            .clone()
            .or_else(|| std::env::var_os("NOCOMPILER_TYPED").map(PathBuf::from))
            .unwrap_or(std::env::current_exe()?.with_file_name("nocompiler-typed"));
        let lean = args
            .lean_dir
            .clone()
            .or_else(|| std::env::var_os("NOCOMPILER_LEAN_DIR").map(PathBuf::from))
            .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean"));
        loop {
            let mut text = render_contracts(true, &signatures);
            text.push_str(&annotated_body);
            fs::write(&annotated, text)?;
            let checker_started = std::time::Instant::now();
            status = Command::new(&checker)
                .arg("check")
                .arg(&annotated)
                .arg("--image")
                .arg(&image.image)
                .arg("--export-lean")
                .arg(dir.join("Proof.lean"))
                .args(["--prove", "--certs"])
                .arg("--lean-dir")
                .arg(&lean)
                .arg("--ledger")
                .arg(&ledger)
                .status()?
                .code()
                .unwrap_or(2);
            checker_attempts_ms.push(checker_started.elapsed().as_millis());
            if !ledger.exists() {
                report = json!({"checker":null,"functions":[],"global_errors":[format!(
                    "checker exited with status {status} without a ledger"
                )]});
                break;
            }
            report = serde_json::from_str(&fs::read_to_string(&ledger)?)?;
            if llvm_fallbacks.is_empty()
                || !matches!(status, 0 | 1)
                || report["global_errors"]
                    .as_array()
                    .is_none_or(|errors| !errors.is_empty())
            {
                break;
            }
            let functions = report["functions"]
                .as_array()
                .ok_or("invalid checker ledger")?;
            let mut retry = false;
            for item in functions {
                let Some(name) = item["name"].as_str() else {
                    continue;
                };
                let reason = match item["status"].as_str() {
                    Some("rejected") if item["error"]["rule"] == "ret-out" => "ret-out",
                    Some("checked") if report["proof_attempt"]["status"] == "failed" => {
                        "lean_unproved"
                    }
                    _ => continue,
                };
                if let Some(baseline) = llvm_fallbacks.remove(name) {
                    signatures.insert(name.to_owned(), baseline);
                    llvm_result_fallbacks.insert(name.to_owned(), reason);
                    retry = true;
                }
            }
            if !retry {
                break;
            }
            // The retry must produce its own ledger and Lean input.
            fs::remove_file(&ledger)?;
            for filename in ["Proof.lean", "Proof.lean.certs.lean"] {
                match fs::remove_file(dir.join(filename)) {
                    Ok(()) => {}
                    Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                    Err(error) => return Err(error.into()),
                }
            }
        }
    }
    fs::write(
        dir.join("contracts.s"),
        render_contracts(false, &signatures),
    )?;
    write_json(
        &dir.join("contracts.json"),
        &json!({
            "schema_version": 1,
            "mir_hints_enabled": !args.no_mir_hints,
            "functions": source_contracts,
        }),
    )?;
    write_json(
        &dir.join("entry-contracts.json"),
        &json!(get_entries(&signatures)?),
    )?;
    if elf_digest(&image.image)? != elf_sha256 {
        return Err("proof input ELF changed during verification".into());
    }
    if let Some(path) = &args.deployment_elf
        && elf_digest(path)? != elf_sha256
    {
        return Err(format!(
            "deployment ELF changed during verification: {}",
            path.display()
        )
        .into());
    }
    let functions = report["functions"]
        .as_array()
        .ok_or("invalid checker ledger")?;
    let mut results = BTreeMap::new();
    let mut failed = status != 0
        || report["global_errors"]
            .as_array()
            .is_some_and(|e| !e.is_empty());
    for name in &args.function {
        let entry = if changed.contains(name.as_str()) {
            json!({"status":"entry_contract_mismatch","reason":"generated contract differs from reviewed contract or is unavailable"})
        } else if !changed.is_empty() {
            json!({"status":"not_checked","reason":"a reviewed entry contract did not match"})
        } else if let Some(reason) = unsupported.get(name) {
            json!({"status":"unsupported","reason":reason})
        } else {
            let symbol = &targets[name];
            if !image.symbols.contains_key(symbol) {
                json!({"name":symbol,"status":"missing_linked_symbol"})
            } else if !selected.contains(symbol) {
                json!({"name":symbol,"status":"unsupported","reason":"no external linkage in optimized assembly, so the entry ABI may differ"})
            } else {
                functions
                    .iter()
                    .find(|item| item["name"] == *symbol)
                    .cloned()
                    .unwrap_or_else(|| json!({"name":symbol,"status":"checker_error"}))
            }
        };
        let verdict = entry["status"].as_str().unwrap_or("checker_error");
        failed |= verdict != "proved" && !(args.allow_assumptions && verdict == "proved_assuming");
        let detail = entry["reason"]
            .as_str()
            .map(|r| format!(" ({r})"))
            .unwrap_or_default();
        println!("{name}: {verdict}{detail}");
        results.insert(name, entry);
    }
    let inferred_raw:Value=Value::Object(requirements.iter().filter(|(_,r)|!r.is_empty()).map(|(name,r)|{
        (name.clone(),Value::Object(r.iter().map(|(reg,region)|(reg.name().to_owned(),
            json!({"bytes":u64::try_from(region.bytes).ok(),"alignment":u64::try_from(region.alignment).ok(),"access":region.mode()}))).collect()))
    }).collect());
    write_json(
        &dir.join("report.json"),
        &json!({
            "schema_version":1,"elf_sha256":elf_sha256,
            "deployment_elf_matched":args.deployment_elf.is_some(),
            "entry_contract_file":"entry-contracts.json",
            "reviewed_entries":reviewed.as_ref().map(|entries| entries.keys().collect::<Vec<_>>()),
            "target":build::TARGET,"profile":args.profile,"rustc_flags":build::flags(!args.no_source_trace),
            "cargo":{"artifacts_file":"cargo-build.json","package":args.package,"binary":args.bin,"features":args.features,
                     "default_features":!args.no_default_features,"all_features":args.all_features,"locked":args.locked},
            "rust_toolchain":build::TOOLCHAIN,"rustc_version":image.version,"checker":report["checker"],
            "proof_attempt":report["proof_attempt"],
            "timing_ms":{"build_and_capture":build_ms,"checker_attempts":checker_attempts_ms},
            "llvm_result_fallbacks":llvm_result_fallbacks,
            "checker_exit_code": (changed.is_empty() && !selected.is_empty()).then_some(status),
            "contract_file":"contracts.s","contract_ir_file":"contracts.json","mir_hints":!args.no_mir_hints,"llvm_hints":args.llvm_hints,"infer_loops":!args.no_infer_loops,"functions":results,
            "chc_solver_enabled":args.chc_solver.is_some(),"chc_pruned_edges":chc_refinement,
            "declared_type_invariants":declared,"inferred_type_invariants":inferred_report,"allocator_assumptions":specs,
            "mir_inlined_callees":callees(&dir.join("inlined.tsv"))?,"mir_direct_callees":callees(&dir.join("mir-calls.tsv"))?,
            "static_call_scope":scope::report(&targets, &funcs, &image.symbols, &external),
            "dwarf_inline_ranges":trace,"inferred_raw_pointer_requirements":inferred_raw,"global_errors":report["global_errors"]
        }),
    )?;
    Ok(
        if !matches!(status, 0 | 1)
            || (changed.is_empty() && !selected.is_empty() && !ledger.exists())
        {
            2
        } else {
            u8::from(failed)
        },
    )
}
fn execute(args: Args) -> Result<u8> {
    let names: BTreeSet<_> = args.function.iter().collect();
    if names.len() != args.function.len()
        || names
            .iter()
            .any(|s| s.trim().is_empty() || s.contains(['\t', '\r', '\n']))
    {
        return Err("function paths must be unique and contain no tabs or newlines".into());
    }
    let dir = if let Some(path) = &args.artifacts {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::create_dir(path)?;
        path.canonicalize()?
    } else {
        tempfile::Builder::new()
            .prefix("nocompiler-rust-")
            .tempdir()?
            .keep()
    };
    println!("Artifacts: {}", dir.display());
    run(&args, &dir)
}
fn main() -> ExitCode {
    let mut args: Vec<_> = std::env::args_os().collect();
    if args.get(1).is_some_and(|a| a == "nocompiler") {
        args.remove(1);
    }
    let Action::Check(args) = Cli::parse_from(args).command;
    match execute(args) {
        Ok(code) => ExitCode::from(code),
        Err(error) => {
            eprintln!("NoCompiler: {error}");
            ExitCode::from(2)
        }
    }
}

mod build;
mod contracts;
mod flow;
mod heap;
mod loops;
mod memory;

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
    #[arg(long)]
    no_infer_loops: bool,
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
        let [name, symbol, output, args] = row.as_slice() else {
            return Err("malformed ABI record".into());
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

fn run(args: &Args, dir: &Path) -> Result<u8> {
    let image = build::compile(args, dir)?;
    let (targets, layouts) = metadata(dir)?;
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
    let requirements = memory::requirements(&funcs, &raw);
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
    let (inferred, inferred_report) = contracts::discover(&funcs, &layouts);
    let stack = memory::stack(&funcs, &requirements, budgets);
    let mut all = String::new();
    let mut selected_text = String::new();
    let mut annotations = BTreeMap::new();
    for name in args.function.iter().filter_map(|path| targets.get(path)) {
        let layout = &layouts[name];
        let mut contract = contracts::build(
            name,
            layout,
            requirements.get(name),
            &declared,
            &inferred,
            heap_users.contains(name) || contracts::owned(layout),
        )?;
        let frame = stack.get(name).map(String::as_str).unwrap_or("stack 0");
        contract.text.push_str(&format!(" {frame}\n"));
        all.push_str(&contract.text);
        if selected.contains(name) {
            selected_text.push_str(&contract.text);
            if !args.no_infer_loops
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
    }
    for contract in external.values() {
        all.push_str(contract);
        selected_text.push_str(contract);
    }
    fs::write(dir.join("contracts.s"), all)?;
    let ledger = dir.join("ledger.json");
    let mut report = json!({"checker":null,"functions":[],"global_errors":[]});
    let mut status = 0;
    if !selected.is_empty() {
        for (index, line) in body.split_inclusive('\n').enumerate() {
            if let Some(annotation) = annotations.get(&(index + 1)) {
                selected_text.push_str(annotation);
            }
            selected_text.push_str(line);
        }
        let annotated = dir.join("annotated.s");
        fs::write(&annotated, selected_text)?;
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
        status = Command::new(checker)
            .arg("check")
            .arg(&annotated)
            .arg("--image")
            .arg(&image.image)
            .arg("--export-lean")
            .arg(dir.join("Proof.lean"))
            .args(["--prove", "--certs"])
            .arg("--lean-dir")
            .arg(lean)
            .arg("--ledger")
            .arg(&ledger)
            .status()?
            .code()
            .unwrap_or(2);
        if ledger.exists() {
            report = serde_json::from_str(&fs::read_to_string(&ledger)?)?;
        } else {
            report["global_errors"] = json!([format!(
                "checker exited with status {status} without a ledger"
            )]);
        }
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
        let entry = if let Some(reason) = unsupported.get(name) {
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
            "schema_version":1,"elf_sha256":format!("{:x}",Sha256::digest(fs::read(&image.image)?)),
            "target":build::TARGET,"profile":"release","rustc_flags":build::flags(!args.no_source_trace),
            "rust_toolchain":build::TOOLCHAIN,"rustc_version":image.version,"checker":report["checker"],
            "contract_file":"contracts.s","infer_loops":!args.no_infer_loops,"functions":results,
            "declared_type_invariants":declared,"inferred_type_invariants":inferred_report,"allocator_assumptions":specs,
            "mir_inlined_callees":callees(&dir.join("inlined.tsv"))?,"mir_direct_callees":callees(&dir.join("mir-calls.tsv"))?,
            "dwarf_inline_ranges":trace,"inferred_raw_pointer_requirements":inferred_raw,"global_errors":report["global_errors"]
        }),
    )?;
    Ok(
        if !matches!(status, 0 | 1) || (!selected.is_empty() && !ledger.exists()) {
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

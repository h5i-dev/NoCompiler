//! `nocompiler-typed check FILE.s [--ledger OUT.json] [--states] [--image LINKED.elf] …`
//!
//! Checks every safe function of a typed assembly file. Exit status 0 when all pass, 1 when
//! one is rejected, 2 on a usage or parse error.

use nocompiler_typed::{asm, check, ledger};
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let usage = "usage: nocompiler-typed link FILE.s... | check FILE.s [--ledger OUT.json] [--states] [--object FILE.o] [--export-lean OUT.lean] [--export-json OUT.json] [--image LINKED.elf [--prove [--certs] [--lean-dir DIR]]] [--loops natural|interval]";
    if args.first().map(String::as_str) == Some("link") {
        // nocompiler-typed link A.s B.s ... [--loops natural]: the whole program (Theorem D)
        let natural = !args.iter().any(|a| a == "interval");
        let mut files = Vec::new();
        // link --image L.elf --prove [--export-lean X.lean] [--lean-dir D]: theorem D for the
        // whole linked program (decisions.md P7 step 3, the default taken)
        let mut l_image: Option<String> = None;
        let mut l_out: Option<String> = None;
        let mut l_dir: Option<String> = None;
        let mut l_prove = false;
        let mut k = 1;
        while k < args.len() {
            let a = &args[k];
            k += 1;
            match a.as_str() {
                "--loops" | "natural" | "interval" => continue,
                "--prove" => {
                    l_prove = true;
                    continue;
                }
                "--image" | "--export-lean" | "--lean-dir" => {
                    let v = args.get(k).cloned();
                    k += 1;
                    match a.as_str() {
                        "--image" => l_image = v,
                        "--export-lean" => l_out = v,
                        _ => l_dir = v,
                    }
                    continue;
                }
                _ => {}
            }
            match std::fs::read_to_string(a) {
                Ok(s) => files.push((a.clone(), s)),
                Err(e) => {
                    eprintln!("{a}: {e}");
                    return ExitCode::from(2);
                }
            }
        }
        let r = nocompiler_typed::link::link(
            &files,
            check::Options {
                record: false,
                natural_loops: natural,
            },
        );
        for e in &r.functions {
            println!("{}: {} ({})", e.name, e.status, e.file);
        }
        if l_prove {
            let Some(img_file) = &l_image else {
                eprintln!("link --prove needs --image");
                return ExitCode::from(2);
            };
            let bytes = match std::fs::read(img_file) {
                Ok(b) => b,
                Err(e) => {
                    eprintln!("{img_file}: {e}");
                    return ExitCode::from(2);
                }
            };
            let (Ok(image), Ok(text)) = (
                nocompiler_typed::object::symbol_addresses(&bytes),
                nocompiler_typed::object::text_words(&bytes),
            ) else {
                eprintln!("{img_file}: not a linked ELF with .text");
                return ExitCode::from(2);
            };
            let sizes = nocompiler_typed::object::symbol_sizes(&bytes).ok();
            let mut checked = Vec::new();
            for (path, src) in &files {
                let prog = match asm::parse(src) {
                    Ok(p) => p,
                    Err(e) => {
                        eprintln!("{path}:{}: [syntax] {}", e.line, e.msg);
                        return ExitCode::from(2);
                    }
                };
                let (ck, rep) = check::check_program_opts(
                    &prog,
                    check::Options {
                        record: true,
                        natural_loops: natural,
                    },
                );
                checked.push((path.clone(), prog, ck, rep));
            }
            let dir = l_dir
                .clone()
                .or_else(|| std::env::var("NOCOMPILER_LEAN_DIR").ok())
                .unwrap_or_else(|| concat!(env!("CARGO_MANIFEST_DIR"), "/../../lean").to_string());
            let lean_dir = std::path::Path::new(&dir);
            let result =
                nocompiler_typed::export::to_lean_linked(&checked, &image, &text, sizes.as_ref())
                    .and_then(|m| nocompiler_typed::prove::certgen_text(lean_dir, &m))
                    .and_then(|m| {
                        if let Some(out) = &l_out {
                            let _ = std::fs::write(out, &m);
                        }
                        nocompiler_typed::prove::run_lean(lean_dir, &m, "prog_meets")
                    });
            match result {
                Ok(ax) if nocompiler_typed::prove::standard(&ax) => {
                    println!("prove: prog_meets (axioms: {})", ax.join(", "))
                }
                Ok(ax) => println!("prove: not proved: nonstandard axioms {}", ax.join(", ")),
                Err(e) => println!("prove: not proved: {e}"),
            }
        }
        for (f, e) in &r.errors {
            println!(
                "{f}:{}: [{}] {}",
                e.line,
                e.rule.as_str(),
                e.msg.lines().next().unwrap_or("")
            );
        }
        return if r.ok() {
            ExitCode::SUCCESS
        } else {
            ExitCode::from(1)
        };
    }
    if args.first().map(String::as_str) != Some("check") || args.len() < 2 {
        eprintln!("{usage}");
        return ExitCode::from(2);
    }
    let file = &args[1];
    let mut ledger_out = None;
    let mut object = None;
    let mut image_file: Option<String> = None;
    let mut prove = false;
    let mut certs = false;
    let mut lean_dir: Option<String> = None;
    let mut states = false;
    let mut natural = true;
    let mut export_lean: Option<String> = None;
    let mut export_json: Option<String> = None;
    let mut i = 2;
    while i < args.len() {
        match args[i].as_str() {
            "--ledger" if i + 1 < args.len() => {
                ledger_out = Some(args[i + 1].clone());
                i += 1;
            }
            "--object" if i + 1 < args.len() => {
                object = Some(args[i + 1].clone());
                i += 1;
            }
            "--image" if i + 1 < args.len() => {
                image_file = Some(args[i + 1].clone());
                i += 1;
            }
            "--prove" => prove = true,
            "--certs" => certs = true,
            "--lean-dir" if i + 1 < args.len() => {
                lean_dir = Some(args[i + 1].clone());
                i += 1;
            }
            "--states" => states = true,
            "--loops"
                if i + 1 < args.len()
                    && (args[i + 1] == "natural" || args[i + 1] == "interval") =>
            {
                natural = args[i + 1] == "natural";
                i += 1;
            }
            "--export-lean" if i + 1 < args.len() => {
                export_lean = Some(args[i + 1].clone());
                i += 1;
            }
            "--export-json" if i + 1 < args.len() => {
                export_json = Some(args[i + 1].clone());
                i += 1;
            }
            _ => {
                eprintln!("{usage}");
                return ExitCode::from(2);
            }
        }
        i += 1;
    }
    let src = match std::fs::read_to_string(file) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("{file}: {e}");
            return ExitCode::from(2);
        }
    };
    let prog = match asm::parse(&src) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("{file}:{}: [syntax] {}", e.line, e.msg);
            return ExitCode::from(2);
        }
    };
    let (ck, mut rep) = check::check_program_opts(
        &prog,
        check::Options {
            record: ledger_out.is_some()
                || states
                || export_lean.is_some()
                || export_json.is_some(),
            natural_loops: natural,
        },
    );
    if let Some(o) = &object {
        match std::fs::read(o) {
            Ok(bytes) => rep
                .global
                .extend(nocompiler_typed::object::compare(&prog, &bytes)),
            Err(e) => {
                eprintln!("{o}: {e}");
                return ExitCode::from(2);
            }
        }
    }
    for e in &rep.global {
        println!("{file}:{}: [{}] {}", e.line, e.rule.as_str(), e.msg);
    }
    for f in &rep.funcs {
        let kind = match f.kind {
            Some(nocompiler_typed::syntax::FnKind::Safe) => "safe",
            Some(nocompiler_typed::syntax::FnKind::Unsafe) => "unsafe",
            Some(nocompiler_typed::syntax::FnKind::Extern) => "extern",
            None => "?",
        };
        match &f.error {
            None if kind == "safe" => println!(
                "{}: checked ({} queries, {} µs)",
                f.name, f.nqueries, f.micros
            ),
            None => println!("{}: {kind} (contract assumed, body not checked)", f.name),
            Some(e) => println!(
                "{}: REJECTED {file}:{}: [{}] {}",
                f.name,
                e.line,
                e.rule.as_str(),
                e.msg
            ),
        }
        if states {
            for (ix, line, s) in &f.states {
                println!("  @{ix} line {line}: {s}");
            }
        }
    }
    let image_bytes = match &image_file {
        None => None,
        Some(p) => match std::fs::read(p) {
            Ok(b) => Some(b),
            Err(e) => {
                eprintln!("{p}: {e}");
                return ExitCode::from(2);
            }
        },
    };
    let image = match &image_bytes {
        None => None,
        Some(b) => match nocompiler_typed::object::symbol_addresses(b) {
            Ok(m) => Some(m),
            Err(e) => {
                eprintln!("{}: {e}", image_file.as_deref().unwrap_or(""));
                return ExitCode::from(2);
            }
        },
    };
    // the linked .text, for the program's theorem (--prove)
    // the linked .text: for local data symbols' addresses, and the program's theorem (--prove)
    // the linked image's symbol sizes: an external callee's code range (P9)
    let sizes = image_bytes
        .as_ref()
        .and_then(|b| nocompiler_typed::object::symbol_sizes(b).ok());
    let text = match &image_bytes {
        Some(b) => match nocompiler_typed::object::text_words(b) {
            Ok(c) => Some(c),
            Err(e) => {
                eprintln!("{}: {e}", image_file.as_deref().unwrap_or(""));
                return ExitCode::from(2);
            }
        },
        None => None,
    };
    let code = if prove { text.clone() } else { None };
    if prove && (image.is_none() || export_lean.is_none()) {
        eprintln!("--prove needs --image and --export-lean");
        return ExitCode::from(2);
    }
    let stem = std::path::Path::new(file)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("prog");
    let module_id: String = stem
        .chars()
        .map(|c| if c.is_alphanumeric() { c } else { '_' })
        .collect();
    let module = format!("NoCompiler.Typed.Export.{module_id}");
    let mut proof = None;
    if let Some(out) = &export_lean {
        let text = nocompiler_typed::export::to_lean_text(
            &prog,
            &ck,
            &rep,
            &module,
            image.as_ref(),
            code.as_ref(),
            text.as_ref(),
            sizes.as_ref(),
        );
        if let Err(e) = std::fs::write(out, &text) {
            eprintln!("{out}: {e}");
            return ExitCode::from(2);
        }
        if prove {
            let partial_fns: Vec<&str> = nocompiler_typed::export::callee_first(&prog, &rep)
                .into_iter()
                .filter(|n| ck.sigs.get(n).is_some_and(|g| g.partial))
                .map(|n| {
                    ck.sigs
                        .get_key_value(&n)
                        .map(|(k, _)| k.as_str())
                        .unwrap_or("")
                })
                .collect();
            let ext = image
                .as_ref()
                .and_then(|img| nocompiler_typed::export::externals(&prog, &ck, &rep, img));
            if ext.is_none() {
                println!(
                    "prove: not attempted (a callee is neither checked here nor declared with a signature and an address)"
                );
            } else if !partial_fns.is_empty() {
                println!(
                    "prove: not attempted (partial functions {}: theorem D covers total programs; I19)",
                    partial_fns.join(", ")
                );
            } else {
                let dir = lean_dir
                    .clone()
                    .or_else(|| std::env::var("NOCOMPILER_LEAN_DIR").ok())
                    .unwrap_or_else(|| {
                        concat!(env!("CARGO_MANIFEST_DIR"), "/../../lean").to_string()
                    });
                let lean_dir = std::path::Path::new(&dir);
                // --certs: the kernel checks recorded certificates, one theorem per point
                let assumes = ext.clone().unwrap_or_default();
                // theorem D, or relative to the external callees' contracts (P9)
                let thm = if assumes.is_empty() {
                    "prog_meets"
                } else {
                    "prog_meets_rel"
                };
                let (proof_text, theorem) = if certs {
                    (
                        nocompiler_typed::prove::certify(lean_dir, &text, &module),
                        thm.to_string(),
                    )
                } else {
                    (Ok(text.clone()), format!("{module}.{thm}"))
                };
                let attempt = match &proof_text {
                    Ok(t) => nocompiler_typed::prove::run_lean(lean_dir, t, &theorem),
                    Err(e) => Err(e.clone()),
                };
                let proof_text = proof_text.unwrap_or_default();
                if certs && !proof_text.is_empty() {
                    // the module the proof is in, next to the export
                    let _ = std::fs::write(format!("{out}.certs.lean"), &proof_text);
                }
                match attempt {
                    Ok(ax) if nocompiler_typed::prove::standard(&ax) => {
                        println!("prove: {theorem} (axioms: {})", ax.join(", "));
                        let order = nocompiler_typed::export::callee_first(&prog, &rep);
                        proof = Some(nocompiler_typed::ledger::Proof {
                            module: if certs {
                                format!("{out}.certs.lean")
                            } else {
                                out.clone()
                            },
                            theorem,
                            axioms: ax,
                            assumes,
                            functions: order
                                .iter()
                                .map(|n| {
                                    (n.clone(), nocompiler_typed::export::callees_in(&prog, n))
                                })
                                .collect(),
                        });
                    }
                    Ok(ax) => println!("prove: not proved: nonstandard axioms {}", ax.join(", ")),
                    Err(e) => println!("prove: not proved: {e}"),
                }
            }
        }
    }
    if let Some(out) = ledger_out {
        let j = ledger::to_json_proof(file, &prog, &ck, &rep, proof.as_ref());
        if let Err(e) = std::fs::write(&out, serde_json::to_string_pretty(&j).unwrap()) {
            eprintln!("{out}: {e}");
            return ExitCode::from(2);
        }
    }
    if let Some(out) = export_json {
        let j = nocompiler_typed::export::to_json_image(&prog, &ck, &rep, image.as_ref());
        if let Err(e) = std::fs::write(&out, serde_json::to_string_pretty(&j).unwrap()) {
            eprintln!("{out}: {e}");
            return ExitCode::from(2);
        }
    }
    if rep.ok() {
        ExitCode::SUCCESS
    } else {
        ExitCode::from(1)
    }
}

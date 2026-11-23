//! `nocompiler-typed check FILE.s [--ledger OUT.json] [--states] [--image LINKED.elf] …`
//!
//! Checks every safe function of a typed assembly file. Exit status 0 when all pass, 1 when
//! one is rejected, 2 on a usage or parse error.

use nocompiler_typed::{asm, check, ledger};
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let usage = "usage: nocompiler-typed link FILE.s... | check FILE.s [--ledger OUT.json] [--states] [--object FILE.o] [--export-lean OUT.lean] [--export-json OUT.json] [--image LINKED.elf [--prove [--lean-dir DIR]]] [--loops natural|interval]";
    if args.first().map(String::as_str) == Some("link") {
        // nocompiler-typed link A.s B.s ... [--loops natural]: the whole program (Theorem D)
        let natural = !args.iter().any(|a| a == "interval");
        let mut files = Vec::new();
        for a in &args[1..] {
            if a == "--loops" || a == "natural" || a == "interval" {
                continue;
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
    let code = match (&image_bytes, prove) {
        (Some(b), true) => match nocompiler_typed::object::text_words(b) {
            Ok(c) => Some(c),
            Err(e) => {
                eprintln!("{}: {e}", image_file.as_deref().unwrap_or(""));
                return ExitCode::from(2);
            }
        },
        _ => None,
    };
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
        let text = nocompiler_typed::export::to_lean_full(
            &prog,
            &ck,
            &rep,
            &module,
            image.as_ref(),
            code.as_ref(),
        );
        if let Err(e) = std::fs::write(out, &text) {
            eprintln!("{out}: {e}");
            return ExitCode::from(2);
        }
        if prove {
            if !nocompiler_typed::export::closed(&prog, &rep) {
                println!("prove: not attempted (a callee is not checked here: theorem D needs every callee)");
            } else {
                let dir = lean_dir
                    .clone()
                    .or_else(|| std::env::var("NOCOMPILER_LEAN_DIR").ok())
                    .unwrap_or_else(|| concat!(env!("CARGO_MANIFEST_DIR"), "/../../lean").to_string());
                let theorem = format!("{module}.prog_meets");
                match nocompiler_typed::prove::run_lean(std::path::Path::new(&dir), &text, &theorem) {
                    Ok(ax) if nocompiler_typed::prove::standard(&ax) => {
                        println!("prove: {theorem} (axioms: {})", ax.join(", "));
                        let order = nocompiler_typed::export::callee_first(&prog, &rep);
                        proof = Some(nocompiler_typed::ledger::Proof {
                            module: out.clone(),
                            theorem,
                            axioms: ax,
                            functions: order
                                .iter()
                                .map(|n| (n.clone(), nocompiler_typed::export::callees_in(&prog, n)))
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

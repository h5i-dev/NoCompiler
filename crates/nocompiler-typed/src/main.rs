//! `nocompiler-typed check FILE.s [--ledger OUT.json] [--states]`
//!
//! Checks every safe function of a typed assembly file. Exit status 0 when all pass, 1 when
//! one is rejected, 2 on a usage or parse error.

use nocompiler_typed::{asm, check, ledger};
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let usage = "usage: nocompiler-typed check FILE.s [--ledger OUT.json] [--states] [--object FILE.o] [--export-lean OUT.lean] [--export-json OUT.json]";
    if args.first().map(String::as_str) != Some("check") || args.len() < 2 {
        eprintln!("{usage}");
        return ExitCode::from(2);
    }
    let file = &args[1];
    let mut ledger_out = None;
    let mut object = None;
    let mut states = false;
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
            "--states" => states = true,
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
    let (ck, mut rep) = check::check_program(
        &prog,
        ledger_out.is_some() || states || export_lean.is_some() || export_json.is_some(),
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
    if let Some(out) = ledger_out {
        let j = ledger::to_json(file, &prog, &ck, &rep);
        if let Err(e) = std::fs::write(&out, serde_json::to_string_pretty(&j).unwrap()) {
            eprintln!("{out}: {e}");
            return ExitCode::from(2);
        }
    }
    if let Some(out) = export_lean {
        let stem = std::path::Path::new(file)
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("prog");
        let module: String = stem
            .chars()
            .map(|c| if c.is_alphanumeric() { c } else { '_' })
            .collect();
        let text = nocompiler_typed::export::to_lean(
            &prog,
            &ck,
            &rep,
            &format!("NoCompiler.Typed.Export.{module}"),
        );
        if let Err(e) = std::fs::write(&out, text) {
            eprintln!("{out}: {e}");
            return ExitCode::from(2);
        }
    }
    if let Some(out) = export_json {
        let j = nocompiler_typed::export::to_json(&prog, &ck, &rep);
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

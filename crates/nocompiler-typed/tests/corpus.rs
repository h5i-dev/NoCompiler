//! Runs every file of tests/typed/corpus and compares each function's verdict with the
//! `#! expect NAME: accept | assumed | external | reject RULE` lines in the file.

use nocompiler_typed::{asm, check};
use std::path::PathBuf;

fn corpus_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tests/typed/corpus")
}

#[test]
fn corpus() {
    let mut files: Vec<PathBuf> = walk(&corpus_dir());
    files.sort();
    assert!(!files.is_empty(), "no corpus files");
    let mut failures = Vec::new();
    let mut n = 0;
    for path in files {
        let src = std::fs::read_to_string(&path).unwrap();
        let name = path
            .strip_prefix(corpus_dir())
            .unwrap()
            .display()
            .to_string();
        let parse_expects = |tag: &str| -> Vec<(String, String)> {
            src.lines()
                .filter_map(|l| l.trim().strip_prefix(tag))
                .filter_map(|l| {
                    l.split_once(':')
                        .map(|(a, b)| (a.trim().to_string(), b.trim().to_string()))
                })
                .collect()
        };
        let expects = parse_expects("#! expect ");
        // the interval rule (S2 as first written, `--loops interval`), kept for comparison
        let expects_interval = parse_expects("#! expect-interval ");
        if expects.is_empty() {
            failures.push(format!("{name}: no '#! expect' line"));
            continue;
        }
        let prog = match asm::parse(&src) {
            Ok(p) => p,
            Err(e) => {
                for (f, want) in &expects {
                    n += 1;
                    if want != "reject syntax" {
                        failures.push(format!(
                            "{name}: {f}: expected {want}, got syntax error line {}: {}",
                            e.line, e.msg
                        ));
                    }
                }
                continue;
            }
        };
        let (ck, rep) = check::check_program(&prog, false);
        if !expects_interval.is_empty() {
            let (_, ri) = check::check_program_opts(
                &prog,
                check::Options {
                    record: false,
                    natural_loops: false,
                },
            );
            for (f, want) in &expects_interval {
                n += 1;
                let got = match ri
                    .funcs
                    .iter()
                    .find(|r| r.name == *f)
                    .and_then(|r| r.error.as_ref())
                {
                    Some(e) => format!("reject {}", e.rule.as_str()),
                    None => "accept".into(),
                };
                if got != *want {
                    failures.push(format!(
                        "{name}: {f} (interval): expected {want}, got {got}"
                    ));
                }
            }
        }
        for (f, want) in &expects {
            n += 1;
            let got = if let Some(g) = rep
                .global
                .iter()
                .find(|g| g.msg.contains(&format!("'{f}'")))
            {
                format!("reject {}", g.rule.as_str())
            } else if let Some(r) = rep.funcs.iter().find(|r| r.name == *f) {
                match (&r.error, r.kind) {
                    (Some(e), _) => format!("reject {}", e.rule.as_str()),
                    (None, Some(nocompiler_typed::syntax::FnKind::Safe)) => "accept".into(),
                    (None, Some(nocompiler_typed::syntax::FnKind::Unsafe)) => "assumed".into(),
                    (None, _) => "external".into(),
                }
            } else {
                match ck.sigs.get(f).map(|s| s.kind) {
                    Some(nocompiler_typed::syntax::FnKind::Unsafe) => "assumed".into(),
                    Some(nocompiler_typed::syntax::FnKind::Extern) => "external".into(),
                    _ => "missing".into(),
                }
            };
            if got != *want {
                let detail = rep
                    .funcs
                    .iter()
                    .find(|r| r.name == *f)
                    .and_then(|r| r.error.as_ref())
                    .map(|e| format!(" (line {}: {})", e.line, e.msg.lines().next().unwrap_or("")))
                    .unwrap_or_default();
                failures.push(format!("{name}: {f}: expected {want}, got {got}{detail}"));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {n} corpus verdicts differ:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

fn walk(d: &std::path::Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    for e in std::fs::read_dir(d).unwrap() {
        let p = e.unwrap().path();
        if p.is_dir() {
            out.extend(walk(&p));
        } else if p.extension().is_some_and(|x| x == "s") {
            out.push(p);
        }
    }
    out
}

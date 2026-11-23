//! The ledger (note, 台帳): per function, its status and the evidence — for a checked safe
//! function, the checker's record of decisions (states, instantiations, solver queries).
//! Status words: `checked` (accepted by this trusted checker, I2 — never `proved`),
//! `rejected`, `assumed` (an unsafe contract), `external` (code outside the machine model).

use crate::asm::Program;
use crate::check::{Checker, Report};
use crate::presburger::Verdict;
use crate::syntax::FnKind;
use serde_json::{Value, json};

pub fn to_json(file: &str, _prog: &Program, ck: &Checker, rep: &Report) -> Value {
    let mut funcs = Vec::new();
    let with_body: std::collections::BTreeSet<&str> =
        rep.funcs.iter().map(|f| f.name.as_str()).collect();
    for f in &rep.funcs {
        let status = match (f.kind, &f.error) {
            (Some(FnKind::Safe), None) => "checked",
            (Some(FnKind::Safe), Some(_)) => "rejected",
            (Some(FnKind::Unsafe), _) => "assumed",
            (Some(FnKind::Extern), _) => "external",
            (None, _) => "unknown",
        };
        funcs.push(json!({
            "name": f.name,
            "status": status,
            "error": f.error.as_ref().map(|e| json!({"rule": e.rule.as_str(), "line": e.line, "message": e.msg})),
            "micros": f.micros,
            "retries": f.retries,
            "states": f.states.iter().map(|(ix, line, s)| json!({"index": ix, "line": line, "state": s})).collect::<Vec<_>>(),
            "instantiations": f.insts.iter().map(|(line, what, s)| json!({"line": line, "at": what, "binding": s})).collect::<Vec<_>>(),
            "queries": f.queries.iter().map(|q| json!({
                "line": q.line, "why": q.why, "micros": q.micros, "hyps": q.hyps, "goal": q.goal,
                "verdict": match q.verdict { Verdict::Proved => "proved", Verdict::Refuted => "refuted", Verdict::Unknown => "unknown" },
            })).collect::<Vec<_>>(),
        }));
    }
    for (name, s) in &ck.sigs {
        if !with_body.contains(name.as_str()) {
            funcs.push(json!({
                "name": name,
                "status": match s.kind { FnKind::Unsafe => "assumed", FnKind::Extern => "external", FnKind::Safe => "declared" },
            }));
        }
    }
    json!({
        "file": file,
        "checker": concat!("nocompiler-typed ", env!("CARGO_PKG_VERSION")),
        "trusted": "the Rust checker and its Presburger procedure are trusted (docs/typed/decisions.md I1, I2)",
        "global_errors": rep.global.iter().map(|e| json!({"rule": e.rule.as_str(), "line": e.line, "message": e.msg})).collect::<Vec<_>>(),
        "functions": funcs,
    })
}

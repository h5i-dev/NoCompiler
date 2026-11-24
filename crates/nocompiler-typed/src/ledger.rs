//! The ledger (note, 台帳): per function, its status and the evidence — for a checked safe
//! function, the checker's record of decisions (states, instantiations, solver queries).
//! Status words: `checked` (accepted by this trusted checker, I2), `proved` (also proved by
//! the Lean checker: a kernel-checked `Prog.check … = true` and theorem D, `Prog.check_sound`,
//! with the standard axioms only; see `Proof`), `rejected`, `assumed` (an unsafe contract),
//! `external` (code outside the machine model).

use crate::asm::Program;
use crate::check::{Checker, Report};
use crate::presburger::Verdict;
use crate::syntax::FnKind;
use serde_json::{Value, json};

/// The Lean evidence for a program (`nocompiler-typed check --prove`): the generated module
/// compiled, and its theorem `prog_meets` (theorem D on the linked image) depends on the
/// standard axioms only.
pub struct Proof {
    /// The Lean module file the theorem is in.
    pub module: String,
    /// The theorem's full name.
    pub theorem: String,
    /// The axioms `#print axioms` reported.
    pub axioms: Vec<String>,
    /// The functions it covers, callee first, with the callees each one was proved with.
    pub functions: Vec<(String, Vec<String>)>,
    /// The external callees whose contracts the theorem assumes (P9); empty for theorem D.
    pub assumes: Vec<String>,
}

pub fn to_json(file: &str, prog: &Program, ck: &Checker, rep: &Report) -> Value {
    to_json_proof(file, prog, ck, rep, None)
}

pub fn to_json_proof(
    file: &str,
    _prog: &Program,
    ck: &Checker,
    rep: &Report,
    proof: Option<&Proof>,
) -> Value {
    let mut funcs = Vec::new();
    let with_body: std::collections::BTreeSet<&str> =
        rep.funcs.iter().map(|f| f.name.as_str()).collect();
    for f in &rep.funcs {
        let status = match (f.kind, &f.error) {
            (Some(FnKind::Safe), None)
                if proof.is_some_and(|p| p.functions.iter().any(|(n, _)| n == &f.name)) =>
            {
                // relative to the external callees' contracts (P9): weaker, and said so
                if proof.is_some_and(|p| !p.assumes.is_empty()) {
                    "proved_assuming"
                } else {
                    "proved"
                }
            }
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
            "evidence": proof.and_then(|p| {
                let (_, callees) = p.functions.iter().find(|(n, _)| n == &f.name)?;
                Some(json!({"lean_module": p.module, "theorem": p.theorem, "axioms": p.axioms, "callees": callees, "assumes": p.assumes}))
            }),
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
        "trusted": "checked: the Rust checker and its Presburger procedure are trusted (docs/typed/decisions.md I1, I2); proved: the Lean kernel, the machine model and the meaning of signatures (Typed/Sem.lean; docs/isa/trust.md)",
        "global_errors": rep.global.iter().map(|e| json!({"rule": e.rule.as_str(), "line": e.line, "message": e.msg})).collect::<Vec<_>>(),
        "functions": funcs,
    })
}

//! Whole-program check (the proof's Theorem D across files): every function the files
//! call is accounted for, signatures agree between the file that defines a function and
//! the files that declare it, and the call graph of the safe functions is acyclic over all
//! files together (S5 per file is not enough: `f: tail g` and `g: tail f` in two files
//! each check on their own).

use crate::asm::{self, Program};
use crate::check::{self, CheckError, Rule};
use crate::isa::{Instr, Target};
use crate::syntax::{FnKind, SSig};
use std::collections::{BTreeMap, BTreeSet};

/// One function of the program and where its evidence comes from.
#[derive(Clone, Debug)]
pub struct Entry {
    pub name: String,
    pub file: String,
    /// `checked` (safe, accepted), `rejected`, `assumed` (unsafe), `external`.
    pub status: &'static str,
}

#[derive(Debug, Default)]
pub struct LinkReport {
    pub functions: Vec<Entry>,
    /// (file, error)
    pub errors: Vec<(String, CheckError)>,
}

impl LinkReport {
    pub fn ok(&self) -> bool {
        self.errors.is_empty() && self.functions.iter().all(|e| e.status != "rejected")
    }
}

pub fn link(files: &[(String, String)], opts: check::Options) -> LinkReport {
    let mut rep = LinkReport::default();
    let mut progs: Vec<(String, Program)> = Vec::new();
    for (name, src) in files {
        match asm::parse(src) {
            Ok(p) => progs.push((name.clone(), p)),
            Err(e) => rep.errors.push((
                name.clone(),
                CheckError {
                    rule: Rule::Syntax,
                    line: e.line,
                    msg: e.msg,
                },
            )),
        }
    }
    // definitions: a function with a body; declarations: a signature without one
    let mut defined: BTreeMap<String, (String, SSig)> = BTreeMap::new();
    let mut declared: Vec<(String, SSig, usize)> = Vec::new();
    let mut calls: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (file, p) in &progs {
        let bodies: BTreeSet<&str> = p.funcs.iter().map(|f| f.name.as_str()).collect();
        for (s, line) in &p.sigs {
            if bodies.contains(s.name.as_str()) {
                if let Some((other, _)) = defined.get(&s.name) {
                    rep.errors.push((
                        file.clone(),
                        CheckError {
                            rule: Rule::Sig,
                            line: *line,
                            msg: format!("'{}' is also defined in {other}", s.name),
                        },
                    ));
                }
                defined.insert(s.name.clone(), (file.clone(), s.clone()));
            } else {
                declared.push((file.clone(), s.clone(), *line));
            }
        }
        for f in &p.funcs {
            let set = calls.entry(f.name.clone()).or_default();
            for pi in &f.instrs {
                if let Instr::Jal {
                    target: Target::Symbol(t),
                    ..
                }
                | Instr::CallPair {
                    target: Target::Symbol(t),
                    ..
                } = &pi.instr
                {
                    set.insert(t.clone());
                }
            }
        }
        let (_, r) = check::check_program_opts(p, opts);
        for g in r.global {
            rep.errors.push((file.clone(), g));
        }
        for f in &r.funcs {
            let status = match (f.kind, &f.error) {
                (Some(FnKind::Safe), None) => "checked",
                (Some(FnKind::Safe), Some(_)) => "rejected",
                (Some(FnKind::Unsafe), _) => "assumed",
                (Some(FnKind::Extern), _) => "external",
                (None, _) => continue,
            };
            rep.functions.push(Entry {
                name: f.name.clone(),
                file: file.clone(),
                status,
            });
            if let Some(e) = &f.error {
                rep.errors.push((file.clone(), e.clone()));
            }
        }
    }
    // declarations must match their definition, or be contracts nobody defines
    for (file, s, line) in &declared {
        match defined.get(&s.name) {
            Some((dfile, d)) => {
                if d != s {
                    rep.errors.push((
                        file.clone(),
                        CheckError {
                            rule: Rule::Sig,
                            line: *line,
                            msg: format!(
                                "the signature of '{}' differs from its definition in {dfile}",
                                s.name
                            ),
                        },
                    ));
                }
            }
            None if s.kind == FnKind::Safe => rep.errors.push((
                file.clone(),
                CheckError {
                    rule: Rule::Sig,
                    line: *line,
                    msg: format!(
                        "safe function '{}' is declared but defined in none of the files",
                        s.name
                    ),
                },
            )),
            None => {
                let status = if s.kind == FnKind::Unsafe {
                    "assumed"
                } else {
                    "external"
                };
                if !rep.functions.iter().any(|e| e.name == s.name) {
                    rep.functions.push(Entry {
                        name: s.name.clone(),
                        file: file.clone(),
                        status,
                    });
                }
            }
        }
    }
    // S5 over the program: no cycle through safe functions
    let safe: BTreeSet<&str> = defined
        .iter()
        .filter(|(_, (_, s))| s.kind == FnKind::Safe)
        .map(|(n, _)| n.as_str())
        .collect();
    for &f in &safe {
        let mut stack: Vec<String> = calls
            .get(f)
            .map(|c| c.iter().cloned().collect())
            .unwrap_or_default();
        let mut seen = BTreeSet::new();
        while let Some(g) = stack.pop() {
            if g == f {
                let file = defined[f].0.clone();
                rep.errors.push((
                    file,
                    CheckError { rule: Rule::Recursion, line: 0, msg: format!("'{f}' is on a cycle of calls between safe functions across the files (S5)") },
                ));
                break;
            }
            if safe.contains(g.as_str()) && seen.insert(g.clone()) {
                stack.extend(calls.get(&g).into_iter().flatten().cloned());
            }
        }
    }
    rep
}

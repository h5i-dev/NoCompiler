//! Export of a checked program for the Lean checker (docs/typed/export.md): signatures,
//! the per-instruction state types (the record), loops, entry-register variables and the
//! variable numbering, as a Lean file of `NoCompiler.Typed` definitions or as JSON.
//!
//! Nothing here is trusted by the Lean side: the instructions it checks come from the
//! decoded image; this is the hint the Lean checker re-checks.

use crate::asm::{Func, Program};
use crate::check::{Cap, Checker, FnExport, Report, State};
use crate::formula::Formula;
use crate::isa::Reg;
use crate::lin::Lin;
use crate::sig::{CapKind, Sig, SigCap};
use crate::syntax::Mode;
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::fmt::Write as _;

fn lean_lin(e: &Lin) -> String {
    let terms: Vec<String> = e
        .terms
        .iter()
        .map(|(v, c)| format!("({c}, {})", v.0))
        .collect();
    format!("⟨{}, [{}]⟩", e.konst, terms.join(", "))
}

fn lean_formula(f: &Formula) -> String {
    match f {
        Formula::True => ".tt".into(),
        Formula::False => ".ff".into(),
        Formula::Ge(e) => format!("(.le ⟨0, []⟩ {})", lean_lin(e)),
        Formula::Eq(e) => format!("(.eq {} ⟨0, []⟩)", lean_lin(e)),
        Formula::Dvd(c, e) => format!("(.dvd {c} {})", lean_lin(e)),
        Formula::And(v) | Formula::Or(v) => {
            let and = matches!(f, Formula::And(_));
            let (op, unit) = if and { (".and", ".tt") } else { (".or", ".ff") };
            let mut it = v.iter().rev();
            match it.next() {
                None => unit.to_string(),
                Some(last) => it.fold(lean_formula(last), |acc, g| {
                    format!("({op} {} {acc})", lean_formula(g))
                }),
            }
        }
        Formula::Not(g) => format!("(.not {})", lean_formula(g)),
    }
}

fn lean_fields(fs: &BTreeMap<i128, Lin>) -> String {
    let v: Vec<String> = fs
        .iter()
        .map(|(k, e)| format!("⟨{k}, {}⟩", lean_lin(e)))
        .collect();
    format!("[{}]", v.join(", "))
}

fn lean_kind(k: &CapKind) -> String {
    match k {
        CapKind::Token(t) => format!(".token {t:?}"),
        CapKind::Bytes {
            base,
            len,
            mode,
            heap,
            fields,
        } => format!(
            ".bytes {{ base := {}, len := {}, mode := {}, heap := {heap}, fields := {} }}",
            lean_lin(base),
            lean_lin(len),
            if *mode == Mode::Rw { ".rw" } else { ".ro" },
            lean_fields(fields)
        ),
    }
}

fn lean_cap(guard: &Formula, kind: &CapKind) -> String {
    format!(
        "{{ guard := {}, kind := {} }}",
        lean_formula(guard),
        lean_kind(kind)
    )
}

fn lean_sigcap(c: &SigCap) -> String {
    lean_cap(&c.guard, &c.kind)
}

fn lean_regs(v: &[(Reg, Lin)]) -> String {
    let x: Vec<String> = v
        .iter()
        .map(|(r, e)| format!("({}, {})", r.0, lean_lin(e)))
        .collect();
    format!("[{}]", x.join(", "))
}

fn conj(fs: &[Formula]) -> Formula {
    Formula::and(fs.to_vec())
}

pub fn lean_sig(s: &Sig) -> String {
    let borrow: Vec<String> = s
        .borrow
        .iter()
        .map(|b| {
            format!(
                "{{ cap := {}, outFields := {} }}",
                lean_sigcap(b),
                lean_fields(&b.exit_fields())
            )
        })
        .collect();
    let take: Vec<String> = s.take.iter().map(lean_sigcap).collect();
    let give: Vec<String> = s.give.iter().map(lean_sigcap).collect();
    let vars = |v: &[crate::lin::Var]| {
        v.iter()
            .map(|x| x.0.to_string())
            .collect::<Vec<_>>()
            .join(", ")
    };
    format!(
        "{{ params := [{}], inRegs := {}, borrow := [{}], take := [{}], pre := {}, outVars := [{}], outRegs := {}, give := [{}], post := {}, stack := {} }}",
        vars(&s.params),
        lean_regs(&s.ins),
        borrow.join(", "),
        take.join(", "),
        lean_formula(&conj(&s.pre)),
        vars(&s.out_vars),
        lean_regs(&s.outs),
        give.join(", "),
        lean_formula(&conj(&s.post)),
        s.stack
    )
}

fn lean_hcap(c: &Cap, borrow_ids: &[u32]) -> String {
    let origin = match borrow_ids.iter().position(|i| *i == c.id) {
        Some(i) => format!("some {i}"),
        None => "none".into(),
    };
    format!(
        "{{ id := {}, cap := {}, origin := {origin} }}",
        c.id,
        lean_cap(&c.guard, &c.kind)
    )
}

fn lean_sty(st: &State, borrow_ids: &[u32]) -> String {
    let regs: Vec<(Reg, Lin)> = Reg::all()
        .skip(1)
        .map(|r| (r, st.regs[r.0 as usize].clone()))
        .collect();
    let facts: Vec<String> = st.facts.iter().map(|(_, f)| lean_formula(f)).collect();
    let caps: Vec<String> = st.caps.iter().map(|c| lean_hcap(c, borrow_ids)).collect();
    format!(
        "{{ regs := {}, facts := [{}], caps := [{}] }}",
        lean_regs(&regs),
        facts.join(", "),
        caps.join(", ")
    )
}

/// The signature as the Lean checker sees it (T on I30): every data symbol's address is a
/// parameter with its range and alignment in `pre`, and each read-only symbol is an
/// ordinary `borrow ℓ_sym ↦ bytes[size] ro {fields}` clause after the signature's own.
pub fn exported_sig(s: &Sig, ck: &Checker) -> Sig {
    let mut e = s.clone();
    if s.syscall {
        return e;
    }
    for (name, v) in &ck.sym_vars {
        e.params.push(*v);
        let (size, align) = ck.sym_info[name];
        let l = Lin::var(*v);
        e.pre.push(Formula::Ge(l.clone()));
        e.pre.push(
            Formula::le(&l.add_const(size).unwrap(), &Lin::konst(crate::lin::TWO64)).unwrap(),
        );
        if align > 1 {
            e.pre.push(Formula::Dvd(align, l));
        }
    }
    for sd in &ck.statics {
        e.borrow.push(SigCap {
            guard: Formula::True,
            kind: CapKind::Bytes {
                base: Lin::var(sd.var),
                len: Lin::konst(sd.size),
                mode: Mode::Ro,
                heap: false,
                fields: sd.fields.clone(),
            },
            out_fields: None,
        });
    }
    e
}

/// Word index of each instruction (a `call`/`tail` pair is two words).
fn word_index(f: &Func) -> Vec<usize> {
    let a0 = f.instrs.first().map(|p| p.addr).unwrap_or(0);
    f.instrs
        .iter()
        .map(|p| ((p.addr - a0) / 4) as usize)
        .collect()
}

fn lean_ident(n: &str) -> String {
    let s: String = n
        .chars()
        .map(|c| {
            if c.is_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect();
    format!("«{s}»")
}

/// A Lean module with one `Sig` per signature and one `Fn` per checked safe function.
pub fn to_lean(prog: &Program, ck: &Checker, rep: &Report, module: &str) -> String {
    let mut o = String::new();
    let _ = writeln!(
        o,
        "-- Generated by nocompiler-typed (docs/typed/export.md). Hints only: the Lean checker"
    );
    let _ = writeln!(
        o,
        "-- re-checks everything against the decoded image. Do not edit."
    );
    let _ = writeln!(o, "import NoCompiler.Typed.Check\n");
    let _ = writeln!(o, "namespace {module}\nopen NoCompiler NoCompiler.Typed\n");
    for (name, s) in &ck.sigs {
        let _ = writeln!(
            o,
            "/-- `{name}` ({:?}{}) -/",
            s.kind,
            if s.partial { ", partial" } else { "" }
        );
        let _ = writeln!(
            o,
            "def sig_{} : Sig :=\n  {}\n",
            lean_ident(name).trim_matches(['«', '»']),
            lean_sig(&exported_sig(s, ck))
        );
    }
    for f in &rep.funcs {
        let Some(ex) = &f.export else { continue };
        let Some(func) = prog.funcs.iter().find(|g| g.name == f.name) else {
            continue;
        };
        let wi = word_index(func);
        let size = func
            .instrs
            .last()
            .map(|p| wi[wi.len() - 1] + p.instr.words())
            .unwrap_or(0);
        let n = lean_ident(&f.name).trim_matches(['«', '»']).to_string();
        let _ = writeln!(
            o,
            "/-- `{}`: section {} offset {:#x} (entry is the symbol's address in the image) -/",
            f.name, func.section, func.instrs[0].addr
        );
        let _ = writeln!(o, "def fn_{n} : Fn where");
        let _ = writeln!(o, "  sig := sig_{n}");
        let _ = writeln!(o, "  entry := {:#x}", func.instrs[0].addr);
        let _ = writeln!(o, "  size := {size}");
        let rv: Vec<String> = ex
            .reg_var
            .iter()
            .map(|(r, v)| format!("({}, {})", r.0, v.0))
            .collect();
        let _ = writeln!(o, "  regVar := [{}]", rv.join(", "));
        let loops: Vec<String> = ex
            .loops
            .iter()
            .map(|(h, l, vs, m)| {
                format!(
                    "{{ head := {}, last := {}, vars := [{}], meas := {} }}",
                    wi[*h],
                    wi[*l],
                    vs.iter()
                        .map(|v| v.0.to_string())
                        .collect::<Vec<_>>()
                        .join(", "),
                    lean_lin(&m.clone().unwrap_or_default())
                )
            })
            .collect();
        let _ = writeln!(o, "  loops := [{}]", loops.join(", "));
        let types: Vec<String> = ex
            .snapshots
            .iter()
            .map(|(ix, st)| format!("    ({}, {})", wi[*ix], lean_sty(st, &ex.borrow_ids)))
            .collect();
        let _ = writeln!(o, "  types := [\n{}]", types.join(",\n"));
        let _ = writeln!(o, "  fresh := {}\n", ex.fresh);
    }
    let _ = writeln!(o, "end {module}");
    o
}

// ---------------------------------------------------------------- JSON

fn j_lin(e: &Lin) -> Value {
    json!({"const": e.konst.to_string(), "terms": e.terms.iter().map(|(v, c)| json!([c.to_string(), v.0])).collect::<Vec<_>>()})
}

fn j_formula(f: &Formula) -> Value {
    match f {
        Formula::True => json!("tt"),
        Formula::False => json!("ff"),
        Formula::Ge(e) => json!({"le": [j_lin(&Lin::default()), j_lin(e)]}),
        Formula::Eq(e) => json!({"eq": [j_lin(e), j_lin(&Lin::default())]}),
        Formula::Dvd(c, e) => json!({"dvd": [c.to_string(), j_lin(e)]}),
        Formula::And(v) => json!({"and": v.iter().map(j_formula).collect::<Vec<_>>()}),
        Formula::Or(v) => json!({"or": v.iter().map(j_formula).collect::<Vec<_>>()}),
        Formula::Not(g) => json!({"not": j_formula(g)}),
    }
}

fn j_kind(k: &CapKind) -> Value {
    match k {
        CapKind::Token(t) => json!({"token": t}),
        CapKind::Bytes {
            base,
            len,
            mode,
            heap,
            fields,
        } => json!({"bytes": {
            "base": j_lin(base), "len": j_lin(len), "mode": if *mode == Mode::Rw { "rw" } else { "ro" }, "heap": heap,
            "fields": fields.iter().map(|(k, e)| json!({"off": k.to_string(), "ty": j_lin(e)})).collect::<Vec<_>>(),
        }}),
    }
}

fn j_regs(v: &[(Reg, Lin)]) -> Value {
    json!(
        v.iter()
            .map(|(r, e)| json!([r.0, j_lin(e)]))
            .collect::<Vec<_>>()
    )
}

fn j_sig(s: &Sig) -> Value {
    let cap = |c: &SigCap| json!({"guard": j_formula(&c.guard), "kind": j_kind(&c.kind)});
    json!({
        "kind": format!("{:?}", s.kind).to_lowercase(),
        "partial": s.partial,
        "params": s.params.iter().map(|v| v.0).collect::<Vec<_>>(),
        "inRegs": j_regs(&s.ins),
        "borrow": s.borrow.iter().map(|b| json!({"cap": cap(b), "outFields": b.exit_fields().iter().map(|(k, e)| json!({"off": k.to_string(), "ty": j_lin(e)})).collect::<Vec<_>>()})).collect::<Vec<_>>(),
        "take": s.take.iter().map(cap).collect::<Vec<_>>(),
        "pre": j_formula(&conj(&s.pre)),
        "outVars": s.out_vars.iter().map(|v| v.0).collect::<Vec<_>>(),
        "outRegs": j_regs(&s.outs),
        "give": s.give.iter().map(cap).collect::<Vec<_>>(),
        "post": j_formula(&conj(&s.post)),
        "stack": s.stack.to_string(),
        "frame": s.frame.as_ref().map(|f| json!({"size": f.size.to_string(), "slots": f.slots.iter().map(|k| k.to_string()).collect::<Vec<_>>(), "addr": f.addr.iter().map(|(o, l)| json!([o.to_string(), l.to_string()])).collect::<Vec<_>>()})),
    })
}

fn j_state(st: &State, ex: &FnExport) -> Value {
    let regs: Vec<(Reg, Lin)> = Reg::all()
        .skip(1)
        .map(|r| (r, st.regs[r.0 as usize].clone()))
        .collect();
    json!({
        "regs": j_regs(&regs),
        "facts": st.facts.iter().map(|(_, f)| j_formula(f)).collect::<Vec<_>>(),
        "slots": st.slots.iter().map(|(k, e)| json!([k.to_string(), j_lin(e)])).collect::<Vec<_>>(),
        "caps": st.caps.iter().map(|c| json!({"id": c.id, "guard": j_formula(&c.guard), "kind": j_kind(&c.kind),
            "origin": ex.borrow_ids.iter().position(|i| *i == c.id)})).collect::<Vec<_>>(),
        "depth": st.depth.to_string(),
    })
}

/// The same content as JSON. Integers that may exceed 2^53 are strings.
pub fn to_json(prog: &Program, ck: &Checker, rep: &Report) -> Value {
    let names: Vec<Value> = (0..ck.names.len())
        .map(|i| json!(ck.names.name(crate::lin::Var(i as u32))))
        .collect();
    let sigs: serde_json::Map<String, Value> = ck
        .sigs
        .iter()
        .map(|(n, s)| (n.clone(), j_sig(&exported_sig(s, ck))))
        .collect();
    let mut fns = Vec::new();
    for f in &rep.funcs {
        let Some(ex) = &f.export else { continue };
        let Some(func) = prog.funcs.iter().find(|g| g.name == f.name) else {
            continue;
        };
        let wi = word_index(func);
        fns.push(json!({
            "name": f.name,
            "section": func.section,
            "offset": func.instrs[0].addr,
            "words": func.instrs.iter().map(|p| p.instr.words()).sum::<usize>(),
            "regVar": ex.reg_var.iter().map(|(r, v)| json!([r.0, v.0])).collect::<Vec<_>>(),
            "loops": ex.loops.iter().map(|(h, l, vs, m)| json!({"head": wi[*h], "last": wi[*l], "vars": vs.iter().map(|v| v.0).collect::<Vec<_>>(), "meas": m.as_ref().map(j_lin)})).collect::<Vec<_>>(),
            "types": ex.snapshots.iter().map(|(ix, st)| json!([wi[*ix], j_state(st, ex)])).collect::<Vec<_>>(),
            "fresh": ex.fresh,
        }));
    }
    json!({"format": "nocompiler-typed export v0", "names": names, "sigs": sigs, "functions": fns})
}

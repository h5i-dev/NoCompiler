//! Export of a checked program for the Lean checker (docs/typed/export.md): signatures,
//! the per-instruction state types (the record), loops, entry-register variables and the
//! variable numbering, as a Lean file of `NoCompiler.Typed` definitions or as JSON.
//!
//! Nothing here is trusted by the Lean side: the instructions it checks come from the
//! decoded image; this is the hint the Lean checker re-checks.

use crate::asm::{Func, Program};
use crate::check::{Cap, Checker, FnExport, Report, State};
use crate::formula::Formula;
use crate::isa::{Instr, Reg, Target};
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

fn lean_sty(st: &State, borrow_ids: &[u32], extra: &[Formula]) -> String {
    let regs: Vec<(Reg, Lin)> = Reg::all()
        .skip(1)
        .map(|r| (r, st.regs[r.0 as usize].clone()))
        .collect();
    let facts: Vec<String> = st
        .facts
        .iter()
        .map(|(_, f)| lean_formula(f))
        .chain(extra.iter().map(lean_formula))
        .collect();
    let caps: Vec<String> = st.caps.iter().map(|c| lean_hcap(c, borrow_ids)).collect();
    let slots: Vec<String> = st
        .slots
        .iter()
        .map(|(k, e)| format!("({k}, {})", lean_lin(e)))
        .collect();
    format!(
        "{{ regs := {}, facts := [{}], caps := [{}], slots := [{}], depth := {} }}",
        lean_regs(&regs),
        facts.join(", "),
        caps.join(", "),
        slots.join(", "),
        st.depth
    )
}

/// The signature as the Lean checker sees it (T on I30): every data symbol's address is a
/// parameter with its range and alignment in `pre`, and each read-only symbol is an
/// ordinary `borrow ℓ_sym ↦ bytes[size] ro {fields}` clause after the signature's own.
pub fn exported_sig(s: &Sig, ck: &Checker) -> Sig {
    exported_sig_at(s, ck, None)
}

/// The equations `ℓ_sym = address` a linked image gives (export.md "Linked image").
fn sym_eqs(ck: &Checker, image: Option<&BTreeMap<String, u64>>) -> Vec<Formula> {
    let Some(img) = image else { return vec![] };
    ck.sym_vars
        .iter()
        .filter_map(|(name, v)| {
            let a = *img.get(name)?;
            Formula::eq(&Lin::var(*v), &Lin::konst(a as i128))
        })
        .collect()
}

/// The linker's split of a pc-relative offset `d` into `%pcrel_hi` (sign-extended, rounded)
/// and `%pcrel_lo` (12-bit signed): `d = (hi << 12) + lo`.
fn hi_lo(d: i128) -> (i128, i128) {
    let hi = (d + 0x800) >> 12;
    (hi, d - (hi << 12))
}

/// The data symbols' variables mapped to their linked addresses.
fn sym_addrs(ck: &Checker, image: Option<&BTreeMap<String, u64>>) -> BTreeMap<crate::lin::Var, Lin> {
    let Some(img) = image else { return BTreeMap::new() };
    ck.sym_vars
        .iter()
        .filter_map(|(name, v)| Some((*v, Lin::konst(*img.get(name)? as i128))))
        .collect()
}

/// A point's type with every data symbol's variable replaced by its address (with
/// `--image`): the Lean checker then finds constant offsets for accesses at `auipc`'s literal
/// addresses, so fields are read (`capSub` compares bases by entailment, and the entry
/// constraint has `ℓ_sym = address`). Expressions that would overflow are kept as they are.
fn pin_state(st: &State, m: &BTreeMap<crate::lin::Var, Lin>) -> State {
    if m.is_empty() {
        return st.clone();
    }
    let l = |e: &Lin| e.subst_all(m).unwrap_or_else(|| e.clone());
    let f = |p: &Formula| p.map_lin(&mut |e| e.subst_all(m)).unwrap_or_else(|| p.clone());
    let mut out = st.clone();
    out.regs = st.regs.iter().map(l).collect();
    out.facts = st.facts.iter().map(|(i, p)| (*i, f(p))).collect();
    out.slots = st.slots.iter().map(|(k, e)| (*k, l(e))).collect();
    for c in &mut out.caps {
        c.guard = f(&c.guard);
        if let CapKind::Bytes {
            base, len, fields, ..
        } = &mut c.kind
        {
            *base = l(base);
            *len = l(len);
            for v in fields.values_mut() {
                *v = l(v);
            }
        }
    }
    out
}

/// `exported_sig`, with the linked addresses of the data symbols in `pre` when an image is
/// given.
pub fn exported_sig_at(s: &Sig, ck: &Checker, image: Option<&BTreeMap<String, u64>>) -> Sig {
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
    e.pre.extend(sym_eqs(ck, image));
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
    to_lean_image(prog, ck, rep, module, None)
}

/// `to_lean` against a linked image: entries and callees at their linked addresses (callees
/// in other files too), and `ℓ_sym = address` in every signature's `pre` and every point's
/// facts, so `auipc`'s literal meets the data capabilities (export.md "Linked image").
pub fn to_lean_image(
    prog: &Program,
    ck: &Checker,
    rep: &Report,
    module: &str,
    image: Option<&BTreeMap<String, u64>>,
) -> String {
    let eqs = sym_eqs(ck, image);
    let pins = sym_addrs(ck, image);
    let addr_of = |name: &str, fallback: Option<u64>| -> Option<u64> {
        match image {
            Some(img) => img.get(name).copied(),
            None => fallback,
        }
    };
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
            lean_sig(&exported_sig_at(s, ck, image))
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
        let entry = addr_of(&f.name, Some(func.instrs[0].addr)).unwrap_or(func.instrs[0].addr);
        let _ = writeln!(o, "  entry := {entry:#x}");
        let _ = writeln!(o, "  size := {size}");
        let rv: Vec<String> = ex
            .reg_var
            .iter()
            .map(|(r, v)| format!("({}, {})", r.0, v.0))
            .collect();
        let _ = writeln!(o, "  regVar := [{}]", rv.join(", "));
        if let Some(fr) = ck.sigs.get(&f.name).and_then(|g| g.frame.as_ref()) {
            let slots: Vec<String> = fr.slots.iter().map(|k| k.to_string()).collect();
            let addr: Vec<String> = fr.addr.iter().map(|(o, l)| format!("({o}, {l})")).collect();
            let _ = writeln!(
                o,
                "  frame := some {{ size := {}, slots := [{}], addr := [{}] }}",
                fr.size,
                slots.join(", "),
                addr.join(", ")
            );
        }
        // callees (T's ask 6): each called function's entry address in the image with the
        // signature it is called at; only callees in the same file and section have a known
        // address before linking (export.md)
        let mut callees: Vec<String> = Vec::new();
        for pi in &func.instrs {
            let (Instr::Jal {
                target: Target::Symbol(s),
                ..
            }
            | Instr::CallPair {
                target: Target::Symbol(s),
                ..
            }) = &pi.instr
            else {
                continue;
            };
            if !ck.sigs.contains_key(s) {
                continue;
            }
            let local = prog
                .funcs
                .iter()
                .find(|g| &g.name == s && g.section == func.section && !g.instrs.is_empty())
                .map(|g| g.instrs[0].addr);
            let Some(a) = addr_of(s, local) else {
                continue;
            };
            let c = format!("({a:#x}, sig_{})", lean_ident(s).trim_matches(['«', '»']));
            if !callees.contains(&c) {
                callees.push(c);
            }
        }
        if !callees.is_empty() {
            let _ = writeln!(o, "  callees := [{}]", callees.join(", "));
        }
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
        // a permutation of all word indices: the checking order, then the rest (unreached
        // points, second words of call pairs) in address order
        let mut tw: Vec<usize> = ex.tau.iter().map(|i| wi[*i]).collect();
        for w in 0..size {
            if !tw.contains(&w) {
                tw.push(w);
            }
        }
        let tau: Vec<String> = tw.iter().map(|w| w.to_string()).collect();
        let _ = writeln!(o, "  tau := [{}]", tau.join(", "));
        // with --image: each auipc %pcrel_hi's L is the linker's %pcrel_lo value, so the
        // register is the exact literal pc + (hi << 12) the Lean checker computes (T's ask b)
        let mut fpins = pins.clone();
        if let Some(img) = image {
            for (ix, l, sym) in &ex.lo_vars {
                if let Some(s_addr) = img.get(sym) {
                    let pc = entry as i128 + 4 * wi[*ix] as i128;
                    let (_, lo) = hi_lo(*s_addr as i128 - pc);
                    fpins.insert(*l, Lin::konst(lo));
                }
            }
        }
        let mut types: Vec<String> = Vec::new();
        for (ix, st) in &ex.snapshots {
            let pst = pin_state(st, &fpins);
            types.push(format!("    ({}, {})", wi[*ix], lean_sty(&pst, &ex.borrow_ids, &eqs)));
            // a call pair is two words: the second one's type is the first one's with the
            // temporary holding auipc's exact value (T's ask a, I21)
            if let Instr::CallPair {
                tmp,
                target: Target::Symbol(g),
                ..
            } = &func.instrs[*ix].instr
            {
                let local = prog
                    .funcs
                    .iter()
                    .find(|h| &h.name == g && h.section == func.section && !h.instrs.is_empty())
                    .map(|h| h.instrs[0].addr);
                if let Some(ga) = addr_of(g, local) {
                    let pc = entry as i128 + 4 * wi[*ix] as i128;
                    let (hi, _) = hi_lo(ga as i128 - pc);
                    let lit = (pc + (hi << 12)).rem_euclid(1i128 << 64);
                    let mut st2 = pst.clone();
                    st2.regs[tmp.0 as usize] = Lin::konst(lit);
                    types.push(format!(
                        "    ({}, {})",
                        wi[*ix] + 1,
                        lean_sty(&st2, &ex.borrow_ids, &eqs)
                    ));
                }
            }
        }
        let _ = writeln!(o, "  types := [\n{}]", types.join(",\n"));
        let _ = writeln!(o, "  fresh := {}\n", ex.fresh);
        // θ per edge into an annotated point: (source word or none for the entry, target
        // word, [(variable, expression)]) — a hint, re-checked (export.md)
        let th: Vec<String> = ex
            .thetas
            .iter()
            .map(|(src, t, m)| {
                let src = if *src == usize::MAX {
                    "none".to_string()
                } else {
                    format!("some {}", wi[*src])
                };
                let b: Vec<String> = m
                    .iter()
                    .map(|(v, e)| format!("({}, {})", v.0, lean_lin(e)))
                    .collect();
                format!("({src}, {}, [{}])", wi[*t], b.join(", "))
            })
            .collect();
        let _ = writeln!(
            o,
            "def theta_{n} : List (Option Nat × Nat × List (Var × IExpr)) := [\n  {}]\n",
            th.join(",\n  ")
        );
    }
    if image.is_some() {
        // theorem D (T's ask 8): the exported functions, each after the ones it calls (S5)
        let exported: Vec<&str> = rep
            .funcs
            .iter()
            .filter(|f| f.export.is_some())
            .map(|f| f.name.as_str())
            .collect();
        let calls = |name: &str| -> Vec<String> {
            prog.funcs
                .iter()
                .find(|g| g.name == name)
                .map(|g| {
                    g.instrs
                        .iter()
                        .filter_map(|pi| match &pi.instr {
                            Instr::Jal {
                                target: Target::Symbol(s),
                                ..
                            }
                            | Instr::CallPair {
                                target: Target::Symbol(s),
                                ..
                            } => Some(s.clone()),
                            _ => None,
                        })
                        .collect()
                })
                .unwrap_or_default()
        };
        let mut order: Vec<&str> = Vec::new();
        while order.len() < exported.len() {
            let next = exported.iter().find(|n| {
                !order.contains(n)
                    && calls(n)
                        .iter()
                        .all(|c| !exported.contains(&c.as_str()) || order.contains(&c.as_str()))
            });
            match next {
                Some(n) => order.push(n),
                // a cycle (S5 rejects it): keep the rest in file order
                None => order.extend(exported.iter().filter(|n| !order.contains(n)).collect::<Vec<_>>()),
            }
        }
        let names: Vec<String> = order
            .iter()
            .map(|n| format!("fn_{}", lean_ident(n).trim_matches(['«', '»'])))
            .collect();
        let _ = writeln!(o, "/-- Callee-first (S5): `Prog.check code [] prog`. -/");
        let _ = writeln!(o, "def prog : List Fn := [{}]\n", names.join(", "));
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

fn j_state(st: &State, ex: &FnExport, extra: &[Formula]) -> Value {
    let regs: Vec<(Reg, Lin)> = Reg::all()
        .skip(1)
        .map(|r| (r, st.regs[r.0 as usize].clone()))
        .collect();
    json!({
        "regs": j_regs(&regs),
        "facts": st.facts.iter().map(|(_, f)| j_formula(f)).chain(extra.iter().map(j_formula)).collect::<Vec<_>>(),
        "slots": st.slots.iter().map(|(k, e)| json!([k.to_string(), j_lin(e)])).collect::<Vec<_>>(),
        "caps": st.caps.iter().map(|c| json!({"id": c.id, "guard": j_formula(&c.guard), "kind": j_kind(&c.kind),
            "origin": ex.borrow_ids.iter().position(|i| *i == c.id)})).collect::<Vec<_>>(),
        "depth": st.depth.to_string(),
    })
}

/// The same content as JSON. Integers that may exceed 2^53 are strings.
pub fn to_json(prog: &Program, ck: &Checker, rep: &Report) -> Value {
    to_json_image(prog, ck, rep, None)
}

/// `to_json` against a linked image, as `to_lean_image`: `entry` (the linked address, or
/// null), `ℓ_sym = address` in the signatures and every point's facts.
pub fn to_json_image(
    prog: &Program,
    ck: &Checker,
    rep: &Report,
    image: Option<&BTreeMap<String, u64>>,
) -> Value {
    let eqs = sym_eqs(ck, image);
    let names: Vec<Value> = (0..ck.names.len())
        .map(|i| json!(ck.names.name(crate::lin::Var(i as u32))))
        .collect();
    let sigs: serde_json::Map<String, Value> = ck
        .sigs
        .iter()
        .map(|(n, s)| (n.clone(), j_sig(&exported_sig_at(s, ck, image))))
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
            "entry": image.and_then(|img| img.get(&f.name)),
            "words": func.instrs.iter().map(|p| p.instr.words()).sum::<usize>(),
            "regVar": ex.reg_var.iter().map(|(r, v)| json!([r.0, v.0])).collect::<Vec<_>>(),
            "loops": ex.loops.iter().map(|(h, l, vs, m)| json!({"head": wi[*h], "last": wi[*l], "vars": vs.iter().map(|v| v.0).collect::<Vec<_>>(), "meas": m.as_ref().map(j_lin)})).collect::<Vec<_>>(),
            "types": ex.snapshots.iter().map(|(ix, st)| json!([wi[*ix], j_state(st, ex, &eqs)])).collect::<Vec<_>>(),
            "thetas": ex.thetas.iter().map(|(src, t, m)| json!({
                "from": if *src == usize::MAX { Value::Null } else { json!(wi[*src]) },
                "to": wi[*t],
                "theta": m.iter().map(|(v, e)| json!([v.0, j_lin(e)])).collect::<Vec<_>>(),
            })).collect::<Vec<_>>(),
            "tau": ex.tau.iter().map(|i| wi[*i]).collect::<Vec<_>>(),
            "fresh": ex.fresh,
        }));
    }
    json!({"format": "nocompiler-typed export v0", "names": names, "sigs": sigs, "functions": fns})
}

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
        "{{ params := [{}], inRegs := {}, borrow := [{}], take := [{}], pre := {}, outVars := [{}], outRegs := {}, give := [{}], post := {}, stack := {}{} }}",
        vars(&s.params),
        lean_regs(&s.ins),
        borrow.join(", "),
        take.join(", "),
        lean_formula(&conj(&s.pre)),
        vars(&s.out_vars),
        lean_regs(&s.outs),
        give.join(", "),
        lean_formula(&conj(&s.post)),
        s.stack,
        // I19: printed only when set, so total signatures read as before
        if s.partial { ", isPartial := true" } else { "" }
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
    sym_eqs_used(ck, image, None)
}

fn sym_eqs_used(
    ck: &Checker,
    image: Option<&BTreeMap<String, u64>>,
    used: Option<&std::collections::BTreeSet<String>>,
) -> Vec<Formula> {
    let Some(img) = image else { return vec![] };
    ck.sym_vars
        .iter()
        .filter(|(name, _)| used.is_none_or(|u| u.contains(name.as_str())))
        .filter_map(|(name, v)| {
            let a = *img.get(name)?;
            Formula::eq(&Lin::var(*v), &Lin::konst(a as i128))
        })
        .collect()
}

/// Canonical variable numbering (decisions.md P7, step 1): a signature's parameters 0.. in
/// order, then its `out` variables, then every other variable below `fresh` in increasing
/// order. A bijection of `[0, n)`, so the Lean checker's bounds (`< fresh`) are kept; the same
/// signature text gets the same numbering in every file and function.
fn canon(sig: &Sig, fresh: u32) -> BTreeMap<crate::lin::Var, crate::lin::Var> {
    use crate::lin::Var;
    let mut top = fresh;
    for v in sig.params.iter().chain(&sig.out_vars).chain(sig.src_names.keys()) {
        top = top.max(v.0 + 1);
    }
    let mut order: Vec<Var> = Vec::new();
    for v in sig.params.iter().chain(&sig.out_vars) {
        if !order.contains(v) {
            order.push(*v);
        }
    }
    for i in 0..top {
        if !order.contains(&Var(i)) {
            order.push(Var(i));
        }
    }
    order
        .into_iter()
        .enumerate()
        .map(|(new, old)| (old, Var(new as u32)))
        .collect()
}

fn as_lins(m: &BTreeMap<crate::lin::Var, crate::lin::Var>) -> BTreeMap<crate::lin::Var, Lin> {
    m.iter().map(|(a, b)| (*a, Lin::var(*b))).collect()
}

fn ren_lin(e: &Lin, m: &BTreeMap<crate::lin::Var, Lin>) -> Lin {
    e.subst_all(m).unwrap_or_else(|| e.clone())
}

fn ren_formula(f: &Formula, m: &BTreeMap<crate::lin::Var, Lin>) -> Formula {
    f.map_lin(&mut |e| e.subst_all(m)).unwrap_or_else(|| f.clone())
}

fn ren_cap(c: &SigCap, m: &BTreeMap<crate::lin::Var, Lin>) -> SigCap {
    let kind = match &c.kind {
        CapKind::Bytes { base, len, mode, heap, fields } => CapKind::Bytes {
            base: ren_lin(base, m),
            len: ren_lin(len, m),
            mode: *mode,
            heap: *heap,
            fields: fields.iter().map(|(k, e)| (*k, ren_lin(e, m))).collect(),
        },
        k => k.clone(),
    };
    SigCap {
        guard: ren_formula(&c.guard, m),
        kind,
        out_fields: c
            .out_fields
            .as_ref()
            .map(|f| f.iter().map(|(k, e)| (*k, ren_lin(e, m))).collect()),
    }
}

/// A signature in another numbering.
fn rename_sig(s: &Sig, vm: &BTreeMap<crate::lin::Var, crate::lin::Var>) -> Sig {
    let m = as_lins(vm);
    let v = |x: &crate::lin::Var| *vm.get(x).unwrap_or(x);
    let mut e = s.clone();
    e.params = s.params.iter().map(v).collect();
    e.out_vars = s.out_vars.iter().map(v).collect();
    e.ins = s.ins.iter().map(|(r, l)| (*r, ren_lin(l, &m))).collect();
    e.outs = s.outs.iter().map(|(r, l)| (*r, ren_lin(l, &m))).collect();
    e.pre = s.pre.iter().map(|f| ren_formula(f, &m)).collect();
    e.post = s.post.iter().map(|f| ren_formula(f, &m)).collect();
    e.borrow = s.borrow.iter().map(|c| ren_cap(c, &m)).collect();
    e.take = s.take.iter().map(|c| ren_cap(c, &m)).collect();
    e.give = s.give.iter().map(|c| ren_cap(c, &m)).collect();
    e
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
    exported_sig_used(s, ck, image, None)
}

/// `exported_sig_at`, listing only the data symbols in `used` (decisions.md P7 step 2) when it
/// is given: a signature then depends on what its function (and its callees) touch, not on
/// the file it is in.
pub fn exported_sig_used(
    s: &Sig,
    ck: &Checker,
    image: Option<&BTreeMap<String, u64>>,
    used: Option<&std::collections::BTreeSet<String>>,
) -> Sig {
    let mut e = s.clone();
    if s.syscall {
        return e;
    }
    let keep = |name: &str| used.is_none_or(|u| u.contains(name));
    for (name, v) in &ck.sym_vars {
        if !keep(name) {
            continue;
        }
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
    for sd in ck.statics.iter().filter(|sd| keep(&sd.name)) {
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
    e.pre.extend(sym_eqs_used(ck, image, used));
    e
}

/// The data symbols each function uses (P7 step 2): those its own `auipc %pcrel_hi`
/// instructions name, those whose address its signature mentions, and its callees', by a
/// fixpoint over the call graph (finite: S5, no recursion; a cycle would just stop growing).
pub fn used_syms(
    prog: &Program,
    ck: &Checker,
    rep: &Report,
) -> BTreeMap<String, std::collections::BTreeSet<String>> {
    use std::collections::BTreeSet;
    let by_var: BTreeMap<crate::lin::Var, &str> =
        ck.sym_vars.iter().map(|(n, v)| (*v, n.as_str())).collect();
    let mut used: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (name, s) in &ck.sigs {
        let mut vs = BTreeSet::new();
        let mut lin_vars = |l: &Lin| vs.extend(l.vars());
        for (_, l) in s.ins.iter().chain(&s.outs) {
            lin_vars(l);
        }
        for c in s.borrow.iter().chain(&s.take).chain(&s.give) {
            if let CapKind::Bytes { base, len, fields, .. } = &c.kind {
                lin_vars(base);
                lin_vars(len);
                fields.values().for_each(&mut lin_vars);
            }
        }
        let mut fv = BTreeSet::new();
        for f in s.pre.iter().chain(&s.post) {
            f.vars(&mut fv);
        }
        vs.extend(fv);
        let mut u: BTreeSet<String> =
            vs.iter().filter_map(|v| by_var.get(v).map(|n| n.to_string())).collect();
        if let Some(fr) = rep.funcs.iter().find(|f| &f.name == name) {
            if let Some(ex) = &fr.export {
                u.extend(ex.lo_vars.iter().map(|(_, _, sym)| sym.clone()));
            }
        }
        used.insert(name.clone(), u);
    }
    loop {
        let mut changed = false;
        for name in ck.sigs.keys() {
            let add: BTreeSet<String> = callees_of(prog, name)
                .iter()
                .filter_map(|g| used.get(g).cloned())
                .flatten()
                .collect();
            let e = used.entry(name.clone()).or_default();
            let before = e.len();
            e.extend(add);
            changed |= e.len() != before;
        }
        if !changed {
            break;
        }
    }
    used
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
    to_lean_full(prog, ck, rep, module, image, None)
}

/// The functions a call instruction of `name` names.
fn callees_of(prog: &Program, name: &str) -> Vec<String> {
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
}

/// The functions `name` calls, deduplicated (the ledger's evidence).
pub fn callees_in(prog: &Program, name: &str) -> Vec<String> {
    let mut v = callees_of(prog, name);
    v.dedup();
    v
}

/// The exported (checked) functions, each after the ones it calls (S5 order).
pub fn callee_first(prog: &Program, rep: &Report) -> Vec<String> {
    let exported: Vec<&str> = rep
        .funcs
        .iter()
        .filter(|f| f.export.is_some())
        .map(|f| f.name.as_str())
        .collect();
    let mut order: Vec<&str> = Vec::new();
    while order.len() < exported.len() {
        let next = exported.iter().find(|n| {
            !order.contains(n)
                && callees_of(prog, n)
                    .iter()
                    .all(|c| !exported.contains(&c.as_str()) || order.contains(&c.as_str()))
        });
        match next {
            Some(n) => order.push(n),
            // a cycle (S5 rejects it): keep the rest in file order
            None => order.extend(exported.iter().filter(|n| !order.contains(n)).collect::<Vec<_>>()),
        }
    }
    order.into_iter().map(String::from).collect()
}

/// Every callee of every exported function is exported too: theorem D needs no external
/// functions (`Prog.check code [] prog`).
pub fn closed(prog: &Program, rep: &Report) -> bool {
    let ex: Vec<&str> = rep
        .funcs
        .iter()
        .filter(|f| f.export.is_some())
        .map(|f| f.name.as_str())
        .collect();
    !ex.is_empty() && ex.iter().all(|n| callees_of(prog, n).iter().all(|c| ex.contains(&c.as_str())))
}

/// `to_lean_image`, and with the linked `.text` (`code`) for a closed program, the program's
/// theorem: `prog_checked` (by the kernel) and `prog_meets` (theorem D, `Prog.check_sound_closed`).
/// The ledger records `proved` when this module compiles (main.rs `--prove`).
pub fn to_lean_full(
    prog: &Program,
    ck: &Checker,
    rep: &Report,
    module: &str,
    image: Option<&BTreeMap<String, u64>>,
    code: Option<&(u64, Vec<u32>)>,
) -> String {
    to_lean_text(prog, ck, rep, module, image, code, code)
}

/// The addresses of the data symbols the linked image's symbol table does not name
/// (assembler-local `.L` labels such as clang's constant pools), from the code itself: the
/// linked `auipc` and its `%pcrel_lo` instruction compute exactly the symbol's address.
fn recover_sym_addrs(
    prog: &Program,
    rep: &Report,
    image: &BTreeMap<String, u64>,
    text: &(u64, Vec<u32>),
) -> BTreeMap<String, u64> {
    let mut img = image.clone();
    let (base, words) = text;
    let word_at = |a: u64| -> Option<u32> {
        let off = a.checked_sub(*base)?;
        words.get((off / 4) as usize).copied()
    };
    for f in &rep.funcs {
        let Some(ex) = &f.export else { continue };
        let Some(func) = prog.funcs.iter().find(|g| g.name == f.name) else { continue };
        let Some(entry) = image.get(&f.name).copied() else { continue };
        let wi = word_index(func);
        for (ix, _, sym) in &ex.lo_vars {
            if img.contains_key(sym) {
                continue;
            }
            let Some(j) = func.instrs.iter().position(|pi| {
                matches!(&pi.reloc, Some(crate::asm::Reloc::PcrelLo(l)) if func.labels.get(l) == Some(ix))
            }) else {
                continue;
            };
            let pc = entry + 4 * wi[*ix] as u64;
            let (Some(wa), Some(wl)) = (word_at(pc), word_at(entry + 4 * wi[j] as u64)) else {
                continue;
            };
            let hi = (wa & 0xffff_f000) as i32 as i64;
            let lo = if wl & 0x7f == 0x23 {
                // S-type (stores)
                ((((wl as i32) >> 25) << 5) | ((wl >> 7) & 0x1f) as i32) as i64
            } else {
                ((wl as i32) >> 20) as i64
            };
            img.insert(sym.clone(), (pc as i64).wrapping_add(hi).wrapping_add(lo) as u64);
        }
    }
    img
}

/// `to_lean_full` with the linked `.text` given separately (`text`, for the addresses of
/// local data symbols) from whether the program's theorem is emitted (`code`).
pub fn to_lean_text(
    prog: &Program,
    ck: &Checker,
    rep: &Report,
    module: &str,
    image: Option<&BTreeMap<String, u64>>,
    code: Option<&(u64, Vec<u32>)>,
    text: Option<&(u64, Vec<u32>)>,
) -> String {
    let recovered = match (image, text) {
        (Some(img), Some(t)) => Some(recover_sym_addrs(prog, rep, img, t)),
        _ => None,
    };
    let image = recovered.as_ref().or(image);
    let pins = sym_addrs(ck, image);
    // P7 step 2: each signature lists only the data symbols its function uses
    let usedm = used_syms(prog, ck, rep);
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
    let with_thm = image.is_some() && code.is_some() && closed(prog, rep);
    let _ = writeln!(
        o,
        "import {}\n",
        if with_thm { "NoCompiler.Typed.Sound.Prog" } else { "NoCompiler.Typed.Check" }
    );
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
            {
                let es = exported_sig_used(s, ck, image, usedm.get(name));
                lean_sig(&rename_sig(&es, &canon(&es, 0)))
            }
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
        // the record in the signature's canonical numbering (P7)
        let fused = usedm.get(&f.name);
        let vm = ck
            .sigs
            .get(&f.name)
            .map(|g| canon(&exported_sig_used(g, ck, image, fused), ex.fresh))
            .unwrap_or_default();
        let lm = as_lins(&vm);
        let vv = |x: &crate::lin::Var| vm.get(x).unwrap_or(x).0;
        let feqs: Vec<Formula> = sym_eqs_used(ck, image, fused)
            .iter()
            .map(|f| ren_formula(f, &lm))
            .collect();
        // the data symbols this function does not use: their capabilities and facts go
        let n_own = ex.borrow_ids.len().saturating_sub(ck.statics.len());
        let unused = |name: &str| fused.is_some_and(|u| !u.contains(name));
        let drop_ids: Vec<u32> = ck
            .statics
            .iter()
            .enumerate()
            .filter(|(_, sd)| unused(&sd.name))
            .filter_map(|(i, _)| ex.borrow_ids.get(n_own + i).copied())
            .collect();
        let drop_vars: std::collections::BTreeSet<crate::lin::Var> = ck
            .sym_vars
            .iter()
            .filter(|(n, _)| unused(n))
            .map(|(_, v)| *v)
            .collect();
        let bids: Vec<u32> =
            ex.borrow_ids.iter().copied().filter(|i| !drop_ids.contains(i)).collect();
        let trim = |st: &State| -> State {
            let mut t = st.clone();
            t.caps.retain(|c| !drop_ids.contains(&c.id));
            t.facts.retain(|(_, f)| {
                let mut vs = std::collections::BTreeSet::new();
                f.vars(&mut vs);
                vs.is_disjoint(&drop_vars)
            });
            t
        };
        // the point types go in their own defs, inserted here once they are known (T: one
        // long `types := [...]` literal elaborates slowly and overflows the recursion depth)
        let fn_start = o.len();
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
            .map(|(r, v)| format!("({}, {})", r.0, vv(v)))
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
        // a permutation of all word indices: the checking order, then the rest (unreached
        // points, second words of call pairs) in address order
        // a call pair's second word comes right after its first (one step in the order)
        let mut tw: Vec<usize> = Vec::new();
        for i in &ex.tau {
            tw.push(wi[*i]);
            if matches!(func.instrs[*i].instr, Instr::CallPair { .. }) {
                tw.push(wi[*i] + 1);
            }
        }
        for w in 0..size {
            if !tw.contains(&w) {
                tw.push(w);
            }
        }
        let tau: Vec<String> = tw.iter().map(|w| w.to_string()).collect();
        let _ = writeln!(o, "  tau := [{}]", tau.join(", "));
        // sorted by the head's position in τ (Lean's `Fn.pos`): structOk wants them in that order
        let pos = |w: usize| tw.iter().position(|&x| x == w).unwrap_or(w);
        let mut lps: Vec<_> = ex.loops.iter().collect();
        lps.sort_by_key(|(h, _, _, _)| pos(wi[*h]));
        let loops: Vec<String> = lps
            .into_iter()
            .map(|(h, l, vs, m)| {
                format!(
                    "{{ head := {}, last := {}, vars := [{}], meas := {} }}",
                    wi[*h],
                    wi[*l],
                    vs.iter()
                        .map(|v| vv(v).to_string())
                        .collect::<Vec<_>>()
                        .join(", "),
                    lean_lin(&ren_lin(&m.clone().unwrap_or_default(), &lm))
                )
            })
            .collect();
        let _ = writeln!(o, "  loops := [{}]", loops.join(", "));
        if !ex.xor_bits.is_empty() {
            let kb: Vec<String> = ex.xor_bits.iter().map(|k| k.to_string()).collect();
            let _ = writeln!(o, "  xorBits := [{}]", kb.join(", "));
        }
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
        // the pins first (on the old variables), the renumbering for the rest
        let comp: BTreeMap<crate::lin::Var, Lin> = vm
            .iter()
            .map(|(old, new)| (*old, fpins.get(old).cloned().unwrap_or_else(|| Lin::var(*new))))
            .collect();
        let mut types: Vec<(usize, String)> = Vec::new();
        for (ix, st) in &ex.snapshots {
            let pst = pin_state(&trim(st), if vm.is_empty() { &fpins } else { &comp });
            types.push((wi[*ix], lean_sty(&pst, &bids, &feqs)));
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
                    types.push((wi[*ix] + 1, lean_sty(&st2, &bids, &feqs)));
                }
            }
        }
        let mut defs = String::new();
        for (w, t) in &types {
            let _ = writeln!(defs, "def ty_{n}_{w} : STy := {t}\n");
        }
        o.insert_str(fn_start, &defs);
        let refs: Vec<String> = types.iter().map(|(w, _)| format!("({w}, ty_{n}_{w})")).collect();
        let _ = writeln!(o, "  types := [{}]", refs.join(", "));
        // the renumbering is a bijection of [0, vm.len()), which may exceed ex.fresh
        let _ = writeln!(o, "  fresh := {}\n", ex.fresh.max(vm.len() as u32));
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
                    .map(|(v, e)| format!("({}, {})", vv(v), lean_lin(&ren_lin(e, &lm))))
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
        let order = callee_first(prog, rep);
        let names: Vec<String> = order
            .iter()
            .map(|n| format!("fn_{}", lean_ident(n).trim_matches(['«', '»'])))
            .collect();
        let _ = writeln!(o, "/-- Callee-first (S5): `Prog.check code [] prog`. -/");
        let _ = writeln!(o, "def prog : List Fn := [{}]\n", names.join(", "));
        if let (Some((base, words)), true) = (code, closed(prog, rep)) {
            // the ledger's evidence (theorem D): the linked image and the program's theorem
            let ws: Vec<String> = words.iter().map(|w| format!("0x{w:08x}#32")).collect();
            let _ = writeln!(o, "/-- The linked `.text`. -/");
            let _ = writeln!(o, "def code : Code := ⟨0x{base:x}#64, #[{}]⟩\n", ws.join(", "));
            // one kernel check per function (each needs a few GB), then the program's
            for n in &names {
                let _ = writeln!(
                    o,
                    "set_option maxRecDepth 100000 in\ntheorem chk_{} : {n}.check code = true := by decide +kernel\n",
                    n.trim_start_matches("fn_")
                );
            }
            let chks: Vec<String> = names
                .iter()
                .map(|n| format!("chk_{}", n.trim_start_matches("fn_")))
                .collect();
            let _ = writeln!(
                o,
                "set_option maxRecDepth 100000 in\n/-- Theorem D's check, by the kernel. -/\ntheorem prog_checked : Prog.check code [] prog = true := by\n  simp only [prog, Prog.check, {}, Bool.true_and]\n  decide +kernel\n",
                chks.join(", ")
            );
            let _ = writeln!(o, "/-- Every function of the program meets its signature (⟦σ⟧, total), for every meaning of tokens. -/");
            let _ = writeln!(o, "theorem prog_meets (T : TokEnv) :\n    ∀ e ∈ Prog.env [] prog, Meets code e.2.2 e.1 T e.2.1 :=\n  Prog.check_sound_closed prog_checked\n");
        }
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
            "tau": ex.tau.iter().flat_map(|i| {
                let pair = matches!(func.instrs[*i].instr, Instr::CallPair { .. });
                std::iter::once(wi[*i]).chain(pair.then_some(wi[*i] + 1))
            }).collect::<Vec<_>>(),
            "fresh": ex.fresh,
        }));
    }
    json!({"format": "nocompiler-typed export v0", "names": names, "sigs": sigs, "functions": fns})
}

#[cfg(test)]
mod tests {
    use super::hi_lo;

    /// The linker's %pcrel_hi/%pcrel_lo split: recombines, `lo` is a 12-bit signed immediate.
    #[test]
    fn hi_lo_splits_like_the_linker() {
        let mut d: i128 = -(1 << 31);
        while d < (1 << 31) - 1 {
            for e in [d, d + 0x7ff, d + 0x800, d + 0x801, -d - 1] {
                let (hi, lo) = hi_lo(e);
                assert_eq!((hi << 12) + lo, e, "d = {e}");
                assert!((-2048..2048).contains(&lo), "d = {e}: lo = {lo}");
            }
            d += 0x12345;
        }
    }
}

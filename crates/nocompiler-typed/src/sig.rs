//! Signatures with their variables resolved (the note's 署名), and the conversion from
//! the syntax tree.

use crate::formula::Formula;
use crate::isa::Reg;
use crate::lin::{Lin, Names, TWO64, Var};
use crate::syntax::{
    FnKind, Mode, RangeKind, SCap, SCapKind, SField, SFormula, SLin, SRegTy, SSig,
};
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq)]
pub enum CapKind {
    Bytes {
        base: Lin,
        len: Lin,
        mode: Mode,
        heap: bool,
        fields: BTreeMap<i128, Lin>,
    },
    Token(String),
}

#[derive(Clone, Debug, PartialEq)]
pub struct SigCap {
    pub guard: Formula,
    pub kind: CapKind,
    /// For a borrow: the fields on exit (I6). `None`: the entry fields.
    pub out_fields: Option<BTreeMap<i128, Lin>>,
}

impl SigCap {
    pub fn exit_fields(&self) -> BTreeMap<i128, Lin> {
        match (&self.out_fields, &self.kind) {
            (Some(f), _) => f.clone(),
            (None, CapKind::Bytes { fields, .. }) => fields.clone(),
            _ => BTreeMap::new(),
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Frame {
    pub size: i128,
    pub slots: Vec<i128>,
    /// (offset, length) from the lowered `sp`.
    pub addr: Vec<(i128, i128)>,
}

#[derive(Clone, Debug)]
pub struct Sig {
    pub name: String,
    pub kind: FnKind,
    pub partial: bool,
    pub params: Vec<Var>,
    pub ins: Vec<(Reg, Lin)>,
    pub borrow: Vec<SigCap>,
    pub take: Vec<SigCap>,
    pub pre: Vec<Formula>,
    pub out_vars: Vec<Var>,
    pub outs: Vec<(Reg, Lin)>,
    pub give: Vec<SigCap>,
    pub post: Vec<Formula>,
    pub stack: i128,
    pub frame: Option<Frame>,
    /// A system call: every register but `a0` is preserved.
    pub syscall: bool,
    pub line: usize,
    /// The source name of each of the signature's variables.
    pub src_names: BTreeMap<Var, String>,
}

pub type Scope = BTreeMap<String, Var>;

pub fn lin(e: &SLin, scope: &Scope) -> Result<Lin, String> {
    let mut r = Lin::konst(e.konst);
    for (n, c) in &e.terms {
        let v = scope
            .get(n)
            .ok_or_else(|| format!("unknown variable '{n}'"))?;
        r.add_term(*v, *c).ok_or("overflow")?;
    }
    Ok(r)
}

pub fn formula(f: &SFormula, scope: &Scope) -> Result<Formula, String> {
    let ovf = || "overflow".to_string();
    Ok(match f {
        SFormula::True => Formula::True,
        SFormula::False => Formula::False,
        SFormula::Le(a, b) => Formula::le(&lin(a, scope)?, &lin(b, scope)?).ok_or_else(ovf)?,
        SFormula::Lt(a, b) => Formula::lt(&lin(a, scope)?, &lin(b, scope)?).ok_or_else(ovf)?,
        SFormula::Eq(a, b) => Formula::eq(&lin(a, scope)?, &lin(b, scope)?).ok_or_else(ovf)?,
        SFormula::Ne(a, b) => {
            Formula::negate(Formula::eq(&lin(a, scope)?, &lin(b, scope)?).ok_or_else(ovf)?)
        }
        SFormula::Dvd(c, e) => Formula::Dvd(*c, lin(e, scope)?),
        SFormula::And(v) => Formula::and(
            v.iter()
                .map(|g| formula(g, scope))
                .collect::<Result<_, _>>()?,
        ),
        SFormula::Or(v) => Formula::or(
            v.iter()
                .map(|g| formula(g, scope))
                .collect::<Result<_, _>>()?,
        ),
        SFormula::Not(g) => Formula::negate(formula(g, scope)?),
        SFormula::Implies(a, b) => Formula::or(vec![
            Formula::negate(formula(a, scope)?),
            formula(b, scope)?,
        ]),
    })
}

pub fn range_fact(k: RangeKind, e: &Lin) -> Formula {
    let (lo, hi) = match k {
        RangeKind::U64 => (0, TWO64),
        RangeKind::I64 => (-(TWO64 / 2), TWO64 / 2),
    };
    Formula::and(vec![
        Formula::le(&Lin::konst(lo), e).unwrap(),
        Formula::lt(e, &Lin::konst(hi)).unwrap(),
    ])
}

fn fields(fs: &[SField], scope: &Scope) -> Result<BTreeMap<i128, Lin>, String> {
    let mut m = BTreeMap::new();
    for f in fs {
        if f.off < 0 {
            return Err(format!("field offset {} is negative", f.off));
        }
        if m.insert(f.off, lin(&f.ty, scope)?).is_some() {
            return Err(format!("field {} given twice", f.off));
        }
    }
    let offs: Vec<i128> = m.keys().copied().collect();
    for w in offs.windows(2) {
        if w[1] - w[0] < 8 {
            return Err(format!("fields {} and {} overlap", w[0], w[1]));
        }
    }
    Ok(m)
}

pub fn cap(c: &SCap, scope: &Scope) -> Result<SigCap, String> {
    resolve_cap(c, scope, true)
}

fn resolve_cap(c: &SCap, scope: &Scope, resolve_exit_fields: bool) -> Result<SigCap, String> {
    let guard = match &c.guard {
        Some(g) => formula(g, scope)?,
        None => Formula::True,
    };
    Ok(match &c.kind {
        SCapKind::Token(t) => SigCap {
            guard,
            kind: CapKind::Token(t.clone()),
            out_fields: None,
        },
        SCapKind::Bytes {
            base,
            len,
            mode,
            heap,
            fields: fs,
            out_fields,
        } => SigCap {
            guard,
            kind: CapKind::Bytes {
                base: lin(base, scope)?,
                len: lin(len, scope)?,
                mode: *mode,
                heap: *heap,
                fields: fields(fs, scope)?,
            },
            out_fields: match out_fields {
                Some(o) if resolve_exit_fields => Some(fields(o, scope)?),
                _ => None,
            },
        },
    })
}

fn cap_names(c: &SCap, out: &mut Vec<String>) {
    if let Some(g) = &c.guard {
        g.names(out);
    }
    if let SCapKind::Bytes {
        base,
        len,
        fields,
        out_fields,
        ..
    } = &c.kind
    {
        out.extend(base.names().cloned());
        out.extend(len.names().cloned());
        for f in fields.iter().chain(out_fields.iter().flatten()) {
            out.extend(f.ty.names().cloned());
        }
    }
}

fn regty_names(r: &SRegTy, out: &mut Vec<String>) {
    if let Some(e) = &r.expr {
        out.extend(e.names().cloned());
    }
}

/// Resolves a signature: its universal variables become fresh variables in `names`; names
/// first used on the exit side become its existential results.
pub fn resolve(s: &SSig, line: usize, names: &mut Names) -> Result<Sig, String> {
    resolve_with(s, line, names, &Scope::new())
}

/// `syms`: the data symbols' address variables, named `@sym` (I32).
pub fn resolve_with(s: &SSig, line: usize, names: &mut Names, syms: &Scope) -> Result<Sig, String> {
    let mut scope = syms.clone();
    let mut src_names: BTreeMap<Var, String> = BTreeMap::new();
    let mut params = Vec::new();
    for p in &s.params {
        if scope.contains_key(p) {
            return Err(format!("variable '{p}' declared twice"));
        }
        let v = names.fresh(p);
        src_names.insert(v, p.clone());
        scope.insert(p.clone(), v);
        params.push(v);
    }
    let mut pre = Vec::new();
    let mut ins = Vec::new();
    for r in &s.ins {
        // the calling convention fixes these at a call: `jal` writes ra, sp is the
        // caller's, x0 is 0 (review finding, I33)
        if r.reg == Reg(0) || r.reg == Reg(1) || r.reg == Reg(2) {
            return Err(format!(
                "'in' may not type {} (fixed by the calling convention)",
                r.reg
            ));
        }
        if ins.iter().any(|(q, _)| *q == r.reg) {
            return Err(format!("register {} typed twice in 'in'", r.reg));
        }
        let e = match &r.expr {
            Some(e) => lin(e, &scope)
                .map_err(|m| format!("in 'in': {m} (entry-side variables must be in [...])"))?,
            None => {
                let v = names.fresh(r.reg.name());
                src_names.insert(v, r.reg.name().to_string());
                params.push(v);
                Lin::var(v)
            }
        };
        if let Some(k) = r.range {
            pre.push(range_fact(k, &e));
        }
        ins.push((r.reg, e));
    }
    let borrow = s
        .borrow
        .iter()
        .map(|c| resolve_cap(c, &scope, false))
        .collect::<Result<Vec<_>, _>>()
        .map_err(|m| format!("in 'borrow': {m}"))?;
    let take = s
        .take
        .iter()
        .map(|c| cap(c, &scope))
        .collect::<Result<Vec<_>, _>>()
        .map_err(|m| format!("in 'take': {m}"))?;
    for t in &take {
        if t.out_fields.is_some() {
            return Err("'take' has no exit fields".into());
        }
    }
    for f in &s.pre {
        pre.push(formula(f, &scope).map_err(|m| format!("in the entry 'where': {m}"))?);
    }
    // Exit side: new names are existential.
    let mut exit_names = Vec::new();
    for r in &s.outs {
        regty_names(r, &mut exit_names);
    }
    for c in &s.give {
        cap_names(c, &mut exit_names);
    }
    for c in s.borrow.iter() {
        if let SCapKind::Bytes {
            out_fields: Some(o),
            ..
        } = &c.kind
        {
            for f in o {
                exit_names.extend(f.ty.names().cloned());
            }
        }
    }
    for f in &s.post {
        f.names(&mut exit_names);
    }
    let mut out_vars = Vec::new();
    let mut xscope = scope.clone();
    for n in exit_names {
        if let std::collections::btree_map::Entry::Vacant(slot) = xscope.entry(n.clone()) {
            let v = names.fresh(&n);
            src_names.insert(v, n);
            slot.insert(v);
            out_vars.push(v);
        }
    }
    // Borrow exit fields may use exit names.
    let borrow = borrow
        .into_iter()
        .zip(&s.borrow)
        .map(|(mut b, sc)| {
            if let SCapKind::Bytes {
                out_fields: Some(o),
                ..
            } = &sc.kind
            {
                b.out_fields = Some(fields(o, &xscope)?);
            }
            Ok(b)
        })
        .collect::<Result<Vec<_>, String>>()?;
    let mut post = Vec::new();
    let mut outs = Vec::new();
    for r in &s.outs {
        if r.reg == Reg(0) || r.reg == Reg(1) || r.reg == Reg(2) {
            return Err(format!(
                "'out' may not type {} (fixed by the calling convention)",
                r.reg
            ));
        }
        if outs.iter().any(|(q, _): &(Reg, Lin)| *q == r.reg) {
            return Err(format!("register {} typed twice in 'out'", r.reg));
        }
        let e = match &r.expr {
            Some(e) => lin(e, &xscope)?,
            None => {
                let v = names.fresh(r.reg.name());
                src_names.insert(v, r.reg.name().to_string());
                out_vars.push(v);
                Lin::var(v)
            }
        };
        if let Some(k) = r.range {
            post.push(range_fact(k, &e));
        }
        outs.push((r.reg, e));
    }
    let give = s
        .give
        .iter()
        .map(|c| cap(c, &xscope))
        .collect::<Result<Vec<_>, _>>()
        .map_err(|m| format!("in 'give': {m}"))?;
    for g in &give {
        if let CapKind::Bytes { mode: Mode::Ro, .. } = g.kind {
            return Err("only 'rw' byte capabilities and tokens can be given (note, 戻り)".into());
        }
    }
    for f in &s.post {
        post.push(formula(f, &xscope)?);
    }
    let stack = s.stack.unwrap_or(0);
    if stack < 0 {
        return Err("negative stack".into());
    }
    let frame = match &s.frame {
        None => None,
        Some(fr) => {
            let f = Frame {
                size: fr.size,
                slots: fr.slots.clone(),
                addr: fr.addr.clone(),
            };
            check_frame(&f, stack)?;
            Some(f)
        }
    };
    Ok(Sig {
        name: s.name.clone(),
        kind: s.kind,
        partial: s.partial,
        params,
        ins,
        borrow,
        take,
        pre,
        out_vars,
        outs,
        give,
        post,
        stack,
        frame,
        syscall: false,
        line,
        src_names,
    })
}

/// S4 and the frame part of S3 (decision I8).
fn check_frame(f: &Frame, stack: i128) -> Result<(), String> {
    if f.size <= 0 || f.size % 16 != 0 {
        return Err(format!(
            "frame size {} must be a positive multiple of 16",
            f.size
        ));
    }
    if f.size > stack {
        return Err(format!("frame size {} exceeds 'stack {}'", f.size, stack));
    }
    let mut ranges: Vec<(i128, i128)> = Vec::new();
    for k in &f.slots {
        if k % 8 != 0 || *k < 0 || k + 8 > f.size {
            return Err(format!("slot {k} must be a multiple of 8 inside the frame"));
        }
        ranges.push((*k, 8));
    }
    for (o, l) in &f.addr {
        if *o < 0 || *l <= 0 || o + l > f.size {
            return Err(format!(
                "address-taken range [{o}, {}) must be non-empty and inside the frame",
                o + l
            ));
        }
        ranges.push((*o, *l));
    }
    ranges.sort();
    for w in ranges.windows(2) {
        if w[0].0 + w[0].1 > w[1].0 {
            return Err(format!("frame ranges at {} and {} overlap", w[0].0, w[1].0));
        }
    }
    Ok(())
}

/// The syscall signatures (note, システムコール; decision I17).
pub fn syscall_sig(num: i128, names: &mut Names) -> Option<Sig> {
    let text = match num {
        // Env.lean's relation (decision I31): an error −e with 1 ≤ e ≤ 4095, or a count
        // r ≤ min(n, MAX_RW_COUNT); a write of n ≥ 1 bytes accepts at least one.
        63 => {
            "fn sys_read [b, n] in a1: int(b), a2: int(n) borrow b ↦ bytes[n] rw where 0 ≤ n < 2^64 out a0: int(r) where −4095 ≤ r ≤ −1 ∨ (0 ≤ r ≤ n ∧ r ≤ 0x7ffff000)"
        }
        64 => {
            "fn sys_write [b, n] in a1: int(b), a2: int(n) borrow b ↦ bytes[n] ro where 0 ≤ n < 2^64 out a0: int(r) where −4095 ≤ r ≤ −1 ∨ (0 ≤ r ≤ n ∧ r ≤ 0x7ffff000 ∧ (n ≥ 1 ⇒ r ≥ 1))"
        }
        _ => return None,
    };
    let crate::syntax::Annot::Sig(s) = crate::syntax::parse_annot(text).ok()? else {
        return None;
    };
    let mut sig = resolve(&s, 0, names).ok()?;
    sig.syscall = true;
    Some(sig)
}

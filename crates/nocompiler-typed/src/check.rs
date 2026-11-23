//! The typing rules (docs/Tab 1.md, 型付け規則) and the structural checks S1–S5
//! (docs/typed/decisions.md, I3), for safe functions.
//!
//! One forward pass in address order: by S2 every edge is forward except back edges to
//! `inv` heads, so the state type of each point is the join of its forward incoming edges,
//! or, at a loop head, the annotation. Every edge is checked against the type of its
//! target (the proof's D7).

use crate::asm::{Func, PInstr, Program, Reloc};
use crate::formula::Formula;
use crate::isa::*;
use crate::lin::{Lin, Names, TWO64, Var};
use crate::presburger::{self, Verdict};
use crate::sig::{self, CapKind, Scope, Sig, SigCap};
use crate::syntax::{FnKind, Mode, SInv, SLin};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

/// The rule a rejection is attributed to. The names are stable: the corpus
/// (tests/typed/corpus) refers to them.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Rule {
    Syntax,
    Sig,
    Profile,
    Cfg,
    StackShape,
    Frame,
    Recursion,
    StaticData,
    MemBounds,
    MemWrite,
    CallSig,
    CallInst,
    CallArg,
    CallPre,
    CallCap,
    CallStack,
    CallPartial,
    Syscall,
    RetPreserved,
    RetOut,
    RetBorrow,
    RetGive,
    LoopInv,
    LoopDecreases,
    Join,
    Object,
}

impl Rule {
    pub fn as_str(self) -> &'static str {
        match self {
            Rule::Syntax => "syntax",
            Rule::Sig => "sig",
            Rule::Profile => "profile",
            Rule::Cfg => "cfg",
            Rule::StackShape => "stack-shape",
            Rule::Frame => "frame",
            Rule::Recursion => "recursion",
            Rule::StaticData => "static-data",
            Rule::MemBounds => "mem-bounds",
            Rule::MemWrite => "mem-write",
            Rule::CallSig => "call-sig",
            Rule::CallInst => "call-inst",
            Rule::CallArg => "call-arg",
            Rule::CallPre => "call-pre",
            Rule::CallCap => "call-cap",
            Rule::CallStack => "call-stack",
            Rule::CallPartial => "call-partial",
            Rule::Syscall => "syscall",
            Rule::RetPreserved => "ret-preserved",
            Rule::RetOut => "ret-out",
            Rule::RetBorrow => "ret-borrow",
            Rule::RetGive => "ret-give",
            Rule::LoopInv => "loop-inv",
            Rule::LoopDecreases => "loop-decreases",
            Rule::Join => "join",
            Rule::Object => "object",
        }
    }
    pub fn all() -> &'static [Rule] {
        use Rule::*;
        &[
            Syntax,
            Sig,
            Profile,
            Cfg,
            StackShape,
            Frame,
            Recursion,
            StaticData,
            MemBounds,
            MemWrite,
            CallSig,
            CallInst,
            CallArg,
            CallPre,
            CallCap,
            CallStack,
            CallPartial,
            Syscall,
            RetPreserved,
            RetOut,
            RetBorrow,
            RetGive,
            LoopInv,
            LoopDecreases,
            Join,
            Object,
        ]
    }
    pub fn parse(s: &str) -> Option<Rule> {
        Rule::all().iter().copied().find(|r| r.as_str() == s)
    }
}

#[derive(Clone, Debug)]
pub struct CheckError {
    pub rule: Rule,
    pub line: usize,
    pub msg: String,
}

/// A held capability: its identity (I12), guard and kind (fields inside).
#[derive(Clone, Debug, PartialEq)]
pub struct Cap {
    pub id: u32,
    pub guard: Formula,
    pub kind: CapKind,
}

/// The state type (Δ; Ψ; Γ; Φ; C) of a program point, plus the frame depth.
#[derive(Clone, Debug)]
pub struct State {
    pub regs: Vec<Lin>,
    /// Ψ, each fact with an identity so joins can intersect (I16).
    pub facts: Vec<(u32, Formula)>,
    /// Φ: slot offset (from the lowered `sp`) → expression.
    pub slots: BTreeMap<i128, Lin>,
    pub caps: Vec<Cap>,
    pub depth: i128,
}

/// One solver query, for the ledger.
#[derive(Clone, Debug)]
pub struct Query {
    pub line: usize,
    pub why: String,
    pub hyps: Vec<String>,
    pub goal: String,
    pub verdict: Verdict,
    pub micros: u128,
}

/// What the exporter needs about a checked function (docs/typed/export.md).
#[derive(Clone, Debug, Default)]
pub struct FnExport {
    /// The variable of each register's entry value: ra, then sp, gp, tp, s0–s11.
    pub reg_var: Vec<(Reg, Var)>,
    /// (head index, last index, bound variables, measure) per loop; "last" is the body's
    /// last point in τ, so the loop is the τ-interval from head to last.
    pub loops: Vec<(usize, usize, Vec<Var>, Option<Lin>)>,
    /// τ: the reached instruction indices in checking order (P1; address order under
    /// `--loops interval`). Every edge but a back edge goes up in τ; loops are intervals.
    pub tau: Vec<usize>,
    /// Identity of each entry `borrow` capability, by clause.
    pub borrow_ids: Vec<u32>,
    /// The state type before each reached instruction (instruction index).
    pub snapshots: Vec<(usize, State)>,
    /// θ per edge into an `inv`/`join` point: (source instruction or `usize::MAX` for the
    /// entry, target instruction, θ).
    pub thetas: Vec<(usize, usize, BTreeMap<Var, Lin>)>,
    /// Variables are numbered below this.
    pub fresh: u32,
    /// The `%pcrel_lo` variable L of each `auipc %pcrel_hi(sym)`: (instruction index, L, sym).
    pub lo_vars: Vec<(usize, Var, String)>,
    /// The bit counts `k` of the masks `2^k − 1` the xor-then-mask rule used (I23): the Lean
    /// checker adds `2^k ∣ a xor b ⇔ 2^k ∣ a − b` at each xor for these.
    pub xor_bits: Vec<u32>,
}

/// What the checker did for one function (the ledger's "判断の記録").
#[derive(Clone, Debug, Default)]
pub struct FnReport {
    pub name: String,
    pub kind: Option<FnKind>,
    pub error: Option<CheckError>,
    /// The state type at each instruction (index, line, text), for reached points.
    pub states: Vec<(usize, usize, String)>,
    /// Instantiations chosen: (line, what, var := expr).
    pub insts: Vec<(usize, String, String)>,
    pub queries: Vec<Query>,
    pub retries: usize,
    pub micros: u128,
    pub export: Option<FnExport>,
    /// Solver queries made (all of them; `queries` keeps them only when recording).
    pub nqueries: usize,
}

#[derive(Clone, Debug, Default)]
pub struct Report {
    pub funcs: Vec<FnReport>,
    /// Errors that are not about one function (signatures, S5).
    pub global: Vec<CheckError>,
}

impl Report {
    pub fn ok(&self) -> bool {
        self.global.is_empty() && self.funcs.iter().all(|f| f.error.is_none())
    }
}

/// Program-wide context: all signatures and the name table.
pub struct Checker {
    pub names: Names,
    pub sigs: BTreeMap<String, Sig>,
    /// Record every query and state in the report (the ledger); off for speed.
    pub record: bool,
    /// Read-only data symbols: implicitly held by every function (note, 静的データ; I30).
    pub statics: Vec<Static>,
    /// Writable data symbols: no implicit capability; a signature lends them (I32).
    pub writable_data: BTreeSet<String>,
    /// Every data symbol's address variable ℓ_sym, named `@sym` in annotations (I32).
    pub sym_vars: BTreeMap<String, Var>,
    /// Size and alignment of every data symbol.
    pub sym_info: BTreeMap<String, (i128, i128)>,
    /// Data symbols that cannot be relied on, with the reason.
    pub unusable_data: BTreeMap<String, String>,
    /// Loops as natural loops of a reducible CFG (proposal P1) instead of address
    /// intervals (S2). Off by default.
    pub natural_loops: bool,
}

#[derive(Clone, Debug)]
pub struct Static {
    pub name: String,
    /// ℓ_sym: the symbol's address after linking (S6).
    pub var: Var,
    pub size: i128,
    pub align: i128,
    /// The 8-byte words the source gives, at offsets that are multiples of 8.
    pub fields: BTreeMap<i128, Lin>,
}

#[derive(Clone, Copy, Debug)]
pub struct Options {
    /// Record states, instantiations and queries (ledger, export).
    pub record: bool,
    /// Proposal P1: natural loops instead of S2's address intervals.
    pub natural_loops: bool,
}

/// Checks every safe function of a parsed program.
impl Default for Options {
    /// Natural loops (P1) are the default since the user's decision of 2026-11-23.
    fn default() -> Self {
        Options {
            record: false,
            natural_loops: true,
        }
    }
}

pub fn check_program(p: &Program, record: bool) -> (Checker, Report) {
    check_program_opts(
        p,
        Options {
            record,
            natural_loops: true,
        },
    )
}

pub fn check_program_opts(p: &Program, opts: Options) -> (Checker, Report) {
    let record = opts.record;
    let mut ck = Checker {
        names: Names::default(),
        sigs: BTreeMap::new(),
        record,
        statics: vec![],
        writable_data: BTreeSet::new(),
        sym_vars: BTreeMap::new(),
        sym_info: BTreeMap::new(),
        unusable_data: BTreeMap::new(),
        natural_loops: opts.natural_loops,
    };
    for (name, d) in &p.data {
        if let Some(why) = &d.unusable {
            ck.unusable_data.insert(name.clone(), why.clone());
            continue;
        }
        let clean: String = name
            .chars()
            .filter(|c| c.is_alphanumeric() || *c == '_')
            .collect();
        let var = ck.names.fresh(&format!("ℓ{clean}"));
        ck.sym_vars.insert(name.clone(), var);
        ck.sym_info
            .insert(name.clone(), (d.bytes.len() as i128, d.align as i128));
        if !d.ro {
            ck.writable_data.insert(name.clone());
            continue;
        }
        let mut fields = BTreeMap::new();
        if d.align >= 8 {
            for k in (0..d.bytes.len() / 8).map(|k| k * 8) {
                let w: Option<Vec<u8>> = d.bytes[k..k + 8].iter().copied().collect();
                if let Some(w) = w {
                    let v = u64::from_le_bytes(w.try_into().unwrap());
                    fields.insert(k as i128, Lin::konst(v as i128));
                }
            }
        }
        ck.statics.push(Static {
            name: name.clone(),
            var,
            size: d.bytes.len() as i128,
            align: d.align as i128,
            fields,
        });
    }
    let mut rep = Report::default();
    for (s, line) in &p.sigs {
        if ck.sigs.contains_key(&s.name) {
            rep.global.push(CheckError {
                rule: Rule::Sig,
                line: *line,
                msg: format!("two signatures for '{}'", s.name),
            });
            continue;
        }
        let syms: Scope = ck
            .sym_vars
            .iter()
            .map(|(n, v)| (format!("@{n}"), *v))
            .collect();
        match sig::resolve_with(s, *line, &mut ck.names, &syms) {
            Ok(sg) => {
                ck.sigs.insert(s.name.clone(), sg);
            }
            Err(m) => rep.global.push(CheckError {
                rule: Rule::Sig,
                line: *line,
                msg: format!("signature of '{}': {m}", s.name),
            }),
        }
    }
    // S5: no cycle among the safe functions' calls.
    let bodies: BTreeMap<&str, &Func> = p.funcs.iter().map(|f| (f.name.as_str(), f)).collect();
    let callees = |f: &Func| -> Vec<String> {
        f.instrs
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
    };
    let safe: Vec<&str> = ck
        .sigs
        .values()
        .filter(|s| s.kind == FnKind::Safe)
        .map(|s| s.name.as_str())
        .collect();
    let mut cyclic = BTreeSet::new();
    for s in &safe {
        // DFS from s looking for s.
        let mut stack: Vec<String> = bodies.get(s).map(|f| callees(f)).unwrap_or_default();
        let mut seen = BTreeSet::new();
        while let Some(g) = stack.pop() {
            if g == *s {
                cyclic.insert(s.to_string());
                break;
            }
            if !seen.insert(g.clone()) || !safe.contains(&g.as_str()) {
                continue;
            }
            if let Some(f) = bodies.get(g.as_str()) {
                stack.extend(callees(f));
            }
        }
    }
    for f in &p.funcs {
        let Some(sg) = ck.sigs.get(&f.name).cloned() else {
            continue;
        };
        let mut fr = FnReport {
            name: f.name.clone(),
            kind: Some(sg.kind),
            ..Default::default()
        };
        if sg.kind != FnKind::Safe {
            rep.funcs.push(fr);
            continue;
        }
        let t0 = std::time::Instant::now();
        if cyclic.contains(&f.name) {
            fr.error = Some(CheckError {
                rule: Rule::Recursion,
                line: f.line,
                msg: "the call graph of safe functions has a cycle through this function (S5)"
                    .into(),
            });
        } else {
            let mut drops = Drops::default();
            loop {
                let mut fc = FnCheck::new(&mut ck, &sg, f, &drops);
                let r = fc.run();
                let exp = fc.export_info();
                let (states, insts, queries) = (fc.states, fc.insts, fc.queries);
                fr.nqueries += fc.nqueries;
                match r {
                    Err(Fail::Retry(d)) if fr.retries < 64 => {
                        fr.retries += 1;
                        drops.merge(d);
                    }
                    Err(Fail::Retry(_)) => {
                        fr.error = Some(CheckError {
                            rule: Rule::LoopInv,
                            line: f.line,
                            msg: "loop head fields did not stabilise".into(),
                        });
                        break;
                    }
                    Err(Fail::Err(e)) => {
                        fr.error = Some(e);
                        fr.states = states;
                        fr.insts = insts;
                        fr.queries = queries;
                        break;
                    }
                    Ok(()) => {
                        fr.export = Some(exp);
                        fr.states = states;
                        fr.insts = insts;
                        fr.queries = queries;
                        break;
                    }
                }
            }
        }
        fr.micros = t0.elapsed().as_micros();
        rep.funcs.push(fr);
    }
    (ck, rep)
}

/// Loop-head fields and slots to drop (I13), found by earlier attempts.
#[derive(Clone, Debug, Default)]
struct Drops {
    fields: BTreeSet<(usize, u32, i128)>,
    slots: BTreeSet<(usize, i128)>,
}

impl Drops {
    fn merge(&mut self, o: Drops) {
        self.fields.extend(o.fields);
        self.slots.extend(o.slots);
    }
}

enum Fail {
    Err(CheckError),
    Retry(Drops),
}

impl From<CheckError> for Fail {
    fn from(e: CheckError) -> Fail {
        Fail::Err(e)
    }
}

type F<T> = Result<T, Fail>;

struct Head {
    state: State,
    /// Variables bound at the head (D7's θ moves only these).
    bound: Vec<Var>,
    inv_vars: Vec<(String, Var)>,
    measure: Option<Lin>,
    line: usize,
}

struct Loop {
    head: usize,

    body: BTreeSet<usize>,
    written: BTreeSet<Reg>,
}

struct FnCheck<'a> {
    ck: &'a mut Checker,
    me: &'a Sig,
    f: &'a Func,
    drops: &'a Drops,
    x_ra: Var,
    sigma0: Var,
    entry_preserved: BTreeMap<Reg, Var>,
    /// Identities of the entry `borrow` capabilities, by clause.
    borrow_ids: Vec<u32>,
    /// Identities of the implicit read-only data capabilities, in `ck.statics` order.
    static_ids: Vec<u32>,
    frame_ids: Vec<u32>,
    next_fact: u32,
    next_cap: u32,
    heads: BTreeMap<usize, Head>,
    loops: Vec<Loop>,
    states: Vec<(usize, usize, String)>,
    snapshots: Vec<(usize, State)>,
    /// θ chosen on each edge into an annotated point: (source, target, θ); source
    /// `usize::MAX` = the function's entry.
    thetas: Vec<(usize, usize, BTreeMap<Var, Lin>)>,
    insts: Vec<(usize, String, String)>,
    queries: Vec<Query>,
    nqueries: usize,
    /// `x = a xor b` for the fresh variables xor results get (true in every state).
    xor_defs: BTreeMap<Var, (Lin, Lin)>,
    /// The `%pcrel_lo` value of each `auipc %pcrel_hi` (by instruction index), I30.
    lo_vars: BTreeMap<usize, Var>,
    /// See `FnExport::xor_bits`.
    xor_bits: std::collections::BTreeSet<u32>,
    /// The order points are checked in, the back edges, and each loop head's body.
    order: Vec<usize>,
    back: BTreeSet<(usize, usize)>,
    loop_bodies: Vec<(usize, BTreeSet<usize>)>,
    line: usize,
}

fn ovf(line: usize) -> CheckError {
    CheckError {
        rule: Rule::Syntax,
        line,
        msg: "arithmetic overflow in an index expression".into(),
    }
}

fn caller_saved(r: Reg) -> bool {
    r != ZERO && !r.is_preserved()
}

impl<'a> FnCheck<'a> {
    fn new(ck: &'a mut Checker, me: &'a Sig, f: &'a Func, drops: &'a Drops) -> Self {
        let x_ra = ck.names.fresh("ra0");
        let sigma0 = ck.names.fresh("σ0");
        FnCheck {
            ck,
            me,
            f,
            drops,
            x_ra,
            sigma0,
            entry_preserved: BTreeMap::new(),
            borrow_ids: vec![],
            static_ids: vec![],
            frame_ids: vec![],
            next_fact: 0,
            next_cap: 0,
            heads: BTreeMap::new(),
            loops: vec![],
            states: vec![],
            snapshots: vec![],
            thetas: vec![],
            insts: vec![],
            queries: vec![],
            nqueries: 0,
            xor_defs: BTreeMap::new(),
            lo_vars: BTreeMap::new(),
            xor_bits: Default::default(),
            order: vec![],
            back: BTreeSet::new(),
            loop_bodies: vec![],
            line: f.line,
        }
    }

    fn export_info(&self) -> FnExport {
        let mut reg_var = vec![(RA, self.x_ra), (SP, self.sigma0)];
        for r in [GP, TP]
            .into_iter()
            .chain(Reg::all().filter(|r| r.is_saved()))
        {
            if let Some(v) = self.entry_preserved.get(&r) {
                reg_var.push((r, *v));
            }
        }
        let tpos: BTreeMap<usize, usize> = self
            .order
            .iter()
            .enumerate()
            .map(|(i, x)| (*x, i))
            .collect();
        let loops = self
            .loops
            .iter()
            .map(|l| {
                let h = self.heads.get(&l.head);
                let last = *l
                    .body
                    .iter()
                    .max_by_key(|x| tpos.get(x).copied().unwrap_or(0))
                    .unwrap();
                (
                    l.head,
                    last,
                    h.map(|h| h.inv_vars.iter().map(|x| x.1).collect())
                        .unwrap_or_default(),
                    h.and_then(|h| h.measure.clone()),
                )
            })
            .collect();
        let lo_vars = self
            .lo_vars
            .iter()
            .filter_map(|(ix, v)| match &self.f.instrs.get(*ix)?.reloc {
                Some(Reloc::PcrelHi(sym)) => Some((*ix, *v, sym.clone())),
                _ => None,
            })
            .collect();
        FnExport {
            xor_bits: self.xor_bits.iter().copied().collect(),
            lo_vars,
            reg_var,
            loops,
            tau: self.order.clone(),
            // the export lists the implicit data capabilities as borrow clauses after the
            // signature's own (export.md), so their identities follow
            borrow_ids: self
                .borrow_ids
                .iter()
                .chain(&self.static_ids)
                .copied()
                .collect(),
            snapshots: self.snapshots.clone(),
            thetas: self.thetas.clone(),
            fresh: self.ck.names.len() as u32,
        }
    }

    fn lo_var(&mut self, auipc_ix: usize) -> Var {
        if let Some(v) = self.lo_vars.get(&auipc_ix) {
            return *v;
        }
        let v = self.fresh("lo");
        self.lo_vars.insert(auipc_ix, v);
        v
    }

    fn err<T>(&self, rule: Rule, msg: impl Into<String>) -> F<T> {
        Err(Fail::Err(CheckError {
            rule,
            line: self.line,
            msg: msg.into(),
        }))
    }

    fn fresh(&mut self, base: &str) -> Var {
        self.ck.names.fresh(base)
    }

    fn add_fact(&mut self, st: &mut State, f: Formula) {
        if f == Formula::True {
            return;
        }
        self.next_fact += 1;
        st.facts.push((self.next_fact, f));
    }

    fn new_cap(&mut self, guard: Formula, kind: CapKind) -> Cap {
        self.next_cap += 1;
        Cap {
            id: self.next_cap,
            guard,
            kind,
        }
    }

    fn show(&self, e: &Lin) -> String {
        e.display(&self.ck.names).to_string()
    }
    fn showf(&self, f: &Formula) -> String {
        f.display(&self.ck.names).to_string()
    }

    /// The facts a capability's validity gives (note: 能力を持っていること自体が事実を生む;
    /// the proof's D2).
    fn cap_facts(c: &Cap) -> Option<Formula> {
        let CapKind::Bytes {
            base, len, fields, ..
        } = &c.kind
        else {
            return None;
        };
        let mut v = vec![
            Formula::Ge(base.clone()),
            Formula::Ge(len.clone()),
            Formula::le(&base.add(len)?, &Lin::konst(TWO64))?,
        ];
        for k in fields.keys() {
            v.push(Formula::le(&Lin::konst(k + 8), len)?);
            v.push(Formula::Dvd(8, base.add_const(*k)?));
        }
        let body = Formula::and(v);
        Some(if c.guard == Formula::True {
            body
        } else {
            Formula::or(vec![Formula::negate(c.guard.clone()), body])
        })
    }

    fn hyps(&self, st: &State) -> Vec<Formula> {
        let mut h: Vec<Formula> = st.facts.iter().map(|(_, f)| f.clone()).collect();
        h.extend(st.caps.iter().filter_map(Self::cap_facts));
        h
    }

    /// Ψ ⊢ goal.
    fn prove(&mut self, st: &State, goal: &Formula, why: &str) -> bool {
        match goal {
            Formula::True => return true,
            Formula::Eq(e) | Formula::Dvd(_, e) if *e == Lin::default() => return true,
            _ => {}
        }
        let hyps = self.hyps(st);
        self.nqueries += 1;
        let t0 = std::time::Instant::now();
        // reachability pruning only sharpens (I24): a small budget suffices
        let budget = if why == "edge reachable?" {
            presburger::Budget {
                constraints: 20_000,
                ..Default::default()
            }
        } else {
            presburger::Budget::default()
        };
        let v = presburger::prove_with(&hyps, goal, budget);
        let micros = t0.elapsed().as_micros();
        if self.ck.record || v != Verdict::Proved {
            let q = Query {
                line: self.line,
                why: why.to_string(),
                hyps: if self.ck.record {
                    hyps.iter().map(|h| self.showf(h)).collect()
                } else {
                    vec![]
                },
                goal: self.showf(goal),
                verdict: v,
                micros,
            };
            if self.ck.record {
                self.queries.push(q);
            } else {
                // keep the last failures only, for messages
                self.queries.push(q);
                if self.queries.len() > 8 {
                    self.queries.remove(0);
                }
            }
        }
        v == Verdict::Proved
    }

    /// `a ≡ b (mod 2^64)`.
    fn prove_eq64(&mut self, st: &State, a: &Lin, b: &Lin, why: &str) -> bool {
        if a == b {
            return true;
        }
        match a.sub(b) {
            Some(d) => self.prove(st, &Formula::Dvd(TWO64, d), why),
            None => false,
        }
    }

    fn prove_eq(&mut self, st: &State, a: &Lin, b: &Lin, why: &str) -> bool {
        if a == b {
            return true;
        }
        match Formula::eq(a, b) {
            Some(g) => self.prove(st, &g, why),
            None => false,
        }
    }

    fn fstate(&self, st: &State) -> String {
        let n = &self.ck.names;
        let mut s = String::new();
        let _ = write!(s, "regs:");
        for r in Reg::all().skip(1) {
            let e = &st.regs[r.0 as usize];
            let _ = write!(s, " {r}={}", e.display(n));
        }
        let _ = write!(s, "\n  facts:");
        for (_, f) in &st.facts {
            let _ = write!(s, " [{}]", f.display(n));
        }
        if !st.slots.is_empty() {
            let _ = write!(s, "\n  slots:");
            for (k, e) in &st.slots {
                let _ = write!(s, " {k}:{}", e.display(n));
            }
        }
        let _ = write!(s, "\n  caps:");
        for c in &st.caps {
            let g = if c.guard == Formula::True {
                String::new()
            } else {
                format!("{} => ", c.guard.display(n))
            };
            match &c.kind {
                CapKind::Token(t) => {
                    let _ = write!(s, " #{} {g}{t};", c.id);
                }
                CapKind::Bytes {
                    base,
                    len,
                    mode,
                    heap,
                    fields,
                } => {
                    let _ = write!(
                        s,
                        " #{} {g}{} |-> bytes[{}] {}{}",
                        c.id,
                        base.display(n),
                        len.display(n),
                        if *mode == Mode::Rw { "rw" } else { "ro" },
                        if *heap { " heap" } else { "" }
                    );
                    if !fields.is_empty() {
                        let _ = write!(s, " {{");
                        for (k, e) in fields {
                            let _ = write!(s, "{k}: int({}), ", e.display(n));
                        }
                        let _ = write!(s, "}}");
                    }
                    let _ = write!(s, ";");
                }
            }
        }
        let _ = write!(s, "\n  depth: {}", st.depth);
        s
    }

    fn fail_detail(&self, st: &State) -> String {
        let mut s = format!("\n  state: {}", self.fstate(st));
        if let Some(q) = self
            .queries
            .iter()
            .rev()
            .find(|q| q.verdict != Verdict::Proved)
        {
            let _ = write!(s, "\n  failed goal: {} ({:?})", q.goal, q.verdict);
        }
        s
    }

    // ------------------------------------------------------------------ structure

    /// Static successors of instruction `ix` (S1/S2 prepass): `None` = leaves the function.
    fn static_succs(&self, ix: usize) -> Vec<usize> {
        let i = &self.f.instrs[ix].instr;
        let next = ix + 1;
        match i {
            Instr::Branch {
                target: Target::Local(t),
                ..
            } => vec![*t, next],
            Instr::Jal {
                rd,
                target: Target::Local(t),
            } if *rd == ZERO => vec![*t],
            Instr::Jal { rd, .. } | Instr::CallPair { rd, .. } if *rd == ZERO => vec![],
            Instr::Jalr { .. } | Instr::Unimp => vec![],
            Instr::Ecall => vec![next],
            _ => vec![next],
        }
    }

    fn structure(&mut self) -> F<()> {
        let n = self.f.instrs.len();
        if n == 0 {
            self.line = self.f.line;
            return self.err(Rule::Cfg, "the function has no instructions");
        }
        // S1: the profile, control targets.
        for pi in self.f.instrs.iter() {
            self.line = pi.line;
            match &pi.instr {
                Instr::Jalr { rd, rs1, off } if !(*rd == ZERO && *rs1 == RA && *off == 0) => {
                    return self.err(
                        Rule::Profile,
                        "computed jump: only 'jalr zero, 0(ra)' (return) is in the profile",
                    );
                }
                Instr::Jal { rd, target } => match target {
                    Target::Local(_) if *rd != ZERO => {
                        return self
                            .err(Rule::Profile, "'jal' with a link register to a local label");
                    }
                    Target::Symbol(s) if *rd != ZERO && *rd != RA => {
                        return self.err(Rule::Profile, format!("call of '{s}' must link in ra"));
                    }
                    Target::Symbol(s) if !self.ck.sigs.contains_key(s) => {
                        return self.err(
                            Rule::CallSig,
                            format!(
                                "no signature for '{s}' (jump to an unknown label or function)"
                            ),
                        );
                    }
                    _ => {}
                },
                Instr::CallPair {
                    target: Target::Local(_),
                    ..
                } => {
                    return self.err(Rule::Profile, "call/tail of a local label");
                }
                Instr::CallPair {
                    target: Target::Symbol(s),
                    ..
                } if !self.ck.sigs.contains_key(s) => {
                    return self.err(Rule::CallSig, format!("no signature for '{s}'"));
                }
                Instr::Branch {
                    target: Target::Symbol(s),
                    ..
                } => {
                    return self.err(
                        Rule::Cfg,
                        format!("branch to '{s}', which is not a label of this function"),
                    );
                }
                Instr::Auipc { .. } => {
                    match &pi.reloc {
                        Some(Reloc::PcrelHi(sym)) if self.ck.sym_vars.contains_key(sym) => {}
                        Some(Reloc::PcrelHi(sym)) if self.ck.unusable_data.contains_key(sym) => {
                            let why = self.ck.unusable_data[sym].clone();
                            return self.err(
                                Rule::StaticData,
                                format!("{why}: the linker may change it (I33)"),
                            );
                        }
                        Some(Reloc::PcrelHi(sym)) => {
                            return self.err(Rule::StaticData, format!("auipc to '{sym}', which is not a data symbol of this file (I30)"));
                        }
                        _ => {
                            return self.err(Rule::StaticData, "auipc without %pcrel_hi(symbol): pc-relative values are not typed (I30)");
                        }
                    }
                }
                i if pi.reloc.is_some() => match pi.reloc.as_ref().unwrap() {
                    Reloc::PcrelLo(label)
                        if matches!(
                            i,
                            Instr::IOp { op: IOp::Addi, .. }
                                | Instr::Load { .. }
                                | Instr::Store { .. }
                        ) =>
                    {
                        let ok = self.f.labels.get(label).is_some_and(|ix| {
                            matches!(self.f.instrs.get(*ix), Some(p) if matches!(p.instr, Instr::Auipc { .. }) && matches!(p.reloc, Some(Reloc::PcrelHi(_))))
                        });
                        if !ok {
                            return self.err(Rule::StaticData, format!("%pcrel_lo({label}) must name the label of an auipc %pcrel_hi in this function"));
                        }
                    }
                    r => {
                        return self.err(
                            Rule::StaticData,
                            format!("relocation operand {r:?} is not supported (I30)"),
                        );
                    }
                },
                _ => {}
            }
        }
        if self.ck.natural_loops {
            self.structure_natural()?;
        } else {
            self.structure_s2()?;
        }
        for (h, body) in self.loop_bodies.clone() {
            let mut written = BTreeSet::new();
            for &k in &body {
                let pi = &self.f.instrs[k];
                if let Some(r) = pi.instr.rd() {
                    written.insert(r);
                }
                let is_call = matches!(&pi.instr, Instr::Jal { rd, target: Target::Symbol(_) } if *rd == RA)
                    || matches!(&pi.instr, Instr::CallPair { rd, .. } if *rd == RA);
                if is_call {
                    written.extend(Reg::all().filter(|r| caller_saved(*r)));
                }
            }
            self.loops.push(Loop {
                head: h,
                body,
                written,
            });
        }
        for (ix, (inv, line)) in &self.f.invs {
            // P1: an `inv` that is not a loop head is a `join` (its measure is unused)
            if inv.is_loop && !self.ck.natural_loops && !self.loops.iter().any(|l| l.head == *ix) {
                self.line = *line;
                return self.err(Rule::Cfg, "'inv' on a label that no backward jump reaches (use 'join' for a forward join)");
            }
        }
        Ok(())
    }

    /// S2 as the note and the proof state it: an edge to a lower or equal address is a back
    /// edge and goes to an `inv` head; a loop is the interval from its head to its last back
    /// edge; intervals nest; no edge enters an interval except at its head.
    fn structure_s2(&mut self) -> F<()> {
        let n = self.f.instrs.len();
        let mut ends: BTreeMap<usize, usize> = BTreeMap::new();
        for ix in 0..n {
            for t in self.static_succs(ix) {
                if t < n && t <= ix {
                    self.line = self.f.instrs[ix].line;
                    match self.f.invs.get(&t) {
                        Some((inv, _)) if inv.is_loop => {}
                        _ => {
                            return self.err(
                                Rule::Cfg,
                                "backward jump to a label without an 'inv' annotation (S2)",
                            );
                        }
                    }
                    self.back.insert((ix, t));
                    let e = ends.entry(t).or_insert(ix);
                    *e = (*e).max(ix);
                }
            }
        }
        let ivs: Vec<(usize, usize)> = ends.iter().map(|(h, e)| (*h, *e)).collect();
        for (i, a) in ivs.iter().enumerate() {
            for b in &ivs[i + 1..] {
                let disjoint = a.1 < b.0 || b.1 < a.0;
                let nested = (a.0 <= b.0 && b.1 <= a.1) || (b.0 <= a.0 && a.1 <= b.1);
                if !disjoint && !nested {
                    self.line = self.f.instrs[b.0].line;
                    return self.err(Rule::Cfg, "loops overlap without nesting (S2)");
                }
            }
        }
        for ix in 0..n {
            for t in self.static_succs(ix) {
                for (h, e) in &ivs {
                    if t > *h && t <= *e && (ix < *h || ix > *e) {
                        self.line = self.f.instrs[ix].line;
                        return self.err(Rule::Cfg, "jump into the middle of a loop (S2)");
                    }
                }
            }
        }
        self.order = (0..n).collect();
        self.loop_bodies = ivs
            .into_iter()
            .map(|(h, e)| (h, (h..=e).collect()))
            .collect();
        Ok(())
    }

    /// The natural-loop reading of S2 (proposal P1, opt-in): a back edge is an edge u → h
    /// where h dominates u, and goes to an `inv` head; the graph without back edges must be
    /// acyclic (the CFG is reducible); a loop is h's natural loop. Points are checked in a
    /// topological order of the acyclic graph.
    fn structure_natural(&mut self) -> F<()> {
        let n = self.f.instrs.len();
        let succ: Vec<Vec<usize>> = (0..n)
            .map(|i| {
                self.static_succs(i)
                    .into_iter()
                    .filter(|t| *t < n)
                    .collect()
            })
            .collect();
        // reverse postorder from the entry
        let mut post = Vec::new();
        let mut seen = vec![false; n];
        let mut stack: Vec<(usize, usize)> = vec![(0, 0)];
        seen[0] = true;
        while let Some((u, k)) = stack.pop() {
            if k < succ[u].len() {
                stack.push((u, k + 1));
                let v = succ[u][k];
                if !seen[v] {
                    seen[v] = true;
                    stack.push((v, 0));
                }
            } else {
                post.push(u);
            }
        }
        let rpo: Vec<usize> = post.iter().rev().copied().collect();
        let mut num = vec![usize::MAX; n];
        for (i, u) in rpo.iter().enumerate() {
            num[*u] = i;
        }
        let mut preds: Vec<Vec<usize>> = vec![vec![]; n];
        for u in 0..n {
            if seen[u] {
                for &v in &succ[u] {
                    preds[v].push(u);
                }
            }
        }
        // dominators (Cooper, Harvey, Kennedy)
        let mut idom = vec![usize::MAX; n];
        idom[0] = 0;
        let intersect = |idom: &Vec<usize>, mut a: usize, mut b: usize| {
            while a != b {
                while num[a] > num[b] {
                    a = idom[a];
                }
                while num[b] > num[a] {
                    b = idom[b];
                }
            }
            a
        };
        let mut changed = true;
        while changed {
            changed = false;
            for &u in rpo.iter().skip(1) {
                let mut new = usize::MAX;
                for &p in &preds[u] {
                    if idom[p] != usize::MAX {
                        new = if new == usize::MAX {
                            p
                        } else {
                            intersect(&idom, p, new)
                        };
                    }
                }
                if new != idom[u] {
                    idom[u] = new;
                    changed = true;
                }
            }
        }
        let dominates = |h: usize, mut u: usize| loop {
            if u == h {
                return true;
            }
            if u == 0 || idom[u] == usize::MAX {
                return false;
            }
            u = idom[u];
        };
        for &u in &rpo {
            for &t in &succ[u] {
                if dominates(t, u) {
                    self.line = self.f.instrs[u].line;
                    match self.f.invs.get(&t) {
                        Some((inv, _)) if inv.is_loop => {}
                        _ => return self.err(
                            Rule::Cfg,
                            "back edge (to a dominating label) without an 'inv' annotation (P1)",
                        ),
                    }
                    self.back.insert((u, t));
                }
            }
        }
        // the graph without back edges is acyclic: Kahn's algorithm over reached points
        let mut indeg = vec![0usize; n];
        for &u in &rpo {
            for &t in &succ[u] {
                if !self.back.contains(&(u, t)) {
                    indeg[t] += 1;
                }
            }
        }
        let mut ready: Vec<usize> = vec![0];
        let mut order = Vec::new();
        while let Some(u) = ready.pop() {
            order.push(u);
            // keep address order among ready points (stable output)
            let mut next: Vec<usize> = Vec::new();
            for &t in &succ[u] {
                if !self.back.contains(&(u, t)) {
                    indeg[t] -= 1;
                    if indeg[t] == 0 {
                        next.push(t);
                    }
                }
            }
            ready.extend(next);
            ready.sort_unstable_by(|a, b| b.cmp(a));
        }
        if order.len() != rpo.len() {
            self.line = self.f.line;
            return self.err(
                Rule::Cfg,
                "the control-flow graph is irreducible: a cycle without a dominating head (P1)",
            );
        }
        // natural loops
        let mut bodies: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
        for &(u, h) in &self.back {
            let body = bodies.entry(h).or_insert_with(|| BTreeSet::from([h]));
            let mut work = vec![u];
            while let Some(x) = work.pop() {
                if body.insert(x) {
                    work.extend(preds[x].iter().copied());
                }
            }
        }
        let _ = order;
        // τ (T's form of P1): an order of the reached points in which every edge other than
        // a back edge goes up and every natural loop is an interval. Built per region of
        // the loop-nesting forest: inner loops collapsed to their head, the region sorted
        // topologically (address order among ready points), inner loops expanded in place.
        let reached: BTreeSet<usize> = rpo.iter().copied().collect();
        let tau = self.tau_region(&reached, 0, &succ, &bodies);
        // check the τ conditions themselves (what the Lean checker will check)
        let mut pos = vec![usize::MAX; n];
        for (i, u) in tau.iter().enumerate() {
            pos[*u] = i;
        }
        let ivs: Vec<(usize, usize, usize)> = bodies
            .iter()
            .map(|(h, b)| (*h, pos[*h], b.iter().map(|x| pos[*x]).max().unwrap()))
            .collect();
        for &u in &tau {
            for &t in &succ[u] {
                let ok = if self.back.contains(&(u, t)) {
                    pos[t] <= pos[u]
                } else {
                    pos[t] > pos[u]
                };
                let entering = ivs.iter().any(|(h, lo, hi)| {
                    t != *h && pos[t] > *lo && pos[t] <= *hi && (pos[u] < *lo || pos[u] > *hi)
                });
                if !ok || entering {
                    self.line = self.f.instrs[u].line;
                    return self.err(
                        Rule::Cfg,
                        "no loop-contiguous order τ for this control-flow graph (P1)",
                    );
                }
            }
        }
        for (h, lo, hi) in &ivs {
            if bodies[h].len() != hi - lo + 1 {
                self.line = self.f.instrs[*h].line;
                return self.err(Rule::Cfg, "a natural loop is not contiguous in τ (P1)");
            }
        }
        self.order = tau;
        self.loop_bodies = bodies.into_iter().collect();
        Ok(())
    }

    /// The τ order of `region` (a loop body with head `head`, or the whole function).
    fn tau_region(
        &self,
        region: &BTreeSet<usize>,
        head: usize,
        succ: &[Vec<usize>],
        bodies: &BTreeMap<usize, BTreeSet<usize>>,
    ) -> Vec<usize> {
        // the maximal loops strictly inside the region
        let inner: Vec<(usize, &BTreeSet<usize>)> = bodies
            .iter()
            .filter(|(h, b)| **h != head && b.is_subset(region) && region.contains(h))
            .filter(|(h, b)| {
                !bodies.iter().any(|(h2, b2)| {
                    *h2 != **h
                        && *h2 != head
                        && b2.is_subset(region)
                        && b.is_subset(b2)
                        && b2.len() > b.len()
                })
            })
            .map(|(h, b)| (*h, b))
            .collect();
        let rep = |x: usize| -> usize {
            inner
                .iter()
                .find(|(_, b)| b.contains(&x))
                .map(|(h, _)| *h)
                .unwrap_or(x)
        };
        let nodes: BTreeSet<usize> = region.iter().map(|x| rep(*x)).collect();
        let mut indeg: BTreeMap<usize, usize> = nodes.iter().map(|x| (*x, 0)).collect();
        let mut edges: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
        for &u in region {
            for &t in &succ[u] {
                if !region.contains(&t) || self.back.contains(&(u, t)) {
                    continue;
                }
                let (a, b) = (rep(u), rep(t));
                if a != b && edges.entry(a).or_default().insert(b) {
                    *indeg.get_mut(&b).unwrap() += 1;
                }
            }
        }
        let mut ready: BTreeSet<usize> = indeg
            .iter()
            .filter(|(_, d)| **d == 0)
            .map(|(x, _)| *x)
            .collect();
        let mut out = Vec::new();
        while let Some(&x) = ready.iter().next() {
            ready.remove(&x);
            match inner.iter().find(|(h, _)| *h == x) {
                Some((h, b)) => out.extend(self.tau_region(b, *h, succ, bodies)),
                None => out.push(x),
            }
            for y in edges.get(&x).cloned().unwrap_or_default() {
                let d = indeg.get_mut(&y).unwrap();
                *d -= 1;
                if *d == 0 {
                    ready.insert(y);
                }
            }
        }
        out
    }

    // ------------------------------------------------------------------ entry (T0)

    fn entry_state(&mut self) -> F<State> {
        let me = self.me;
        let mut regs: Vec<Lin> = Vec::with_capacity(32);
        for r in Reg::all() {
            regs.push(if r == ZERO {
                Lin::konst(0)
            } else {
                Lin::default()
            });
        }
        for r in Reg::all().skip(1) {
            let v = if r == RA {
                self.x_ra
            } else if r == SP {
                self.sigma0
            } else if r.is_preserved() {
                let v = self.fresh(&format!("{}0", r.name()));
                self.entry_preserved.insert(r, v);
                v
            } else {
                self.fresh(r.name())
            };
            regs[r.0 as usize] = Lin::var(v);
        }
        for (r, e) in &me.ins {
            if *r == ZERO || *r == SP || *r == RA || r.is_preserved() {
                self.line = me.line;
                return self.err(
                    Rule::Sig,
                    format!("'in' may not type {r} (it is fixed by the calling convention)"),
                );
            }
            regs[r.0 as usize] = e.clone();
        }
        let mut st = State {
            regs,
            facts: vec![],
            slots: BTreeMap::new(),
            caps: vec![],
            depth: 0,
        };
        for f in me.pre.clone() {
            self.add_fact(&mut st, f);
        }
        let s0 = Lin::var(self.sigma0);
        self.add_fact(&mut st, Formula::in_u64(&s0).unwrap());
        self.add_fact(&mut st, Formula::Dvd(16, s0.clone()));
        self.add_fact(&mut st, Formula::le(&Lin::konst(me.stack), &s0).unwrap());
        for b in &me.borrow {
            let c = self.new_cap(b.guard.clone(), b.kind.clone());
            self.borrow_ids.push(c.id);
            st.caps.push(c);
        }
        for t in &me.take {
            let c = self.new_cap(t.guard.clone(), t.kind.clone());
            st.caps.push(c);
        }
        // every data symbol's address is its linked address (S6): in range and aligned
        for (name, v) in self.ck.sym_vars.clone() {
            let (size, align) = self.ck.sym_info[&name];
            let l = Lin::var(v);
            self.add_fact(&mut st, Formula::Ge(l.clone()));
            self.add_fact(
                &mut st,
                Formula::le(&l.add_const(size).unwrap(), &Lin::konst(TWO64)).unwrap(),
            );
            if align > 1 {
                self.add_fact(&mut st, Formula::Dvd(align, l.clone()));
            }
        }
        for sd in self.ck.statics.clone() {
            let l = Lin::var(sd.var);
            let c = self.new_cap(
                Formula::True,
                CapKind::Bytes {
                    base: l,
                    len: Lin::konst(sd.size),
                    mode: Mode::Ro,
                    heap: false,
                    fields: sd.fields.clone(),
                },
            );
            self.static_ids.push(c.id);
            st.caps.push(c);
        }
        Ok(st)
    }

    // ------------------------------------------------------------------ main pass

    fn run(&mut self) -> F<()> {
        self.structure()?;
        let n = self.f.instrs.len();
        let mut incoming: Vec<Vec<(usize, State)>> = vec![Vec::new(); n];
        let entry = self.entry_state()?;
        incoming[0].push((usize::MAX, entry));
        for ix in self.order.clone() {
            let edges = std::mem::take(&mut incoming[ix]);
            self.line = self.f.instrs[ix].line;
            let st = if let Some((inv, line)) = self.f.invs.get(&ix).cloned() {
                if edges.is_empty() {
                    continue;
                }
                self.build_point(ix, &inv, line, edges)?
            } else {
                if edges.is_empty() {
                    continue;
                }
                self.join(edges.into_iter().map(|e| e.1).collect())?
            };
            if self.ck.record {
                let s = self.fstate(&st);
                self.states.push((ix, self.f.instrs[ix].line, s));
                self.snapshots.push((ix, st.clone()));
            }
            let succs = self.step(ix, st)?;
            for (t, s) in succs {
                self.line = self.f.instrs[ix].line;
                if t >= n {
                    return self.err(Rule::Cfg, "control falls off the end of the function");
                }
                if !self.back.contains(&(ix, t)) {
                    incoming[t].push((ix, s));
                } else {
                    self.back_edge(ix, t, s)?;
                }
            }
        }
        Ok(())
    }

    /// A forward join without annotation (I16, note decision 2).
    fn join(&mut self, mut edges: Vec<State>) -> F<State> {
        if edges.len() == 1 {
            return Ok(edges.pop().unwrap());
        }
        let d = edges[0].depth;
        if edges.iter().any(|e| e.depth != d) {
            return self.err(
                Rule::StackShape,
                "the frame depth differs between the edges into this point (S3)",
            );
        }
        let mut out = edges[0].clone();
        for r in Reg::all().skip(1) {
            let e0 = &edges[0].regs[r.0 as usize];
            if edges.iter().any(|e| e.regs[r.0 as usize] != *e0) {
                out.regs[r.0 as usize] = Lin::var(self.fresh(r.name()));
            }
        }
        out.facts
            .retain(|(id, _)| edges.iter().all(|e| e.facts.iter().any(|(j, _)| j == id)));
        out.slots
            .retain(|k, v| edges.iter().all(|e| e.slots.get(k) == Some(v)));
        let mut caps = Vec::new();
        for c in &edges[0].caps {
            let others: Vec<&Cap> = edges[1..]
                .iter()
                .filter_map(|e| e.caps.iter().find(|d| d.id == c.id))
                .collect();
            if others.len() + 1 != edges.len() {
                continue;
            }
            let mut c = c.clone();
            let mut guards = vec![c.guard.clone()];
            for o in &others {
                if o.guard != c.guard {
                    guards.push(o.guard.clone());
                }
                if let (CapKind::Bytes { fields, .. }, CapKind::Bytes { fields: of, .. }) =
                    (&mut c.kind, &o.kind)
                {
                    fields.retain(|k, v| of.get(k) == Some(v));
                }
            }
            if guards.len() > 1 {
                c.guard = Formula::and(guards);
            }
            caps.push(c);
        }
        out.caps = caps;
        Ok(out)
    }

    /// The enclosing loop heads' variables and the signature's, for annotation names.
    fn scope_at(&self, ix: usize) -> Scope {
        let mut sc = Scope::new();
        // signature parameters: names are those given to `fresh` (unique), so map by the
        // signature's own text names.
        for (n, v) in self.sig_scope() {
            sc.insert(n, v);
        }
        for l in &self.loops {
            if l.head != ix
                && l.body.contains(&ix)
                && let Some(h) = self.heads.get(&l.head)
            {
                for (n, v) in &h.inv_vars {
                    sc.insert(n.clone(), *v);
                }
            }
        }
        sc
    }

    fn sig_scope(&self) -> Vec<(String, Var)> {
        // Parameters were created with their source names (fresh adds a suffix only on a
        // clash, then the source name is the prefix before the digits).
        self.me
            .params
            .iter()
            .map(|v| (self.me.src_names[v].clone(), *v))
            .chain(self.ck.sym_vars.iter().map(|(n, v)| (format!("@{n}"), *v)))
            .collect()
    }

    /// A loop head or an annotated forward join: build its state type from the annotation
    /// and the incoming edges, and check every incoming edge against it (D7).
    fn build_point(
        &mut self,
        ix: usize,
        inv: &SInv,
        line: usize,
        edges: Vec<(usize, State)>,
    ) -> F<State> {
        self.line = line;
        let rule = if inv.is_loop {
            Rule::LoopInv
        } else {
            Rule::Join
        };
        let d = edges[0].1.depth;
        if edges.iter().any(|e| e.1.depth != d) {
            return self.err(
                Rule::StackShape,
                "the frame depth differs between the edges into this point (S3)",
            );
        }
        let mut scope = self.scope_at(ix);
        let mut inv_vars = Vec::new();
        let mut bound = Vec::new();
        for n in &inv.vars {
            let v = self.fresh(n);
            scope.insert(n.clone(), v);
            inv_vars.push((n.clone(), v));
            bound.push(v);
        }
        let written: BTreeSet<Reg> = if inv.is_loop {
            self.loops
                .iter()
                .find(|l| l.head == ix)
                .map(|l| l.written.clone())
                .unwrap_or_default()
        } else {
            BTreeSet::new()
        };
        let mut st = edges[0].1.clone();
        let mut annotated = BTreeSet::new();
        let mut where_facts = Vec::new();
        for rt in &inv.regs {
            if rt.reg == ZERO || rt.reg == SP {
                return self.err(Rule::Syntax, format!("{} cannot be annotated", rt.reg));
            }
            let e = match &rt.expr {
                Some(e) => sig::lin(e, &scope).map_err(|m| CheckError {
                    rule: Rule::Syntax,
                    line,
                    msg: m,
                })?,
                None => {
                    let v = self.fresh(rt.reg.name());
                    bound.push(v);
                    Lin::var(v)
                }
            };
            if let Some(k) = rt.range {
                where_facts.push(sig::range_fact(k, &e));
            }
            annotated.insert(rt.reg);
            st.regs[rt.reg.0 as usize] = e;
        }
        for r in Reg::all().skip(1) {
            if annotated.contains(&r) {
                continue;
            }
            let e0 = &edges[0].1.regs[r.0 as usize];
            if written.contains(&r) || edges.iter().any(|e| e.1.regs[r.0 as usize] != *e0) {
                let v = self.fresh(r.name());
                bound.push(v);
                st.regs[r.0 as usize] = Lin::var(v);
            }
        }
        st.facts
            .retain(|(id, _)| edges.iter().all(|e| e.1.facts.iter().any(|(j, _)| j == id)));
        st.slots.retain(|k, v| {
            edges.iter().all(|e| e.1.slots.get(k) == Some(v))
                && !self.drops.slots.contains(&(ix, *k))
        });
        st.caps
            .retain(|c| edges.iter().all(|e| e.1.caps.iter().any(|d| d.id == c.id)));
        for c in st.caps.iter_mut() {
            if let CapKind::Bytes { fields, .. } = &mut c.kind {
                fields.retain(|k, v| {
                    !self.drops.fields.contains(&(ix, c.id, *k))
                        && edges.iter().all(|e| {
                            e.1.caps.iter().any(|d| d.id == c.id && matches!(&d.kind, CapKind::Bytes { fields: g, .. } if g.get(k) == Some(v)))
                        })
                });
            }
            // a guard that differs between edges: the conjunction (weaker capability)
            let gs: Vec<Formula> = edges
                .iter()
                .filter_map(|e| {
                    e.1.caps
                        .iter()
                        .find(|d| d.id == c.id)
                        .map(|d| d.guard.clone())
                })
                .collect();
            if gs.iter().any(|g| *g != c.guard) {
                c.guard = Formula::and(gs);
            }
        }
        for f in &inv.wher {
            where_facts.push(sig::formula(f, &scope).map_err(|m| CheckError {
                rule: Rule::Syntax,
                line,
                msg: m,
            })?);
        }
        for f in where_facts {
            self.add_fact(&mut st, f);
        }
        let measure = match &inv.decreases {
            Some(e) => Some(sig::lin(e, &scope).map_err(|m| CheckError {
                rule: Rule::Syntax,
                line,
                msg: m,
            })?),
            None => None,
        };
        // (P1: an `inv` on a label that heads no loop is a `join` and needs no measure)
        let heads_loop = self.loops.iter().any(|l| l.head == ix);
        if inv.is_loop && heads_loop && measure.is_none() && !self.me.partial {
            return self.err(
                Rule::LoopDecreases,
                "a loop of a function that is not 'partial' needs 'decreases'",
            );
        }
        let head = Head {
            state: st.clone(),
            bound,
            inv_vars,
            measure,

            line,
        };
        for (src, e) in &edges {
            self.line = if *src == usize::MAX {
                self.f.line
            } else {
                self.f.instrs[*src].line
            };
            let theta = self.instantiate_head(&head, e, *src)?;
            if self.ck.record {
                self.thetas.push((*src, ix, theta.clone()));
            }
            self.subtype(e, &head, &theta, rule, None)?;
        }
        self.heads.insert(ix, head);
        Ok(st)
    }

    /// θ for the head's bound variables on an edge with state `e`.
    fn instantiate_head(&mut self, h: &Head, e: &State, src: usize) -> F<BTreeMap<Var, Lin>> {
        let mut th: BTreeMap<Var, Lin> = BTreeMap::new();
        // fresh register variables: the edge's expressions
        for r in Reg::all().skip(1) {
            if let Some(v) = h.state.regs[r.0 as usize].as_var()
                && h.bound.contains(&v)
            {
                th.entry(v).or_insert_with(|| e.regs[r.0 as usize].clone());
            }
        }
        let eqs: Vec<(Lin, Lin)> = Reg::all()
            .skip(1)
            .map(|r| {
                (
                    h.state.regs[r.0 as usize].clone(),
                    e.regs[r.0 as usize].clone(),
                )
            })
            .collect();
        let hints = if src == usize::MAX {
            vec![]
        } else {
            self.f.instrs[src].hints.clone()
        };
        let scope: Scope = h.inv_vars.iter().cloned().collect();
        self.solve_vars(&mut th, &h.bound, &eqs, &hints, &scope, e)?;
        for v in &h.bound {
            if !th.contains_key(v) {
                let n = self.ck.names.name(*v).to_string();
                return self.err(Rule::CallInst, format!("cannot instantiate '{n}' on this edge: type a register with a bare int({n}), or write '#: with {n} := …' before the jump"));
            }
        }
        if self.ck.record {
            for (v, x) in &th {
                if h.inv_vars.iter().any(|(_, w)| w == v) {
                    self.insts.push((
                        self.line,
                        format!("head line {}", h.line),
                        format!("{} := {}", self.ck.names.name(*v), self.show(x)),
                    ));
                }
            }
        }
        Ok(th)
    }

    /// Fills θ for `vars`: bare equations `x = e`, then equations solvable for one unknown
    /// with a coefficient dividing the rest, then hints. Only a choice of θ: every
    /// obligation is still proved afterwards.
    fn solve_vars(
        &mut self,
        th: &mut BTreeMap<Var, Lin>,
        vars: &[Var],
        eqs: &[(Lin, Lin)],
        hints: &[(String, SLin)],
        hint_scope: &Scope,
        st: &State,
    ) -> F<()> {
        for (pat, val) in eqs {
            if let Some(v) = pat.as_var()
                && vars.contains(&v)
            {
                th.entry(v).or_insert_with(|| val.clone());
            }
        }
        loop {
            let mut progress = false;
            for (pat, val) in eqs {
                let unknown: Vec<Var> = pat
                    .vars()
                    .filter(|v| vars.contains(v) && !th.contains_key(v))
                    .collect();
                if unknown.len() != 1 {
                    continue;
                }
                let x = unknown[0];
                let c = pat.coef(x);
                let mut rest = pat.clone();
                rest.terms.remove(&x);
                let Some(rest) = rest.subst_all(th) else {
                    continue;
                };
                let Some(num) = val.sub(&rest) else { continue };
                if num.konst % c == 0 && num.terms.values().all(|k| k % c == 0) {
                    let mut q = num.clone();
                    q.konst /= c;
                    for k in q.terms.values_mut() {
                        *k /= c;
                    }
                    th.insert(x, q);
                    progress = true;
                }
            }
            if !progress {
                break;
            }
        }
        if !hints.is_empty() {
            // hint expressions may use the signature's names and enclosing loop variables
            let mut sc = self.scope_at(usize::MAX);
            for l in &self.loops {
                if let Some(h) = self.heads.get(&l.head) {
                    for (n, v) in &h.inv_vars {
                        sc.insert(n.clone(), *v);
                    }
                }
            }
            for (n, e) in hints {
                let Some(v) = hint_scope.get(n) else { continue };
                if th.contains_key(v) {
                    continue;
                }
                let x = sig::lin(e, &sc).map_err(|m| CheckError {
                    rule: Rule::Syntax,
                    line: self.line,
                    msg: format!("in 'with': {m}"),
                })?;
                th.insert(*v, x);
            }
        }
        let _ = st;
        Ok(())
    }

    /// Σ_edge ⊑ θ(Σ_target) (the proof's D7).
    fn subtype(
        &mut self,
        e: &State,
        h: &Head,
        th: &BTreeMap<Var, Lin>,
        rule: Rule,
        back_head: Option<usize>,
    ) -> F<()> {
        let t = &h.state;
        if e.depth != t.depth {
            return self.err(
                Rule::StackShape,
                "frame depth differs from the annotated point (S3)",
            );
        }
        let sub = |x: &Lin| x.subst_all(th);
        for r in Reg::all().skip(1) {
            let Some(want) = sub(&t.regs[r.0 as usize]) else {
                return Err(ovf(self.line).into());
            };
            let have = e.regs[r.0 as usize].clone();
            if !self.prove_eq64(e, &have, &want, &format!("{r} at the annotated point")) {
                let msg = format!(
                    "{r} is {} here but the annotation at line {} needs {}{}",
                    self.show(&have),
                    h.line,
                    self.show(&want),
                    self.fail_detail(e)
                );
                return self.err(rule, msg);
            }
        }
        for (k, v) in &t.slots {
            let Some(want) = sub(v) else {
                return Err(ovf(self.line).into());
            };
            let ok = match e.slots.get(k).cloned() {
                Some(have) => self.prove_eq64(e, &have, &want, "slot"),
                None => false,
            };
            if !ok {
                if let Some(hix) = back_head {
                    let mut d = Drops::default();
                    d.slots.insert((hix, *k));
                    return Err(Fail::Retry(d));
                }
                return self.err(rule, format!("slot {k} does not match the annotated point"));
            }
        }
        for c in &t.caps {
            let Some(ec) = e.caps.iter().find(|d| d.id == c.id).cloned() else {
                return self.err(
                    rule,
                    format!(
                        "capability #{} held at the annotated point is missing on this edge{}",
                        c.id,
                        self.fail_detail(e)
                    ),
                );
            };
            let Some(g) = c.guard.map_lin(&mut |x| x.subst_all(th)) else {
                return Err(ovf(self.line).into());
            };
            if g != ec.guard && ec.guard != Formula::True {
                let imp = Formula::or(vec![Formula::negate(g), ec.guard.clone()]);
                if !self.prove(e, &imp, "capability guard") {
                    return self.err(
                        rule,
                        format!("capability #{}: its guard is weaker on this edge", c.id),
                    );
                }
            }
            if let (CapKind::Bytes { fields, .. }, CapKind::Bytes { fields: ef, .. }) =
                (&c.kind, &ec.kind)
            {
                for (k, v) in fields {
                    let Some(want) = sub(v) else {
                        return Err(ovf(self.line).into());
                    };
                    let ok = match ef.get(k).cloned() {
                        Some(have) => self.prove_eq64(e, &have, &want, "field"),
                        None => false,
                    };
                    if !ok {
                        if let Some(hix) = back_head {
                            let mut d = Drops::default();
                            d.fields.insert((hix, c.id, *k));
                            return Err(Fail::Retry(d));
                        }
                        return self.err(
                            rule,
                            format!("field {k} of capability #{} does not match", c.id),
                        );
                    }
                }
            }
        }
        for (id, f) in &t.facts {
            // Skipping by identity is right only if θ does not move the fact: a head's own
            // constraint is inherited by the back edge but is about this iteration.
            let mut fv = BTreeSet::new();
            f.vars(&mut fv);
            if e.facts.iter().any(|(j, _)| j == id) && !fv.iter().any(|v| th.contains_key(v)) {
                continue;
            }
            let Some(g) = f.map_lin(&mut |x| x.subst_all(th)) else {
                return Err(ovf(self.line).into());
            };
            if !self.prove(e, &g, "annotation constraint") {
                let msg = format!(
                    "the constraint {} of the annotation at line {} does not follow here{}",
                    self.showf(&g),
                    h.line,
                    self.fail_detail(e)
                );
                return self.err(rule, msg);
            }
        }
        Ok(())
    }

    fn back_edge(&mut self, src: usize, t: usize, e: State) -> F<()> {
        let Some(h) = self.heads.remove(&t) else {
            return self.err(
                Rule::Cfg,
                "backward jump to a loop head that was never reached",
            );
        };
        let r = (|| -> F<()> {
            let th = self.instantiate_head(&h, &e, src)?;
            if self.ck.record {
                self.thetas.push((src, t, th.clone()));
            }
            self.subtype(&e, &h, &th, Rule::LoopInv, Some(t))?;
            if let Some(m) = &h.measure {
                let Some(next) = m.subst_all(&th) else {
                    return Err(ovf(self.line).into());
                };
                let g = Formula::and(vec![
                    Formula::Ge(m.clone()),
                    Formula::lt(&next, m).ok_or_else(|| ovf(self.line))?,
                ]);
                if !self.prove(&e, &g, "decreases") {
                    let msg = format!(
                        "the measure {} does not decrease to {} while staying ≥ 0 on this back edge{}",
                        self.show(m),
                        self.show(&next),
                        self.fail_detail(&e)
                    );
                    return self.err(Rule::LoopDecreases, msg);
                }
            }
            Ok(())
        })();
        self.heads.insert(t, h);
        r
    }

    // ------------------------------------------------------------------ helpers

    fn reg(&self, st: &State, r: Reg) -> Lin {
        st.regs[r.0 as usize].clone()
    }

    fn set(&mut self, st: &mut State, rd: Reg, e: Lin) -> F<()> {
        if rd == ZERO {
            return Ok(());
        }
        if rd == SP {
            return self.err(
                Rule::StackShape,
                "sp is written only by 'addi sp, sp, ±F' (S3)",
            );
        }
        st.regs[rd.0 as usize] = e;
        Ok(())
    }

    /// A fresh variable for an unknown 64-bit word: `0 ≤ x < 2^64`.
    fn unknown_word(&mut self, st: &mut State, base: &str) -> Lin {
        let x = Lin::var(self.fresh(base));
        self.add_fact(st, Formula::in_u64(&x).unwrap());
        x
    }

    /// u(e): the unsigned representative.
    fn urep(&mut self, st: &mut State, e: &Lin) -> F<Lin> {
        if let Some(c) = e.as_const() {
            return Ok(Lin::konst(c.rem_euclid(TWO64)));
        }
        let rng = Formula::in_u64(e).ok_or_else(|| ovf(self.line))?;
        if self.prove(st, &rng, "u(e) = e") {
            return Ok(e.clone());
        }
        // witness-free (so the Lean checker can instantiate every variable of the record):
        // 2^64 ∣ e − x rather than e = x + 2^64·k
        let x = Lin::var(self.fresh("u"));
        self.add_fact(
            st,
            Formula::Dvd(TWO64, e.sub(&x).ok_or_else(|| ovf(self.line))?),
        );
        self.add_fact(st, Formula::in_u64(&x).unwrap());
        Ok(x)
    }

    /// s(e): the signed representative.
    fn srep(&mut self, st: &mut State, e: &Lin) -> F<Lin> {
        let h = TWO64 / 2;
        if let Some(c) = e.as_const() {
            let u = c.rem_euclid(TWO64);
            return Ok(Lin::konst(if u >= h { u - TWO64 } else { u }));
        }
        let rng = sig::range_fact(crate::syntax::RangeKind::I64, e);
        if self.prove(st, &rng, "s(e) = e") {
            return Ok(e.clone());
        }
        let x = Lin::var(self.fresh("s"));
        self.add_fact(
            st,
            Formula::Dvd(TWO64, e.sub(&x).ok_or_else(|| ovf(self.line))?),
        );
        self.add_fact(st, sig::range_fact(crate::syntax::RangeKind::I64, &x));
        Ok(x)
    }

    /// The quotient `q = ⌊e / d⌋` (fresh), as `0 ≤ e − d·q < d` (no remainder variable).
    fn divq(&mut self, st: &mut State, e: &Lin, d: i128) -> F<Lin> {
        let line = self.line;
        let q = Lin::var(self.fresh("q"));
        let rest = e
            .sub(&q.scale(d).ok_or_else(|| ovf(line))?)
            .ok_or_else(|| ovf(line))?;
        self.add_fact(st, Formula::Ge(rest.clone()));
        self.add_fact(
            st,
            Formula::lt(&rest, &Lin::konst(d)).ok_or_else(|| ovf(line))?,
        );
        Ok(q)
    }

    /// The remainder `r = e mod d` (fresh), as `d ∣ e − r`, `0 ≤ r < d` (no quotient variable).
    fn divr(&mut self, st: &mut State, e: &Lin, d: i128) -> F<Lin> {
        let line = self.line;
        let r = Lin::var(self.fresh("r"));
        self.add_fact(st, Formula::Dvd(d, e.sub(&r).ok_or_else(|| ovf(line))?));
        self.add_fact(st, Formula::Ge(r.clone()));
        self.add_fact(
            st,
            Formula::lt(&r, &Lin::konst(d)).ok_or_else(|| ovf(line))?,
        );
        Ok(r)
    }

    /// The 32-bit result rule: `e = x + 2^32·j`, `−2^31 ≤ x < 2^31`.
    fn word32(&mut self, st: &mut State, e: &Lin) -> F<Lin> {
        if let Some(c) = e.as_const() {
            return Ok(Lin::konst(c.rem_euclid(1 << 32) as u32 as i32 as i128));
        }
        let x = Lin::var(self.fresh("w"));
        self.add_fact(
            st,
            Formula::Dvd(1 << 32, e.sub(&x).ok_or_else(|| ovf(self.line))?),
        );
        self.add_fact(st, Formula::le(&Lin::konst(-(1 << 31)), &x).unwrap());
        self.add_fact(st, Formula::lt(&x, &Lin::konst(1 << 31)).unwrap());
        Ok(x)
    }

    /// zext32(e): `e = z + 2^32·j`, `0 ≤ z < 2^32`.
    fn zext32(&mut self, st: &mut State, e: &Lin) -> F<Lin> {
        if let Some(c) = e.as_const() {
            return Ok(Lin::konst(c.rem_euclid(1 << 32)));
        }
        self.divr(st, e, 1 << 32)
    }

    /// `x` with `x = 1 ⇔ a < b` (given representatives).
    fn set_less(&mut self, st: &mut State, a: &Lin, b: &Lin) -> F<Lin> {
        if let (Some(x), Some(y)) = (a.as_const(), b.as_const()) {
            return Ok(Lin::konst((x < y) as i128));
        }
        let x = Lin::var(self.fresh("b"));
        let one = Formula::eq(&x, &Lin::konst(1)).unwrap();
        let zero = Formula::eq(&x, &Lin::konst(0)).unwrap();
        let lt = Formula::lt(a, b).ok_or_else(|| ovf(self.line))?;
        let ge = Formula::le(b, a).ok_or_else(|| ovf(self.line))?;
        self.add_fact(
            st,
            Formula::or(vec![
                Formula::and(vec![one, lt]),
                Formula::and(vec![zero, ge]),
            ]),
        );
        Ok(x)
    }

    // ------------------------------------------------------------------ one instruction

    fn step(&mut self, ix: usize, mut st: State) -> F<Vec<(usize, State)>> {
        let pi: &PInstr = &self.f.instrs[ix];
        let ins = pi.instr.clone();
        let next = ix + 1;
        let me = self.me;
        // I30: the immediate of a `%pcrel_lo(label)` operand is the variable L of that auipc
        let sym_off: Option<Lin> = match &pi.reloc {
            Some(Reloc::PcrelLo(label)) => {
                let aix = self.f.labels[label];
                Some(Lin::var(self.lo_var(aix)))
            }
            _ => None,
        };
        if let (Instr::Auipc { rd, .. }, Some(Reloc::PcrelHi(sym))) = (&ins, &pi.reloc) {
            // auipc rd, %pcrel_hi(sym) = ℓ_sym − lo, where lo is the paired %pcrel_lo value
            let l = self.ck.sym_vars[sym];
            let lo = self.lo_var(ix);
            let e = Lin::var(l)
                .sub(&Lin::var(lo))
                .ok_or_else(|| ovf(self.line))?;
            self.set(&mut st, *rd, e)?;
            return Ok(vec![(next, st)]);
        }
        if let Some(off) = sym_off.clone() {
            match &ins {
                Instr::IOp {
                    op: IOp::Addi,
                    rd,
                    rs1,
                    ..
                } => {
                    let e = self
                        .reg(&st, *rs1)
                        .add(&off)
                        .ok_or_else(|| ovf(self.line))?;
                    self.set(&mut st, *rd, e)?;
                }
                Instr::Load { op, rd, rs1, .. } => self.load(&mut st, *op, *rd, *rs1, off)?,
                Instr::Store { op, rs1, rs2, .. } => self.store(&mut st, *op, *rs1, *rs2, off)?,
                _ => unreachable!("checked by structure()"),
            }
            return Ok(vec![(next, st)]);
        }
        // constant folding: all register operands constant
        if let Some((rd, r1, r2)) = comp_operands(&ins) {
            let a = st.regs[r1.0 as usize].as_const();
            let b = st.regs[r2.0 as usize].as_const();
            if let (Some(a), Some(b)) = (a, b)
                && !(rd == SP)
            {
                let (a, b) = (a.rem_euclid(TWO64) as u64, b.rem_euclid(TWO64) as u64);
                if let Some(v) = eval(&ins, a, b) {
                    self.set(&mut st, rd, Lin::konst(v as i128))?;
                    return Ok(vec![(next, st)]);
                }
            }
        }
        let line_ = self.line;
        let ovf_ = move || ovf(line_);
        match ins {
            Instr::IOp {
                op: IOp::Addi,
                rd,
                rs1,
                imm,
            } if rd == SP => {
                if rs1 != SP {
                    return self.err(
                        Rule::StackShape,
                        "sp is written only by 'addi sp, sp, ±F' (S3)",
                    );
                }
                self.frame_move(&mut st, imm)?;
                Ok(vec![(next, st)])
            }
            Instr::IOp { op, rd, rs1, imm } => {
                let e = self.reg(&st, rs1);
                let v = match op {
                    IOp::Addi => e.add_const(imm as i128).ok_or_else(ovf_)?,
                    IOp::Xori if imm == -1 => Lin::konst(-1).sub(&e).ok_or_else(ovf_)?,
                    IOp::Andi => self.and_const(&mut st, &e, imm as i128)?,
                    IOp::Ori => self.bitop(&mut st, BitOp::Or, &e, &Lin::konst(imm as i128))?,
                    IOp::Xori => self.bitop(&mut st, BitOp::Xor, &e, &Lin::konst(imm as i128))?,
                    IOp::Sltiu => {
                        let u = self.urep(&mut st, &e)?;
                        self.set_less(&mut st, &u, &Lin::konst((imm as i128).rem_euclid(TWO64)))?
                    }
                    IOp::Slti => {
                        let s = self.srep(&mut st, &e)?;
                        self.set_less(&mut st, &s, &Lin::konst(imm as i128))?
                    }
                };
                self.set(&mut st, rd, v)?;
                Ok(vec![(next, st)])
            }
            Instr::Lui { rd, imm } => {
                let v = ((imm as u64) << 12) as u32 as i32 as i128;
                self.set(&mut st, rd, Lin::konst(v))?;
                Ok(vec![(next, st)])
            }
            Instr::Addiw { rd, rs1, imm } => {
                let e = self.reg(&st, rs1).add_const(imm as i128).ok_or_else(ovf_)?;
                let v = self.word32(&mut st, &e)?;
                self.set(&mut st, rd, v)?;
                Ok(vec![(next, st)])
            }
            Instr::Shift { op, rd, rs1, sh } => {
                let e = self.reg(&st, rs1);
                let p = 1i128 << sh;
                let v = match op {
                    ShOp::Slli => e.scale(p).ok_or_else(ovf_)?,
                    ShOp::Srli => {
                        let u = self.urep(&mut st, &e)?;
                        self.divq(&mut st, &u, p)?
                    }
                    ShOp::Srai => {
                        let s = self.srep(&mut st, &e)?;
                        self.divq(&mut st, &s, p)?
                    }
                    ShOp::SlliUw => {
                        let z = self.zext32(&mut st, &e)?;
                        z.scale(p).ok_or_else(ovf_)?
                    }
                    ShOp::Rori => self.unknown_word(&mut st, "x"),
                };
                self.set(&mut st, rd, v)?;
                Ok(vec![(next, st)])
            }
            Instr::ShiftW { op, rd, rs1, sh } => {
                let e = self.reg(&st, rs1);
                let v = match op {
                    ShWOp::Slliw => {
                        let m = e.scale(1i128 << sh).ok_or_else(ovf_)?;
                        self.word32(&mut st, &m)?
                    }
                    // srliw by c ≥ 1: the low word shifted right, < 2^31, so sign extension
                    // keeps it: zext32(e) = 2^c·x + r
                    ShWOp::Srliw if sh >= 1 => {
                        let z = self.zext32(&mut st, &e)?;
                        self.divq(&mut st, &z, 1i128 << sh)?
                    }
                    _ => self.unknown_word(&mut st, "x"),
                };
                self.set(&mut st, rd, v)?;
                Ok(vec![(next, st)])
            }
            Instr::ROp { op, rd, rs1, rs2 } => {
                let (a, b) = (self.reg(&st, rs1), self.reg(&st, rs2));
                let v = match op {
                    ROp::Add => a.add(&b).ok_or_else(ovf_)?,
                    ROp::Sub => a.sub(&b).ok_or_else(ovf_)?,
                    ROp::Sh1add | ROp::Sh2add | ROp::Sh3add => {
                        let k = match op {
                            ROp::Sh1add => 2,
                            ROp::Sh2add => 4,
                            _ => 8,
                        };
                        a.scale(k).and_then(|x| x.add(&b)).ok_or_else(ovf_)?
                    }
                    ROp::Mul => match (a.as_const(), b.as_const()) {
                        (Some(c), _) => b.scale(c).ok_or_else(ovf_)?,
                        (_, Some(c)) => a.scale(c).ok_or_else(ovf_)?,
                        _ => self.unknown_word(&mut st, "x"),
                    },
                    ROp::And => match (a.as_const(), b.as_const()) {
                        (Some(c), _) => self.and_const(&mut st, &b, signed64(c))?,
                        (_, Some(c)) => self.and_const(&mut st, &a, signed64(c))?,
                        _ => self.bitop(&mut st, BitOp::And, &a, &b)?,
                    },
                    ROp::Or => self.bitop(&mut st, BitOp::Or, &a, &b)?,
                    ROp::Xor => self.bitop(&mut st, BitOp::Xor, &a, &b)?,
                    ROp::Sltu => {
                        let (ua, ub) = (self.urep(&mut st, &a)?, self.urep(&mut st, &b)?);
                        self.set_less(&mut st, &ua, &ub)?
                    }
                    ROp::Slt => {
                        let (sa, sb) = (self.srep(&mut st, &a)?, self.srep(&mut st, &b)?);
                        self.set_less(&mut st, &sa, &sb)?
                    }
                    ROp::Minu | ROp::Maxu | ROp::Min | ROp::Max => {
                        let unsigned = matches!(op, ROp::Minu | ROp::Maxu);
                        let (ra, rb) = if unsigned {
                            (self.urep(&mut st, &a)?, self.urep(&mut st, &b)?)
                        } else {
                            (self.srep(&mut st, &a)?, self.srep(&mut st, &b)?)
                        };
                        let x = Lin::var(self.fresh("m"));
                        let min = matches!(op, ROp::Minu | ROp::Min);
                        let (f1, f2) = if min {
                            (Formula::le(&x, &ra), Formula::le(&x, &rb))
                        } else {
                            (Formula::le(&ra, &x), Formula::le(&rb, &x))
                        };
                        self.add_fact(&mut st, f1.ok_or_else(ovf_)?);
                        self.add_fact(&mut st, f2.ok_or_else(ovf_)?);
                        let eitheror = Formula::or(vec![
                            Formula::eq(&x, &ra).ok_or_else(ovf_)?,
                            Formula::eq(&x, &rb).ok_or_else(ovf_)?,
                        ]);
                        self.add_fact(&mut st, eitheror);
                        x
                    }
                    ROp::Remu | ROp::Divu => {
                        let ua = self.urep(&mut st, &a)?;
                        match b.as_const().map(|c| c.rem_euclid(TWO64)) {
                            Some(c) if c > 0 => {
                                if op == ROp::Remu {
                                    self.divr(&mut st, &ua, c)?
                                } else {
                                    self.divq(&mut st, &ua, c)?
                                }
                            }
                            _ => {
                                let ub = self.urep(&mut st, &b)?;
                                let pos = Formula::lt(&Lin::konst(0), &ub).ok_or_else(ovf_)?;
                                let x = self.unknown_word(&mut st, "x");
                                if op == ROp::Remu && self.prove(&st, &pos, "remu divisor > 0") {
                                    self.add_fact(&mut st, Formula::lt(&x, &ub).ok_or_else(ovf_)?);
                                    self.add_fact(&mut st, Formula::le(&x, &ua).ok_or_else(ovf_)?);
                                } else if op == ROp::Divu
                                    && self.prove(&st, &pos, "divu divisor > 0")
                                {
                                    self.add_fact(&mut st, Formula::le(&x, &ua).ok_or_else(ovf_)?);
                                }
                                x
                            }
                        }
                    }
                    _ => self.unknown_word(&mut st, "x"),
                };
                self.set(&mut st, rd, v)?;
                Ok(vec![(next, st)])
            }
            Instr::RWOp { op, rd, rs1, rs2 } => {
                let (a, b) = (self.reg(&st, rs1), self.reg(&st, rs2));
                let v = match op {
                    RWOp::Addw => {
                        let s = a.add(&b).ok_or_else(ovf_)?;
                        self.word32(&mut st, &s)?
                    }
                    RWOp::Subw => {
                        let s = a.sub(&b).ok_or_else(ovf_)?;
                        self.word32(&mut st, &s)?
                    }
                    // srlw by a constant amount c (mod 32) ≥ 1: as srliw
                    RWOp::Srlw if b.as_const().is_some_and(|c| c.rem_euclid(32) >= 1) => {
                        let c = b.as_const().unwrap().rem_euclid(32);
                        let z = self.zext32(&mut st, &a)?;
                        self.divq(&mut st, &z, 1i128 << c)?
                    }
                    RWOp::Mulw if a.is_const() || b.is_const() => {
                        let s = match (a.as_const(), b.as_const()) {
                            (Some(c), _) => b.scale(c),
                            (_, Some(c)) => a.scale(c),
                            _ => None,
                        }
                        .ok_or_else(ovf_)?;
                        self.word32(&mut st, &s)?
                    }
                    RWOp::AddUw | RWOp::Sh1addUw | RWOp::Sh2addUw | RWOp::Sh3addUw => {
                        let k = match op {
                            RWOp::AddUw => 1,
                            RWOp::Sh1addUw => 2,
                            RWOp::Sh2addUw => 4,
                            _ => 8,
                        };
                        let z = self.zext32(&mut st, &a)?;
                        z.scale(k).and_then(|x| x.add(&b)).ok_or_else(ovf_)?
                    }
                    _ => self.unknown_word(&mut st, "x"),
                };
                self.set(&mut st, rd, v)?;
                Ok(vec![(next, st)])
            }
            Instr::UOp { op, rd, rs1 } => {
                let e = self.reg(&st, rs1);
                let v = match op {
                    UOp::ZextH => self.divr(&mut st, &e, 1 << 16)?,
                    UOp::Clz | UOp::Ctz | UOp::Cpop => {
                        let x = self.unknown_word(&mut st, "x");
                        self.add_fact(&mut st, Formula::le(&x, &Lin::konst(64)).unwrap());
                        x
                    }
                    UOp::Clzw | UOp::Ctzw | UOp::Cpopw => {
                        let x = self.unknown_word(&mut st, "x");
                        self.add_fact(&mut st, Formula::le(&x, &Lin::konst(32)).unwrap());
                        x
                    }
                    _ => self.unknown_word(&mut st, "x"),
                };
                self.set(&mut st, rd, v)?;
                Ok(vec![(next, st)])
            }
            Instr::Load { op, rd, rs1, off } => {
                self.load(&mut st, op, rd, rs1, Lin::konst(off as i128))?;
                Ok(vec![(next, st)])
            }
            Instr::Store { op, rs1, rs2, off } => {
                self.store(&mut st, op, rs1, rs2, Lin::konst(off as i128))?;
                Ok(vec![(next, st)])
            }
            Instr::Branch {
                op,
                rs1,
                rs2,
                target,
            } => {
                let Target::Local(t) = target else {
                    unreachable!()
                };
                let (a, b) = (self.reg(&st, rs1), self.reg(&st, rs2));
                let (taken, not) = match op {
                    BrOp::Beq | BrOp::Bne => {
                        let d = a.sub(&b).ok_or_else(ovf_)?;
                        let eq = Formula::Dvd(TWO64, d);
                        if op == BrOp::Beq {
                            (eq.clone(), Formula::negate(eq))
                        } else {
                            (Formula::negate(eq.clone()), eq)
                        }
                    }
                    BrOp::Bltu | BrOp::Bgeu => {
                        let (ua, ub) = (self.urep(&mut st, &a)?, self.urep(&mut st, &b)?);
                        let lt = Formula::lt(&ua, &ub).ok_or_else(ovf_)?;
                        let ge = Formula::le(&ub, &ua).ok_or_else(ovf_)?;
                        if op == BrOp::Bltu { (lt, ge) } else { (ge, lt) }
                    }
                    BrOp::Blt | BrOp::Bge => {
                        let (sa, sb) = (self.srep(&mut st, &a)?, self.srep(&mut st, &b)?);
                        let lt = Formula::lt(&sa, &sb).ok_or_else(ovf_)?;
                        let ge = Formula::le(&sb, &sa).ok_or_else(ovf_)?;
                        if op == BrOp::Blt { (lt, ge) } else { (ge, lt) }
                    }
                };
                let mut out = Vec::new();
                for (tgt, f) in [(t, taken), (next, not)] {
                    // an edge whose condition the facts refute is never taken (I24); asked as
                    // Ψ ⊢ ¬f rather than Ψ ∧ f ⊢ false, so unrelated facts are left out
                    if self.prove(&st, &Formula::negate(f.clone()), "edge reachable?") {
                        continue;
                    }
                    let mut s = st.clone();
                    self.add_fact(&mut s, f);
                    out.push((tgt, s));
                }
                Ok(out)
            }
            Instr::Jal { rd, target } => match target {
                Target::Local(t) => Ok(vec![(t, st)]),
                Target::Symbol(f) => {
                    if rd == ZERO {
                        self.tail_call(&st, &f, ix)?;
                        Ok(vec![])
                    } else {
                        let s = self.call(&st, &f, ix, RA)?;
                        Ok(vec![(next, s)])
                    }
                }
            },
            Instr::CallPair { rd, tmp, target } => {
                let Target::Symbol(f) = target else {
                    unreachable!()
                };
                if rd == ZERO {
                    // tmp is clobbered before the jump; the callee sees it as int
                    let mut s = st.clone();
                    let v = self.fresh(tmp.name());
                    self.set(&mut s, tmp, Lin::var(v))?;
                    self.tail_call(&s, &f, ix)?;
                    Ok(vec![])
                } else {
                    let s = self.call(&st, &f, ix, tmp)?;
                    Ok(vec![(next, s)])
                }
            }
            Instr::Jalr { .. } => {
                self.ret(&st, None, ix)?;
                Ok(vec![])
            }
            Instr::Ecall => {
                let a7 = self.reg(&st, A7);
                let Some(num) = a7.as_const() else {
                    return self.err(
                        Rule::Syscall,
                        format!("ecall needs a7 to be a constant, it is {}", self.show(&a7)),
                    );
                };
                match num {
                    93 | 94 => Ok(vec![]),
                    63 | 64 => {
                        let Some(sg) = sig::syscall_sig(num, &mut self.ck.names) else {
                            unreachable!()
                        };
                        let s = self.apply_call(&st, &sg, ix, None)?;
                        Ok(vec![(next, s)])
                    }
                    _ => self.err(
                        Rule::Syscall,
                        format!("syscall {num} is not one of 63, 64, 93, 94"),
                    ),
                }
            }
            Instr::Unimp => self.err(
                Rule::Profile,
                "unimp has no step: a safe function may not reach it",
            ),
            Instr::Auipc { .. } => self.err(Rule::StaticData, "auipc (I14)"),
            #[allow(unreachable_patterns)]
            _ => {
                let _ = me;
                self.err(Rule::Profile, "instruction not handled")
            }
        }
    }

    /// `and`/`or`/`xor` (I29): exact on two values provably in {0, 1}; `or`/`xor` with a
    /// constant whose bits are provably disjoint from the other operand's is `+`; an `xor`
    /// result remembers its operands for the mask rule in `and_const`.
    fn bitop(&mut self, st: &mut State, op: BitOp, a: &Lin, b: &Lin) -> F<Lin> {
        let line_ = self.line;
        let ovf_ = move || ovf(line_);
        // constant operand (or both: folded earlier)
        let (x, c) = match (a.as_const(), b.as_const()) {
            (_, Some(c)) => (a.clone(), Some(c)),
            (Some(c), _) => (b.clone(), Some(c)),
            _ => (a.clone(), None),
        };
        if let (Some(c), BitOp::Or | BitOp::Xor) = (c, op) {
            let cu = c.rem_euclid(TWO64);
            if cu == 0 {
                return Ok(x);
            }
            let u = self.urep(st, &x)?;
            let j = cu.trailing_zeros();
            if j > 0
                && self.prove(
                    st,
                    &Formula::lt(&u, &Lin::konst(1i128 << j)).ok_or_else(ovf_)?,
                    "bits below the constant's",
                )
            {
                return Ok(u.add_const(cu).ok_or_else(ovf_)?);
            }
            let top = 128 - cu.leading_zeros();
            if top < 64
                && self.prove(
                    st,
                    &Formula::Dvd(1i128 << top, u.clone()),
                    "bits above the constant's",
                )
            {
                return Ok(u.add_const(cu).ok_or_else(ovf_)?);
            }
        }
        if c.is_none() {
            let bit = |e: &Lin| {
                Formula::and(vec![
                    Formula::Ge(e.clone()),
                    Formula::le(e, &Lin::konst(1)).unwrap_or(Formula::False),
                ])
            };
            if self.prove(st, &bit(a), "0/1 operand") && self.prove(st, &bit(b), "0/1 operand") {
                let x = Lin::var(self.fresh("b"));
                let eqc =
                    |e: &Lin, v: i128| Formula::eq(e, &Lin::konst(v)).unwrap_or(Formula::False);
                let mut cases = Vec::new();
                for (p, q) in [(0, 0), (0, 1), (1, 0), (1, 1)] {
                    let r = match op {
                        BitOp::And => p & q,
                        BitOp::Or => p | q,
                        BitOp::Xor => p ^ q,
                    };
                    cases.push(Formula::and(vec![eqc(a, p), eqc(b, q), eqc(&x, r)]));
                }
                self.add_fact(st, Formula::or(cases));
                return Ok(x);
            }
        }
        let x = self.unknown_word(st, "x");
        if op == BitOp::Xor
            && let Some(v) = x.as_var()
        {
            self.xor_defs.insert(v, (a.clone(), b.clone()));
            // a xor b = 0 ⇔ a ≡ b (mod 2^64)
            let d = a.sub(b).ok_or_else(|| ovf(self.line))?;
            let zero = Formula::Eq(x.clone());
            let f = Formula::or(vec![
                Formula::and(vec![zero.clone(), Formula::Dvd(TWO64, d.clone())]),
                Formula::and(vec![
                    Formula::negate(zero),
                    Formula::negate(Formula::Dvd(TWO64, d)),
                ]),
            ]);
            self.add_fact(st, f);
        }
        Ok(x)
    }

    /// `andi`-style rule for a constant mask `c` (signed 64-bit).
    fn and_const(&mut self, st: &mut State, e: &Lin, c: i128) -> F<Lin> {
        let line_ = self.line;
        let ovf_ = move || ovf(line_);
        if c >= 0 && (c + 1).count_ones() == 1 {
            // c = 2^k − 1: x = e mod 2^k
            let r = self.divr(st, e, c + 1)?;
            // (a xor b) mod 2^k = 0 ⇔ a ≡ b (mod 2^k)
            if let Some((a, b)) = e.as_var().and_then(|v| self.xor_defs.get(&v)).cloned() {
                self.xor_bits.insert((c + 1).trailing_zeros());
                let d = a.sub(&b).ok_or_else(ovf_)?;
                let zero = Formula::Eq(r.clone());
                let f = Formula::or(vec![
                    Formula::and(vec![zero.clone(), Formula::Dvd(c + 1, d.clone())]),
                    Formula::and(vec![
                        Formula::negate(zero),
                        Formula::negate(Formula::Dvd(c + 1, d)),
                    ]),
                ]);
                self.add_fact(st, f);
            }
            return Ok(r);
        }
        if c < 0 && (-c).count_ones() == 1 {
            // c = −2^k: x = u(e) − (u(e) mod 2^k)
            let u = self.urep(st, e)?;
            let q = self.divq(st, &u, -c)?;
            return Ok(q.scale(-c).ok_or_else(ovf_)?);
        }
        if c >= 0 && c.count_ones() == 1 {
            // a single bit 2^k: x ∈ {0, 2^k}, x = 2^k ⇔ bit k of e is set
            let q = self.divq(st, e, c)?; // 0 ≤ e − c·q < c
            let bit = self.divr(st, &q, 2)?; // 2 ∣ q − bit
            return Ok(bit.scale(c).ok_or_else(ovf_)?);
        }
        let x = self.unknown_word(st, "x");
        if c >= 0 {
            self.add_fact(st, Formula::le(&x, &Lin::konst(c)).unwrap());
        }
        Ok(x)
    }

    // ------------------------------------------------------------------ frame

    fn frame_move(&mut self, st: &mut State, imm: i64) -> F<()> {
        let me = self.me;
        let Some(fr) = me.frame.clone() else {
            return self.err(
                Rule::StackShape,
                "sp moves but the signature declares no 'frame' (I8)",
            );
        };
        let s0 = Lin::var(self.sigma0);
        if imm as i128 == -fr.size && st.depth == 0 {
            st.depth = fr.size;
            st.regs[SP.0 as usize] = s0.add_const(-fr.size).unwrap();
            st.slots.clear();
            self.frame_ids.clear();
            for (o, l) in &fr.addr {
                let c = self.new_cap(
                    Formula::True,
                    CapKind::Bytes {
                        base: s0.add_const(o - fr.size).unwrap(),
                        len: Lin::konst(*l),
                        mode: Mode::Rw,
                        heap: false,
                        fields: BTreeMap::new(),
                    },
                );
                self.frame_ids.push(c.id);
                st.caps.push(c);
            }
            Ok(())
        } else if imm as i128 == fr.size && st.depth == fr.size {
            for id in self.frame_ids.clone() {
                match st.caps.iter().find(|c| c.id == id) {
                    Some(c) if c.guard == Formula::True => {}
                    _ => return self.err(Rule::Frame, "the epilogue needs every address-taken frame range back (it was given away)"),
                }
            }
            st.caps.retain(|c| !self.frame_ids.contains(&c.id));
            st.slots.clear();
            st.depth = 0;
            st.regs[SP.0 as usize] = s0;
            Ok(())
        } else {
            self.err(Rule::StackShape, format!("'addi sp, sp, {imm}' at depth {}: only -{} (prologue) and {} (epilogue) are allowed (S3)", st.depth, fr.size, fr.size))
        }
    }

    fn slot_of(&self, st: &State, rs1: Reg, off: i128) -> Option<i128> {
        if rs1 != SP || st.depth == 0 {
            return None;
        }
        let fr = self.me.frame.as_ref()?;
        fr.slots.contains(&off).then_some(off)
    }

    // ------------------------------------------------------------------ memory

    /// The capability covering `[a, a + w)`, with `w ∣ a`; its index in `st.caps`.
    /// The capability covering the access, and the address expression used: first `a`
    /// itself, then its unsigned representative u(a), which is the actual address
    /// (the proof's Lemma 1) when `a` is only known modulo 2^64.
    fn find_cap(&mut self, st: &mut State, a: &Lin, w: i128, write: bool) -> F<(usize, Lin)> {
        let first = self.find_cap_at(st, a, w, write);
        match first {
            Ok(i) => Ok((i, a.clone())),
            Err(Fail::Err(e)) if e.rule == Rule::MemBounds && !e.msg.contains("aligned") => {
                let u = self.urep(st, a)?;
                if u == *a {
                    return Err(Fail::Err(e));
                }
                match self.find_cap_at(st, &u, w, write) {
                    Ok(i) => Ok((i, u)),
                    Err(_) => Err(Fail::Err(e)),
                }
            }
            Err(e) => Err(e),
        }
    }

    fn find_cap_at(&mut self, st: &mut State, a: &Lin, w: i128, write: bool) -> F<usize> {
        let line_ = self.line;
        let ovf_ = move || ovf(line_);
        // try capabilities sharing variables with the address first
        let mut order: Vec<usize> = (0..st.caps.len()).collect();
        let av: BTreeSet<Var> = a.vars().collect();
        order.sort_by_key(|i| match &st.caps[*i].kind {
            CapKind::Bytes { base, .. } => !base.vars().any(|v| av.contains(&v)),
            _ => true,
        });
        let mut ro_hit = false;
        for i in order {
            let c = st.caps[i].clone();
            let CapKind::Bytes {
                base, len, mode, ..
            } = &c.kind
            else {
                continue;
            };
            let inb = Formula::and(vec![
                Formula::le(base, a).ok_or_else(ovf_)?,
                Formula::le(
                    &a.add_const(w).ok_or_else(ovf_)?,
                    &base.add(len).ok_or_else(ovf_)?,
                )
                .ok_or_else(ovf_)?,
            ]);
            if !self.prove(st, &inb, "access within capability") {
                continue;
            }
            if c.guard != Formula::True {
                if !self.prove(st, &c.guard, "capability guard") {
                    continue;
                }
                st.caps[i].guard = Formula::True;
            }
            if write && *mode == Mode::Ro {
                ro_hit = true;
                continue;
            }
            if w > 1 && !self.prove(st, &Formula::Dvd(w, a.clone()), "alignment") {
                let msg = format!(
                    "access of {w} bytes at {} is not provably {w}-aligned{}",
                    self.show(a),
                    self.fail_detail(st)
                );
                return self.err(Rule::MemBounds, msg);
            }
            return Ok(i);
        }
        if ro_hit {
            return self.err(
                Rule::MemWrite,
                format!(
                    "store to {}: the capability covering it is read-only",
                    self.show(a)
                ),
            );
        }
        let msg = format!(
            "no capability provably covers the {w}-byte access at {}{}",
            self.show(a),
            self.fail_detail(st)
        );
        self.err(Rule::MemBounds, msg)
    }

    fn load(&mut self, st: &mut State, op: LdOp, rd: Reg, rs1: Reg, off: Lin) -> F<()> {
        if rd == SP {
            return self.err(Rule::StackShape, "load into sp (S3)");
        }
        if let Some(k) = off.as_const().and_then(|o| self.slot_of(st, rs1, o)) {
            if op != LdOp::Ld {
                return self.err(Rule::Frame, "a save slot is accessed only with ld/sd");
            }
            let v = match st.slots.get(&k) {
                Some(e) => e.clone(),
                None => self.unknown_word(st, "x"),
            };
            return self.set(st, rd, v);
        }
        let w = op.width() as i128;
        let a = self.reg(st, rs1).add(&off).ok_or_else(|| ovf(self.line))?;
        let (i, a) = self.find_cap(st, &a, w, false)?;
        if w == 8
            && let CapKind::Bytes { base, fields, .. } = st.caps[i].kind.clone()
        {
            let d = a.sub(&base).ok_or_else(|| ovf(self.line))?;
            let k = match d.as_const() {
                Some(k) => Some(k),
                None => {
                    let mut hit = None;
                    for k in fields.keys() {
                        if self.prove_eq(st, &d, &Lin::konst(*k), "field offset") {
                            hit = Some(*k);
                            break;
                        }
                    }
                    hit
                }
            };
            if let Some(k) = k
                && let Some(e) = fields.get(&k)
            {
                return self.set(st, rd, e.clone());
            }
        }
        let x = Lin::var(self.fresh("x"));
        let (lo, hi) = match (w, op.signed()) {
            (8, _) => (0, TWO64),
            (_, false) => (0, 1i128 << (8 * w)),
            (_, true) => (-(1i128 << (8 * w - 1)), 1i128 << (8 * w - 1)),
        };
        self.add_fact(st, Formula::le(&Lin::konst(lo), &x).unwrap());
        self.add_fact(st, Formula::lt(&x, &Lin::konst(hi)).unwrap());
        self.set(st, rd, x)
    }

    fn store(&mut self, st: &mut State, op: StOp, rs1: Reg, rs2: Reg, off: Lin) -> F<()> {
        let val = self.reg(st, rs2);
        if let Some(k) = off.as_const().and_then(|o| self.slot_of(st, rs1, o)) {
            if op != StOp::Sd {
                return self.err(Rule::Frame, "a save slot is accessed only with ld/sd");
            }
            st.slots.insert(k, val);
            return Ok(());
        }
        let w = op.width() as i128;
        let a = self.reg(st, rs1).add(&off).ok_or_else(|| ovf(self.line))?;
        let (i, a) = self.find_cap(st, &a, w, true)?;
        let CapKind::Bytes {
            base,
            mut fields,
            mode,
            heap,
            len,
        } = st.caps[i].kind.clone()
        else {
            unreachable!()
        };
        let d = a.sub(&base).ok_or_else(|| ovf(self.line))?;
        match (w, d.as_const()) {
            (8, Some(k)) => {
                fields.retain(|f, _| *f == k || (f - k).abs() >= 8);
                fields.insert(k, val);
            }
            _ => {
                let keys: Vec<i128> = fields.keys().copied().collect();
                for f in keys {
                    let fstart = base.add_const(f).ok_or_else(|| ovf(self.line))?;
                    let disj = Formula::or(vec![
                        Formula::le(&a.add_const(w).ok_or_else(|| ovf(self.line))?, &fstart)
                            .ok_or_else(|| ovf(self.line))?,
                        Formula::le(&fstart.add_const(8).ok_or_else(|| ovf(self.line))?, &a)
                            .ok_or_else(|| ovf(self.line))?,
                    ]);
                    if !self.prove(st, &disj, "store misses field") {
                        fields.remove(&f);
                    }
                }
            }
        }
        st.caps[i].kind = CapKind::Bytes {
            base,
            len,
            mode,
            heap,
            fields,
        };
        Ok(())
    }

    // ------------------------------------------------------------------ calls

    fn call(&mut self, st: &State, f: &str, ix: usize, link: Reg) -> F<State> {
        let Some(sg) = self.ck.sigs.get(f).cloned() else {
            return self.err(Rule::CallSig, format!("no signature for '{f}'"));
        };
        let _ = link;
        self.apply_call(st, &sg, ix, None)
    }

    fn tail_call(&mut self, st: &State, f: &str, ix: usize) -> F<()> {
        let Some(sg) = self.ck.sigs.get(f).cloned() else {
            return self.err(Rule::CallSig, format!("no signature for '{f}'"));
        };
        if st.depth != 0 {
            return self.err(
                Rule::StackShape,
                "tail call with the frame still allocated (S3)",
            );
        }
        let x_ra = Lin::var(self.x_ra);
        let ra = self.reg(st, RA);
        if !self.prove_eq64(st, &ra, &x_ra, "ra at tail call") {
            return self.err(
                Rule::RetPreserved,
                format!("tail call: ra is {}, not the entry ra", self.show(&ra)),
            );
        }
        let post = self.apply_call(st, &sg, ix, None)?;
        self.ret(&post, Some(&sg), ix)
    }

    /// The call rule (note, 呼出し, steps 1–5) for signature `sg`; returns the state after
    /// the callee returns.
    fn apply_call(&mut self, st: &State, sg: &Sig, ix: usize, _tail: Option<()>) -> F<State> {
        let me = self.me;
        let line_ = self.line;
        let ovf_ = move || ovf(line_);
        let what = if sg.syscall {
            "syscall".to_string()
        } else {
            format!("call of '{}'", sg.name)
        };
        let crule = if sg.syscall {
            Rule::Syscall
        } else {
            Rule::CallArg
        };
        if sg.partial && !me.partial {
            return self.err(
                Rule::CallPartial,
                format!("{what}: a function that is not 'partial' cannot call a 'partial' one"),
            );
        }
        let mut st = st.clone();
        // 1. instantiation
        let mut th: BTreeMap<Var, Lin> = BTreeMap::new();
        let eqs: Vec<(Lin, Lin)> = sg
            .ins
            .iter()
            .map(|(r, e)| (e.clone(), self.reg(&st, *r)))
            .collect();
        let hint_scope: Scope = sg
            .params
            .iter()
            .map(|v| (sg.src_names[v].clone(), *v))
            .collect();
        let hints = self.f.instrs[ix].hints.clone();
        self.solve_vars(&mut th, &sg.params, &eqs, &[], &hint_scope, &st)?;
        // from capabilities: a clause whose base is known and whose length is a bare
        // unknown variable takes the length of a held capability with that base
        for c in sg.borrow.iter().chain(&sg.take) {
            let CapKind::Bytes { base, len, .. } = &c.kind else {
                continue;
            };
            let Some(lv) = len.as_var() else { continue };
            if th.contains_key(&lv) || !sg.params.contains(&lv) {
                continue;
            }
            let Some(b) = base.subst_all(&th) else {
                continue;
            };
            if b.vars()
                .any(|v| sg.params.contains(&v) && !th.contains_key(&v))
            {
                continue;
            }
            for hc in st.caps.clone() {
                if let CapKind::Bytes {
                    base: hb, len: hl, ..
                } = &hc.kind
                    && self.prove_eq(&st, hb, &b, "capability base for instantiation")
                {
                    th.insert(lv, hl.clone());
                    break;
                }
            }
        }
        self.solve_vars(&mut th, &sg.params, &eqs, &hints, &hint_scope, &st)?;
        // 3. capability matching (fields may instantiate variables)
        let matched = self.match_caps(&mut st, sg, &mut th, &what)?;
        for v in &sg.params {
            if !th.contains_key(v) {
                let n = sg.src_names[v].clone();
                return self.err(
                    Rule::CallInst,
                    format!(
                        "{what}: cannot instantiate '{n}'; write '#: with {n} := …' before the call"
                    ),
                );
            }
        }
        if self.ck.record {
            for v in &sg.params {
                self.insts.push((
                    self.line,
                    what.clone(),
                    format!("{} := {}", self.ck.names.name(*v), self.show(&th[v])),
                ));
            }
        }
        // 2. arguments and constraints
        for (r, e) in &sg.ins {
            let want = e.subst_all(&th).ok_or_else(ovf_)?;
            let have = self.reg(&st, *r);
            if !self.prove_eq64(&st, &have, &want, "argument") {
                let msg = format!(
                    "{what}: {r} is {} but the signature needs {}{}",
                    self.show(&have),
                    self.show(&want),
                    self.fail_detail(&st)
                );
                return self.err(crule, msg);
            }
        }
        for p in &sg.pre {
            let g = p.map_lin(&mut |x| x.subst_all(&th)).ok_or_else(ovf_)?;
            if !self.prove(&st, &g, "callee precondition") {
                let msg = format!(
                    "{what}: the precondition {} does not follow{}",
                    self.showf(&g),
                    self.fail_detail(&st)
                );
                return self.err(
                    if sg.syscall {
                        Rule::Syscall
                    } else {
                        Rule::CallPre
                    },
                    msg,
                );
            }
        }
        // the borrowed ranges' checks need θ complete: redo the range part now
        for m in &matched {
            self.check_match_range(&st, sg, m, &th, &what)?;
        }
        self.check_rw_disjoint(&st, sg, &matched, &th, &what)?;
        // 4. stack
        if st.depth + sg.stack > me.stack {
            return self.err(
                Rule::CallStack,
                format!(
                    "{what}: frame {} + callee stack {} > stack {}",
                    st.depth, sg.stack, me.stack
                ),
            );
        }
        // 5. the state after the call
        let mut th2 = th.clone();
        for v in &sg.out_vars {
            let n = sg.src_names[v].clone();
            let w = self.fresh(&n);
            th2.insert(*v, Lin::var(w));
        }
        for r in Reg::all().skip(1) {
            let keep = r.is_preserved() || (sg.syscall && r != A0);
            if !keep {
                let v = self.fresh(r.name());
                st.regs[r.0 as usize] = Lin::var(v);
            }
        }
        for (r, e) in &sg.outs {
            st.regs[r.0 as usize] = e.subst_all(&th2).ok_or_else(ovf_)?;
        }
        // capabilities: take'd ones leave; rw-lent ranges lose overlapping fields, then get
        // the callee's exit fields
        let taken: BTreeSet<u32> = matched
            .iter()
            .filter(|m| m.take)
            .map(|m| m.cap_id)
            .collect();
        st.caps.retain(|c| !taken.contains(&c.id));
        for m in &matched {
            if m.take {
                continue;
            }
            let clause = &sg.borrow[m.clause];
            let CapKind::Bytes {
                base: cb,
                len: cl,
                mode: Mode::Rw,
                ..
            } = &clause.kind
            else {
                continue;
            };
            let (lb, ll) = (
                cb.subst_all(&th).ok_or_else(ovf_)?,
                cl.subst_all(&th).ok_or_else(ovf_)?,
            );
            let Some(i) = st.caps.iter().position(|c| c.id == m.cap_id) else {
                continue;
            };
            let CapKind::Bytes {
                base,
                len,
                mode,
                heap,
                mut fields,
            } = st.caps[i].kind.clone()
            else {
                continue;
            };
            let keys: Vec<i128> = fields.keys().copied().collect();
            for k in keys {
                let fstart = base.add_const(k).ok_or_else(ovf_)?;
                let disj = Formula::or(vec![
                    Formula::le(&lb.add(&ll).ok_or_else(ovf_)?, &fstart).ok_or_else(ovf_)?,
                    Formula::le(&fstart.add_const(8).ok_or_else(ovf_)?, &lb).ok_or_else(ovf_)?,
                ]);
                if !self.prove(&st, &disj, "lent range misses field") {
                    fields.remove(&k);
                }
            }
            let exitf = clause.exit_fields();
            if !exitf.is_empty() {
                let d = lb.sub(&base).ok_or_else(ovf_)?;
                if let Some(d) = d.as_const() {
                    for (k, e) in exitf {
                        fields.insert(d + k, e.subst_all(&th2).ok_or_else(ovf_)?);
                    }
                }
            }
            st.caps[i].kind = CapKind::Bytes {
                base,
                len,
                mode,
                heap,
                fields,
            };
        }
        for g in &sg.give {
            let guard = g
                .guard
                .map_lin(&mut |x| x.subst_all(&th2))
                .ok_or_else(ovf_)?;
            let kind = subst_kind(&g.kind, &th2).ok_or_else(ovf_)?;
            let c = self.new_cap(guard, kind);
            st.caps.push(c);
        }
        for p in &sg.post {
            let f = p.map_lin(&mut |x| x.subst_all(&th2)).ok_or_else(ovf_)?;
            self.add_fact(&mut st, f);
        }
        Ok(st)
    }

    /// Step 3 of the call rule: assigns a held capability to each `borrow`/`take` clause.
    fn match_caps(
        &mut self,
        st: &mut State,
        sg: &Sig,
        th: &mut BTreeMap<Var, Lin>,
        what: &str,
    ) -> F<Vec<Match>> {
        let mut out: Vec<Match> = Vec::new();
        let clauses: Vec<(usize, bool, SigCap)> = sg
            .borrow
            .iter()
            .enumerate()
            .map(|(i, c)| (i, false, c.clone()))
            .chain(
                sg.take
                    .iter()
                    .enumerate()
                    .map(|(i, c)| (i, true, c.clone())),
            )
            .collect();
        for (ci, take, clause) in clauses {
            if clause.guard != Formula::True {
                return self.err(
                    Rule::CallCap,
                    format!("{what}: guarded borrow/take clauses are not supported"),
                );
            }
            let exclusive_used = |out: &Vec<Match>, id: u32| {
                out.iter().any(|m| m.cap_id == id && (m.take || m.token))
            };
            let mut found = None;
            match &clause.kind {
                CapKind::Token(t) => {
                    for c in &st.caps {
                        if matches!(&c.kind, CapKind::Token(u) if u == t)
                            && c.guard == Formula::True
                            && !out.iter().any(|m| m.cap_id == c.id)
                        {
                            found = Some(Match {
                                clause: ci,
                                take,
                                token: true,
                                cap_id: c.id,
                            });
                            break;
                        }
                    }
                    if found.is_none() {
                        return self.err(Rule::CallCap, format!("{what}: no token {t} held"));
                    }
                }
                CapKind::Bytes {
                    base,
                    len,
                    mode,
                    heap,
                    fields,
                } => {
                    let Some(b) = base.subst_all(th) else {
                        return Err(ovf(self.line).into());
                    };
                    let Some(n) = len.subst_all(th) else {
                        return Err(ovf(self.line).into());
                    };
                    let known = !b
                        .vars()
                        .chain(n.vars())
                        .any(|v| sg.params.contains(&v) && !th.contains_key(&v));
                    if !known {
                        let base_known = !b
                            .vars()
                            .any(|v| sg.params.contains(&v) && !th.contains_key(&v));
                        if base_known {
                            let msg = format!(
                                "{what}: no held capability starts at {} (needed for the clause's length){}",
                                self.show(&b),
                                self.fail_detail(st)
                            );
                            return self.err(Rule::CallCap, msg);
                        }
                        let msg = format!(
                            "{what}: cannot instantiate the range {} |-> bytes[{}] of a clause; write '#: with …'",
                            self.show(base),
                            self.show(len)
                        );
                        return self.err(Rule::CallInst, msg);
                    }
                    for i in 0..st.caps.len() {
                        let c = st.caps[i].clone();
                        let CapKind::Bytes {
                            base: hb,
                            len: hl,
                            mode: hm,
                            heap: hh,
                            fields: hf,
                        } = &c.kind
                        else {
                            continue;
                        };
                        if exclusive_used(&out, c.id) {
                            continue;
                        }
                        if take && out.iter().any(|m| m.cap_id == c.id) {
                            continue;
                        }
                        if *mode == Mode::Rw && *hm == Mode::Ro {
                            continue;
                        }
                        if (take || *heap) && (hm != mode || hh != heap) {
                            continue;
                        }
                        let fits = if take || *heap {
                            self.prove_eq(st, hb, &b, "take: same base")
                                && self.prove_eq(st, hl, &n, "take: same length")
                        } else {
                            let g = Formula::and(vec![
                                Formula::le(hb, &b).ok_or_else(|| ovf(self.line))?,
                                Formula::le(
                                    &b.add(&n).ok_or_else(|| ovf(self.line))?,
                                    &hb.add(hl).ok_or_else(|| ovf(self.line))?,
                                )
                                .ok_or_else(|| ovf(self.line))?,
                            ]);
                            self.prove(st, &g, "lent range inside capability")
                        };
                        if !fits {
                            continue;
                        }
                        if c.guard != Formula::True {
                            if !self.prove(st, &c.guard, "capability guard") {
                                continue;
                            }
                            st.caps[i].guard = Formula::True;
                        }
                        // fields: the matched capability has them at the same address
                        let d = b.sub(hb).ok_or_else(|| ovf(self.line))?;
                        let mut ok = true;
                        if !fields.is_empty() {
                            let Some(d) = d.as_const() else {
                                continue;
                            };
                            for (k, e) in fields {
                                let Some(have) = hf.get(&(d + k)).cloned() else {
                                    ok = false;
                                    break;
                                };
                                // instantiate a bare field variable
                                if let Some(v) = e.as_var()
                                    && sg.params.contains(&v)
                                    && !th.contains_key(&v)
                                {
                                    th.insert(v, have.clone());
                                }
                            }
                        }
                        if !ok {
                            continue;
                        }
                        found = Some(Match {
                            clause: ci,
                            take,
                            token: false,
                            cap_id: c.id,
                        });
                        break;
                    }
                    if found.is_none() {
                        let msg = format!(
                            "{what}: no held capability matches the {} clause {} |-> bytes[{}] {}{}",
                            if take { "take" } else { "borrow" },
                            self.show(&b),
                            self.show(&n),
                            if *mode == Mode::Rw { "rw" } else { "ro" },
                            self.fail_detail(st)
                        );
                        return self.err(Rule::CallCap, msg);
                    }
                }
            }
            out.push(found.unwrap());
        }
        Ok(out)
    }

    /// The parts of matching that need θ complete: length ≥ 0 and field values.
    fn check_match_range(
        &mut self,
        st: &State,
        sg: &Sig,
        m: &Match,
        th: &BTreeMap<Var, Lin>,
        what: &str,
    ) -> F<()> {
        let clause = if m.take {
            &sg.take[m.clause]
        } else {
            &sg.borrow[m.clause]
        };
        let CapKind::Bytes {
            base, len, fields, ..
        } = &clause.kind
        else {
            return Ok(());
        };
        let line_ = self.line;
        let ovf_ = move || ovf(line_);
        let n = len.subst_all(th).ok_or_else(ovf_)?;
        if !self.prove(st, &Formula::Ge(n.clone()), "lent length ≥ 0") {
            return self.err(
                Rule::CallCap,
                format!(
                    "{what}: the lent length {} is not provably ≥ 0",
                    self.show(&n)
                ),
            );
        }
        // every field the clause names, on entry and on exit, lies inside the lent range
        // (D2's k + 8 ≤ n for the callee's capability; Lemma 8 P4, I33)
        let mut offs: BTreeSet<i128> = fields.keys().copied().collect();
        offs.extend(clause.exit_fields().keys().copied());
        for k in offs {
            let g = Formula::le(&Lin::konst(k + 8), &n).ok_or_else(ovf_)?;
            if !self.prove(st, &g, "field inside the lent range") {
                return self.err(
                    Rule::CallCap,
                    format!(
                        "{what}: field {k} does not provably lie inside the lent length {}",
                        self.show(&n)
                    ),
                );
            }
        }
        if fields.is_empty() {
            return Ok(());
        }
        let b = base.subst_all(th).ok_or_else(ovf_)?;
        let c = st.caps.iter().find(|c| c.id == m.cap_id).cloned().unwrap();
        let CapKind::Bytes {
            base: hb,
            fields: hf,
            ..
        } = &c.kind
        else {
            return Ok(());
        };
        let d = b.sub(hb).ok_or_else(ovf_)?.as_const().unwrap_or(0);
        for (k, e) in fields {
            let want = e.subst_all(th).ok_or_else(ovf_)?;
            let have = hf.get(&(d + k)).cloned().unwrap_or_default();
            if !self.prove_eq64(st, &have, &want, "field of a lent capability") {
                return self.err(
                    Rule::CallCap,
                    format!(
                        "{what}: field {k} is {} but the signature needs {}",
                        self.show(&have),
                        self.show(&want)
                    ),
                );
            }
        }
        Ok(())
    }

    /// A `rw` loan does not overlap any other loan of the same call from the same
    /// capability (loans from different capabilities are disjoint by I5).
    fn check_rw_disjoint(
        &mut self,
        st: &State,
        sg: &Sig,
        ms: &[Match],
        th: &BTreeMap<Var, Lin>,
        what: &str,
    ) -> F<()> {
        let line_ = self.line;
        let ovf_ = move || ovf(line_);
        let range = |m: &Match| -> Option<(Lin, Lin, Mode)> {
            let c = if m.take {
                &sg.take[m.clause]
            } else {
                &sg.borrow[m.clause]
            };
            match &c.kind {
                CapKind::Bytes {
                    base, len, mode, ..
                } => Some((base.subst_all(th)?, len.subst_all(th)?, *mode)),
                CapKind::Token(_) => None,
            }
        };
        for i in 0..ms.len() {
            for j in i + 1..ms.len() {
                if ms[i].cap_id != ms[j].cap_id {
                    continue;
                }
                if ms[i].token || ms[j].token || ms[i].take || ms[j].take {
                    return self.err(Rule::CallCap, format!("{what}: one capability matched to two clauses, one of them take or a token"));
                }
                let (Some((b1, n1, m1)), Some((b2, n2, m2))) = (range(&ms[i]), range(&ms[j]))
                else {
                    return Err(ovf(self.line).into());
                };
                if m1 == Mode::Ro && m2 == Mode::Ro {
                    continue;
                }
                let disj = Formula::or(vec![
                    Formula::le(&b1.add(&n1).ok_or_else(ovf_)?, &b2).ok_or_else(ovf_)?,
                    Formula::le(&b2.add(&n2).ok_or_else(ovf_)?, &b1).ok_or_else(ovf_)?,
                ]);
                if !self.prove(st, &disj, "rw loans disjoint") {
                    let msg = format!(
                        "{what}: a rw loan overlaps another loan from the same capability{}",
                        self.fail_detail(st)
                    );
                    return self.err(Rule::CallCap, msg);
                }
            }
        }
        Ok(())
    }

    // ------------------------------------------------------------------ return

    /// The return rule (note, 戻り; the proof's Lemma 10). `tail`: the callee whose
    /// post-state `st` is (its `ra` is not ours to check again).
    fn ret(&mut self, st: &State, tail: Option<&Sig>, ix: usize) -> F<()> {
        let me = self.me;
        let line_ = self.line;
        let ovf_ = move || ovf(line_);
        if st.depth != 0 {
            return self.err(
                Rule::StackShape,
                "return with the frame still allocated (S3)",
            );
        }
        if tail.is_none() {
            let x_ra = Lin::var(self.x_ra);
            let ra = self.reg(st, RA);
            if !self.prove_eq64(st, &ra, &x_ra, "ra preserved") {
                return self.err(
                    Rule::RetPreserved,
                    format!(
                        "ra is {}, not the entry ra{}",
                        self.show(&ra),
                        self.fail_detail(st)
                    ),
                );
            }
        }
        let s0 = Lin::var(self.sigma0);
        if !self.prove_eq64(st, &self.reg(st, SP), &s0, "sp preserved") {
            return self.err(Rule::RetPreserved, "sp is not the entry sp");
        }
        for (r, v) in self.entry_preserved.clone() {
            let have = self.reg(st, r);
            if !self.prove_eq64(st, &have, &Lin::var(v), "callee-saved preserved") {
                return self.err(
                    Rule::RetPreserved,
                    format!("{r} is {}, not its entry value", self.show(&have)),
                );
            }
        }
        // existential results
        let mut th: BTreeMap<Var, Lin> = me.params.iter().map(|v| (*v, Lin::var(*v))).collect();
        let eqs: Vec<(Lin, Lin)> = me
            .outs
            .iter()
            .map(|(r, e)| (e.clone(), self.reg(st, *r)))
            .collect();
        let hint_scope: Scope = me
            .out_vars
            .iter()
            .map(|v| (me.src_names[v].clone(), *v))
            .collect();
        let hints = self.f.instrs[ix].hints.clone();
        self.solve_vars(&mut th, &me.out_vars, &eqs, &hints, &hint_scope, st)?;
        // from given capabilities: an unknown bare base/length takes a held one's
        for g in &me.give {
            let CapKind::Bytes { base, len, .. } = &g.kind else {
                continue;
            };
            for c in &st.caps {
                let CapKind::Bytes {
                    base: hb, len: hl, ..
                } = &c.kind
                else {
                    continue;
                };
                let Some(b) = base.subst_all(&th) else {
                    continue;
                };
                if let Some(v) = b
                    .as_var()
                    .filter(|v| me.out_vars.contains(v) && !th.contains_key(v))
                {
                    th.insert(v, hb.clone());
                }
                if let Some(v) = len
                    .as_var()
                    .filter(|v| me.out_vars.contains(v) && !th.contains_key(v))
                    && base.subst_all(&th).as_ref() == Some(hb)
                {
                    th.insert(v, hl.clone());
                }
            }
        }
        for v in &me.out_vars {
            if !th.contains_key(v) {
                let n = me.src_names[v].clone();
                return self.err(Rule::RetOut, format!("cannot instantiate the result variable '{n}'; write '#: with {n} := …' before the return"));
            }
        }
        for (r, e) in &me.outs {
            let want = e.subst_all(&th).ok_or_else(ovf_)?;
            let have = self.reg(st, *r);
            if !self.prove_eq64(st, &have, &want, "result register") {
                let msg = format!(
                    "{r} is {} but 'out' needs {}{}",
                    self.show(&have),
                    self.show(&want),
                    self.fail_detail(st)
                );
                return self.err(Rule::RetOut, msg);
            }
        }
        for p in &me.post {
            let g = p.map_lin(&mut |x| x.subst_all(&th)).ok_or_else(ovf_)?;
            if !self.prove(st, &g, "postcondition") {
                let msg = format!(
                    "the exit constraint {} does not follow{}",
                    self.showf(&g),
                    self.fail_detail(st)
                );
                return self.err(Rule::RetOut, msg);
            }
        }
        // borrowed capabilities come back, by identity (I12), with their exit fields
        let mut used: BTreeSet<u32> = BTreeSet::new();
        for (ci, id) in self.borrow_ids.clone().into_iter().enumerate() {
            let clause = &me.borrow[ci];
            let Some(c) = st.caps.iter().find(|c| c.id == id).cloned() else {
                return self.err(Rule::RetBorrow, format!("the borrowed capability of clause {} is not held at the return (it was consumed){}", ci + 1, self.fail_detail(st)));
            };
            if c.guard != Formula::True && c.guard != clause.guard {
                return self.err(
                    Rule::RetBorrow,
                    format!(
                        "borrow clause {}: the capability is only conditionally held",
                        ci + 1
                    ),
                );
            }
            if let CapKind::Bytes { fields, .. } = &c.kind {
                for (k, e) in clause.exit_fields() {
                    let want = e.subst_all(&th).ok_or_else(ovf_)?;
                    let ok = match fields.get(&k).cloned() {
                        Some(have) => self.prove_eq64(st, &have, &want, "exit field"),
                        None => false,
                    };
                    if !ok {
                        return self.err(
                            Rule::RetBorrow,
                            format!(
                                "borrow clause {}: field {k} is not int({}) at the return",
                                ci + 1,
                                self.show(&want)
                            ),
                        );
                    }
                }
            }
            used.insert(id);
        }
        // given capabilities: one held capability each, one-to-one
        let gives = match tail {
            None => me.give.clone(),
            Some(_) => me.give.clone(),
        };
        for (gi, g) in gives.iter().enumerate() {
            let guard = g
                .guard
                .map_lin(&mut |x| x.subst_all(&th))
                .ok_or_else(ovf_)?;
            if guard != Formula::True
                && self.prove(st, &Formula::negate(guard.clone()), "give guard false")
            {
                continue;
            }
            let kind = subst_kind(&g.kind, &th).ok_or_else(ovf_)?;
            let mut found = None;
            for c in st.caps.clone() {
                if used.contains(&c.id) {
                    continue;
                }
                let ok = match (&kind, &c.kind) {
                    (CapKind::Token(a), CapKind::Token(b)) => a == b,
                    (
                        CapKind::Bytes {
                            base,
                            len,
                            mode,
                            heap,
                            fields,
                        },
                        CapKind::Bytes {
                            base: hb,
                            len: hl,
                            mode: hm,
                            heap: hh,
                            fields: hf,
                        },
                    ) => {
                        mode == hm
                            && heap == hh
                            && self.prove_eq(st, base, hb, "give: same base")
                            && self.prove_eq(st, len, hl, "give: same length")
                            && fields
                                .iter()
                                .all(|(k, e)| hf.get(k).is_some_and(|h| h == e))
                    }
                    _ => false,
                };
                if !ok {
                    continue;
                }
                if c.guard != Formula::True {
                    let imp = Formula::or(vec![Formula::negate(guard.clone()), c.guard.clone()]);
                    if !self.prove(st, &imp, "give: guard") {
                        continue;
                    }
                }
                found = Some(c.id);
                break;
            }
            match found {
                Some(id) => {
                    used.insert(id);
                }
                None => {
                    return self.err(
                        Rule::RetGive,
                        format!(
                            "give clause {}: no held capability matches it{}",
                            gi + 1,
                            self.fail_detail(st)
                        ),
                    );
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum BitOp {
    And,
    Or,
    Xor,
}

struct Match {
    clause: usize,
    take: bool,
    token: bool,
    cap_id: u32,
}

fn subst_kind(k: &CapKind, th: &BTreeMap<Var, Lin>) -> Option<CapKind> {
    Some(match k {
        CapKind::Token(t) => CapKind::Token(t.clone()),
        CapKind::Bytes {
            base,
            len,
            mode,
            heap,
            fields,
        } => CapKind::Bytes {
            base: base.subst_all(th)?,
            len: len.subst_all(th)?,
            mode: *mode,
            heap: *heap,
            fields: fields
                .iter()
                .map(|(k, e)| Some((*k, e.subst_all(th)?)))
                .collect::<Option<_>>()?,
        },
    })
}

fn signed64(c: i128) -> i128 {
    let u = c.rem_euclid(TWO64);
    if u >= TWO64 / 2 { u - TWO64 } else { u }
}

/// (rd, rs1, rs2) of a computational instruction, for constant folding.
fn comp_operands(i: &Instr) -> Option<(Reg, Reg, Reg)> {
    Some(match i {
        Instr::IOp { rd, rs1, .. }
        | Instr::Addiw { rd, rs1, .. }
        | Instr::Shift { rd, rs1, .. }
        | Instr::ShiftW { rd, rs1, .. }
        | Instr::UOp { rd, rs1, .. } => (*rd, *rs1, ZERO),
        Instr::ROp { rd, rs1, rs2, .. } | Instr::RWOp { rd, rs1, rs2, .. } => (*rd, *rs1, *rs2),
        _ => return None,
    })
}

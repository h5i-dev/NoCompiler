//! The note's "証明なしでできる点検": every function the checker accepts is run on an
//! interpreter that enforces the signature's permissions (the capabilities' ranges, `rw`
//! for writes, and the stack below the entry `sp`), from random entry states that satisfy
//! the signature. A stuck access, a misaligned access, a run that does not end, or a return
//! that breaks the calling convention means the checker (or a rule) is wrong. It cannot
//! show there is no hole; it can find one.
//!
//! Scope: functions whose callees are other functions of the same file (run for real) or
//! syscalls 63/64/93/94. Functions calling unsafe/extern contracts are skipped (no model of
//! the callee), and so are signatures whose variables cannot be sampled (tokens, guards).

use nocompiler_typed::asm::{self, Func, Program};
use nocompiler_typed::check;
use nocompiler_typed::formula::Formula;
use nocompiler_typed::isa::*;
use nocompiler_typed::lin::{Lin, TWO64, Var};
use nocompiler_typed::sig::{CapKind, Sig};
use nocompiler_typed::syntax::{FnKind, Mode};
use std::collections::{BTreeMap, HashMap};
use std::path::PathBuf;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }
}

fn eval_lin(e: &Lin, v: &BTreeMap<Var, i128>) -> Option<i128> {
    let mut s = e.konst;
    for (x, c) in &e.terms {
        s = s.checked_add(c.checked_mul(*v.get(x)?)?)?;
    }
    Some(s)
}

fn eval_f(f: &Formula, v: &BTreeMap<Var, i128>) -> Option<bool> {
    Some(match f {
        Formula::True => true,
        Formula::False => false,
        Formula::Ge(e) => eval_lin(e, v)? >= 0,
        Formula::Eq(e) => eval_lin(e, v)? == 0,
        Formula::Dvd(c, e) => eval_lin(e, v)?.rem_euclid(*c) == 0,
        Formula::And(g) => {
            for h in g {
                if !eval_f(h, v)? {
                    return Some(false);
                }
            }
            true
        }
        Formula::Or(g) => {
            for h in g {
                if eval_f(h, v)? {
                    return Some(true);
                }
            }
            false
        }
        Formula::Not(g) => !eval_f(g, v)?,
    })
}

#[derive(Clone, Debug)]
struct Region {
    lo: u64,
    hi: u64,
    write: bool,
}

struct Machine<'a> {
    prog: &'a Program,
    sigs: &'a BTreeMap<String, Sig>,
    /// Ranges given away with `take` (no longer accessible).
    revoked: Vec<(u64, u64)>,
    next_alloc: u64,
    /// Data symbol → address.
    data: HashMap<String, u64>,
    regs: [u64; 32],
    mem: HashMap<u64, u8>,
    regions: Vec<Region>,
    steps: u64,
}

const RET_MAGIC: u64 = 0x0000_dead_0000;

#[derive(Debug)]
enum Stop {
    Returned,
    Exited,
    Fault(String),
    /// The environment could not be modelled for this run (no sample of a contract).
    Skip,
}

impl Machine<'_> {
    fn allowed(&self, a: u64, w: u64, write: bool) -> bool {
        (0..w).all(|i| {
            let b = a.wrapping_add(i);
            !self.revoked.iter().any(|(lo, hi)| *lo <= b && b < *hi)
                && self
                    .regions
                    .iter()
                    .any(|r| r.lo <= b && b < r.hi && (!write || r.write))
        })
    }
    fn load(&self, a: u64, w: u64) -> u64 {
        (0..w).fold(0u64, |acc, i| {
            acc | (*self.mem.get(&a.wrapping_add(i)).unwrap_or(&0) as u64) << (8 * i)
        })
    }
    fn store(&mut self, a: u64, w: u64, v: u64) {
        for i in 0..w {
            self.mem.insert(a.wrapping_add(i), (v >> (8 * i)) as u8);
        }
    }
    fn set(&mut self, r: Reg, v: u64) {
        if r != ZERO {
            self.regs[r.0 as usize] = v;
        }
    }

    /// Runs `f` until it returns to `RET_MAGIC` (a call to another function of the file
    /// pushes nothing: the callee returns to the link address).
    fn run(&mut self, f: &Func, rng: &mut Rng) -> Stop {
        // Code layout: each function at base 0x10_0000 * (k+1), instruction i at +4·word.
        let funcs: Vec<&Func> = self.prog.funcs.iter().collect();
        let fidx = |name: &str| funcs.iter().position(|g| g.name == name);
        let addr_of = |k: usize, i: usize| -> u64 {
            let g = funcs[k];
            0x10_0000 * (k as u64 + 1) + (g.instrs[i].addr - g.instrs[0].addr)
        };
        let locate = |pc: u64| -> Option<(usize, usize)> {
            let k = (pc / 0x10_0000).checked_sub(1)? as usize;
            let g = funcs.get(k)?;
            let off = pc - 0x10_0000 * (k as u64 + 1);
            let i = g
                .instrs
                .iter()
                .position(|p| p.addr - g.instrs[0].addr == off)?;
            Some((k, i))
        };
        let mut pc = addr_of(fidx(&f.name).unwrap(), 0);
        loop {
            if pc == RET_MAGIC {
                return Stop::Returned;
            }
            self.steps += 1;
            if self.steps > 200_000 {
                return Stop::Fault("did not end in 200000 steps".into());
            }
            let Some((k, i)) = locate(pc) else {
                return Stop::Fault(format!("jump to {pc:#x}, not an instruction"));
            };
            let g = funcs[k];
            let ins = &g.instrs[i].instr;
            let r = |x: Reg| self.regs[x.0 as usize];
            let next = pc + 4 * ins.words() as u64;
            let target = |t: &Target| -> Option<u64> {
                match t {
                    Target::Local(j) => Some(addr_of(k, *j)),
                    Target::Symbol(s) => fidx(s).map(|kk| addr_of(kk, 0)),
                }
            };
            match ins {
                Instr::Load { op, rd, rs1, off } => {
                    let a = r(*rs1).wrapping_add(*off as u64);
                    let w = op.width() as u64;
                    if a % w != 0 {
                        return Stop::Fault(format!(
                            "misaligned load at {a:#x} (line {})",
                            g.instrs[i].line
                        ));
                    }
                    if !self.allowed(a, w, false) {
                        return Stop::Fault(format!(
                            "load of {w} at {a:#x} outside the permission (line {})",
                            g.instrs[i].line
                        ));
                    }
                    let v = self.load(a, w);
                    let v = if op.signed() {
                        ((v << (64 - 8 * w)) as i64 >> (64 - 8 * w)) as u64
                    } else {
                        v
                    };
                    self.set(*rd, v);
                    pc = next;
                }
                Instr::Store { op, rs1, rs2, off } => {
                    let a = r(*rs1).wrapping_add(*off as u64);
                    let w = op.width() as u64;
                    if a % w != 0 {
                        return Stop::Fault(format!(
                            "misaligned store at {a:#x} (line {})",
                            g.instrs[i].line
                        ));
                    }
                    if !self.allowed(a, w, true) {
                        return Stop::Fault(format!(
                            "store of {w} at {a:#x} outside the permission (line {})",
                            g.instrs[i].line
                        ));
                    }
                    let v = r(*rs2);
                    self.store(a, w, v);
                    pc = next;
                }
                Instr::Branch {
                    op,
                    rs1,
                    rs2,
                    target: t,
                } => {
                    let (a, b) = (r(*rs1), r(*rs2));
                    let take = match op {
                        BrOp::Beq => a == b,
                        BrOp::Bne => a != b,
                        BrOp::Blt => (a as i64) < (b as i64),
                        BrOp::Bge => (a as i64) >= (b as i64),
                        BrOp::Bltu => a < b,
                        BrOp::Bgeu => a >= b,
                    };
                    pc = if take { target(t).unwrap() } else { next };
                }
                Instr::Jal { rd, target: t } | Instr::CallPair { rd, target: t, .. } => {
                    if let Instr::CallPair { tmp, .. } = ins {
                        let v = rng.next();
                        self.set(*tmp, v);
                    }
                    self.set(*rd, next);
                    match target(t) {
                        Some(tg) => pc = tg,
                        None => {
                            let Target::Symbol(name) = t else {
                                unreachable!()
                            };
                            let Some(sig) = self.sigs.get(name) else {
                                return Stop::Fault(format!(
                                    "call of '{name}' without a signature"
                                ));
                            };
                            let ret = self.regs[RA.0 as usize];
                            match self.contract(sig, rng) {
                                Ok(true) => {}
                                Ok(false) => return Stop::Skip,
                                Err(e) => {
                                    return Stop::Fault(format!("line {}: {e}", g.instrs[i].line));
                                }
                            }
                            // the callee returns to ra (next for a call, our caller for a tail call)
                            pc = ret;
                        }
                    }
                }
                Instr::Jalr { rd, rs1, off } => {
                    let t = r(*rs1).wrapping_add(*off as u64) & !1;
                    self.set(*rd, next);
                    pc = t;
                }
                Instr::Ecall => {
                    match r(A7) {
                        93 | 94 => return Stop::Exited,
                        63 | 64 => {
                            let (b, n) = (r(A1), r(A2));
                            // read (63) stores into the buffer; write (64) reads it
                            let stores = r(A7) == 63;
                            if n > 0 && !self.allowed(b, n.min(1 << 20), stores) {
                                return Stop::Fault(format!(
                                    "syscall {} buffer [{b:#x}, +{n}) outside the permission",
                                    r(A7)
                                ));
                            }
                            let res = if rng.below(8) == 0 {
                                -(1 + rng.below(4095) as i64) as u64
                            } else {
                                // Env.lean: r ≤ min(n, MAX_RW_COUNT); a write of n ≥ 1 takes ≥ 1
                                let top = n.min(0x7fff_f000);
                                let lo = u64::from(!stores && n >= 1);
                                lo + rng.below(top + 1 - lo)
                            };
                            if stores && (res as i64) > 0 {
                                for j in 0..res {
                                    let v = rng.next() as u8;
                                    self.mem.insert(b + j, v);
                                }
                            }
                            self.set(A0, res);
                        }
                        n => return Stop::Fault(format!("syscall {n}")),
                    }
                    pc = next;
                }
                Instr::Auipc { rd, .. } => {
                    // with %pcrel_hi(sym); the paired %pcrel_lo immediate is 0 in the text
                    match &g.instrs[i].reloc {
                        Some(asm::Reloc::PcrelHi(sym)) => {
                            let a = self.data[sym];
                            self.set(*rd, a);
                        }
                        _ => return Stop::Fault("auipc without a symbol".into()),
                    }
                    pc = next;
                }
                Instr::Unimp => return Stop::Fault("unimp reached".into()),
                _ => {
                    let (r1, r2) = match ins {
                        Instr::ROp { rs1, rs2, .. } | Instr::RWOp { rs1, rs2, .. } => {
                            (r(*rs1), r(*rs2))
                        }
                        Instr::IOp { rs1, .. }
                        | Instr::Addiw { rs1, .. }
                        | Instr::Shift { rs1, .. }
                        | Instr::ShiftW { rs1, .. }
                        | Instr::UOp { rs1, .. } => (r(*rs1), 0),
                        _ => (0, 0),
                    };
                    let v = eval(ins, r1, r2).expect("computational");
                    self.set(ins.rd().unwrap_or(ZERO), v);
                    pc = next;
                }
            }
        }
    }
}

impl Machine<'_> {
    /// A call of a function known only by its contract: check what the caller must
    /// provide, then act as some function satisfying the contract would. `Ok(false)`: no
    /// valuation found (the run is skipped).
    fn contract(&mut self, sig: &Sig, rng: &mut Rng) -> Result<bool, String> {
        // θ for the parameters: bare in-registers (unsigned or signed representative)
        let mut cands: Vec<BTreeMap<Var, i128>> = vec![BTreeMap::new()];
        for (r, e) in &sig.ins {
            if let Some(v) = e.as_var().filter(|v| sig.params.contains(v)) {
                let u = self.regs[r.0 as usize] as i128;
                let mut next = Vec::new();
                for c in &cands {
                    for x in [u, u - TWO64] {
                        let mut c2 = c.clone();
                        c2.insert(v, x);
                        next.push(c2);
                    }
                }
                cands = next;
                cands.truncate(16);
            }
        }
        // lengths from the regions at a clause's base
        for c in &mut cands {
            for cl in sig.borrow.iter().chain(&sig.take) {
                if let CapKind::Bytes { base, len, .. } = &cl.kind
                    && let (Some(b), Some(lv)) = (eval_lin(base, c), len.as_var())
                    && !c.contains_key(&lv)
                    && let Some(rg) = self.regions.iter().find(|rg| rg.lo as i128 == b)
                {
                    c.insert(lv, (rg.hi - rg.lo) as i128);
                }
            }
        }
        let pre = Formula::and(sig.pre.clone());
        let Some(th) = cands.into_iter().find(|c| eval_f(&pre, c) == Some(true)) else {
            if sig
                .params
                .iter()
                .all(|v| sig.ins.iter().any(|(_, e)| e.as_var() == Some(*v)))
            {
                return Err(format!(
                    "call of '{}': no valuation of the arguments satisfies the precondition",
                    sig.name
                ));
            }
            return Ok(false);
        };
        if sig.params.iter().any(|v| !th.contains_key(v)) {
            return Ok(false);
        }
        // lent and taken ranges must be permitted to the caller
        let mut rw_ranges = Vec::new();
        for (k, cl) in sig.borrow.iter().chain(&sig.take).enumerate() {
            let CapKind::Bytes {
                base, len, mode, ..
            } = &cl.kind
            else {
                continue;
            };
            let (b, n) = (eval_lin(base, &th).unwrap(), eval_lin(len, &th).unwrap());
            if n < 0 {
                return Err(format!("call of '{}': negative length {n}", sig.name));
            }
            if n > 0
                && (b < 0 || b + n > TWO64 || !self.allowed(b as u64, n as u64, *mode == Mode::Rw))
            {
                return Err(format!(
                    "call of '{}': clause {} range [{b:#x}, +{n}) not permitted to the caller",
                    sig.name,
                    k + 1
                ));
            }
            if *mode == Mode::Rw {
                rw_ranges.push((b as u64, n as u64, k < sig.borrow.len()));
            }
            if k >= sig.borrow.len() {
                self.revoked.push((b as u64, (b + n) as u64));
            }
        }
        // the callee may write what it was lent rw
        for (b, n, _) in &rw_ranges {
            for j in 0..*n {
                let v = rng.next() as u8;
                self.mem.insert(b + j, v);
            }
        }
        for r in Reg::all().skip(1) {
            if !r.is_preserved() {
                let v = rng.next();
                self.set(r, v);
            }
        }
        // results: given capabilities get fresh memory; other variables are sampled
        for _ in 0..300 {
            let mut t2 = th.clone();
            let mut allocs = Vec::new();
            for g in &sig.give {
                if let CapKind::Bytes { base, .. } = &g.kind
                    && let Some(v) = base.as_var().filter(|v| sig.out_vars.contains(v))
                {
                    // sometimes the null result a guarded give allows
                    let a = if g.guard != Formula::True && rng.below(4) == 0 {
                        0
                    } else {
                        self.next_alloc
                    };
                    t2.insert(v, a as i128);
                    allocs.push(a);
                }
            }
            for v in &sig.out_vars {
                if !t2.contains_key(v) {
                    let x = match rng.below(5) {
                        0 => 0,
                        1 => -1,
                        2 => rng.below(8) as i128,
                        3 => {
                            th.values()
                                .nth(rng.below(th.len().max(1) as u64) as usize)
                                .copied()
                                .unwrap_or(0)
                                - rng.below(3) as i128
                        }
                        _ => rng.below(100) as i128,
                    };
                    t2.insert(*v, x);
                }
            }
            if eval_f(&Formula::and(sig.post.clone()), &t2) != Some(true) {
                continue;
            }
            for g in &sig.give {
                if eval_f(&g.guard, &t2) != Some(true) {
                    continue;
                }
                if let CapKind::Bytes {
                    base, len, mode, ..
                } = &g.kind
                {
                    let (b, n) = (eval_lin(base, &t2).unwrap(), eval_lin(len, &t2).unwrap());
                    if n > 1 << 20 {
                        return Ok(false);
                    }
                    self.regions.push(Region {
                        lo: b as u64,
                        hi: (b + n) as u64,
                        write: *mode == Mode::Rw,
                    });
                    self.next_alloc = (b + n) as u64 + 0x10_0000;
                    self.next_alloc = self.next_alloc.next_multiple_of(0x1000);
                }
            }
            // exit fields of borrows
            for cl in &sig.borrow {
                if let CapKind::Bytes { base, .. } = &cl.kind {
                    let b = eval_lin(base, &t2).unwrap();
                    for (k, e) in cl.exit_fields() {
                        if let Some(x) = eval_lin(&e, &t2) {
                            self.store((b + k) as u64, 8, x.rem_euclid(TWO64) as u64);
                        }
                    }
                }
            }
            for (r, e) in &sig.outs {
                let x = eval_lin(e, &t2).unwrap();
                self.set(*r, x.rem_euclid(TWO64) as u64);
            }
            let _ = allocs;
            return Ok(true);
        }
        Ok(false)
    }
}

/// (base, length, mode, fields) of one capability's memory.
type Layout = (u64, u64, Mode, BTreeMap<i128, Lin>);

/// Samples a valuation and memory layout for `s`; `None` if the signature is outside
/// what this tester handles or no sample satisfies it.
fn sample(s: &Sig, rng: &mut Rng) -> Option<(BTreeMap<Var, i128>, Vec<Layout>)> {
    let caps: Vec<_> = s.borrow.iter().chain(&s.take).collect();
    if caps.iter().any(|c| c.guard != Formula::True) {
        return None;
    }
    // tokens: nothing to lay out (the contracts' state is not modelled)
    let caps: Vec<_> = caps
        .into_iter()
        .filter(|c| !matches!(c.kind, CapKind::Token(_)))
        .collect();
    // base variables: bare variables that are a capability's base
    let mut bases: Vec<Var> = Vec::new();
    for c in &caps {
        if let CapKind::Bytes { base, .. } = &c.kind {
            bases.push(base.as_var()?);
        }
    }
    'try_: for _ in 0..400 {
        let mut v: BTreeMap<Var, i128> = BTreeMap::new();
        for p in &s.params {
            if bases.contains(p) {
                continue;
            }
            let x = match rng.below(8) {
                6 => -(rng.below(8) as i128) - 1,
                7 => (1i128 << 63) + rng.below(4) as i128,
                0 => 0,
                1 => 1,
                2 => rng.below(8) as i128,
                3 => rng.below(70) as i128,
                4 => (rng.below(4) as i128) * 8,
                _ => rng.below(300) as i128,
            };
            v.insert(*p, x);
        }
        // lay capabilities out far apart; alignment random (8- or 16-aligned mostly)
        let mut layout = Vec::new();
        let mut next_area: u64 = 0x4000_0000;
        for c in &caps {
            let CapKind::Bytes {
                base,
                len,
                mode,
                fields,
                ..
            } = &c.kind
            else {
                unreachable!()
            };
            let b = base.as_var()?;
            let mis = match rng.below(4) {
                0 => rng.below(16),
                _ => 0,
            };
            let a = next_area + mis;
            v.insert(b, a as i128);
            let Some(n) = eval_lin(len, &v) else {
                continue 'try_;
            };
            if !(0..=1 << 20).contains(&n) {
                continue 'try_;
            }
            layout.push((a, n as u64, *mode, fields.clone()));
            next_area += 0x100_0000;
        }
        let pre = Formula::and(s.pre.clone());
        if eval_f(&pre, &v) != Some(true) {
            continue;
        }
        // fields must lie inside and be aligned (D2)
        for (a, n, _, f) in &layout {
            for k in f.keys() {
                if *k + 8 > *n as i128 || (*a as i128 + k) % 8 != 0 {
                    continue 'try_;
                }
            }
        }
        return Some((v, layout));
    }
    None
}

fn run_case(
    prog: &Program,
    sigs: &BTreeMap<String, Sig>,
    f: &Func,
    s: &Sig,
    rng: &mut Rng,
) -> Result<bool, String> {
    let Some((v, layout)) = sample(s, rng) else {
        return Ok(false);
    };
    let mut m = Machine {
        prog,
        sigs,
        revoked: vec![],
        next_alloc: 0x5000_0000,
        data: HashMap::new(),
        regs: [0; 32],
        mem: HashMap::new(),
        regions: vec![],
        steps: 0,
    };
    // data symbols, laid out apart, aligned as declared; unknown bytes random
    let mut next_data: u64 = 0x3000_0000;
    for (name, d) in &prog.data {
        let a = next_data.next_multiple_of(d.align.max(1));
        m.data.insert(name.clone(), a);
        for (j, b) in d.bytes.iter().enumerate() {
            let v = b.unwrap_or(rng.next() as u8);
            m.mem.insert(a + j as u64, v);
        }
        m.regions.push(Region {
            lo: a,
            hi: a + d.bytes.len() as u64,
            write: !d.ro,
        });
        next_data = a + d.bytes.len() as u64 + 0x1000;
    }
    for x in m.regs.iter_mut().skip(1) {
        *x = rng.next();
    }
    for (a, n, mode, fields) in &layout {
        m.regions.push(Region {
            lo: *a,
            hi: a + n,
            write: *mode == Mode::Rw,
        });
        for j in 0..*n {
            let b = rng.next() as u8;
            m.mem.insert(a + j, b);
        }
        for (k, e) in fields {
            let x = eval_lin(e, &v).ok_or("field of an unsampled variable")?;
            m.store((*a as i128 + k) as u64, 8, x.rem_euclid(TWO64) as u64);
        }
    }
    let sp: u64 = 0x7000_0000;
    m.regions.push(Region {
        lo: sp - s.stack as u64,
        hi: sp,
        write: true,
    });
    for (r, e) in &s.ins {
        let x = eval_lin(e, &v).ok_or("in-register of an unsampled variable")?;
        m.regs[r.0 as usize] = x.rem_euclid(TWO64) as u64;
    }
    m.regs[SP.0 as usize] = sp;
    m.regs[RA.0 as usize] = RET_MAGIC;
    let saved: Vec<(usize, u64)> = (0..32)
        .filter(|r| Reg(*r as u8).is_preserved())
        .map(|r| (r, m.regs[r]))
        .collect();
    match m.run(f, rng) {
        Stop::Exited => Ok(true),
        Stop::Skip => Ok(false),
        // a `partial` function need not end
        Stop::Fault(msg) if s.partial && msg.starts_with("did not end") => Ok(true),
        Stop::Fault(msg) => Err(format!(
            "{} with {:?}: {msg}",
            f.name,
            v.values().collect::<Vec<_>>()
        )),
        Stop::Returned => {
            for (r, x) in saved {
                if m.regs[r] != x {
                    return Err(format!("{}: {} not preserved", f.name, Reg(r as u8)));
                }
            }
            // Q2: some choice of the result variables (from bare out-registers, either
            // representative) satisfies the out types and the exit constraint
            let mut cands: Vec<BTreeMap<Var, i128>> = vec![v.clone()];
            for (r, e) in &s.outs {
                if let Some(x) = e.as_var().filter(|x| s.out_vars.contains(x)) {
                    let u = m.regs[r.0 as usize] as i128;
                    let mut next = Vec::new();
                    for c in &cands {
                        for val in [u, u - TWO64] {
                            let mut c2 = c.clone();
                            c2.insert(x, val);
                            next.push(c2);
                        }
                    }
                    cands = next;
                    cands.truncate(64);
                }
            }
            let post = Formula::and(s.post.clone());
            let decided: Vec<bool> = cands
                .iter()
                .filter_map(|c| {
                    let outs_ok = s.outs.iter().all(|(r, e)| {
                        eval_lin(e, c)
                            .is_none_or(|x| x.rem_euclid(TWO64) as u64 == m.regs[r.0 as usize])
                    });
                    eval_f(&post, c).map(|p| p && outs_ok)
                })
                .collect();
            if !decided.is_empty() && !decided.iter().any(|b| *b) {
                return Err(format!(
                    "{}: returned registers violate 'out'/the exit constraint",
                    f.name
                ));
            }
            // Q3: borrowed capabilities' exit fields
            for cl in &s.borrow {
                if let CapKind::Bytes { base, .. } = &cl.kind
                    && let Some(b) = eval_lin(base, &v)
                {
                    for (k, e) in cl.exit_fields() {
                        let Some(c) = cands.first() else { continue };
                        if let Some(x) = eval_lin(&e, c)
                            && m.load((b + k) as u64, 8) != x.rem_euclid(TWO64) as u64
                        {
                            return Err(format!(
                                "{}: exit field {k} of a borrowed capability is wrong",
                                f.name
                            ));
                        }
                    }
                }
            }
            Ok(true)
        }
    }
}

fn files() -> Vec<PathBuf> {
    let mut out = Vec::new();
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut stack = vec![root.join("tests/typed/corpus"), root.join("examples/typed")];
    if let Ok(extra) = std::env::var("NC_TYPED_EXEC_DIR") {
        stack.push(PathBuf::from(extra));
    }
    while let Some(d) = stack.pop() {
        let Ok(rd) = std::fs::read_dir(&d) else {
            continue;
        };
        for e in rd {
            let p = e.unwrap().path();
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().is_some_and(|x| x == "s") {
                out.push(p);
            }
        }
    }
    out.sort();
    out
}

#[test]
fn accepted_functions_do_not_get_stuck() {
    let mut rng = Rng(0x2545_f491_4f6c_dd1d);
    let mut ran = 0;
    let mut skipped = Vec::new();
    let mut bad = Vec::new();
    for p in files() {
        let src = std::fs::read_to_string(&p).unwrap();
        let Ok(prog) = asm::parse(&src) else { continue };
        // functions accepted with the default rules or with proposal P1 (natural loops)
        let (ck, rep) = check::check_program(&prog, false);
        let p1 = check::Options {
            record: false,
            natural_loops: true,
        };
        let (_, rep_p1) = check::check_program_opts(&prog, p1);
        for fr in &rep.funcs {
            let ok_p1 = rep_p1
                .funcs
                .iter()
                .any(|g| g.name == fr.name && g.error.is_none());
            if (fr.error.is_some() && !ok_p1) || fr.kind != Some(FnKind::Safe) {
                continue;
            }
            let f = prog.funcs.iter().find(|g| g.name == fr.name).unwrap();
            let s = &ck.sigs[&fr.name];
            let mut any = false;
            for _ in 0..300 {
                match run_case(&prog, &ck.sigs, f, s, &mut rng) {
                    Ok(true) => any = true,
                    Ok(false) => continue,
                    Err(e) => {
                        bad.push(format!("{}: {e}", p.display()));
                        break;
                    }
                }
            }
            if any {
                ran += 1;
            } else {
                skipped.push(format!("{}: {} (no sample)", p.display(), fr.name));
            }
        }
    }
    eprintln!(
        "exec: ran {ran} accepted functions; skipped {}:\n  {}",
        skipped.len(),
        skipped.join("\n  ")
    );
    assert!(
        bad.is_empty(),
        "accepted functions that got stuck:\n{}",
        bad.join("\n")
    );
    assert!(ran > 0);
}

/// The tester has teeth: on functions the checker rejects for a memory reason, it finds a
/// fault (so a checker that wrongly accepted them would be caught).
#[test]
fn tester_finds_the_known_holes() {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tests/typed/corpus");
    let cases = [
        ("neg_bounds_off_by_one.s", "sum"),
        ("neg_blt_index.s", "get"),
        ("neg_use_after_free.s", "use_after_free"),
        ("neg_store_ro.s", "zero_first"),
        ("neg_static_oob.s", "lookup"),
        ("neg_null_unchecked.s", "no_null_check"),
        ("neg_ret_s0.s", "f"),
        ("neg_out.s", "inc"),
        ("neg_exit_field.s", "set_one"),
    ];
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    let mut missed = Vec::new();
    for (file, name) in cases {
        let src = std::fs::read_to_string(dir.join(file)).unwrap();
        let prog = asm::parse(&src).unwrap();
        let (ck, _) = check::check_program(&prog, false);
        let f = prog.funcs.iter().find(|g| g.name == name).unwrap();
        let s = &ck.sigs[name];
        let found = (0..2000).any(|_| run_case(&prog, &ck.sigs, f, s, &mut rng).is_err());
        if !found {
            missed.push(format!("{file}: {name}"));
        }
    }
    assert!(
        missed.is_empty(),
        "the tester found no fault in: {missed:?}"
    );
}

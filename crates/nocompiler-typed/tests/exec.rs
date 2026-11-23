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
}

impl Machine<'_> {
    fn allowed(&self, a: u64, w: u64, write: bool) -> bool {
        (0..w).all(|i| {
            let b = a.wrapping_add(i);
            self.regions
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
                Instr::Jal { rd, target: t } => {
                    self.set(*rd, next);
                    let Some(tg) = target(t) else {
                        return Stop::Fault("call of a function without a body".into());
                    };
                    pc = tg;
                }
                Instr::CallPair { rd, tmp, target: t } => {
                    self.set(*tmp, rng.next());
                    self.set(*rd, next);
                    let Some(tg) = target(t) else {
                        return Stop::Fault("call of a function without a body".into());
                    };
                    pc = tg;
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
                            let write = r(A7) == 63;
                            if n > 0 && !self.allowed(b, n.min(1 << 20), write) {
                                return Stop::Fault(format!(
                                    "syscall {} buffer [{b:#x}, +{n}) outside the permission",
                                    r(A7)
                                ));
                            }
                            let res = if rng.below(8) == 0 {
                                -(1 + rng.below(4095) as i64) as u64
                            } else {
                                rng.below(n.min(0x7fff_f000) + 1)
                            };
                            if write && (res as i64) > 0 {
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

/// (base, length, mode, fields) of one capability's memory.
type Layout = (u64, u64, Mode, BTreeMap<i128, Lin>);

/// Samples a valuation and memory layout for `s`; `None` if the signature is outside
/// what this tester handles or no sample satisfies it.
fn sample(s: &Sig, rng: &mut Rng) -> Option<(BTreeMap<Var, i128>, Vec<Layout>)> {
    let caps: Vec<_> = s.borrow.iter().chain(&s.take).collect();
    if caps
        .iter()
        .any(|c| c.guard != Formula::True || matches!(c.kind, CapKind::Token(_)))
    {
        return None;
    }
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
            let x = match rng.below(6) {
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

fn run_case(prog: &Program, f: &Func, s: &Sig, rng: &mut Rng) -> Result<bool, String> {
    let Some((v, layout)) = sample(s, rng) else {
        return Ok(false);
    };
    let mut m = Machine {
        prog,
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
            Ok(true)
        }
    }
}

fn files() -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut stack =
        vec![PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tests/typed/corpus")];
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
        let (ck, rep) = check::check_program(&prog, false);
        for fr in &rep.funcs {
            if fr.error.is_some() || fr.kind != Some(FnKind::Safe) {
                continue;
            }
            let f = prog.funcs.iter().find(|g| g.name == fr.name).unwrap();
            // callees must have bodies here
            let calls_contract = f.instrs.iter().any(|pi| match &pi.instr {
                Instr::Jal {
                    target: Target::Symbol(s),
                    ..
                }
                | Instr::CallPair {
                    target: Target::Symbol(s),
                    ..
                } => {
                    ck.sigs.get(s).is_none_or(|g| g.kind != FnKind::Safe)
                        || !prog.funcs.iter().any(|g| g.name == *s)
                }
                _ => false,
            });
            if calls_contract {
                skipped.push(format!("{}: {} (calls a contract)", p.display(), fr.name));
                continue;
            }
            let s = &ck.sigs[&fr.name];
            let mut any = false;
            for _ in 0..300 {
                match run_case(&prog, f, s, &mut rng) {
                    Ok(true) => any = true,
                    Ok(false) => break,
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

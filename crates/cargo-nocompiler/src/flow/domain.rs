//! Abstract domains and the worklist solver over the RV64 CFG.
use super::{Graph, State, call, merge, word_key};
use nocompiler_typed::{
    asm::Func,
    isa::*,
    lin::{Lin, Var},
};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Interval {
    lo: u64,
    hi: u64,
}

impl Interval {
    const TOP: Self = Self {
        lo: 0,
        hi: u64::MAX,
    };

    fn negative(self) -> Option<bool> {
        let lower = (self.lo as i64).is_negative();
        let upper = (self.hi as i64).is_negative();
        (lower == upper).then_some(lower)
    }

    fn shifted(self, offset: i64) -> Option<Self> {
        Some(Self {
            lo: self.lo.checked_add_signed(offset)?,
            hi: self.hi.checked_add_signed(offset)?,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct UnsignedDomain(BTreeMap<Reg, Interval>);

/// Sparse upper bounds on differences of unsigned register representatives.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct DifferenceBounds(BTreeMap<(Reg, Reg), i128>);

impl DifferenceBounds {
    /// Assign an affine copy when unsigned arithmetic is known to stay
    /// in range. Translate both directions of the source's pair bounds.
    fn assign_offset(&mut self, dst: Reg, src: Reg, offset: i64) {
        let offset = i128::from(offset);
        let mut translated = Vec::new();
        for (&(a, b), &bound) in &self.0 {
            if a == src && b != dst {
                translated.push(((dst, b), bound + offset));
            }
            if b == src && a != dst {
                translated.push(((a, dst), bound - offset));
            }
        }
        self.forget(dst);
        if dst != src {
            translated.extend([((dst, src), offset), ((src, dst), -offset)]);
        }
        self.0.extend(
            translated.into_iter().filter(|&(_, bound)| {
                (-i128::from(u64::MAX)..i128::from(u64::MAX)).contains(&bound)
            }),
        );
    }

    fn forget(&mut self, reg: Reg) {
        self.0.retain(|&(a, b), _| a != reg && b != reg);
    }

    /// Add a constraint and propagate paths through the new edge.
    fn refine(&mut self, low: Reg, high: Reg, bound: i128) -> bool {
        if low == high {
            return bound >= 0;
        }
        if self
            .0
            .get(&(low, high))
            .is_some_and(|&prior| prior <= bound)
        {
            return true;
        }
        if self
            .0
            .get(&(high, low))
            .is_some_and(|&reverse| reverse + bound < 0)
        {
            return false;
        }
        let mut left = vec![(low, 0)];
        let mut right = vec![(high, 0)];
        for (&(a, b), &delta) in &self.0 {
            if b == low {
                left.push((a, delta));
            }
            if a == high {
                right.push((b, delta));
            }
        }
        for (a, prefix) in left {
            for &(b, suffix) in &right {
                if a != b {
                    let through = prefix + bound + suffix;
                    if through < -i128::from(u64::MAX) {
                        return false;
                    }
                    self.0
                        .entry((a, b))
                        .and_modify(|prior| *prior = (*prior).min(through))
                        .or_insert(through);
                }
            }
        }
        true
    }
}

/// A congruence modulo a power of two, represented by known low bits.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
struct LowBits {
    count: u32,
    value: u64,
}

impl LowBits {
    fn mask(count: u32) -> u64 {
        u64::MAX.checked_shr(64 - count).unwrap_or(0)
    }

    fn new(count: u32, value: u64) -> Self {
        Self {
            count,
            value: value & Self::mask(count),
        }
    }

    fn constant(value: u64) -> Self {
        Self { count: 64, value }
    }

    fn join(self, other: Self) -> Self {
        let common = (self.value ^ other.value).trailing_zeros();
        Self::new(self.count.min(other.count).min(common), self.value)
    }

    fn add(self, other: Self) -> Self {
        Self::new(
            self.count.min(other.count),
            self.value.wrapping_add(other.value),
        )
    }

    fn negate(self) -> Self {
        Self::new(self.count, self.value.wrapping_neg())
    }
}

/// Bounds on the offset of an RV64 address relative to one symbolic input.
/// Hardware addition remains modulo 2^64. The checker separately establishes
/// that the resulting access is valid inside the proposed region.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) struct RelativeAddress {
    pub(crate) base: Var,
    pub(crate) lo: i128,
    pub(crate) hi: i128,
    low_bits: LowBits,
}

impl RelativeAddress {
    pub(crate) fn aligned(self, alignment: i128) -> bool {
        let Ok(alignment) = u64::try_from(alignment) else {
            return false;
        };
        alignment.is_power_of_two()
            && self.low_bits.count >= alignment.trailing_zeros()
            && self.low_bits.value % alignment == 0
    }

    fn offset(self, lo: i128, hi: i128, bits: LowBits) -> Option<Self> {
        Some(Self {
            base: self.base,
            lo: self.lo.checked_add(lo)?,
            hi: self.hi.checked_add(hi)?,
            low_bits: self.low_bits.add(bits),
        })
    }
}

#[derive(Clone, PartialEq, Eq)]
pub(crate) struct AbstractState {
    pub(crate) exact: State,
    unsigned: UnsignedDomain,
    differences: DifferenceBounds,
    value_differences: BTreeMap<(Var, Var), i128>,
    nonzero_implies_less: BTreeMap<Reg, BTreeSet<(Var, Var)>>,
    addresses: BTreeMap<Reg, RelativeAddress>,
    low_bits: BTreeMap<Reg, LowBits>,
}

impl AbstractState {
    pub(crate) fn value_difference(&self, left: Var, right: Var) -> Option<i128> {
        self.value_differences.get(&(left, right)).copied()
    }

    pub(crate) fn unsigned_max(&self, reg: Reg) -> u64 {
        self.interval(reg).hi
    }

    pub(crate) fn relative_address(&self, reg: Reg, offset: i64) -> Option<RelativeAddress> {
        let address = self
            .exact
            .reg(reg)
            .and_then(word_key)
            .map(|(base, delta)| RelativeAddress {
                base,
                lo: delta,
                hi: delta,
                low_bits: LowBits::constant(delta as u64),
            })
            .or_else(|| self.addresses.get(&reg).copied())?;
        address.offset(
            offset.into(),
            offset.into(),
            LowBits::constant(offset as u64),
        )
    }

    fn interval(&self, reg: Reg) -> Interval {
        if let Some(value) = self.exact.reg(reg).and_then(|e| e.as_const()) {
            return Interval {
                lo: value as u64,
                hi: value as u64,
            };
        }
        self.unsigned.0.get(&reg).copied().unwrap_or(Interval::TOP)
    }

    fn known_bits(&self, reg: Reg) -> LowBits {
        let range = self.interval(reg);
        if range.lo == range.hi {
            LowBits::constant(range.lo)
        } else {
            self.low_bits.get(&reg).copied().unwrap_or_default()
        }
    }

    fn transfer_bits(&self, instr: &Instr) -> LowBits {
        match *instr {
            Instr::IOp {
                op: IOp::Addi,
                rs1,
                imm,
                ..
            } => self.known_bits(rs1).add(LowBits::constant(imm as u64)),
            Instr::IOp {
                op: IOp::Andi,
                rs1,
                imm,
                ..
            } => {
                let bits = self.known_bits(rs1);
                let mask = imm as u64;
                LowBits::new(
                    (LowBits::mask(bits.count) | !mask).trailing_ones(),
                    bits.value & mask,
                )
            }
            Instr::Shift {
                op: ShOp::Slli,
                rs1,
                sh,
                ..
            } => {
                let bits = self.known_bits(rs1);
                LowBits::new((bits.count + sh).min(64), bits.value << sh)
            }
            Instr::ROp {
                op: ROp::Add | ROp::Sub,
                rs1,
                rs2,
                ..
            } => {
                let rhs = self.known_bits(rs2);
                let rhs = if matches!(*instr, Instr::ROp { op: ROp::Sub, .. }) {
                    rhs.negate()
                } else {
                    rhs
                };
                self.known_bits(rs1).add(rhs)
            }
            _ => LowBits::default(),
        }
    }

    fn constrain(&mut self, reg: Reg, interval: Interval) {
        if reg == ZERO {
            return;
        }
        if interval == Interval::TOP {
            self.unsigned.0.remove(&reg);
        } else {
            self.unsigned.0.insert(reg, interval);
        }
        if interval.lo == interval.hi {
            self.exact
                .regs
                .insert(reg, Lin::konst(i128::from(interval.lo)));
        }
    }

    fn step(&mut self, instr: &Instr) {
        let binary = |op, a: Interval, b: Interval| {
            let (lo, hi) = match op {
                ROp::Add => (a.lo.checked_add(b.lo)?, a.hi.checked_add(b.hi)?),
                ROp::Sub => (a.lo.checked_sub(b.hi)?, a.hi.checked_sub(b.lo)?),
                ROp::And => (0, a.hi.min(b.hi)),
                _ => return None,
            };
            Some(Interval { lo, hi })
        };
        let bounds = match *instr {
            Instr::ROp { op, rs1, rs2, .. } if matches!(op, ROp::Add | ROp::Sub | ROp::And) => {
                binary(op, self.interval(rs1), self.interval(rs2))
            }
            Instr::Shift {
                op: ShOp::Srli,
                rs1,
                sh,
                ..
            } => {
                let range = self.interval(rs1);
                Some(Interval {
                    lo: range.lo >> sh,
                    hi: range.hi >> sh,
                })
            }
            Instr::Shift {
                op: ShOp::Slli,
                rs1,
                sh,
                ..
            } => {
                let range = self.interval(rs1);
                (range.hi <= u64::MAX >> sh).then(|| Interval {
                    lo: range.lo << sh,
                    hi: range.hi << sh,
                })
            }
            Instr::Load {
                op: op @ (LdOp::Lbu | LdOp::Lhu | LdOp::Lwu),
                ..
            } => Some(Interval {
                lo: 0,
                hi: (1u64 << (8 * op.width())) - 1,
            }),
            Instr::IOp {
                op: IOp::Addi,
                rs1,
                imm,
                ..
            } => self.interval(rs1).shifted(imm),
            Instr::IOp {
                op: IOp::Andi, imm, ..
            } if imm >= 0 => Some(Interval {
                lo: 0,
                hi: imm as u64,
            }),
            Instr::IOp {
                op: IOp::Slti | IOp::Sltiu,
                ..
            }
            | Instr::ROp {
                op: ROp::Slt | ROp::Sltu,
                ..
            } => Some(Interval { lo: 0, hi: 1 }),
            _ => None,
        };
        let bits = self.transfer_bits(instr);
        let relative = match *instr {
            Instr::IOp {
                op: IOp::Addi,
                rs1,
                imm,
                ..
            } => self.relative_address(rs1, imm),
            Instr::ROp {
                op: ROp::Add | ROp::Sub,
                rs1,
                rs2,
                ..
            } => {
                let shifted = |pointer, scalar, subtract| {
                    let relative = self.relative_address(pointer, 0)?;
                    let range = self.interval(scalar);
                    if range == Interval::TOP {
                        return None;
                    }
                    let (lo, hi) = (i128::from(range.lo), i128::from(range.hi));
                    let (lo, hi) = if subtract { (-hi, -lo) } else { (lo, hi) };
                    let bits = self.known_bits(scalar);
                    relative.offset(lo, hi, if subtract { bits.negate() } else { bits })
                };
                if matches!(*instr, Instr::ROp { op: ROp::Sub, .. }) {
                    shifted(rs1, rs2, true)
                } else {
                    shifted(rs1, rs2, false).or_else(|| shifted(rs2, rs1, false))
                }
            }
            _ => None,
        };
        let implications = match *instr {
            Instr::ROp {
                op: ROp::Sltu,
                rs1,
                rs2,
                ..
            } => self
                .exact
                .reg(rs1)
                .and_then(|e| e.as_var())
                .zip(self.exact.reg(rs2).and_then(|e| e.as_var()))
                .into_iter()
                .collect(),
            Instr::ROp {
                op: ROp::And,
                rs1,
                rs2,
                ..
            } => [rs1, rs2]
                .iter()
                .filter_map(|reg| self.nonzero_implies_less.get(reg))
                .flatten()
                .copied()
                .collect(),
            Instr::IOp {
                op: IOp::Addi,
                rs1,
                imm: 0,
                ..
            } => self
                .nonzero_implies_less
                .get(&rs1)
                .cloned()
                .unwrap_or_default(),
            _ => BTreeSet::new(),
        };
        self.exact.step(instr, None);
        if call(instr).is_some() || matches!(*instr, Instr::Ecall | Instr::Jalr { rd: RA, .. }) {
            self.unsigned.0.retain(|r, _| r.is_preserved());
            self.addresses.retain(|r, _| r.is_preserved());
            self.nonzero_implies_less.retain(|r, _| r.is_preserved());
            self.low_bits.retain(|r, _| r.is_preserved());
            self.differences.0.retain(|&(a, b), _| {
                (a == ZERO || a.is_preserved()) && (b == ZERO || b.is_preserved())
            });
        } else if let Some(rd) = instr.rd()
            && rd != ZERO
        {
            if implications.is_empty() {
                self.nonzero_implies_less.remove(&rd);
            } else {
                self.nonzero_implies_less.insert(rd, implications);
            }
            if let Instr::IOp {
                op: IOp::Addi,
                rs1,
                imm,
                ..
            } = *instr
                && bounds.is_some_and(|range| range.lo != range.hi)
            {
                self.differences.assign_offset(rd, rs1, imm);
            } else {
                self.differences.forget(rd);
            }
            if bits.count > 0 {
                self.low_bits.insert(rd, bits);
            } else {
                self.low_bits.remove(&rd);
            }
            if let Some(relative) = relative {
                self.addresses.insert(rd, relative);
            } else {
                self.addresses.remove(&rd);
            }
            // Transfer replaces the old range. Exact affine facts, when available,
            // still take precedence over intervals.
            if let Some(bounds) = bounds {
                self.constrain(rd, bounds);
            } else {
                self.unsigned.0.remove(&rd);
            }
        }
    }

    fn edge(&mut self, instr: &Instr, index: usize, successor: usize) -> bool {
        if let Instr::Branch {
            op,
            rs1,
            rs2,
            target: Target::Local(target),
        } = *instr
            && target != index + 1
        {
            let taken = successor == target;
            let a = self.interval(rs1);
            let b = self.interval(rs2);
            if matches!(op, BrOp::Beq | BrOp::Bne) {
                if taken == (op == BrOp::Beq) {
                    let common = Interval {
                        lo: a.lo.max(b.lo),
                        hi: a.hi.min(b.hi),
                    };
                    if common.lo > common.hi
                        || !self.differences.refine(rs1, rs2, 0)
                        || !self.differences.refine(rs2, rs1, 0)
                    {
                        return false;
                    }
                    self.constrain(rs1, common);
                    self.constrain(rs2, common);
                    return self.reduce_intervals();
                }
                if let Some(reg) = match (rs1, rs2) {
                    (ZERO, reg) | (reg, ZERO) => Some(reg),
                    _ => None,
                } && let Some(facts) = self.nonzero_implies_less.get(&reg)
                {
                    for &pair in facts {
                        self.value_differences
                            .entry(pair)
                            .and_modify(|bound| *bound = (*bound).min(-1))
                            .or_insert(-1);
                    }
                }
                return rs1 != rs2 && !(a.lo == a.hi && a == b);
            }
            let op = match op {
                BrOp::Blt | BrOp::Bge => {
                    let (Some(left), Some(right)) = (a.negative(), b.negative()) else {
                        return true;
                    };
                    if left != right {
                        return taken == (left == (op == BrOp::Blt));
                    }
                    if op == BrOp::Blt {
                        BrOp::Bltu
                    } else {
                        BrOp::Bgeu
                    }
                }
                _ => op,
            };
            let ordered = match (op, taken) {
                (BrOp::Bltu, true) | (BrOp::Bgeu, false) => Some((rs1, rs2, 1i128)),
                (BrOp::Bltu, false) | (BrOp::Bgeu, true) => Some((rs2, rs1, 0)),
                _ => None,
            };
            if let Some((low, high, gap)) = ordered {
                if let (Some(left), Some(right)) = (
                    self.exact.reg(low).and_then(|e| e.as_var()),
                    self.exact.reg(high).and_then(|e| e.as_var()),
                ) {
                    self.value_differences
                        .entry((left, right))
                        .and_modify(|bound| *bound = (*bound).min(-gap))
                        .or_insert(-gap);
                }
                return self.differences.refine(low, high, -gap) && self.reduce_intervals();
            }
        }
        true
    }

    fn reduce_intervals(&mut self) -> bool {
        let facts: Vec<_> = self
            .differences
            .0
            .iter()
            .map(|(&pair, &bound)| (pair, bound))
            .collect();
        // A simple path through the register relations has at most 31 edges.
        // Bounding propagation also avoids iterating an inconsistent cycle indefinitely.
        for _ in Reg::all() {
            let mut changed = false;
            for &((low, high), bound) in &facts {
                let a = self.interval(low);
                let b = self.interval(high);
                let upper = i128::from(b.hi) + bound;
                let lower = i128::from(a.lo) - bound;
                if upper < i128::from(a.lo) || lower > i128::from(b.hi) {
                    return false;
                }
                if upper < i128::from(a.hi) {
                    self.constrain(
                        low,
                        Interval {
                            lo: a.lo,
                            hi: upper as u64,
                        },
                    );
                    changed = true;
                }
                if lower > i128::from(b.lo) {
                    self.constrain(
                        high,
                        Interval {
                            lo: lower as u64,
                            hi: b.hi,
                        },
                    );
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        true
    }

    fn narrow(&mut self, incoming: Self) {
        for reg in Reg::all() {
            let old = self.interval(reg);
            let new = incoming.interval(reg);
            let bounds = Interval {
                lo: old.lo.max(new.lo),
                hi: old.hi.min(new.hi),
            };
            if bounds.lo <= bounds.hi {
                self.constrain(reg, bounds);
            }
        }
        for (reg, value) in incoming.exact.regs {
            self.exact.regs.entry(reg).or_insert(value);
        }
        self.exact.words.extend(incoming.exact.words);
        for (reg, bits) in incoming.low_bits {
            let prior = self.low_bits.entry(reg).or_default();
            if bits.count > prior.count {
                *prior = bits;
            }
        }
        for (reg, address) in incoming.addresses {
            self.addresses.entry(reg).or_insert(address);
        }
        for (pair, bound) in incoming.value_differences {
            self.value_differences
                .entry(pair)
                .and_modify(|old| *old = (*old).min(bound))
                .or_insert(bound);
        }
        for (pair, bound) in incoming.differences.0 {
            self.differences
                .0
                .entry(pair)
                .and_modify(|old| *old = (*old).min(bound))
                .or_insert(bound);
        }
    }

    fn join(&self, incoming: &Self, widen: bool) -> Self {
        let exact = merge([&self.exact, &incoming.exact].into_iter());
        let unsigned = UnsignedDomain(
            Reg::all()
                .filter(|&r| r != ZERO)
                .filter_map(|r| {
                    let a = self.interval(r);
                    let b = incoming.interval(r);
                    let bounds = Interval {
                        lo: if widen && b.lo < a.lo {
                            0
                        } else {
                            a.lo.min(b.lo)
                        },
                        hi: if widen && b.hi > a.hi {
                            u64::MAX
                        } else {
                            a.hi.max(b.hi)
                        },
                    };
                    (bounds != Interval::TOP).then_some((r, bounds))
                })
                .collect(),
        );
        let differences = DifferenceBounds(
            self.differences
                .0
                .iter()
                .filter_map(|(pair, a)| {
                    let b = incoming.differences.0.get(pair)?;
                    (!widen || b <= a).then_some((*pair, (*a).max(*b)))
                })
                .collect(),
        );
        let addresses = Reg::all()
            .filter_map(|reg| {
                let left = self.relative_address(reg, 0)?;
                let right = incoming.relative_address(reg, 0)?;
                if left.base != right.base || (widen && (right.lo < left.lo || right.hi > left.hi))
                {
                    return None;
                }
                Some((
                    reg,
                    RelativeAddress {
                        base: left.base,
                        lo: left.lo.min(right.lo),
                        hi: left.hi.max(right.hi),
                        low_bits: left.low_bits.join(right.low_bits),
                    },
                ))
            })
            .collect();
        Self {
            exact,
            unsigned,
            differences,
            value_differences: self
                .value_differences
                .iter()
                .filter_map(|(pair, a)| {
                    let b = incoming.value_differences.get(pair)?;
                    Some((*pair, (*a).max(*b)))
                })
                .collect(),
            nonzero_implies_less: self
                .nonzero_implies_less
                .iter()
                .filter_map(|(reg, facts)| {
                    let common: BTreeSet<_> = facts
                        .intersection(incoming.nonzero_implies_less.get(reg)?)
                        .copied()
                        .collect();
                    (!common.is_empty()).then_some((*reg, common))
                })
                .collect(),
            addresses,
            low_bits: Reg::all()
                .filter(|&reg| reg != ZERO)
                .filter_map(|reg| {
                    let bits = self.known_bits(reg).join(incoming.known_bits(reg));
                    (bits.count > 0).then_some((reg, bits))
                })
                .collect(),
        }
    }
}

pub(crate) fn analyze(func: &Func, start: State) -> Vec<Option<State>> {
    analyze_detailed(func, start)
        .into_iter()
        .map(|entry| entry.map(|entry| entry.exact))
        .collect()
}

/// Forward interpretation of the full CFG. The returned states are pre-states.
/// Widen at the targets of reverse-postorder retreating edges, which cut every cycle.
pub(crate) fn analyze_detailed(func: &Func, start: State) -> Vec<Option<AbstractState>> {
    analyze_with_edges(func, start, &crate::chc::Edges::new())
}

pub(crate) fn analyze_with_edges(
    func: &Func,
    start: State,
    unreachable: &crate::chc::Edges,
) -> Vec<Option<AbstractState>> {
    let cfg = Graph::new(func);
    let mut states = vec![None; func.instrs.len()];
    if states.is_empty() {
        return Vec::new();
    }
    let mut rank = vec![usize::MAX; states.len()];
    for (order, &node) in cfg.inner.reverse_postorder.iter().enumerate() {
        rank[node] = order;
    }
    let mut widening_points = vec![false; states.len()];
    for &node in &cfg.inner.reverse_postorder {
        for &next in &cfg.inner.successors[node] {
            if rank[next] <= rank[node] {
                widening_points[next] = true;
            }
        }
    }
    let mut updates = vec![0u8; states.len()];
    let mut pending = VecDeque::from([0]);
    let mut queued = vec![false; states.len()];
    queued[0] = true;
    let initial = AbstractState {
        exact: start,
        unsigned: UnsignedDomain(BTreeMap::new()),
        differences: DifferenceBounds::default(),
        value_differences: BTreeMap::new(),
        nonzero_implies_less: BTreeMap::new(),
        addresses: BTreeMap::new(),
        low_bits: BTreeMap::new(),
    };
    states[0] = Some(initial.clone());
    let mut widened = false;
    while let Some(node) = pending.pop_front() {
        queued[node] = false;
        let instr = &func.instrs[node].instr;
        let mut state = states[node].as_ref().expect("queued CFG state").clone();
        state.step(instr);
        for &next in &cfg.inner.successors[node] {
            if unreachable.contains(&(node, next)) {
                continue;
            }
            let mut candidate = state.clone();
            if !candidate.edge(instr, node, next) {
                continue;
            }
            if let Some(old) = &states[next] {
                let widen = widening_points[next] && updates[next] >= 2;
                let joined = old.join(&candidate, widen);
                widened |= widen && joined != old.join(&candidate, false);
                candidate = joined;
                if *old == candidate {
                    continue;
                }
            }
            states[next] = Some(candidate);
            updates[next] = updates[next].saturating_add(1);
            if !queued[next] {
                queued[next] = true;
                pending.push_back(next);
            }
        }
    }
    if widened {
        // Every sweep recomputes incoming states from a snapshot that already
        // covers reachable executions. No state is strengthened using a single predecessor.
        for _ in 0..2 {
            let mut incoming = vec![None; states.len()];
            incoming[0] = Some(initial.clone());
            for &node in &cfg.inner.reverse_postorder {
                let Some(mut state) = states[node].clone() else {
                    continue;
                };
                let instr = &func.instrs[node].instr;
                state.step(instr);
                for &next in &cfg.inner.successors[node] {
                    if unreachable.contains(&(node, next)) {
                        continue;
                    }
                    let mut edge = state.clone();
                    if edge.edge(instr, node, next) {
                        incoming[next] = Some(match &incoming[next] {
                            Some(previous) => previous.join(&edge, false),
                            None => edge,
                        });
                    }
                }
            }
            for (old, incoming) in states.iter_mut().zip(incoming) {
                if let (Some(old), Some(incoming)) = (old, incoming) {
                    old.narrow(incoming);
                }
            }
        }
    }
    states
}

#[cfg(test)]
mod tests {
    use super::*;

    fn state() -> AbstractState {
        AbstractState {
            exact: super::super::entry(),
            unsigned: UnsignedDomain(BTreeMap::new()),
            differences: DifferenceBounds::default(),
            value_differences: BTreeMap::new(),
            nonzero_implies_less: BTreeMap::new(),
            addresses: BTreeMap::new(),
            low_bits: BTreeMap::new(),
        }
    }

    #[test]
    fn narrowing_recovers_a_bound_at_the_cycle_header() {
        let program = nocompiler_typed::asm::parse(
            r#"
.type scan, @function
scan:
    li a1, 0
    li a2, 1000
.Lloop:
    addi a1, a1, 1
    bltu a1, a2, .Lloop
    ret
.size scan, .-scan
"#,
        )
        .unwrap();
        let func = &program.funcs[0];
        let states = analyze_detailed(func, super::super::entry());
        assert_eq!(
            states[func.labels[".Lloop"]]
                .as_ref()
                .unwrap()
                .interval(Reg(11)),
            Interval { lo: 0, hi: 999 },
        );
    }

    #[test]
    fn unsigned_branch_bounds_propagate_through_intermediate_registers() {
        let mut state = state();
        let (a, b, c) = (Reg(10), Reg(11), Reg(12));
        state.constrain(c, Interval { lo: 2, hi: 2 });
        for (rs1, rs2) in [(a, b), (b, c)] {
            assert!(state.edge(
                &Instr::Branch {
                    op: BrOp::Bltu,
                    rs1,
                    rs2,
                    target: Target::Local(2)
                },
                0,
                2,
            ));
        }
        assert_eq!(state.interval(a), Interval { lo: 0, hi: 0 });
        assert_eq!(state.interval(b), Interval { lo: 1, hi: 1 });
    }

    #[test]
    fn join_retains_a_difference_implied_by_different_paths() {
        let mut left = state();
        let mut right = state();
        let (a, b, c, d) = (Reg(10), Reg(11), Reg(12), Reg(13));
        for (state, via) in [(&mut left, b), (&mut right, c)] {
            assert!(state.differences.refine(a, via, -1));
            assert!(state.differences.refine(via, d, 0));
        }
        let joined = left.join(&right, false);
        assert_eq!(joined.differences.0, BTreeMap::from([((a, d), -1)]));
    }

    #[test]
    fn nonwrapping_addition_translates_difference_bounds() {
        let mut state = state();
        let (a, b) = (Reg(10), Reg(11));
        state.constrain(a, Interval { lo: 0, hi: 100 });
        assert!(state.differences.refine(a, b, -3));
        state.step(&Instr::IOp {
            op: IOp::Addi,
            rd: a,
            rs1: a,
            imm: 2,
        });
        assert_eq!(state.differences.0[&(a, b)], -1);
    }

    #[test]
    fn unsigned_addition_discards_interval_when_range_crosses_wraparound() {
        let mut state = state();
        let reg = Reg(10);
        state.constrain(
            reg,
            Interval {
                lo: u64::MAX - 1,
                hi: u64::MAX,
            },
        );
        state.step(&Instr::IOp {
            op: IOp::Addi,
            rd: reg,
            rs1: reg,
            imm: 1,
        });
        assert_eq!(state.interval(reg), Interval::TOP);
    }
}

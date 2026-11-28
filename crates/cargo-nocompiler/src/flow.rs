//! Forward RV64 abstract interpretation for annotation candidates.
//! The linked-image checker validates emitted annotations.
use nocompiler_typed::{
    asm::Func,
    isa::*,
    lin::{Lin, Var},
};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

pub type Nodes = BTreeSet<usize>;
#[derive(Clone, Default, PartialEq, Eq)]
pub struct State {
    pub regs: BTreeMap<Reg, Lin>,
    pub words: BTreeMap<(Var, i128), Lin>,
}
pub const ENTRY_SP: Var = Var(u32::MAX);
pub fn entry() -> State {
    State {
        regs: BTreeMap::from([(SP, Lin::var(ENTRY_SP))]),
        words: BTreeMap::new(),
    }
}
impl State {
    pub fn reg(&self, reg: Reg) -> Option<Lin> {
        if reg == ZERO {
            Some(Lin::default())
        } else {
            self.regs.get(&reg).cloned()
        }
    }
    pub fn after_call(&mut self) {
        self.regs.retain(|r, _| r.is_preserved());
        self.words.clear();
    }
    pub fn edge_constant(
        &self,
        instr: &Instr,
        index: usize,
        successor: usize,
    ) -> Option<(Reg, Lin)> {
        if let Instr::Branch {
            op: op @ (BrOp::Beq | BrOp::Bne),
            rs1,
            rs2,
            target: Target::Local(target),
        } = *instr
            && target != index + 1
            && (successor == target) == (op == BrOp::Beq)
        {
            match (self.reg(rs1), self.reg(rs2)) {
                (Some(value), _) if value.as_const().is_some() && rs2 != ZERO => Some((rs2, value)),
                (_, Some(value)) if value.as_const().is_some() && rs1 != ZERO => Some((rs1, value)),
                _ => None,
            }
        } else {
            None
        }
    }
    pub fn step(&mut self, instr: &Instr, opaque: Option<Var>) {
        let out = match *instr {
            Instr::IOp {
                op: IOp::Addi,
                rs1,
                imm,
                ..
            } => self.reg(rs1).and_then(|v| v.add_const(imm.into())),
            Instr::Shift {
                op: ShOp::Slli,
                rs1,
                sh,
                ..
            } => self.reg(rs1).and_then(|v| v.scale(1i128 << sh)),
            Instr::ROp {
                op: op @ (ROp::Add | ROp::Sub),
                rs1,
                rs2,
                ..
            } => self
                .reg(rs1)
                .zip(self.reg(rs2))
                .and_then(|(a, b)| if op == ROp::Add { a.add(&b) } else { a.sub(&b) }),
            _ if low_bit_mask(instr) => opaque.map(Lin::var),
            Instr::Lui { imm, .. } => Some(Lin::konst(((imm << 12) as i32).into())),
            Instr::Load {
                op: LdOp::Ld,
                rs1,
                off,
                ..
            } => address(self, rs1, off)
                .and_then(word_key)
                .and_then(|key| self.words.get(&key).cloned()),
            Instr::Store { op, rs1, rs2, off } => {
                let key = address(self, rs1, off).and_then(word_key);
                self.words.retain(|&(base, start), _| {
                    key.is_some_and(|(v, offset)| {
                        base == v
                            && (start + 8 <= offset || offset + i128::from(op.width()) <= start)
                    })
                });
                if let (StOp::Sd, Some(key), Some(value)) = (op, key, self.reg(rs2)) {
                    self.words.insert(key, value);
                }
                return;
            }
            Instr::CallPair { .. }
            | Instr::Jal {
                target: Target::Symbol(_),
                ..
            }
            | Instr::Jalr { rd: RA, .. }
            | Instr::Ecall => {
                self.after_call();
                return;
            }
            _ => None,
        };
        if let Some(rd) = instr.rd() {
            if let Some(value) = out {
                self.regs.insert(rd, value);
            } else {
                self.regs.remove(&rd);
            }
        }
    }
}

pub fn low_bit_mask(instr: &Instr) -> bool {
    matches!(*instr, Instr::IOp { op: IOp::Andi, imm, .. }
        if imm > 0 && (imm as u64 + 1).is_power_of_two())
}

pub fn address(state: &State, base: Reg, offset: i64) -> Option<Lin> {
    state.reg(base)?.add_const(offset.into())
}
pub fn word_key(value: Lin) -> Option<(Var, i128)> {
    let (var, coef) = value.terms.first_key_value()?;
    (value.terms.len() == 1 && *coef == 1).then_some((*var, value.konst))
}

pub fn access(instr: &Instr) -> Option<(Reg, i64, u32, bool)> {
    match *instr {
        Instr::Load { op, rs1, off, .. } => Some((rs1, off, op.width(), false)),
        Instr::Store { op, rs1, off, .. } => Some((rs1, off, op.width(), true)),
        _ => None,
    }
}

pub fn call(instr: &Instr) -> Option<(&str, bool)> {
    match instr {
        Instr::CallPair {
            rd,
            target: Target::Symbol(name),
            ..
        }
        | Instr::Jal {
            rd,
            target: Target::Symbol(name),
        } => Some((name, *rd == ZERO)),
        _ => None,
    }
}

pub fn merge<'a>(mut states: impl Iterator<Item = &'a State>) -> State {
    let Some(first) = states.next() else {
        return State::default();
    };
    let mut result = first.clone();
    for state in states {
        result.regs.retain(|r, v| state.regs.get(r) == Some(v));
        result.words.retain(|r, v| state.words.get(r) == Some(v));
    }
    result
}

pub struct AffineJoin {
    pub bases: [Lin; 2],
    pub steps: [i128; 2],
    pub min: i128,
    pub max: i128,
}

/// Find the integer line through incoming pairs of affine values. The
/// symbolic components must be fixed across edges; only the distance along
/// the line can vary.
pub fn affine_join(incoming: &[&State], anchor: Reg, related: Reg) -> Option<AffineJoin> {
    let a = incoming.first()?.reg(anchor)?;
    let b = incoming.first()?.reg(related)?;
    let offsets: Vec<_> = incoming
        .iter()
        .map(|state| {
            let x = state.reg(anchor)?.sub(&a)?.as_const()?;
            let y = state.reg(related)?.sub(&b)?.as_const()?;
            Some((x, y))
        })
        .collect::<Option<_>>()?;
    let &(x, y) = offsets.iter().find(|&&(x, y)| x != 0 && y != 0)?;
    let gcd = |mut a: u128, mut b: u128| {
        while b != 0 {
            (a, b) = (b, a % b);
        }
        a
    };
    let divisor = i128::try_from(gcd(x.unsigned_abs(), y.unsigned_abs())).ok()?;
    let dx = x / divisor;
    let dy = y / divisor;
    let mut lo = 0;
    let mut hi = 0;
    let mut stride = 0;
    for (x, y) in offsets {
        let t = x.checked_div(dx)?;
        if dx.checked_mul(t)? != x || dy.checked_mul(t)? != y {
            return None;
        }
        lo = lo.min(t);
        hi = hi.max(t);
        stride = gcd(stride, t.unsigned_abs());
    }
    let stride = i128::try_from(stride).ok()?;
    Some(AffineJoin {
        bases: [a, b],
        steps: [dx.checked_mul(stride)?, dy.checked_mul(stride)?],
        min: lo.checked_div(stride)?,
        max: hi.checked_div(stride)?,
    })
}

pub struct Graph {
    inner: nocompiler_typed::cfg::ControlFlow,
}
impl Graph {
    pub fn new(func: &Func) -> Self {
        Self {
            inner: nocompiler_typed::cfg::ControlFlow::new(func),
        }
    }
    pub fn natural_loops(&self) -> BTreeMap<usize, (Nodes, Nodes)> {
        let mut bodies: BTreeMap<_, _> =
            nocompiler_typed::cfg::loop_bodies(&self.inner.predecessors, &self.inner.back_edges)
                .into_iter()
                .map(|(head, body)| (head, (Nodes::new(), body)))
                .collect();
        for &(latch, head) in &self.inner.back_edges {
            if let Some((latches, _)) = bodies.get_mut(&head) {
                latches.insert(latch);
            }
        }
        bodies
    }
    pub fn order(&self, loops: &BTreeMap<usize, (Nodes, Nodes)>) -> Option<Schedule> {
        let mut preds: Vec<Nodes> = self
            .inner
            .predecessors
            .iter()
            .map(|p| p.iter().copied().collect())
            .collect();
        let reachable: Nodes = self.inner.reverse_postorder.iter().copied().collect();
        let mut successors = vec![vec![]; preds.len()];
        for &node in &reachable {
            if let Some((latches, _)) = loops.get(&node) {
                preds[node].retain(|p| !latches.contains(p));
            }
            for &p in &preds[node] {
                successors[p].push(node);
            }
        }
        let mut pending: VecDeque<_> = reachable
            .iter()
            .copied()
            .filter(|&n| preds[n].is_empty())
            .collect();
        let mut degrees: Vec<_> = preds.iter().map(Nodes::len).collect();
        let mut order = vec![];
        while let Some(node) = pending.pop_front() {
            order.push(node);
            for &next in &successors[node] {
                degrees[next] -= 1;
                if degrees[next] == 0 {
                    pending.push_back(next);
                }
            }
        }
        (order.len() == reachable.len()).then_some(Schedule { preds, order })
    }
}
pub struct Schedule {
    pub preds: Vec<Nodes>,
    pub order: Vec<usize>,
}

pub fn calls(func: &Func) -> impl Iterator<Item = (&str, bool)> {
    func.instrs.iter().filter_map(|p| call(&p.instr))
}

mod domain;
pub(crate) use domain::{
    AbstractState, RelativeAddress, analyze, analyze_detailed, analyze_with_edges,
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn affine_join_accepts_distinct_steps_and_rejects_non_collinear_values() {
        let (a, b) = (Reg(10), Reg(11));
        let (p, n) = (Lin::var(Var(0)), Lin::var(Var(1)));
        let mut states: Vec<_> = [0, 7, 12]
            .into_iter()
            .map(|i| State {
                regs: BTreeMap::from([
                    (a, p.add_const(6 * i).unwrap()),
                    (b, n.add_const(-4 * i).unwrap()),
                ]),
                ..State::default()
            })
            .collect();
        let refs: Vec<_> = states.iter().collect();
        let join = affine_join(&refs, a, b).unwrap();
        assert_eq!(join.steps, [6, -4]);
        assert_eq!((join.min, join.max), (0, 12));

        states[2].regs.insert(b, n.add_const(-47).unwrap());
        let refs: Vec<_> = states.iter().collect();
        assert!(affine_join(&refs, a, b).is_none());
    }
}

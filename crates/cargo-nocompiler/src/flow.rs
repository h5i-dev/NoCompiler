//! Speculative affine facts. The linked-image checker validates every emitted hint.
use nocompiler_typed::{
    asm::Func,
    isa::*,
    lin::{Lin, Var},
};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

pub type Nodes = BTreeSet<usize>;
#[derive(Clone, Default)]
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
            Instr::IOp {
                op: IOp::Andi,
                imm: 1 | 3 | 7 | 15,
                ..
            } => opaque.map(Lin::var),
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
            Instr::CallPair { .. } | Instr::Ecall => {
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

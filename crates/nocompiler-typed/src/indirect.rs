//! Candidate callees for register calls in an ELF proof.
use nocompiler_typed::{
    asm::{Func, Program},
    isa::{IOp, Instr, RA, Reg, ShOp, Target, ZERO},
    lin::TWO64,
    syntax::{SFormula, SInv, SLin, SRegTy},
};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

/// Give the Rust checker and exporter a direct-call view of constant register
/// calls. The Lean checker still sees the actual decoded JALR in the linked image.
pub fn resolve_register_calls(program: &mut Program, symbols: &BTreeMap<String, u64>) {
    let mut targets = BTreeMap::<u64, Option<&str>>::new();
    for (signature, _) in &program.sigs {
        if let Some(&addr) = symbols.get(&signature.name) {
            targets
                .entry(addr)
                .and_modify(|name| *name = None)
                .or_insert(Some(&signature.name));
        }
    }

    for body in &mut program.funcs {
        let states = constants_at_entries(body);
        for (index, (point, state)) in body.instrs.iter_mut().zip(states).enumerate() {
            let (Some(registers), Instr::Jalr { rd, rs1, off }) = (state, &point.instr) else {
                continue;
            };
            if (*rd != RA && *rd != ZERO) || (*rd, *rs1, *off) == (ZERO, RA, 0) {
                continue;
            }
            let Some(bases) = known(&registers, *rs1) else {
                continue;
            };
            let Some(callees): Option<BTreeSet<String>> = bases
                .iter()
                .map(|base| {
                    targets
                        .get(&(base.wrapping_add_signed(*off) & !1))?
                        .map(str::to_owned)
                })
                .collect()
            else {
                continue;
            };
            if *rd == ZERO && bases.len() != 1 {
                continue;
            }
            if bases.len() > 1 {
                body.invs
                    .entry(index)
                    .or_insert_with(|| (target_join(index, *rs1, &bases), point.line));
            }
            let Some(callee) = callees.first().cloned() else {
                continue;
            };
            program
                .indirect_callees
                .entry(body.name.clone())
                .or_default()
                .extend(callees);
            point.instr = Instr::Jal {
                rd: *rd,
                target: Target::Symbol(callee),
            };
        }
    }
}

fn target_join(index: usize, register: Reg, bases: &BTreeSet<u64>) -> SInv {
    let name = format!("__noco_jalr_{index}");
    let value = SLin {
        terms: BTreeMap::from([(name.clone(), 1)]),
        konst: 0,
    };
    let cases = bases
        .iter()
        .map(|&base| {
            let difference = SLin {
                konst: -i128::from(base),
                ..value.clone()
            };
            SFormula::Dvd(TWO64, difference)
        })
        .collect();
    SInv {
        is_loop: false,
        vars: vec![name],
        regs: vec![SRegTy {
            reg: register,
            expr: Some(value),
            range: None,
        }],
        wher: vec![SFormula::Or(cases)],
        decreases: None,
    }
}

type Registers = [Option<BTreeSet<u64>>; 32];
const MAX_TARGET_BASES: usize = 8;

fn known(registers: &Registers, reg: Reg) -> Option<BTreeSet<u64>> {
    if reg == ZERO {
        Some(BTreeSet::from([0]))
    } else {
        registers[usize::from(reg.0)].clone()
    }
}

/// Union finite sets at joins, widening to unknown when the set grows too large.
fn constants_at_entries(body: &Func) -> Vec<Option<Registers>> {
    let mut states = vec![None; body.instrs.len()];
    if states.is_empty() {
        return states;
    }
    states[0] = Some(std::array::from_fn(|_| None));
    let mut pending = VecDeque::from([0]);
    while let Some(index) = pending.pop_front() {
        let point = &body.instrs[index];
        let mut regs = states[index]
            .clone()
            .expect("queued points have an incoming state");
        let next = Some(index + 1);
        let successors = match point.instr {
            Instr::Branch {
                target: Target::Local(target),
                ..
            } => [next, Some(target)],
            Instr::Jal {
                rd: ZERO,
                target: Target::Local(target),
            } => [Some(target), None],
            Instr::Jal { rd: ZERO, .. }
            | Instr::Jalr { rd: ZERO, .. }
            | Instr::CallPair { rd: ZERO, .. }
            | Instr::Unimp => [None, None],
            Instr::Jal { .. } | Instr::Jalr { .. } | Instr::CallPair { .. } | Instr::Ecall => {
                regs.fill(None);
                [next, None]
            }
            _ => {
                if let Some(rd) = point.instr.rd()
                    && rd != ZERO
                {
                    let value = if point.reloc.is_some() {
                        None
                    } else {
                        match point.instr {
                            Instr::Lui { imm, .. } => {
                                Some(BTreeSet::from([((imm << 12) as i32 as i64) as u64]))
                            }
                            Instr::IOp {
                                op: IOp::Addi,
                                rs1,
                                imm,
                                ..
                            } => known(&regs, rs1).map(|vs| {
                                vs.into_iter().map(|v| v.wrapping_add_signed(imm)).collect()
                            }),
                            Instr::Addiw { rs1, imm, .. } => known(&regs, rs1).map(|vs| {
                                vs.into_iter()
                                    .map(|v| (v.wrapping_add_signed(imm) as i32 as i64) as u64)
                                    .collect()
                            }),
                            Instr::Shift {
                                op: ShOp::Slli,
                                rs1,
                                sh,
                                ..
                            } => known(&regs, rs1)
                                .map(|vs| vs.into_iter().map(|v| v.wrapping_shl(sh)).collect()),
                            _ => None,
                        }
                    };
                    regs[usize::from(rd.0)] = value;
                }
                [next, None]
            }
        };
        for next in successors.into_iter().flatten() {
            if next >= states.len() {
                continue;
            }
            if let Some(old) = &mut states[next] {
                let mut changed = false;
                for (prior, value) in old.iter_mut().zip(&regs) {
                    if prior.is_none() {
                        continue;
                    }
                    let joined = prior.as_ref().zip(value.as_ref()).and_then(|(a, b)| {
                        let union: BTreeSet<_> = a.union(b).copied().collect();
                        (union.len() <= MAX_TARGET_BASES).then_some(union)
                    });
                    if *prior != joined {
                        *prior = joined;
                        changed = true;
                    }
                }
                if changed {
                    pending.push_back(next);
                }
            } else {
                states[next] = Some(regs.clone());
                pending.push_back(next);
            }
        }
    }
    states
}

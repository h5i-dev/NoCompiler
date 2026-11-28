//! Candidate callees for register calls in an ELF proof.
use nocompiler_typed::{
    asm::{Func, Program, Reloc},
    cfg::ControlFlow,
    isa::{IOp, Instr, RA, Reg, ShOp, Target, ZERO},
    lin::TWO64,
    syntax::{SFormula, SInv, SLin, SRegTy},
};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

/// Resolve function addresses materialized by a linked AUIPC/ADDI pair.
fn resolve_function_addresses(
    body: &mut Func,
    symbols: &BTreeMap<String, u64>,
    functions: &BTreeMap<u64, Option<&str>>,
) {
    let Some(&entry) = symbols.get(&body.name) else {
        return;
    };
    let Some(first) = body.instrs.first() else {
        return;
    };
    let start = first.addr;
    let mut pairs = BTreeMap::<usize, Vec<usize>>::new();
    for (index, point) in body.instrs.iter().enumerate() {
        if let Some(Reloc::PcrelLo(label)) = &point.reloc
            && let Some(&high) = body.labels.get(label)
        {
            pairs.entry(high).or_default().push(index);
        }
    }
    for (high, lows) in pairs {
        let Some(point) = body.instrs.get(high) else {
            continue;
        };
        let (Instr::Auipc { .. }, Some(Reloc::PcrelHi(name))) = (&point.instr, &point.reloc) else {
            continue;
        };
        let Some(&address) = symbols.get(name) else {
            continue;
        };
        if functions.get(&address).and_then(|n| *n) != Some(name.as_str()) {
            continue;
        }
        if lows
            .iter()
            .any(|&i| !matches!(body.instrs[i].instr, Instr::IOp { op: IOp::Addi, .. }))
        {
            continue;
        }
        let Some(pc) = point
            .addr
            .checked_sub(start)
            .and_then(|offset| entry.checked_add(offset))
        else {
            continue;
        };
        let displacement = i128::from(address) - i128::from(pc);
        let low = (displacement + 2048).rem_euclid(4096) - 2048;
        let upper = displacement - low;
        if i32::try_from(upper).is_err() {
            continue;
        }
        body.instrs[high].reloc = Some(Reloc::LinkedAuipc(pc.wrapping_add_signed(upper as i64)));
        for low_index in lows {
            let point = &mut body.instrs[low_index];
            if let Instr::IOp { imm, .. } = &mut point.instr {
                *imm = low as i64;
                point.reloc = None;
            }
        }
    }
}

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
        resolve_function_addresses(body, symbols, &targets);
        let cfg = ControlFlow::new(body);
        let states = constants_at_entries(body);
        let mut target_registers = BTreeSet::new();
        for (point, state) in body.instrs.iter().zip(&states) {
            if let (Instr::Jalr { rd: RA, rs1, off }, Some(registers)) = (&point.instr, state)
                && known(registers, *rs1).is_some_and(|values| {
                    values.len() > 1
                        && values.iter().all(|value| {
                            targets
                                .get(&(value.wrapping_add_signed(*off) & !1))
                                .is_some_and(Option::is_some)
                        })
                })
            {
                target_registers.insert(*rs1);
            }
        }
        for (index, state) in states.iter().enumerate() {
            if target_registers.is_empty()
                || cfg.predecessors[index].len() < 2
                || body.invs.contains_key(&index)
            {
                continue;
            }
            let Some(registers) = state else { continue };
            let mut joined = None::<SInv>;
            // Preserve constants at the merge, before any copies or arithmetic
            // in the shared continuation leading to the register call.
            for reg in Reg::all() {
                let Some(values) = known(registers, reg).filter(|values| values.len() > 1) else {
                    continue;
                };
                if !target_registers.contains(&reg)
                    && !values.iter().all(|value| targets.contains_key(value))
                {
                    continue;
                }
                let part = target_join(index, reg, &values);
                if let Some(join) = &mut joined {
                    join.vars.extend(part.vars);
                    join.regs.extend(part.regs);
                    join.wher.extend(part.wher);
                } else {
                    joined = Some(part);
                }
            }
            if let Some(annotation) = joined {
                body.invs
                    .insert(index, (annotation, body.instrs[index].line));
            }
        }
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
    let name = format!("__noco_jalr_{index}_{}", register.0);
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
                    let value = if let Some(Reloc::LinkedAuipc(address)) = point.reloc {
                        Some(BTreeSet::from([address]))
                    } else if point.reloc.is_some() {
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

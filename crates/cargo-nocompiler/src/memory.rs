use crate::{
    contract_ir::{Access, Expr, Input, Summary},
    contracts::Layout,
    flow::{
        ENTRY_SP, State, access, address, analyze, analyze_detailed, analyze_with_edges, call,
        calls, entry,
    },
};
use nocompiler_typed::{
    asm::Func,
    cfg::ControlFlow,
    isa::{Instr, Reg, SP},
    lin::{Lin, Var},
};
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    path::Path,
};

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Region {
    pub bytes: i128,
    pub alignment: i128,
    pub writable: bool,
}
impl Region {
    pub fn mode(self) -> &'static str {
        if self.writable { "rw" } else { "ro" }
    }
}
pub type Regions = BTreeMap<Reg, Region>;
pub type Requirements = BTreeMap<String, Regions>;

fn union_requirements(into: &mut Regions, from: &Regions) -> bool {
    let mut changed = false;
    for (&reg, incoming) in from {
        let current = into.entry(reg).or_insert(Region {
            bytes: 0,
            alignment: 1,
            writable: false,
        });
        let joined = Region {
            bytes: current.bytes.max(incoming.bytes),
            alignment: current.alignment.max(incoming.alignment),
            writable: current.writable || incoming.writable,
        };
        changed |= joined != *current;
        *current = joined;
    }
    changed
}

/// Local obligations are already expressed relative to function inputs.
/// Backward union computes the regions needed by all continuations of entry.
fn entry_demands<T: Default>(
    func: &Func,
    mut demands: Vec<T>,
    union: impl Fn(&mut T, &T) -> bool,
) -> T {
    let cfg = ControlFlow::new(func);
    let mut queue: VecDeque<_> = cfg.reverse_postorder.iter().rev().copied().collect();
    let mut queued = vec![true; demands.len()];
    while let Some(node) = queue.pop_front() {
        queued[node] = false;
        for &pred in &cfg.predecessors[node] {
            if pred == node {
                continue;
            }
            let (left, right) = demands.split_at_mut(node.max(pred));
            let (from, into) = if node < pred {
                (&left[node], &mut right[0])
            } else {
                (&right[0], &mut left[pred])
            };
            if union(into, from) && !queued[pred] {
                queue.push_back(pred);
                queued[pred] = true;
            }
        }
    }
    demands.into_iter().next().unwrap_or_default()
}

fn argument_regs(layout: &Layout) -> impl Iterator<Item = Reg> {
    layout.args.iter().scan(10u8, |next, arg| {
        let reg = Reg(*next);
        *next += if arg.starts_with("slice:") { 2 } else { 1 };
        Some(reg)
    })
}

fn substitute_access(access: &Access, callee: &Layout, state: &State) -> Option<(Lin, i128)> {
    let registers: Vec<_> = argument_regs(callee).collect();
    let result = access.offset.terms.iter().try_fold(
        state
            .reg(*registers.get(access.argument)?)?
            .add_const(access.offset.constant)?,
        |sum, (&input, &coefficient)| {
            let reg = match input {
                Input::Value(index) => *registers.get(index)?,
                Input::Length(index) => Reg(registers.get(index)?.0 + 1),
            };
            sum.add(&state.reg(reg)?.scale(coefficient)?)
        },
    )?;
    access
        .bytes
        .terms
        .is_empty()
        .then_some((result, access.bytes.constant))
}

/// Pick an upper bound only when it is provably at least as tight as
/// every alternative. Otherwise retain the original input expression.
fn tight_upper(
    input: Var,
    scalars: &BTreeMap<Var, Input>,
    difference: impl Fn(Var, Var) -> Option<i128>,
) -> Option<(Input, i128)> {
    let candidates: Vec<_> = scalars
        .keys()
        .filter_map(|&limit| {
            let delta = difference(input, limit)?;
            (input != limit && delta < 0).then_some((limit, delta))
        })
        .collect();
    candidates.iter().find_map(|&(limit, delta)| {
        candidates
            .iter()
            .all(|&(other, other_delta)| {
                limit == other
                    || difference(limit, other).is_some_and(|bound| {
                        bound
                            .checked_add(delta)
                            .is_some_and(|upper| upper <= other_delta)
                    })
            })
            .then_some((scalars[&limit], delta))
    })
}

/// Lift computed RV64 addresses to input-relative affine access demands.
fn symbolic_accesses(
    func: &Func,
    layout: &Layout,
    callees: &BTreeMap<String, Summary>,
    layouts: &BTreeMap<String, Layout>,
) -> Summary {
    let mut entry_state = entry();
    let mut bases = BTreeMap::new();
    let mut scalars = BTreeMap::new();
    for (index, (arg, reg)) in layout.args.iter().zip(argument_regs(layout)).enumerate() {
        let id = Var(u32::from(reg.0));
        if arg == "ptr" {
            entry_state.regs.insert(reg, Lin::var(id));
            bases.insert(id, index);
        } else if arg == "uword" {
            entry_state.regs.insert(reg, Lin::var(id));
            scalars.insert(id, Input::Value(index));
        } else if arg.starts_with("slice:") {
            entry_state
                .regs
                .insert(Reg(reg.0 + 1), Lin::var(Var(u32::from(reg.0 + 1))));
            scalars.insert(Var(u32::from(reg.0 + 1)), Input::Length(index));
        }
    }
    if bases.is_empty() {
        return Summary::default();
    }
    let lift = |addr: Lin, width, alignment, write, state: &crate::flow::AbstractState| {
        let mut root = None;
        let mut offset = Expr::constant(addr.konst);
        let mut bounded = Expr::constant(addr.konst);
        for (&id, &coefficient) in &addr.terms {
            if let Some(&index) = bases.get(&id) {
                if coefficient != 1 || root.replace(index).is_some() {
                    return None;
                }
            } else {
                let input = *scalars.get(&id)?;
                if coefficient <= 0 {
                    return None;
                }
                offset = offset.add(&Expr::input(input), coefficient)?;
                let (upper, delta) = tight_upper(id, &scalars, |left, right| {
                    state.value_difference(left, right)
                })
                .unwrap_or((input, 0));
                let term = Expr::input(upper).add(&Expr::constant(delta), 1)?;
                bounded = bounded.add(&term, coefficient)?;
            }
        }
        Some(Access {
            argument: root?,
            offset: if bounded.constant.checked_add(width)? >= 0 {
                bounded
            } else {
                offset
            },
            bytes: Expr::constant(width),
            alignment,
            write,
        })
    };
    let demands = func
        .instrs
        .iter()
        .zip(analyze_detailed(func, entry_state))
        .map(|(point, state)| {
            let mut demands = BTreeSet::new();
            let Some(state) = state else { return demands };
            if let Some((base, displacement, width, write)) = access(&point.instr)
                && let Some(addr) = address(&state.exact, base, displacement)
                && addr.konst >= 0
            {
                demands.extend(lift(addr, width.into(), width.into(), write, &state));
            }
            if let Some((callee, _)) = call(&point.instr)
                && let Some(summary) = callees.get(callee)
            {
                let callee = &layouts[callee];
                for demand in &summary.accesses {
                    if let Some((addr, width)) = substitute_access(demand, callee, &state.exact) {
                        demands.extend(lift(addr, width, demand.alignment, demand.write, &state));
                    }
                }
            }
            demands
        })
        .collect();
    let accesses = entry_demands(func, demands, |into, from| {
        let size = into.len();
        into.extend(from.iter().cloned());
        into.len() != size
    });
    Summary {
        accesses,
        ..Summary::default()
    }
}

pub fn symbolic_requirements(
    funcs: &[Func],
    layouts: &BTreeMap<String, Layout>,
) -> BTreeMap<String, Summary> {
    let mut summaries = BTreeMap::new();
    let mut pending: BTreeMap<_, _> = funcs
        .iter()
        .filter(|func| {
            layouts[&func.name].is_unsafe && layouts[&func.name].args.iter().any(|arg| arg == "ptr")
        })
        .map(|func| (func.name.as_str(), func))
        .collect();
    loop {
        let ready: Vec<_> = pending
            .values()
            .copied()
            .filter(|func| calls(func).all(|(callee, _)| !pending.contains_key(callee)))
            .collect();
        if ready.is_empty() {
            return summaries;
        }
        for func in ready {
            let summary = symbolic_accesses(func, &layouts[&func.name], &summaries, layouts);
            summaries.insert(func.name.clone(), summary);
            pending.remove(func.name.as_str());
        }
    }
}

pub fn requirements(
    funcs: &[Func],
    pointers: &BTreeMap<String, BTreeMap<Reg, Var>>,
    solver: Option<&Path>,
) -> (Requirements, BTreeMap<String, usize>) {
    let mut refined = BTreeMap::new();
    let mut pending: BTreeMap<_, _> = funcs
        .iter()
        .filter(|f| pointers.get(&f.name).is_some_and(|p| !p.is_empty()))
        .map(|f| (f.name.clone(), f))
        .collect();
    let mut all = Requirements::new();
    loop {
        let ready: Vec<_> = pending
            .values()
            .copied()
            .filter(|f| calls(f).all(|(c, _)| !pending.contains_key(c)))
            .collect();
        if ready.is_empty() {
            break;
        }
        for f in ready {
            let vars = &pointers[&f.name];
            let mut start = entry();
            start
                .regs
                .extend(vars.iter().map(|(&r, &v)| (r, Lin::var(v))));
            let mut demands = vec![Regions::new(); f.instrs.len()];
            if !f.instrs.iter().any(|p| {
                matches!(p.instr, Instr::Ecall)
                    || matches!(p.instr, Instr::Jalr {rd,..} if rd != nocompiler_typed::isa::ZERO)
            }) {
                let unreachable = solver
                    .map(|path| crate::chc::unreachable(f, path))
                    .unwrap_or_default();
                if !unreachable.is_empty() {
                    refined.insert(f.name.clone(), unreachable.len());
                }
                for ((point, state), regions) in f
                    .instrs
                    .iter()
                    .zip(analyze_with_edges(f, start, &unreachable))
                    .zip(&mut demands)
                {
                    let Some(state) = state else { continue };
                    let instr = &point.instr;
                    let mut add = |value: Option<crate::flow::RelativeAddress>,
                                   size: i128,
                                   align: i128,
                                   write: bool| {
                        let Some(address) = value else {
                            return;
                        };
                        let Some((&reg, _)) = vars.iter().find(|&(_, v)| *v == address.base) else {
                            return;
                        };
                        if address.lo < 0 || !address.aligned(align) {
                            return;
                        }
                        let Some(end) = address
                            .hi
                            .checked_add(size)
                            .filter(|&end| end <= i128::from(i64::MAX))
                        else {
                            return;
                        };
                        let found = regions.entry(reg).or_insert(Region {
                            bytes: 0,
                            alignment: 1,
                            writable: false,
                        });
                        found.bytes = found.bytes.max(end);
                        found.alignment = found.alignment.max(align);
                        found.writable |= write;
                    };
                    if let Some((base, offset, width, write)) = access(instr) {
                        add(
                            state.relative_address(base, offset),
                            width.into(),
                            width.into(),
                            write,
                        );
                    }
                    if let Some((callee, _)) = call(instr)
                        && let Some(requirements) = all.get(callee)
                    {
                        for (&reg, region) in requirements {
                            add(
                                state.relative_address(reg, 0),
                                region.bytes,
                                region.alignment,
                                region.writable,
                            );
                        }
                    }
                }
            }
            all.insert(
                f.name.clone(),
                entry_demands(f, demands, union_requirements),
            );
            pending.remove(&f.name);
        }
    }
    (all, refined)
}

fn frame(func: &Func, requirements: &Requirements) -> (i128, String) {
    let states = analyze(func, entry());
    let depth = |state: &State| {
        state
            .reg(SP)?
            .sub(&Lin::var(ENTRY_SP))?
            .as_const()?
            .checked_neg()
    };
    let Some(depths) = states
        .iter()
        .flatten()
        .map(depth)
        .collect::<Option<BTreeSet<_>>>()
    else {
        return (0, String::new());
    };
    // The frame rule permits one fixed allocation depth on each path.
    let mut allocated = depths.into_iter().filter(|&depth| depth != 0);
    let Some(size) = allocated
        .next()
        .filter(|&depth| depth > 0 && depth % 16 == 0)
    else {
        return (0, String::new());
    };
    if allocated.next().is_some() {
        return (0, String::new());
    }
    let mut taken = BTreeSet::new();
    let mut accesses = BTreeSet::new();
    for (point, state) in func.instrs.iter().zip(states.iter()) {
        let Some(state) = state.as_ref().filter(|state| depth(state) == Some(size)) else {
            continue;
        };
        let instr = &point.instr;
        let range = |reg, offset, width| {
            let start = address(state, reg, offset)?
                .sub(&state.reg(SP)?)?
                .as_const()?;
            let end = start.checked_add(width)?;
            (start >= 0 && start < end && end <= size).then_some((start, end))
        };
        if let Some((base, offset, width, _)) = access(instr)
            && let Some(span) = range(base, offset, width.into())
        {
            accesses.insert(span);
            if base != SP {
                taken.insert(span);
            }
        }
        if let Some((callee, false)) = call(instr)
            && let Some(regions) = requirements.get(callee)
        {
            for (&reg, region) in regions {
                taken.extend(range(reg, 0, region.bytes));
            }
        }
    }
    accesses.extend(taken.iter().copied());
    let mut slots = vec![];
    let mut ranges: Vec<(i128, i128)> = vec![];
    for &(start, end) in &accesses {
        if !taken.contains(&(start, end))
            && end - start == 8
            && start % 8 == 0
            && !accesses
                .iter()
                .any(|&(a, b)| (a, b) != (start, end) && a < end && start < b)
        {
            slots.push(start.to_string());
        } else if let Some(last) = ranges.last_mut()
            && start <= last.1
        {
            last.1 = last.1.max(end);
        } else {
            ranges.push((start, end));
        }
    }
    let mut text = format!("frame {size} ");
    if !slots.is_empty() {
        text.push_str(&format!("slots {} ", slots.join(", ")));
    }
    if !ranges.is_empty() {
        text.push_str(&format!(
            "addr {} ",
            ranges
                .iter()
                .map(|(a, b)| format!("[{a}, {b})"))
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    (size, text)
}

pub fn stack(
    funcs: &[Func],
    requirements: &Requirements,
    mut budgets: BTreeMap<String, i128>,
) -> BTreeMap<String, String> {
    let frames: BTreeMap<_, _> = funcs
        .iter()
        .map(|f| (f.name.clone(), frame(f, requirements)))
        .collect();
    loop {
        let ready: Vec<_> = funcs
            .iter()
            .filter(|f| {
                !budgets.contains_key(&f.name) && calls(f).all(|(c, _)| budgets.contains_key(c))
            })
            .map(|f| {
                let size = frames[&f.name].0;
                (
                    f.name.clone(),
                    calls(f)
                        .filter_map(|(c, tail)| budgets[c].checked_add(if tail { 0 } else { size }))
                        .fold(size, i128::max),
                )
            })
            .collect();
        if ready.is_empty() {
            break;
        }
        budgets.extend(ready);
    }
    frames
        .into_iter()
        .map(|(name, (size, frame))| {
            let total = budgets.get(&name).copied().unwrap_or(size);
            (name, format!("{frame}stack {total}"))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bound_selection_depends_on_ordering_facts() {
        let (index, first, second) = (Var(1), Var(2), Var(3));
        let scalars = BTreeMap::from([
            (index, Input::Value(0)),
            (first, Input::Value(1)),
            (second, Input::Value(2)),
        ]);
        let mut bounds = BTreeMap::from([((index, first), -1), ((index, second), -1)]);
        assert_eq!(
            tight_upper(index, &scalars, |a, b| bounds.get(&(a, b)).copied()),
            None
        );
        bounds.insert((second, first), 0);
        assert_eq!(
            tight_upper(index, &scalars, |a, b| bounds.get(&(a, b)).copied()),
            Some((Input::Value(2), -1)),
        );
    }
}

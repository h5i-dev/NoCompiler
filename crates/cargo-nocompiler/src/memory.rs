use crate::flow::{Graph, State, access, address, call, calls, entry, merge, word_key};
use nocompiler_typed::{
    asm::Func,
    isa::{IOp, Instr, Reg, SP},
    lin::{Lin, Var},
};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy)]
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

fn walk(func: &Func, start: State, mut visit: impl FnMut(&Instr, &State)) {
    let graph = Graph::new(func);
    let Some(order) = graph.order(&BTreeMap::new()) else {
        return;
    };
    let mut states = vec![State::default(); func.instrs.len()];
    for i in order.order {
        let mut state = if i == 0 {
            start.clone()
        } else {
            merge(order.preds[i].iter().map(|&p| &states[p]))
        };
        let instr = &func.instrs[i].instr;
        visit(instr, &state);
        state.step(instr, None);
        states[i] = state;
    }
}
pub fn requirements(
    funcs: &[Func],
    pointers: &BTreeMap<String, BTreeMap<Reg, Var>>,
) -> Requirements {
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
            let mut regions = Regions::new();
            if !f.instrs.iter().any(|p| {
                matches!(p.instr, Instr::Ecall)
                    || matches!(p.instr, Instr::Jalr {rd,..} if rd != nocompiler_typed::isa::ZERO)
            }) {
                walk(f, start, |instr, state| {
                    let mut add = |value: Option<Lin>, size: i128, align: i128, write: bool| {
                        let Some((base, offset)) = value.and_then(word_key) else {
                            return;
                        };
                        let Some((&reg, _)) = vars.iter().find(|&(_, v)| *v == base) else {
                            return;
                        };
                        if offset < 0 || offset % align != 0 {
                            return;
                        }
                        let Some(end) = offset.checked_add(size) else {
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
                            address(state, base, offset),
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
                                state.reg(reg),
                                region.bytes,
                                region.alignment,
                                region.writable,
                            );
                        }
                    }
                });
            }
            all.insert(f.name.clone(), regions);
            pending.remove(&f.name);
        }
    }
    all
}

fn frame(func: &Func, requirements: &Requirements) -> (i128, String) {
    let size = match func.instrs.first().map(|p| &p.instr) {
        Some(Instr::IOp {
            op: IOp::Addi,
            rd: SP,
            rs1: SP,
            imm,
        }) => -i128::from(*imm),
        _ => 0,
    };
    if size <= 0 || size % 16 != 0 {
        return (0, String::new());
    }
    let mut taken = BTreeSet::new();
    walk(func, entry(), |instr, state| {
        if let Some((name, false)) = call(instr)
            && let Some(regions) = requirements.get(name)
        {
            for (&reg, region) in regions {
                if let Some(offset) = state
                    .reg(reg)
                    .zip(state.reg(SP))
                    .and_then(|(a, b)| a.sub(&b))
                    .and_then(|x| x.as_const())
                    && let Some(end) = offset.checked_add(region.bytes)
                    && offset >= 0
                    && end <= size
                {
                    taken.insert((offset, end));
                }
            }
        }
    });
    let accesses: BTreeSet<_> = func
        .instrs
        .iter()
        .filter_map(|p| {
            let (base, offset, width, _) = access(&p.instr)?;
            let start = i128::from(offset);
            let end = start + i128::from(width);
            (base == SP && start >= 0 && end <= size).then_some((start, end))
        })
        .chain(taken.iter().copied())
        .collect();
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

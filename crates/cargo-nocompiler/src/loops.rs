use crate::flow::{Graph, State, access, merge};
use nocompiler_typed::{
    asm::Func,
    isa::{BrOp, IOp, Instr, Reg, SP, Target, ZERO},
    lin::{Lin, Names, Var},
};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone)]
pub struct Slice {
    pub base: Var,
    pub length: Var,
    pub stride: i128,
}

type Registers = BTreeMap<Reg, Lin>;
type Candidate = (Registers, Vec<String>);

fn difference(value: &Lin, reg: Reg) -> Option<Lin> {
    value.sub(&Lin::var(Var(u32::from(reg.0))))
}

fn candidate(
    func: &Func,
    body: &BTreeSet<usize>,
    instr: &Instr,
    entry: &State,
    post: &State,
    remaining: Var,
    context: &Context<'_>,
) -> Option<Candidate> {
    let (op, left, right) = match *instr {
        Instr::Branch {
            op: BrOp::Bne,
            rs1,
            rs2,
            ..
        } => (BrOp::Bne, rs1, rs2),
        Instr::Branch {
            op: BrOp::Bgeu,
            rs1,
            rs2,
            ..
        } => (BrOp::Bgeu, rs2, rs1),
        _ => return None,
    };
    let old = |reg: Reg| {
        if reg == ZERO {
            return Some((Lin::default(), 0));
        }
        let update = post.reg(reg)?;
        entry.regs.iter().find_map(|(&carried, initial)| {
            if post.regs.get(&carried) != Some(&update) {
                return None;
            }
            Some((initial.clone(), difference(&update, carried)?.as_const()?))
        })
    };
    let fixed = || {
        let (a, da) = old(left)?;
        let (b, db) = old(right)?;
        let mut distance = a.sub(&b)?;
        let mut scale = db.checked_sub(da)?;
        if scale == 0 {
            return None;
        }
        let mut lower = 1;
        if op == BrOp::Bgeu {
            if da <= 0 || db != 0 {
                return None;
            }
            lower = da;
            distance = distance.add_const(scale)?;
            scale = -1;
        }
        if distance.konst % scale != 0 || distance.terms.values().any(|v| v % scale != 0) {
            return None;
        }
        let trip = Lin {
            konst: distance.konst / scale,
            terms: distance
                .terms
                .into_iter()
                .map(|(v, c)| (v, c / scale))
                .collect(),
        };
        let length = context
            .slices
            .iter()
            .map(|s| s.length)
            .find(|&n| {
                trip.coef(n) == 1
                    && trip.konst <= 0
                    && trip.terms.iter().all(|(&v, &k)| {
                        v == n
                            || context.opaque.contains(&v)
                            || (context.prefixes.get(&v) == Some(&n) && k == -1)
                    })
            })
            .or_else(|| trip.as_var().and_then(|v| context.tails.get(&v).copied()))?;
        let mut bounds = vec![format!(
            "{lower} <= {} <= {}",
            context.names.name(remaining),
            context.names.name(length)
        )];
        let shift = trip.sub(&Lin::var(remaining))?;
        let mut regs = Registers::new();
        for (&reg, start) in &entry.regs {
            if reg == SP {
                continue;
            }
            let Some(step) = post
                .regs
                .get(&reg)
                .and_then(|v| difference(v, reg))
                .and_then(|x| x.as_const())
            else {
                continue;
            };
            if step == 0 || step % lower != 0 {
                continue;
            }
            let value = start.add(&shift.scale(step / lower)?)?;
            if value.vars().any(|v| context.hidden(v)) {
                continue;
            }
            if op == BrOp::Bgeu {
                let aligned: BTreeSet<_> = body
                    .iter()
                    .filter_map(|&node| {
                        let (base, offset, width, _) = access(&func.instrs[node].instr)?;
                        (base == reg && width > 1 && step % i128::from(width) == 0)
                            .then_some((width, offset))
                    })
                    .collect();
                for (width, offset) in aligned {
                    bounds.push(format!(
                        "{width} | ({})",
                        value.add_const(offset.into())?.display(context.names)
                    ));
                }
            }
            regs.insert(reg, value);
        }
        (!regs.is_empty()).then_some((regs, bounds))
    };
    fixed().or_else(|| {
        if op != BrOp::Bne || right != ZERO {
            return None;
        }
        let length = entry.reg(left)?.as_var()?;
        if !context.slices.iter().any(|s| s.length == length) {
            return None;
        }
        let delta = difference(&post.reg(left)?, left)?;
        let (&term, &scale) = delta.terms.first_key_value()?;
        let shift = Lin::var(remaining).sub(&Lin::var(length))?;
        let mut regs = Registers::new();
        for (&reg, start) in &entry.regs {
            if reg == SP || start.vars().any(|v| context.hidden(v)) {
                continue;
            }
            let Some(step) = post.regs.get(&reg).and_then(|v| difference(v, reg)) else {
                continue;
            };
            let coeff = step.coef(term);
            if coeff == 0 || coeff % scale != 0 {
                continue;
            }
            let multiple = coeff / scale;
            if delta.scale(multiple).as_ref() == Some(&step) {
                regs.insert(reg, start.add(&shift.scale(multiple)?)?);
            }
        }
        (regs.len() >= 2).then(|| {
            (
                regs,
                vec![format!(
                    "1 <= {} <= {}",
                    context.names.name(remaining),
                    context.names.name(length)
                )],
            )
        })
    })
}

struct Context<'a> {
    names: &'a mut Names,
    slices: &'a [Slice],
    opaque: BTreeSet<Var>,
    prefixes: BTreeMap<Var, Var>,
    tails: BTreeMap<Var, Var>,
}
impl Context<'_> {
    fn hidden(&self, v: Var) -> bool {
        v == crate::flow::ENTRY_SP
            || self.opaque.contains(&v)
            || self.prefixes.contains_key(&v)
            || self.tails.contains_key(&v)
    }
}

fn registers(regs: &Registers, names: &Names) -> String {
    regs.iter()
        .map(|(r, e)| format!("{r}: int({})", e.display(names)))
        .collect::<Vec<_>>()
        .join(", ")
}

fn join_relations(
    node: usize,
    instr: &Instr,
    incoming: &[&State],
    merged: &State,
    context: &mut Context<'_>,
) -> (Registers, Vec<String>, Vec<String>) {
    let mut regs = Registers::new();
    let mut vars = vec![];
    let mut bounds = vec![];
    let keys: Vec<_> = incoming[0]
        .regs
        .keys()
        .copied()
        .filter(|r| !merged.regs.contains_key(r) && incoming.iter().all(|p| p.regs.contains_key(r)))
        .collect();
    for slice in context.slices {
        for &cursor in &keys {
            if regs.contains_key(&cursor) {
                continue;
            }
            'bases: for base in [Lin::var(slice.base), Lin::default()] {
                let Some(distances) = incoming
                    .iter()
                    .map(|s| {
                        let d = s.reg(cursor)?.sub(&base)?.as_const()?;
                        (d >= 0 && d % slice.stride == 0).then_some(d / slice.stride)
                    })
                    .collect::<Option<Vec<_>>>()
                else {
                    continue;
                };
                for &count in &keys {
                    if count == cursor || regs.contains_key(&count) {
                        continue;
                    }
                    for count_base in [Lin::var(slice.length), Lin::default()] {
                        if !incoming
                            .iter()
                            .zip(&distances)
                            .all(|(s, d)| s.reg(count) == count_base.add_const(-d))
                        {
                            continue;
                        }
                        let name = format!("prefix{node}_{}", vars.len());
                        let var = context.names.fresh(&name);
                        let (mut p, mut n) = (base.clone(), count_base);
                        p.add_term(var, slice.stride).unwrap();
                        n.add_term(var, -1).unwrap();
                        regs.extend([(cursor, p), (count, n)]);
                        bounds.push(format!(
                            "{} <= {name} <= {}",
                            distances.iter().min().unwrap(),
                            distances.iter().max().unwrap()
                        ));
                        vars.push(name);
                        context.prefixes.insert(var, slice.length);
                        break 'bases;
                    }
                }
            }
        }
    }
    if regs.is_empty()
        && let Instr::Branch {
            op: BrOp::Bgeu | BrOp::Bltu,
            rs1: cursor,
            rs2: end,
            ..
        } = *instr
        && !merged.regs.contains_key(&cursor)
    {
        for slice in context.slices {
            let mut endpoint = Lin::var(slice.base);
            endpoint.add_term(slice.length, slice.stride).unwrap();
            if merged.regs.get(&end) == Some(&endpoint)
                && incoming
                    .iter()
                    .all(|s| s.regs.get(&cursor).is_some_and(|e| e.coef(slice.base) == 1))
            {
                let name = format!("tail{node}");
                let var = context.names.fresh(&name);
                endpoint.add_term(var, -1).unwrap();
                regs.insert(cursor, endpoint);
                bounds.push(format!(
                    "0 <= {name} <= {}{}",
                    slice.stride,
                    context.names.name(slice.length)
                ));
                vars.push(name);
                if slice.stride == 1 {
                    context.tails.insert(var, slice.length);
                }
                break;
            }
        }
    }
    (regs, vars, bounds)
}

pub fn annotate(
    func: &Func,
    initial: &State,
    names: &mut Names,
    slices: &[Slice],
) -> BTreeMap<usize, String> {
    let graph = Graph::new(func);
    let loops = graph.natural_loops();
    if loops.is_empty() {
        return BTreeMap::new();
    }
    let Some(schedule) = graph.order(&loops) else {
        return BTreeMap::new();
    };
    let writes: BTreeMap<_, BTreeSet<_>> = loops
        .iter()
        .map(|(&head, (_, body))| {
            let regs = body
                .iter()
                .filter_map(|&n| func.instrs[n].instr.rd())
                .collect();
            (head, regs)
        })
        .collect();
    let mut context = Context {
        names,
        slices,
        opaque: BTreeSet::new(),
        prefixes: BTreeMap::new(),
        tails: BTreeMap::new(),
    };
    let mut states = vec![State::default(); func.instrs.len()];
    let mut facts = vec![BTreeSet::new(); func.instrs.len()];
    let mut loop_vars = BTreeMap::new();
    let mut annotations = BTreeMap::new();
    for &node in &schedule.order {
        let ins = &func.instrs[node];
        let label = func.labels.values().any(|&i| i == node);
        let preds = &schedule.preds[node];
        let mut nonzero = BTreeSet::new();
        let mut state = if node == 0 {
            initial.clone()
        } else {
            let incoming: Vec<_> = preds.iter().map(|&p| &states[p]).collect();
            let mut merged = merge(incoming.iter().copied());
            merged.regs.retain(|_, e| {
                !e.vars().any(|v| {
                    loop_vars
                        .iter()
                        .any(|(h, w)| v == *w && !loops[h].1.contains(&node))
                })
            });
            for (count, &p) in preds.iter().enumerate() {
                let mut edge: BTreeSet<Var> = facts[p].clone();
                if let Instr::Branch {
                    op: op @ (BrOp::Beq | BrOp::Bne),
                    rs1,
                    rs2: ZERO,
                    target: Target::Local(t),
                } = func.instrs[p].instr
                    && t != p + 1
                    && (node == t) == (op == BrOp::Bne)
                    && let Some(v) = states[p].reg(rs1).and_then(|e| e.as_var())
                    && slices.iter().any(|s| s.length == v)
                {
                    edge.insert(v);
                }
                if count == 0 {
                    nonzero = edge;
                } else {
                    nonzero.retain(|v| edge.contains(v));
                }
            }
            if label && incoming.len() > 1 && !loops.contains_key(&node) {
                let (regs, vars, mut bounds) =
                    join_relations(node, &ins.instr, &incoming, &merged, &mut context);
                for &v in &nonzero {
                    bounds.insert(0, format!("1 <= {}", context.names.name(v)));
                }
                if !bounds.is_empty() {
                    let params = if vars.is_empty() {
                        String::new()
                    } else {
                        format!(" [{}]", vars.join(", "))
                    };
                    let types = registers(&regs, context.names);
                    let types = if types.is_empty() {
                        types
                    } else {
                        format!(" {types}")
                    };
                    annotations.insert(
                        ins.line,
                        format!("\t#: join{params}{types} where {}\n", bounds.join(", ")),
                    );
                    merged.regs.extend(regs);
                }
            }
            merged
        };
        if let Some((latches, body)) = loops.get(&node) {
            let name = if annotations.is_empty() {
                "remaining".into()
            } else {
                format!("remaining{}", annotations.len())
            };
            let remaining = context.names.fresh(&name);
            let mut iteration = BTreeMap::<usize, State>::new();
            for &i in schedule.order.iter().filter(|i| body.contains(i)) {
                let mut local = if i == node {
                    State {
                        regs: Reg::all()
                            .filter(|r| *r != ZERO)
                            .map(|r| (r, Lin::var(Var(u32::from(r.0)))))
                            .collect(),
                        words: BTreeMap::new(),
                    }
                } else {
                    merge(schedule.preds[i].iter().filter_map(|p| iteration.get(p)))
                };
                if i != node
                    && let Some(changed) = writes.get(&i)
                {
                    local.regs.retain(|r, _| !changed.contains(r));
                    local.words.clear();
                }
                // The remaining-count recurrence uses the pre-branch state.
                if !latches.contains(&i) {
                    local.step(&func.instrs[i].instr, Some(Var(u32::MAX - 1 - i as u32)));
                }
                iteration.insert(i, local);
            }
            let mut proposals = latches.iter().map(|&l| {
                candidate(
                    func,
                    body,
                    &func.instrs[l].instr,
                    &state,
                    &iteration[&l],
                    remaining,
                    &context,
                )
            });
            let result = proposals
                .next()
                .flatten()
                .filter(|first| proposals.all(|next| next.as_ref() == Some(first)));
            state.regs.retain(|r, _| !writes[&node].contains(r));
            state.words.clear();
            if label && let Some((regs, bounds)) = result {
                annotations.insert(
                    ins.line,
                    format!(
                        "\t#: inv [{name}] {} where {} decreases {name}\n",
                        registers(&regs, context.names),
                        bounds.join(", ")
                    ),
                );
                loop_vars.insert(node, remaining);
                state.regs.extend(regs);
            }
        }
        let opaque = matches!(
            ins.instr,
            Instr::IOp {
                op: IOp::Andi,
                imm: 1 | 3 | 7 | 15,
                ..
            }
        )
        .then(|| context.names.fresh(&format!("opaque{node}")));
        state.step(&ins.instr, opaque);
        if let Some(opaque) = opaque {
            context.opaque.insert(opaque);
        }
        facts[node] = nonzero;
        states[node] = state;
    }
    annotations
}

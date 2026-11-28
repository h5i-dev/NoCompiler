use crate::flow::{Graph, State, access, affine_join, analyze, low_bit_mask, merge};
use nocompiler_typed::{
    asm::Func,
    cfg::ControlFlow,
    isa::{BrOp, Instr, Reg, SP, Target, ZERO},
    lin::{Lin, Names, Var},
};
use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet},
};

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

// Project an affine predicate expressed over the synthetic header registers
// through an entry or latch state. The same transfer handles copies,
// multiple progressing operands and a predicate formed in a temporary.
fn substitute_registers(expr: &Lin, state: &State) -> Option<Lin> {
    let mut result = Lin::konst(expr.konst);
    for (&var, &coefficient) in &expr.terms {
        let reg = u8::try_from(var.0).ok().filter(|&id| id < 32)?;
        result = result.add(&state.reg(Reg(reg))?.scale(coefficient)?)?;
    }
    Some(result)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Guard {
    Nonzero,
    Ordered { strict: bool },
}

/// Normalize the predicate on the edge that continues iteration.
fn continuing_guard(instr: &Instr, node: usize, successor: usize) -> Option<(Guard, Reg, Reg)> {
    let Instr::Branch {
        op,
        rs1,
        rs2,
        target: Target::Local(target),
    } = *instr
    else {
        return None;
    };
    if target == node + 1 {
        return None;
    }
    let taken = target == successor;
    match (op, taken) {
        (BrOp::Bne, true) | (BrOp::Beq, false) => Some((Guard::Nonzero, rs1, rs2)),
        (BrOp::Bltu, true) | (BrOp::Bgeu, false) => {
            Some((Guard::Ordered { strict: true }, rs1, rs2))
        }
        (BrOp::Bgeu, true) | (BrOp::Bltu, false) => {
            Some((Guard::Ordered { strict: false }, rs2, rs1))
        }
        _ => None,
    }
}

/// Locate branches whose selected edge is necessary to reach this latch
/// without crossing the loop header again. A latch need not be conditional.
fn guards_for_latch(
    func: &Func,
    cfg: &ControlFlow,
    body: &BTreeSet<usize>,
    header: usize,
    latch: usize,
) -> Vec<(usize, (Guard, Reg, Reg))> {
    let mut guards = Vec::new();
    if let Some(guard) = continuing_guard(&func.instrs[latch].instr, latch, header) {
        guards.push((latch, guard));
    }
    let reaches = |start, omit| {
        let mut seen = BTreeSet::new();
        let mut pending = vec![start];
        while let Some(node) = pending.pop() {
            if Some(node) == omit || !body.contains(&node) || !seen.insert(node) {
                continue;
            }
            if node == latch {
                return true;
            }
            pending.extend(
                cfg.successors[node]
                    .iter()
                    .copied()
                    .filter(|&next| next != header),
            );
        }
        false
    };
    for &node in body {
        if node == latch {
            continue;
        }
        let [left, right] = cfg.successors[node].as_slice() else {
            continue;
        };
        if reaches(header, Some(node)) {
            continue;
        }
        let selected = match (reaches(*left, Some(header)), reaches(*right, Some(header))) {
            (true, false) => *left,
            (false, true) => *right,
            _ => continue,
        };
        if let Some(guard) = continuing_guard(&func.instrs[node].instr, node, selected) {
            guards.push((node, guard));
        }
    }
    guards
}

struct Iteration<'a> {
    predicate: &'a State,
    latch: &'a State,
    predicate_at_latch: bool,
    shared_ordered_measure: bool,
}

fn candidate(
    func: &Func,
    body: &BTreeSet<usize>,
    (guard, left, right): (Guard, Reg, Reg),
    entry: &State,
    iteration: Iteration<'_>,
    remaining: Var,
    context: &Context<'_>,
) -> Option<Candidate> {
    if iteration.shared_ordered_measure
        && (!iteration.predicate_at_latch || !matches!(guard, Guard::Ordered { .. }))
    {
        return None;
    }
    let predicate = iteration.predicate;
    let post = iteration.latch;
    let fixed = || {
        let observed = predicate.reg(left)?.sub(&predicate.reg(right)?)?;
        let initial = substitute_registers(&observed, entry)?;
        let next = substitute_registers(&observed, post)?;
        let delta = next.sub(&observed)?.as_const()?;
        let mut distance = initial.add_const(delta.checked_neg()?)?;
        let mut scale = delta.checked_neg()?;
        if scale == 0 {
            return None;
        }
        let mut lower = 1;
        let mut unit = 1;
        if let Guard::Ordered { strict } = guard {
            let progress = delta;
            if progress <= 0 {
                return None;
            }
            unit = progress;
            if iteration.shared_ordered_measure {
                // The header measure is the distance to the comparison
                // endpoint, independent of this latch's step size.
                distance = distance.add_const(-i128::from(!strict))?;
            } else {
                lower = progress.checked_add(i128::from(strict))?;
                distance = distance.add_const(scale)?;
            }
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
            .or_else(|| trip.as_var().and_then(|v| context.tails.get(&v).copied()));
        let upper = if let Some(length) = length {
            context.names.name(length).to_owned()
        } else if let Some(count) = trip.as_const().filter(|&count| count >= lower) {
            count.to_string()
        } else {
            if trip.vars().any(|v| context.hidden(v)) {
                return None;
            }
            trip.display(context.names).to_string()
        };
        let mut bounds = vec![format!(
            "{lower} <= {} <= {}",
            context.names.name(remaining),
            upper
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
            if step == 0 || step % unit != 0 {
                continue;
            }
            let value = start.add(&shift.scale(step / unit)?)?;
            if value.vars().any(|v| context.hidden(v)) {
                continue;
            }
            if matches!(guard, Guard::Ordered { .. }) {
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
        if guard != Guard::Nonzero || !iteration.predicate_at_latch {
            return None;
        }
        let observed = predicate.reg(left)?.sub(&predicate.reg(right)?)?;
        let reversed = observed.scale(-1)?;
        // A symbolic step can still preserve an affine relation when all
        // carried registers move by a constant multiple of the same change.
        let (ranking, upper) = entry.regs.iter().find_map(|(&reg, upper)| {
            let updated = post.reg(reg)?;
            (reg != SP
                && !upper.vars().any(|v| context.hidden(v))
                && (updated == observed || updated == reversed))
                .then_some((reg, upper))
        })?;
        let delta = difference(&post.reg(ranking)?, ranking)?;
        let (&term, &scale) = delta.terms.first_key_value()?;
        let shift = Lin::var(remaining).sub(upper)?;
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
        regs.contains_key(&ranking).then(|| {
            (
                regs,
                vec![format!(
                    "1 <= {} <= {}",
                    context.names.name(remaining),
                    upper.display(context.names)
                )],
            )
        })
    })
}

/// Recover the next measure from the actual latch transition under the
/// candidate's register equations. Unconstrained registers stay symbolic.
fn decreases_on_latch(regs: &Registers, latch: &State, remaining: Var) -> bool {
    let evaluate = || {
        let inputs: BTreeMap<_, _> = Reg::all()
            .map(|reg| {
                let id = u32::from(reg.0);
                let value = regs
                    .get(&reg)
                    .cloned()
                    .unwrap_or_else(|| Lin::var(Var(u32::MAX / 2 + id)));
                (Var(id), value)
            })
            .collect();
        let transitioned = |reg| latch.reg(reg)?.subst_all(&inputs);
        let (&anchor, expression) = regs.iter().find(|(_, expr)| expr.coef(remaining) != 0)?;
        let coefficient = expression.coef(remaining);
        let residual = transitioned(anchor)?.sub(&expression.subst(remaining, &Lin::default())?)?;
        let divide = |value: i128| {
            (value.checked_rem(coefficient)? == 0).then_some(value.checked_div(coefficient)?)
        };
        let next = Lin {
            konst: divide(residual.konst)?,
            terms: residual
                .terms
                .iter()
                .map(|(&var, &value)| Some((var, divide(value)?)))
                .collect::<Option<_>>()?,
        };
        let progress = Lin::var(remaining).sub(&next)?.as_const()?;
        Some(
            progress > 0
                && regs.iter().all(|(&reg, expr)| {
                    transitioned(reg)
                        .zip(expr.subst(remaining, &next))
                        .is_some_and(|(actual, expected)| actual == expected)
                }),
        )
    };
    evaluate().unwrap_or(false)
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

/// Track which incoming registers can flow into a memory address. Transfer
/// uses the same affine instruction semantics as the forward analysis.
fn address_dependencies(func: &Func, cfg: &ControlFlow) -> Vec<BTreeSet<Reg>> {
    let inputs: Registers = Reg::all()
        .filter(|&r| r != ZERO)
        .map(|r| (r, Lin::var(Var(u32::from(r.0)))))
        .collect();
    let transfers: Vec<_> = func
        .instrs
        .iter()
        .map(|point| {
            let mut state = State {
                regs: inputs.clone(),
                words: BTreeMap::new(),
            };
            state.step(&point.instr, None);
            state
        })
        .collect();
    let mut dependencies = vec![BTreeSet::new(); func.instrs.len()];
    let mut pending: BTreeSet<_> = cfg.reverse_postorder.iter().copied().collect();
    while let Some(node) = pending.pop_last() {
        let mut used = BTreeSet::new();
        if let Some((base, ..)) = access(&func.instrs[node].instr) {
            used.insert(base);
        }
        for &next in &cfg.successors[node] {
            for &reg in &dependencies[next] {
                if let Some(expression) = transfers[node].reg(reg) {
                    used.extend(expression.vars().map(|v| Reg(v.0 as u8)));
                }
            }
        }
        if used != dependencies[node] {
            dependencies[node] = used;
            pending.extend(cfg.predecessors[node].iter().copied());
        }
    }
    dependencies
}

fn join_relations(
    node: usize,
    instr: &Instr,
    address_inputs: &BTreeSet<Reg>,
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
    for &anchor in &keys {
        if !address_inputs.contains(&anchor) || regs.contains_key(&anchor) {
            continue;
        }
        let related_registers = keys
            .iter()
            .copied()
            .filter(|&reg| reg != anchor)
            .chain(std::iter::once(anchor));
        for related in related_registers {
            if regs.contains_key(&related) {
                continue;
            }
            let Some(join) = affine_join(incoming, anchor, related) else {
                continue;
            };
            let [mut a, mut b] = join.bases;
            if a.vars().chain(b.vars()).any(|v| context.hidden(v)) {
                continue;
            }
            let name = format!("offset{node}_{}", vars.len());
            let var = context.names.fresh(&name);
            if a.add_term(var, join.steps[0]).is_none() || b.add_term(var, join.steps[1]).is_none()
            {
                continue;
            }
            regs.insert(anchor, a);
            if related != anchor {
                regs.insert(related, b);
            }
            bounds.push(format!("{} <= {name} <= {}", join.min, join.max));
            vars.push(name);
            break;
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
    let cfg = ControlFlow::new(func);
    let loops = graph.natural_loops();
    let has_join = func.labels.values().any(|&node| {
        cfg.predecessors
            .get(node)
            .is_some_and(|edges| edges.len() > 1)
    });
    if loops.is_empty() && !has_join {
        return BTreeMap::new();
    }
    let Some(schedule) = graph.order(&loops) else {
        return BTreeMap::new();
    };
    let fixed = if loops.is_empty() {
        Vec::new()
    } else {
        analyze(func, initial.clone())
    };
    let address_inputs = address_dependencies(func, &cfg);
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
            let refined: Vec<_> = preds
                .iter()
                .map(|&p| {
                    let mut edge = Cow::Borrowed(&states[p]);
                    if let Some((reg, value)) = edge.edge_constant(&func.instrs[p].instr, p, node) {
                        edge.to_mut().regs.insert(reg, value);
                    }
                    edge
                })
                .collect();
            let incoming: Vec<_> = refined.iter().map(Cow::as_ref).collect();
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
                let (regs, vars, mut bounds) = join_relations(
                    node,
                    &ins.instr,
                    &address_inputs[node],
                    &incoming,
                    &merged,
                    &mut context,
                );
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
            let name = context.names.name(remaining).to_owned();
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
            let proposals: Vec<_> = latches
                .iter()
                .map(|&latch| {
                    guards_for_latch(func, &cfg, body, node, latch)
                        .into_iter()
                        .flat_map(|(test, guard)| {
                            [false, true]
                                .into_iter()
                                .map(move |shared_ordered_measure| {
                                    (test, guard, shared_ordered_measure)
                                })
                        })
                        .filter_map(|(test, guard, shared_ordered_measure)| {
                            candidate(
                                func,
                                body,
                                guard,
                                &state,
                                Iteration {
                                    predicate: iteration.get(&test)?,
                                    latch: iteration.get(&latch)?,
                                    predicate_at_latch: test == latch,
                                    shared_ordered_measure,
                                },
                                remaining,
                                &context,
                            )
                        })
                        .collect::<Vec<_>>()
                })
                .collect();
            let result = proposals.into_iter().flatten().find(|(regs, _)| {
                latches.len() == 1
                    || latches.iter().all(|latch| {
                        iteration
                            .get(latch)
                            .is_some_and(|state| decreases_on_latch(regs, state, remaining))
                    })
            });
            state.regs.retain(|r, expr| {
                fixed[node]
                    .as_ref()
                    .is_some_and(|header| header.regs.get(r) == Some(expr))
            });
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
        let opaque =
            low_bit_mask(&ins.instr).then(|| context.names.fresh(&format!("opaque{node}")));
        state.step(&ins.instr, opaque);
        if let Some(opaque) = opaque {
            context.opaque.insert(opaque);
        }
        facts[node] = nonzero;
        states[node] = state;
    }
    annotations
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn guarded_unconditional_latch_generates_checked_ranking() {
        let source = r#"#: fn countdown [n] in a0: u64(n) out a0: int
.type countdown, @function
countdown:
    beq a0, zero, .Ldone
.Lloop:
    addi a0, a0, -1
    beq a0, zero, .Ldone
    j .Lloop
.Ldone:
    ret
.size countdown, .-countdown
"#;
        let parsed = nocompiler_typed::asm::parse(source).unwrap();
        let mut names = Names::default();
        let n = names.fresh("n");
        let mut initial = crate::flow::entry();
        initial.regs.insert(Reg(10), Lin::var(n));
        let annotations = annotate(&parsed.funcs[0], &initial, &mut names, &[]);
        assert!(
            annotations
                .values()
                .any(|line| line.contains("decreases remaining"))
        );
        let generated = source
            .lines()
            .enumerate()
            .map(|(line, text)| {
                let annotation = annotations
                    .get(&(line + 1))
                    .map(String::as_str)
                    .unwrap_or("");
                format!("{annotation}{text}\n")
            })
            .collect::<String>();
        let instrumented = nocompiler_typed::asm::parse(&generated).unwrap();
        let (_, report) = nocompiler_typed::check::check_program(&instrumented, false);
        assert!(report.ok(), "{report:?}");
    }

    #[test]
    fn shared_ranking_for_back_edges_with_different_steps() {
        let source = r#"#: fn scan [n] in a0: u64(n) where n <= 1000 out a0: int
.type scan, @function
scan:
    li a1, 0
    li a3, 0
    beq a0, zero, .Ldone
.Lloop:
    beq a2, zero, .Lslow
    addi a1, a1, 2
    addi a3, a3, 2
    bltu a1, a0, .Lloop
    j .Ldone
.Lslow:
    addi a1, a1, 1
    bltu a1, a0, .Lloop
.Ldone:
    ret
.size scan, .-scan
"#;
        let parsed = nocompiler_typed::asm::parse(source).unwrap();
        let mut names = Names::default();
        let n = names.fresh("n");
        let mut initial = crate::flow::entry();
        initial.regs.insert(Reg(10), Lin::var(n));
        let annotations = annotate(&parsed.funcs[0], &initial, &mut names, &[]);
        assert!(
            annotations
                .values()
                .any(|line| line.contains("decreases remaining") && !line.contains("a3:"))
        );
        let generated = source
            .lines()
            .enumerate()
            .map(|(line, text)| {
                let annotation = annotations
                    .get(&(line + 1))
                    .map(String::as_str)
                    .unwrap_or("");
                format!("{annotation}{text}\n")
            })
            .collect::<String>();
        let instrumented = nocompiler_typed::asm::parse(&generated).unwrap();
        let (_, report) = nocompiler_typed::check::check_program(&instrumented, false);
        assert!(report.ok(), "{report:?}");
    }

    #[test]
    fn acyclic_join_tracks_address_through_copy() {
        let source = r#"#: fn read [p] in a0: int(p) borrow p |-> bytes[16] ro where 8 | p out a0: int
.type read, @function
read:
    beq a1, zero, .Lsecond
    j .Ljoin
.Lsecond:
    addi a0, a0, 8
.Ljoin:
    mv a3, a0
    ld a0, 0(a3)
    ret
.size read, .-read
"#;
        let parsed = nocompiler_typed::asm::parse(source).unwrap();
        let mut names = Names::default();
        let p = names.fresh("p");
        let mut initial = crate::flow::entry();
        initial.regs.insert(Reg(10), Lin::var(p));
        let annotations = annotate(&parsed.funcs[0], &initial, &mut names, &[]);
        let copy_line = source
            .lines()
            .position(|line| line.contains("mv a3, a0"))
            .unwrap()
            + 1;
        assert!(annotations[&copy_line].contains("#: join"));
        let generated = source
            .lines()
            .enumerate()
            .map(|(line, text)| {
                let annotation = annotations
                    .get(&(line + 1))
                    .map(String::as_str)
                    .unwrap_or("");
                format!("{annotation}{text}\n")
            })
            .collect::<String>();
        let instrumented = nocompiler_typed::asm::parse(&generated).unwrap();
        let (_, report) = nocompiler_typed::check::check_program(&instrumented, false);
        assert!(report.ok(), "{report:?}");
    }
}

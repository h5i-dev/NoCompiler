//! Optional candidates from the pinned LLVM toolchain.
use crate::{
    Result,
    build::output,
    contract_ir::{Expr, Input},
    llvm_ir::{self, Function, Instruction, Operand, Type},
};
use nocompiler_typed::{asm::Func, isa::Reg, lin::Lin};
use serde::Deserialize;
use serde_json::{Value as Json, json};
use serde_yaml_ng::Value;
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
    process::Command,
};

#[derive(Clone, Copy)]
pub struct WordRange {
    pub lower: u64,
    pub upper: u64,
}

#[derive(Clone, Copy)]
pub struct LoopTrip {
    pub iterations: Option<i128>,
    pub count_arg: Option<Reg>,
    pub left: Reg,
    pub right: Reg,
}

pub struct Frame {
    pub size: i128,
    pub slots: BTreeSet<(i128, i128)>,
}

#[derive(Default)]
pub struct Hints {
    pub ranges: BTreeMap<String, WordRange>,
    pub affine_results: BTreeMap<String, Expr>,
    pub affine_values: BTreeMap<String, BTreeMap<String, Expr>>,
    pub trips: BTreeMap<String, Vec<LoopTrip>>,
    pub frames: BTreeMap<String, Frame>,
}

pub fn capture(sysroot: &Path, bin: &Path, ir: &Path, dir: &Path) -> Result<Hints> {
    let machine = dir.join("llvm-machine.mir");
    output(
        Command::new(bin.join("llc"))
            .args(["-O3", "-stop-after=prolog-epilog", "-o"])
            .arg(&machine)
            .arg(ir),
    )?;
    let machine = machine_functions(&fs::read_to_string(machine)?)?;
    let evolution = Command::new(bin.join("opt"))
        .args(["-passes=print<scalar-evolution>", "-disable-output"])
        .arg(ir)
        .output()?;
    if !evolution.status.success() {
        return Err(format!(
            "LLVM ScalarEvolution failed: {}",
            String::from_utf8_lossy(&evolution.stderr)
        )
        .into());
    }
    fs::write(dir.join("llvm-scev.txt"), &evolution.stderr)?;
    let ir = fs::read_to_string(ir)?;
    let scalar_returns = scalar_return_registers(&machine);
    let functions = llvm_ir::capture(sysroot, &ir)?;
    let mut affine_results = BTreeMap::new();
    let mut affine_values = BTreeMap::new();
    for (name, function) in &functions {
        if let Some((result, values)) = affine_analysis(function) {
            if scalar_returns.contains(name.as_str())
                && let Some(result) = result
            {
                affine_results.insert(name.clone(), result);
            }
            let matched: BTreeMap<_, _> = values
                .into_iter()
                .filter_map(|(id, expr)| Some((function.value_names.get(&id)?.clone(), expr)))
                .collect();
            if !matched.is_empty() {
                affine_values.insert(name.clone(), matched);
            }
        }
    }
    Ok(Hints {
        ranges: ranges(&ir, &scalar_returns),
        affine_results,
        affine_values,
        trips: loop_trips(&String::from_utf8(evolution.stderr)?, &machine, &functions),
        frames: frames(&machine),
    })
}

struct MachineFunction {
    name: String,
    body: String,
    stack_size: Option<i128>,
    stack_objects: Vec<(i128, i128)>,
}

fn machine_functions(document: &str) -> Result<Vec<MachineFunction>> {
    let mut functions = Vec::new();
    for item in serde_yaml_ng::Deserializer::from_str(document) {
        let document = Value::deserialize(item)?;
        let Some(name) = document.get("name").and_then(Value::as_str) else {
            // The initial YAML document contains the embedded LLVM module.
            continue;
        };
        let Some(body) = document.get("body").and_then(Value::as_str) else {
            continue;
        };
        let stack_size = document
            .get("frameInfo")
            .and_then(|frame| frame.get("stackSize"))
            .and_then(Value::as_i64)
            .map(i128::from);
        let stack_objects = document
            .get("stack")
            .and_then(Value::as_sequence)
            .into_iter()
            .flatten()
            .filter_map(|object| {
                Some((
                    i128::from(object.get("offset")?.as_i64()?),
                    i128::from(object.get("size")?.as_i64()?),
                ))
            })
            .collect();
        functions.push(MachineFunction {
            name: name.to_owned(),
            body: body.to_owned(),
            stack_size,
            stack_objects,
        });
    }
    Ok(functions)
}

fn frames(machine: &[MachineFunction]) -> BTreeMap<String, Frame> {
    machine
        .iter()
        .filter_map(|function| {
            let size = function.stack_size?;
            if size <= 0 || size % 16 != 0 {
                return None;
            }
            let slots: BTreeSet<_> = function
                .stack_objects
                .iter()
                .filter_map(|&(offset, length)| {
                    let start = size.checked_add(offset)?;
                    let end = start.checked_add(length)?;
                    (start >= 0 && start < end && end <= size).then_some((start, end))
                })
                .collect();
            (!slots.is_empty()).then_some((function.name.clone(), Frame { size, slots }))
        })
        .collect()
}

fn number(text: &str) -> Option<usize> {
    text.split(|c: char| !c.is_ascii_digit())
        .next()?
        .parse()
        .ok()
}

// Only signatures whose lowered arguments each occupy one integer register.
fn count_register(ir: &BTreeMap<String, Function>, symbol: &str, variable: &str) -> Option<Reg> {
    let parameters = &ir.get(symbol)?.parameters;
    if parameters
        .iter()
        .any(|p| !matches!(p.ty, Type::Word | Type::Pointer))
    {
        return None;
    }
    let name = variable.strip_prefix('%')?;
    let index = parameters
        .iter()
        .position(|p| p.name == name && p.ty == Type::Word)?;
    Some(Reg(10 + u8::try_from(index).ok()?))
}

fn latch_registers(body: &[&str], head: usize) -> Option<(Reg, Reg)> {
    let mut fallthrough = None;
    let mut jump = None;
    for line in body {
        if let Some(target) = line.strip_prefix("PseudoBR %bb.") {
            jump = number(target);
        }
        if let Some((op @ ("BNE" | "BEQ"), branch)) = line.split_once(' ') {
            let mut operands = branch.split(',');
            let reg = |operand: &str| {
                let (_, reg) = operand.split_once("$x")?;
                let reg = number(reg)?;
                (reg < 32).then_some(Reg(reg as u8))
            };
            let left = reg(operands.next()?)?;
            let right = reg(operands.next()?)?;
            let target = number(operands.next()?.trim().strip_prefix("%bb.")?)?;
            if op == "BNE" && target == head {
                return Some((left, right));
            }
            if op == "BEQ" && target != head {
                fallthrough = Some((left, right));
            }
        }
    }
    (jump == Some(head)).then_some(fallthrough).flatten()
}

fn loop_trips(
    evolution: &str,
    machine: &[MachineFunction],
    ir: &BTreeMap<String, Function>,
) -> BTreeMap<String, Vec<LoopTrip>> {
    let counts: BTreeMap<_, _> = evolution
        .split("Classifying expressions for: @")
        .skip(1)
        .filter_map(|record| {
            let (name, body) = record.split_once('\n')?;
            let name = name.trim();
            let counts: BTreeMap<_, _> = body
                .lines()
                .filter_map(|line| {
                    let (head, count) = line
                        .strip_prefix("Loop %")?
                        .split_once(": backedge-taken count is ")?;
                    let count = count.trim();
                    let iterations =
                        match count.strip_prefix("i64 ").unwrap_or(count).parse::<i128>() {
                            Ok(value) => Some(value.checked_add(1)?),
                            Err(_) if count.contains('%') && !count.contains("CouldNotCompute") => {
                                None
                            }
                            Err(_) => return None,
                        };
                    if iterations.is_some_and(|n| n <= 0) {
                        return None;
                    }
                    let count_arg = count
                        .strip_prefix("(-1 + ")
                        .and_then(|rest| {
                            let (variable, _) = rest.split_once(')')?;
                            variable.starts_with('%').then_some(variable)
                        })
                        .and_then(|variable| count_register(ir, name, variable));
                    Some((head, (iterations, count_arg)))
                })
                .collect();
            (!counts.is_empty()).then_some((name, counts))
        })
        .collect();

    machine
        .iter()
        .filter_map(|function| {
            let name = function.name.as_str();
            let body = &function.body;
            let counts = counts.get(name)?;
            let mut block = None;
            let mut edges = Vec::new();
            let mut blocks = BTreeMap::<usize, Vec<&str>>::new();
            let mut labels = BTreeMap::new();
            for line in body.lines().map(str::trim) {
                if let Some(id) = line.strip_prefix("bb.") {
                    block = number(id);
                    if let Some(block) = block
                        && let Some((_, label)) = id.split_once('.')
                    {
                        labels.insert(block, label.trim_end_matches(':'));
                    }
                } else if let Some(from) = block {
                    blocks.entry(from).or_default().push(line);
                    if let Some(successors) = line.strip_prefix("successors:") {
                        edges.extend(successors.split(',').filter_map(|edge| {
                            let (_, target) = edge.split_once("%bb.")?;
                            Some((from, number(target)?))
                        }));
                    }
                }
            }
            let entry = *blocks.keys().next()?;
            let reachable = |target, omit| {
                let mut todo = vec![entry];
                let mut seen = BTreeSet::new();
                while let Some(next) = todo.pop() {
                    if Some(next) == omit || !seen.insert(next) {
                        continue;
                    }
                    if next == target {
                        return true;
                    }
                    todo.extend(edges.iter().filter_map(|&(a, b)| (a == next).then_some(b)));
                }
                false
            };
            let backedges: Vec<_> = edges
                .iter()
                .copied()
                .filter(|&(from, to)| reachable(from, None) && !reachable(from, Some(to)))
                .collect();
            let trips: Vec<_> = backedges
                .iter()
                .filter_map(|&(latch, head)| {
                    let (iterations, count_arg) = *labels
                        .get(&head)
                        .and_then(|label| counts.get(label))
                        .or_else(|| {
                            (backedges.len() == 1 && counts.len() == 1)
                                .then(|| counts.values().next())
                                .flatten()
                        })?;
                    let (left, right) = latch_registers(blocks.get(&latch)?, head)?;
                    Some(LoopTrip {
                        iterations,
                        count_arg,
                        left,
                        right,
                    })
                })
                .collect();
            (!trips.is_empty()).then_some((name.to_owned(), trips))
        })
        .collect()
}

fn scalar_return_registers(machine: &[MachineFunction]) -> BTreeSet<&str> {
    let mut returns = BTreeSet::new();
    for function in machine {
        let mut sites = function
            .body
            .lines()
            .filter(|line| line.split_whitespace().next() == Some("PseudoRET"))
            .peekable();
        if sites.peek().is_some()
            && sites.all(|site| {
                site.split_once("implicit ").is_some_and(|(_, reg)| {
                    reg.split(',').next().is_some_and(|r| r.trim() == "$x10")
                })
            })
        {
            returns.insert(function.name.as_str());
        }
    }
    returns
}

fn affine_analysis(function: &Function) -> Option<(Option<Expr>, BTreeMap<usize, Expr>)> {
    let size = function.blocks.len();
    let mut dependencies = vec![BTreeSet::new(); size];
    let block_index: BTreeMap<_, _> = function
        .blocks
        .iter()
        .enumerate()
        .map(|(ix, block)| (block.id, ix))
        .collect();
    for (index, block) in function.blocks.iter().enumerate() {
        for to in &block.successors {
            dependencies[*block_index.get(to)?].insert(index);
        }
    }
    let mut remaining: Vec<_> = dependencies.iter().map(BTreeSet::len).collect();
    let mut pending: BTreeSet<_> = (0..size).filter(|&index| remaining[index] == 0).collect();
    let mut returned = None;
    let mut common_return = true;
    let mut values: BTreeMap<_, _> = function
        .parameters
        .iter()
        .enumerate()
        .filter(|(_, parameter)| matches!(parameter.ty, Type::Word | Type::Pointer))
        .map(|(index, parameter)| (parameter.id, Expr::input(Input::Value(index))))
        .collect();
    let mut slots = BTreeSet::new();
    let mut exits = vec![BTreeMap::new(); size];
    while let Some(index) = pending.pop_first() {
        let mut incoming = dependencies[index].iter().map(|&index| &exits[index]);
        let mut stored = incoming.next().cloned().unwrap_or_default();
        for other in incoming {
            stored.retain(|slot, value| other.get(slot) == Some(value));
        }
        let block = &function.blocks[index];
        for instruction in &block.instructions {
            let resolve = |operand| match operand {
                Operand::Constant(value) => Some(Expr::constant(value)),
                Operand::Value(id) => values.get(&id).cloned(),
            };
            let binary = |a, b| resolve(a).zip(resolve(b));
            let output = match *instruction {
                Instruction::Return(value) => {
                    if let Some(value) = resolve(value) {
                        common_return &= returned.as_ref().is_none_or(|prior| prior == &value);
                        returned = Some(value);
                    } else {
                        common_return = false;
                    }
                    None
                }
                Instruction::Alloca(slot) => {
                    slots.insert(slot);
                    None
                }
                Instruction::Store(value, slot) => {
                    if slots.contains(&slot) {
                        if let Some(value) = resolve(value) {
                            stored.insert(slot, value);
                        } else {
                            stored.remove(&slot);
                        }
                    } else {
                        stored.clear();
                    }
                    None
                }
                Instruction::Clobber => {
                    stored.clear();
                    None
                }
                Instruction::Load(id, slot) => Some((id, stored.get(&slot).cloned())),
                Instruction::Phi(id, ref args) => {
                    let mut incoming = args.iter().copied().map(resolve);
                    Some((
                        id,
                        incoming
                            .next()
                            .flatten()
                            .filter(|first| incoming.all(|value| value.as_ref() == Some(first))),
                    ))
                }
                Instruction::Add(id, a, b) => {
                    Some((id, binary(a, b).and_then(|(a, b)| a.add(&b, 1))))
                }
                Instruction::Sub(id, a, b) => {
                    Some((id, binary(a, b).and_then(|(a, b)| a.add(&b, -1))))
                }
                Instruction::Mul(id, a, b) => Some((
                    id,
                    binary(a, b).and_then(|(a, b)| {
                        if a.terms.is_empty() {
                            b.scale(a.constant)
                        } else if b.terms.is_empty() {
                            a.scale(b.constant)
                        } else {
                            None
                        }
                    }),
                )),
                Instruction::Shift(id, a, b) => Some((
                    id,
                    binary(a, b).and_then(|(a, b)| {
                        if b.terms.is_empty() && (0..64).contains(&b.constant) {
                            a.scale(1i128 << b.constant)
                        } else {
                            None
                        }
                    }),
                )),
            };
            if let Some((id, Some(value))) = output {
                values.insert(id, value);
            }
        }
        exits[index] = stored;
        for to in block.successors.iter().collect::<BTreeSet<_>>() {
            let next = *block_index.get(to)?;
            remaining[next] -= 1;
            if remaining[next] == 0 {
                pending.insert(next);
            }
        }
    }
    let complete = remaining.iter().all(|&count| count == 0);
    let scalar_return =
        function.result == Type::Word && function.parameters.iter().all(|p| p.ty == Type::Word);
    Some((
        returned.filter(|_| complete && common_return && scalar_return),
        values,
    ))
}

/// Match definitions by the affine expression computed in both IRs. Results
/// are candidates and identify every matching live location before each point.
pub fn affine_locations(
    func: &Func,
    entry: &crate::flow::State,
    values: &BTreeMap<String, Expr>,
) -> Vec<Json> {
    let mut by_expression = BTreeMap::<Lin, Vec<&str>>::new();
    for (name, expr) in values {
        let lowered =
            expr.terms
                .iter()
                .try_fold(Lin::konst(expr.constant), |sum, (&input, &coef)| {
                    let Input::Value(index) = input else {
                        return None;
                    };
                    sum.add(
                        &entry
                            .reg(Reg(10 + u8::try_from(index).ok()?))?
                            .scale(coef)?,
                    )
                });
        if let Some(lowered) = lowered {
            by_expression.entry(lowered).or_default().push(name);
        }
    }
    let mut result = Vec::new();
    for (index, state) in crate::flow::analyze(func, entry.clone())
        .into_iter()
        .enumerate()
    {
        let Some(state) = state else { continue };
        for (reg, expr) in &state.regs {
            if let Some(values) = by_expression.get(expr) {
                result
                    .push(json!({"instruction": index, "register": reg.name(), "values": values}));
            }
        }
        for (&(base, offset), expr) in &state.words {
            if base == crate::flow::ENTRY_SP
                && let Some(values) = by_expression.get(expr)
                && let Ok(offset) = i64::try_from(offset)
            {
                result.push(
                    json!({"instruction": index, "entry_sp_offset": offset, "values": values}),
                );
            }
        }
    }
    result
}

fn ranges(ir: &str, returns: &BTreeSet<&str>) -> BTreeMap<String, WordRange> {
    ir.lines()
        .filter_map(|line| {
            let signature = line.strip_prefix("define ")?;
            let (result, function) = signature.split_once('@')?;
            let (name, _) = function.split_once('(')?;
            let name = name.trim_matches('"');
            if !returns.contains(name) {
                return None;
            }
            let (_, range) = result.split_once("range(i64 ")?;
            let (bounds, _) = range.split_once(')')?;
            let (lower, upper) = bounds.split_once(',')?;
            let lower = lower.trim().parse().ok()?;
            let upper = upper.trim().parse().ok()?;
            (lower < upper).then_some((name.to_owned(), WordRange { lower, upper }))
        })
        .collect()
}

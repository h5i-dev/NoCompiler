//! Optional candidates from the pinned LLVM toolchain.
use crate::{
    Result,
    build::output,
    contract_ir::{Expr, Input},
};
use nocompiler_typed::isa::Reg;
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
    pub trips: BTreeMap<String, Vec<LoopTrip>>,
    pub frames: BTreeMap<String, Frame>,
}

pub fn capture(bin: &Path, ir: &Path, dir: &Path) -> Result<Hints> {
    let machine = dir.join("llvm-machine.mir");
    output(
        Command::new(bin.join("llc"))
            .args(["-O3", "-stop-after=prolog-epilog", "-o"])
            .arg(&machine)
            .arg(ir),
    )?;
    let machine = fs::read_to_string(machine)?;
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
    Ok(Hints {
        ranges: ranges(&ir, &scalar_returns),
        affine_results: affine_results(&ir, &scalar_returns),
        trips: loop_trips(&String::from_utf8(evolution.stderr)?, &machine, &ir),
        frames: frames(&machine),
    })
}

fn machine_functions(machine: &str) -> impl Iterator<Item = (&str, &str, &str)> {
    machine.split("\n---\n").filter_map(|record| {
        let (header, body) = record.split_once("\nbody:")?;
        let name = header.lines().find_map(|line| line.strip_prefix("name:"))?;
        Some((name.trim().trim_matches('\''), header, body))
    })
}

fn frames(machine: &str) -> BTreeMap<String, Frame> {
    machine_functions(machine)
        .filter_map(|(name, header, _)| {
            let size = header
                .lines()
                .find_map(|line| line.trim().strip_prefix("stackSize:"))?
                .trim()
                .parse::<i128>()
                .ok()?;
            if size <= 0 || size % 16 != 0 {
                return None;
            }
            let (_, objects) = header.split_once("\nstack:\n")?;
            let slots: BTreeSet<_> = objects
                .lines()
                .take_while(|line| line.starts_with(' '))
                .filter_map(|line| {
                    let object = line.trim().strip_prefix("- { id:")?;
                    let property = |name| {
                        object
                            .split_once(name)?
                            .1
                            .split(',')
                            .next()?
                            .trim()
                            .parse::<i128>()
                            .ok()
                    };
                    let offset = property(", offset:")?;
                    let length = property(", size:")?;
                    let start = size.checked_add(offset)?;
                    let end = start.checked_add(length)?;
                    (start >= 0 && start < end && end <= size).then_some((start, end))
                })
                .collect();
            (!slots.is_empty()).then_some((name.to_string(), Frame { size, slots }))
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
fn count_register(ir: &str, symbol: &str, variable: &str) -> Option<Reg> {
    let (_, args) = ir.lines().find_map(|line| {
        let (head, function) = line.strip_prefix("define ")?.split_once('@')?;
        let (name, args) = function.split_once('(')?;
        (name == symbol && !head.contains("cc ")).then_some((name, args))
    })?;
    let mut found = None;
    let args = llvm_arguments(args)?;
    for (index, arg) in args.enumerate() {
        let mut words = arg.split_whitespace();
        let ty = words.next()?;
        if !matches!(ty, "ptr" | "i64") || index >= 8 {
            return None;
        }
        if words.last()? == variable && ty == "i64" {
            found = Some(Reg(10 + index as u8));
        }
    }
    found
}

fn llvm_arguments(args: &str) -> Option<impl Iterator<Item = &str>> {
    let mut depth = 0;
    let end = args.char_indices().find_map(|(index, c)| match c {
        '(' => {
            depth += 1;
            None
        }
        ')' if depth != 0 => {
            depth -= 1;
            None
        }
        ')' => Some(index),
        _ => None,
    })?;
    Some(args[..end].split(move |c| match c {
        '(' => {
            depth += 1;
            false
        }
        ')' => {
            depth -= 1;
            false
        }
        ',' => depth == 0,
        _ => false,
    }))
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

fn loop_trips(evolution: &str, machine: &str, ir: &str) -> BTreeMap<String, Vec<LoopTrip>> {
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

    machine_functions(machine)
        .filter_map(|(name, _, body)| {
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

fn scalar_return_registers(machine: &str) -> BTreeSet<&str> {
    let mut returns = BTreeSet::new();
    for (name, _, body) in machine_functions(machine) {
        let mut sites = body
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
            returns.insert(name);
        }
    }
    returns
}

struct AffineBlock<'a> {
    lines: Vec<&'a str>,
    predecessors: Vec<usize>,
}

fn affine_blocks(body: &str) -> Option<Vec<AffineBlock<'_>>> {
    let mut blocks: Vec<Vec<&str>> = Vec::new();
    let mut labels = BTreeMap::new();
    for line in body.lines().map(str::trim).take_while(|line| *line != "}") {
        if line.is_empty() || line.starts_with(';') {
            continue;
        }
        if let Some(label) = line.split_whitespace().next()?.strip_suffix(':') {
            labels.insert(label, blocks.len());
            blocks.push(Vec::new());
        } else {
            if blocks.is_empty() {
                blocks.push(Vec::new());
            }
            blocks.last_mut()?.push(line);
        }
    }

    let mut predecessors = vec![BTreeSet::new(); blocks.len()];
    for (index, block) in blocks.iter_mut().enumerate() {
        let terminator = *block.last()?;
        if terminator.starts_with("br ") {
            for destination in terminator.split("label %").skip(1) {
                let destination = destination.split([',', ' ']).next()?;
                predecessors[*labels.get(destination)?].insert(index);
            }
            block.pop();
        } else if !terminator.starts_with("ret i64 ") && terminator != "unreachable" {
            return None;
        }
    }

    // Cyclic or unsupported control flow uses the block-local fallback.
    let mut successors = vec![Vec::new(); blocks.len()];
    let mut pending = BTreeSet::new();
    let mut indegree: Vec<_> = predecessors.iter().map(BTreeSet::len).collect();
    for (index, inputs) in predecessors.iter().enumerate() {
        if inputs.is_empty() {
            pending.insert(index);
        }
        for &predecessor in inputs {
            successors[predecessor].push(index);
        }
    }
    let mut order = Vec::with_capacity(blocks.len());
    let mut position = vec![0; blocks.len()];
    while let Some(index) = pending.pop_first() {
        let incoming = predecessors[index].iter().map(|&p| position[p]).collect();
        position[index] = order.len();
        order.push(AffineBlock {
            lines: std::mem::take(&mut blocks[index]),
            predecessors: incoming,
        });
        for &next in &successors[index] {
            indegree[next] -= 1;
            if indegree[next] == 0 {
                pending.insert(next);
            }
        }
    }
    if order.len() != blocks.len() {
        return None;
    }
    Some(order)
}

fn affine_results(ir: &str, returns: &BTreeSet<&str>) -> BTreeMap<String, Expr> {
    ir.split("\ndefine ")
        .skip(1)
        .filter_map(|definition| {
            let (header, body) = definition.split_once('{')?;
            let (result, symbol) = header.split_once('@')?;
            if !result.trim().ends_with("i64") || result.contains("cc ") {
                return None;
            }
            let (symbol, args) = symbol.split_once('(')?;
            let name = symbol.trim_matches('"');
            if !returns.contains(name) {
                return None;
            }
            let mut values = BTreeMap::<&str, Expr>::new();
            for (index, arg) in llvm_arguments(args)?
                .filter(|arg| !arg.trim().is_empty())
                .enumerate()
            {
                let mut words = arg.split_whitespace();
                if words.next()? != "i64" || index >= 8 {
                    return None;
                }
                let var = words.last()?;
                if !var.starts_with('%') {
                    return None;
                }
                values.insert(var, Expr::input(Input::Value(index)));
            }
            let mut returned = None;
            let mut local_slots = BTreeSet::new();
            let blocks = affine_blocks(body).unwrap_or_else(|| {
                vec![AffineBlock {
                    lines: body
                        .lines()
                        .map(str::trim)
                        .take_while(|line| *line != "}")
                        .collect(),
                    predecessors: Vec::new(),
                }]
            });
            let mut exits = Vec::<BTreeMap<&str, Expr>>::new();
            for block in blocks {
                let mut incoming = block.predecessors.iter().map(|&index| &exits[index]);
                let mut stored = incoming.next().cloned().unwrap_or_default();
                for other in incoming {
                    stored.retain(|slot, value| other.get(slot) == Some(value));
                }
                for line in block.lines {
                    let resolve = |name: &str| {
                        let name = name.trim();
                        if name.starts_with('%') {
                            values.get(name).cloned()
                        } else {
                            name.parse().ok().map(Expr::constant)
                        }
                    };
                    if let Some(ret) = line.strip_prefix("ret i64 ") {
                        let value = resolve(ret.split(',').next()?)?;
                        if returned.as_ref().is_some_and(|prior| prior != &value) {
                            return None;
                        }
                        returned = Some(value);
                    } else if let Some(store) = line.strip_prefix("store ") {
                        let store = store.strip_prefix("volatile ").unwrap_or(store);
                        let write = store.strip_prefix("i64 ").and_then(|operands| {
                            let (value, destination) = operands.split_once(',')?;
                            let slot = destination.trim().strip_prefix("ptr ")?;
                            let slot = slot.split(',').next()?.trim();
                            local_slots.contains(slot).then_some((slot, resolve(value)))
                        });
                        match write {
                            Some((slot, Some(value))) => {
                                stored.insert(slot, value);
                            }
                            Some((slot, None)) => {
                                stored.remove(slot);
                            }
                            None => stored.clear(),
                        }
                    } else if let Some((name, decl)) = line.split_once(" = ") {
                        if decl.split_whitespace().take(3).any(|op| {
                            matches!(op, "call" | "invoke" | "callbr" | "atomicrmw" | "cmpxchg")
                        }) {
                            stored.clear();
                        }
                        if decl
                            .strip_prefix("alloca i64, align ")
                            .is_some_and(|align| {
                                align
                                    .split(',')
                                    .next()
                                    .is_some_and(|n| n.parse::<u64>().is_ok())
                            })
                        {
                            local_slots.insert(name);
                            continue;
                        }
                        let expr = if let Some(load) = decl.strip_prefix("load ") {
                            let load = load.strip_prefix("volatile ").unwrap_or(load);
                            load.strip_prefix("i64, ptr ")
                                .and_then(|arg| stored.get(arg.split(',').next()?.trim()))
                                .cloned()
                        } else if let Some(phi) = decl.strip_prefix("phi i64 ") {
                            let mut incoming = phi.split('[').skip(1).map(|pair| {
                                let (pair, _) = pair.split_once(']')?;
                                resolve(pair.split_once(',')?.0)
                            });
                            incoming
                                .next()
                                .flatten()
                                .filter(|first| incoming.all(|value| value.as_ref() == Some(first)))
                        } else {
                            (|| {
                                let (op, operands) = decl.split_once(" i64 ")?;
                                let (left, right) = operands.split_once(',')?;
                                let a = resolve(left)?;
                                let b = resolve(right.split(',').next()?)?;
                                match op.split_whitespace().next()? {
                                    "add" => a.add(&b, 1),
                                    "sub" => a.add(&b, -1),
                                    "mul" if b.terms.is_empty() => a.scale(b.constant),
                                    "shl"
                                        if b.terms.is_empty() && (0..64).contains(&b.constant) =>
                                    {
                                        a.scale(1i128 << b.constant)
                                    }
                                    _ => None,
                                }
                            })()
                        };
                        if let Some(expr) = expr {
                            values.insert(name, expr);
                        }
                    } else if !line.is_empty() && !line.starts_with(';') && !line.starts_with('#') {
                        // Block boundaries, calls without results, and unknown memory effects.
                        stored.clear();
                    }
                }
                exits.push(stored);
            }
            Some((name.to_owned(), returned?))
        })
        .collect()
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

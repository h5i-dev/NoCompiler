use crate::{
    flow::{State, entry},
    loops::Slice,
    memory::Regions,
};
use nocompiler_typed::{
    asm::Func,
    isa::{BrOp, IOp, Instr, LdOp, Reg, StOp},
    lin::{Lin, Names, Var},
};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};

pub type Rules = BTreeMap<String, BTreeMap<String, String>>;

#[derive(Clone)]
pub struct Layout {
    pub output: String,
    pub args: Vec<String>,
}

fn fields(description: &str) -> (&str, BTreeMap<&str, (i128, &str)>) {
    let mut parts = description.split(';');
    let name = parts.next().unwrap_or_default();
    let fields = parts
        .filter_map(|p| {
            let mut p = p.split('@');
            Some((p.next()?, (p.next()?.parse().ok()?, p.next()?)))
        })
        .collect();
    (name, fields)
}

pub fn pointers(layout: &Layout) -> BTreeMap<Reg, Var> {
    let mut register = 10;
    let mut result = BTreeMap::new();
    for arg in &layout.args {
        if arg == "ptr" {
            result.insert(Reg(register), Var(register.into()));
        }
        register += if arg.starts_with("slice:") { 2 } else { 1 };
    }
    result
}

pub fn discover(funcs: &[Func], layouts: &BTreeMap<String, Layout>) -> (Rules, Value) {
    let mut candidates = Rules::new();
    let mut witnesses = BTreeMap::<String, Vec<String>>::new();
    let mut conflicting = BTreeSet::new();
    for f in funcs {
        let mut register = 10;
        for arg in &layouts[&f.name].args {
            let parts: Vec<_> = arg.splitn(5, ':').collect();
            if let ["struct", _, align, "rw", descr] = parts.as_slice()
                && align.parse::<i128>().unwrap_or(0) >= 8
            {
                let (name, fields) = fields(descr);
                let lengths: Vec<_> = fields
                    .iter()
                    .filter_map(|(&k, &(offset, d))| {
                        (matches!(k, "len" | "length") && d == "word").then_some((k, offset))
                    })
                    .collect();
                let arrays: Vec<_> = fields
                    .iter()
                    .filter_map(|(&k, (_, d))| Some((k, d.parse::<i128>().ok()?)))
                    .collect();
                if let ([(field, offset)], [(array, capacity)]) =
                    (lengths.as_slice(), arrays.as_slice())
                    && *capacity > 0
                    && checked_growth(f, Reg(register), *offset, *capacity)
                {
                    let pair = BTreeMap::from([((*field).to_owned(), (*array).to_owned())]);
                    if candidates
                        .get(name)
                        .is_some_and(|previous| *previous != pair)
                    {
                        conflicting.insert(name.to_owned());
                    }
                    candidates.insert(name.to_owned(), pair);
                    witnesses
                        .entry(name.to_owned())
                        .or_default()
                        .push(f.name.clone());
                }
            }
            register += if arg.starts_with("slice:") { 2 } else { 1 };
        }
    }
    candidates.retain(|name, _| !conflicting.contains(name));
    let report = Value::Object(
        candidates
            .iter()
            .map(|(n, p)| (n.clone(), json!({"fields":p,"witnesses":witnesses[n]})))
            .collect(),
    );
    (candidates, report)
}

fn checked_growth(func: &Func, base: Reg, offset: i128, capacity: i128) -> bool {
    let mut length = BTreeSet::new();
    let mut increment = BTreeSet::new();
    let mut comparison = false;
    let mut state = State::default();
    for p in &func.instrs {
        match p.instr {
            Instr::Load {
                op: LdOp::Ld,
                rd,
                rs1,
                off,
            } if rs1 == base && i128::from(off) == offset => {
                length.insert(rd);
            }
            Instr::Store {
                op: StOp::Sd,
                rs1,
                rs2,
                off,
            } if rs1 == base
                && i128::from(off) == offset
                && comparison
                && increment.contains(&rs2) =>
            {
                return true;
            }
            Instr::Branch {
                op: BrOp::Bgeu | BrOp::Bltu,
                rs1,
                rs2,
                ..
            } => {
                comparison |= [(rs1, rs2), (rs2, rs1)].into_iter().any(|(a, b)| {
                    length.contains(&a)
                        && state
                            .reg(b)
                            .and_then(|v| v.as_const())
                            .is_some_and(|k| k == capacity || k == capacity - 1)
                });
            }
            Instr::IOp {
                op: IOp::Addi,
                rd,
                rs1,
                imm: 1,
            } if length.contains(&rs1) => {
                increment.insert(rd);
            }
            _ => {}
        }
        state.step(&p.instr, None);
    }
    false
}

pub struct Contract {
    pub text: String,
    pub names: Names,
    pub state: State,
    pub slices: Vec<Slice>,
}

pub fn build(
    symbol: &str,
    layout: &Layout,
    requirements: Option<&Regions>,
    declared: &Rules,
    inferred: &Rules,
    heap: bool,
) -> Result<Contract, String> {
    let mut names = Names::default();
    let mut state = entry();
    let mut slices = vec![];
    let mut params = vec![];
    let mut inputs = vec![];
    let mut borrow = vec![];
    let mut take = vec![];
    let mut pre = vec![];
    let mut post = vec![];
    let mut register = 10;
    let mut param = |name: String| {
        let var = names.fresh(&name);
        params.push(name);
        var
    };
    if heap {
        borrow.push("Heap".to_owned());
    }
    for (index, arg) in layout.args.iter().enumerate() {
        let reg = Reg(register);
        register += 1;
        if arg == "word" {
            let name = format!("x{index}");
            state.regs.insert(reg, Lin::var(param(name.clone())));
            inputs.push(format!("{reg}: int({name})"));
            continue;
        }
        let base = format!("p{index}");
        if arg == "ptr" {
            if let Some(region) = requirements.and_then(|r| r.get(&reg)) {
                param(base.clone());
                inputs.push(format!("{reg}: int({base})"));
                borrow.push(format!(
                    "{base} |-> bytes[{}] {}",
                    region.bytes,
                    region.mode()
                ));
                if region.alignment > 1 {
                    pre.push(format!("{} | {base}", region.alignment));
                }
            } else {
                inputs.push(format!("{reg}: int"));
            }
            continue;
        }
        let parts: Vec<_> = arg.splitn(5, ':').collect();
        let [kind, size, align, ..] = parts.as_slice() else {
            return Err(format!("invalid argument layout {arg}"));
        };
        let var = param(base.clone());
        state.regs.insert(reg, Lin::var(var));
        if *kind == "box" {
            inputs.push(format!("{reg}: u64({base})"));
            take.push(format!("{base} |-> bytes[{size}] rw heap"));
            pre.extend([format!("{base} != 0"), format!("{align} | {base}")]);
            continue;
        }
        let Some(permission) = parts.get(3) else {
            return Err(format!("invalid reference layout {arg}"));
        };
        inputs.push(format!("{reg}: int({base})"));
        let mut region = size.to_string();
        if *kind == "slice" {
            let length = format!("n{index}");
            let length_var = param(length.clone());
            let len_reg = Reg(register);
            register += 1;
            inputs.push(format!("{len_reg}: u64({length})"));
            state.regs.insert(len_reg, Lin::var(length_var));
            let stride: i128 = size
                .parse()
                .map_err(|_| format!("invalid slice size {size}"))?;
            if stride > 0 {
                slices.push(Slice {
                    base: var,
                    length: length_var,
                    stride,
                });
            }
            region = format!("{size}*{length}");
        }
        let mut cap = format!("{base} |-> bytes[{region}] {permission}");
        if *kind == "struct" {
            let (ty, fields) = fields(parts[4]);
            let mut entry_fields = vec![];
            let mut exit_fields = vec![];
            if let Some(rules) = declared.get(ty).or_else(|| inferred.get(ty)) {
                for (field, array) in rules {
                    let info = fields
                        .get(field.as_str())
                        .zip(fields.get(array.as_str()))
                        .filter(|((_, kind), (_, capacity))| {
                            *kind == "word"
                                && capacity.parse::<u64>().is_ok()
                                && align.parse::<u64>().unwrap_or(0) >= 8
                        });
                    let Some(((offset, _), (_, capacity))) = info else {
                        if declared.contains_key(ty) {
                            return Err(format!(
                                "invalid length/array invariant for {ty}: {field}, {array}"
                            ));
                        }
                        continue;
                    };
                    let name = format!("field{index}_{}", entry_fields.len());
                    state
                        .words
                        .insert((var, *offset), Lin::var(param(name.clone())));
                    entry_fields.push(format!("{offset}: int({name})"));
                    pre.push(format!("0 <= {name} <= {capacity}"));
                    if *permission == "rw" {
                        exit_fields.push(format!("{offset}: int({name}_after)"));
                        post.push(format!("0 <= {name}_after <= {capacity}"));
                    }
                }
            }
            if !entry_fields.is_empty() {
                cap.push_str(&format!(" {{{}}}", entry_fields.join(", ")));
            }
            if !exit_fields.is_empty() {
                cap.push_str(&format!(" -> {{{}}}", exit_fields.join(", ")));
            }
        }
        borrow.push(cap);
        if *align != "1" {
            pre.push(format!("{align} | {base}"));
        }
        if *kind == "slice" {
            pre.push(format!("{base} + {region} < 2^64"));
        }
    }
    let mut text = format!("#: fn {symbol} [{}]", params.join(", "));
    for (kind, entries) in [
        ("in", inputs),
        ("borrow", borrow),
        ("take", take),
        ("where", pre),
    ] {
        if !entries.is_empty() {
            text.push_str(&format!(" {kind} {}", entries.join(", ")));
        }
    }
    let ret: Vec<_> = layout.output.split(':').collect();
    match ret.as_slice() {
        ["box", size, align] => {
            text.push_str(&format!(
                " out a0: u64(boxout) give boxout |-> bytes[{size}] rw heap"
            ));
            post.extend(["boxout != 0".to_string(), format!("{align} | boxout")]);
        }
        ["pair"] => text.push_str(" out a0: int, a1: int"),
        ["word"] => text.push_str(" out a0: int"),
        ["void"] if !post.is_empty() => text.push_str(" out a0: int"),
        ["void"] => {}
        _ => return Err(format!("unknown ABI result {}", layout.output)),
    }
    if !post.is_empty() {
        text.push_str(&format!(" where {}", post.join(", ")));
    }
    Ok(Contract {
        text,
        names,
        state,
        slices,
    })
}

pub fn owned(layout: &Layout) -> bool {
    layout.output.starts_with("box:") || layout.args.iter().any(|a| a.starts_with("box:"))
}

use crate::{
    contract_ir::{Expr, Input, Pointer, Summary, ViewEnd},
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

/// A source contract independent of the register assignment.
#[derive(Default)]
pub struct SourceContract {
    raw: BTreeMap<usize, (Expr, u64, bool)>,
    view: Option<Pointer>,
    view_end: Option<ViewEnd>,
    result: Option<Expr>,
    fields: BTreeMap<(usize, u64), Expr>,
}

pub(crate) fn input_name(input: Input) -> String {
    match input {
        Input::Value(i) => format!("x{i}"),
        Input::Length(i) => format!("n{i}"),
    }
}

fn supported_expression(layout: &Layout, expression: &Expr) -> bool {
    expression.terms.keys().all(|input| match *input {
        Input::Value(i) => layout
            .args
            .get(i)
            .is_some_and(|a| matches!(a.as_str(), "word" | "uword")),
        Input::Length(i) => layout.args.get(i).is_some_and(|a| a.starts_with("slice:")),
    })
}

pub fn infer_source(layout: &Layout, summary: &Summary) -> SourceContract {
    let mut contract = SourceContract::default();
    for (i, arg) in layout.args.iter().enumerate() {
        if arg != "ptr" {
            continue;
        }
        let mut region = None::<(Expr, u64, bool)>;
        let mut compatible = true;
        for access in summary.accesses.iter().filter(|a| a.argument == i) {
            let Some(end) = access.offset.add(&access.bytes, 1) else {
                compatible = false;
                break;
            };
            if !supported_expression(layout, &end)
                || access.alignment == 0
                || access.offset.constant % i128::from(access.alignment) != 0
                || access
                    .offset
                    .terms
                    .values()
                    .any(|c| *c % i128::from(access.alignment) != 0)
            {
                compatible = false;
                break;
            }
            if let Some((extent, align, write)) = &mut region {
                if extent.terms != end.terms {
                    compatible = false;
                    break;
                }
                extent.constant = extent.constant.max(end.constant);
                *align = (*align).max(access.alignment);
                *write |= access.write;
            } else {
                region = Some((end, access.alignment, access.write));
            }
        }
        if compatible
            && let Some((end, align, write)) = region
            && (end.constant > 0 || (end.constant == 0 && !end.terms.is_empty()))
            && end.terms.values().all(|&c| c > 0)
        {
            contract.raw.insert(i, (end, align, write));
        }
    }
    if layout.output == "pair"
        && let Some(view) = &summary.returned_view
        && layout.args.get(view.argument).is_some_and(|a| {
            a.starts_with("slice:") || a.starts_with("ref:") || a.starts_with("struct:")
        })
        && supported_expression(layout, &view.offset)
        && view
            .length
            .as_ref()
            .is_some_and(|n| supported_expression(layout, n))
    {
        contract.view = Some(view.clone());
    }
    if layout.output == "pair"
        && contract.view.is_none()
        && let Some(view) = &summary.view_end
        && layout.args.get(view.argument).is_some_and(|shape| {
            shape.starts_with("slice:") || shape.starts_with("ref:") || shape.starts_with("struct:")
        })
        && supported_expression(layout, &view.end)
    {
        contract.view_end = Some(view.clone());
    }
    if layout.output == "word"
        && let Some(value) = &summary.returned_scalar
        && supported_expression(layout, value)
    {
        contract.result = Some(value.clone());
    }
    for (&(i, offset), value) in &summary.field_writes {
        if layout
            .args
            .get(i)
            .is_some_and(|a| a.starts_with("struct:") && a.split(':').nth(3) == Some("rw"))
            && offset % 8 == 0
            && supported_expression(layout, value)
        {
            contract.fields.insert((i, offset), value.clone());
        }
    }
    contract
}

pub fn source_report(
    layout: &Layout,
    summary: Option<&Summary>,
    contract: &SourceContract,
) -> Value {
    let arguments: Vec<_> = layout
        .args
        .iter()
        .enumerate()
        .map(|(index, shape)| {
            let parts: Vec<_> = shape.splitn(5, ':').collect();
            match parts.as_slice() {
                [
                    kind @ ("slice" | "ref" | "struct"),
                    size,
                    align,
                    permission,
                    ..,
                ] => {
                    let capacity = if *kind == "slice" {
                        format!("{size}*n{index}")
                    } else {
                        size.to_string()
                    };
                    json!({"argument": index, "kind": kind, "capacity_bytes": capacity,
                           "alignment": align, "permission": permission})
                }
                ["box", size, align] => json!({"argument": index, "kind": "box", "bytes": size,
                                               "alignment": align, "ownership": "take"}),
                [kind, ..] => json!({"argument": index, "kind": kind}),
                [] => Value::Null,
            }
        })
        .collect();
    let requirements: Vec<_> = contract
        .raw
        .iter()
        .map(|(argument, (bytes, alignment, write))| {
            json!({"argument": argument, "bytes": bytes.render(input_name),
                   "alignment": alignment, "access": if *write { "rw" } else { "ro" }})
        })
        .collect();
    let accessed: Vec<_> = summary
        .into_iter()
        .flat_map(|s| &s.accesses)
        .map(|access| {
            json!({"argument": access.argument, "offset": access.offset.render(input_name),
                   "bytes": access.bytes.render(input_name), "alignment": access.alignment,
                   "write": access.write})
        })
        .collect();
    let updated: Vec<_> = contract
        .fields
        .iter()
        .map(|((argument, offset), value)| {
            json!({"argument": argument, "offset": offset, "value": value.render(input_name)})
        })
        .collect();
    let view = contract.view.as_ref().map(|view| {
        json!({"argument": view.argument, "offset": view.offset.render(input_name),
               "length": view.length.as_ref().map(|n| n.render(input_name))})
    });
    json!({
        "arguments": arguments,
        "result_abi_shape": layout.output,
        "mir_analyzed": summary.is_some(),
        "mir_widened_view_joins": summary.map_or(0, |s| s.widened_view_joins),
        "mir_accesses": accessed,
        "raw_requirements": requirements,
        "returned_view": view,
        "returned_view_end": contract.view_end.as_ref().map(|view|
            json!({"argument": view.argument, "stride": view.stride, "offset": view.end.render(input_name)})),

        "scalar_result": contract.result.as_ref().map(|e| e.render(input_name)),
        "field_writes": updated,
        "drop_arguments": summary.map(|s| &s.drops),
        "unresolved_mir_access": summary.is_some_and(|s| s.unresolved_access),
    })
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
    source: Option<&SourceContract>,
    llvm_range: Option<crate::llvm::WordRange>,
    llvm_result: Option<&Expr>,
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
    let mut dynamic_slices = vec![];
    let mut words = BTreeMap::new();
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
        if matches!(arg.as_str(), "word" | "uword") {
            let name = format!("x{index}");
            let var = param(name.clone());
            words.insert(Input::Value(index), var);
            state.regs.insert(reg, Lin::var(var));
            let kind = if arg == "uword" { "u64" } else { "int" };
            inputs.push(format!("{reg}: {kind}({name})"));
            continue;
        }
        let base = format!("p{index}");
        if arg == "ptr" {
            let machine_region = requirements.and_then(|r| r.get(&reg));
            if let Some((bytes, alignment, write)) = source.and_then(|s| s.raw.get(&index)) {
                let var = param(base.clone());
                inputs.push(format!("{reg}: int({base})"));
                state.regs.insert(reg, Lin::var(var));
                let mut alignment = i128::from(*alignment);
                let mut write = *write;
                let size = if bytes.terms.is_empty() {
                    let mut length = bytes.constant;
                    if let Some(region) = machine_region {
                        length = length.max(region.bytes);
                        alignment = alignment.max(region.alignment);
                        write |= region.mode() == "rw";
                    }
                    length.to_string()
                } else {
                    bytes.render(input_name)
                };
                let permission = if write { "rw" } else { "ro" };
                borrow.push(format!("{base} |-> bytes[{size}] {permission}"));
                if alignment > 1 {
                    pre.push(format!("{alignment} | {base}"));
                }
                if !bytes.terms.is_empty() {
                    pre.push(format!("{base} + ({size}) < 2^64"));
                }
                if bytes.constant == 0
                    && bytes.terms.len() == 1
                    && let Some((&input, &stride)) = bytes.terms.first_key_value()
                {
                    dynamic_slices.push((var, input, stride));
                }
            } else if let Some(region) = machine_region {
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
            words.insert(Input::Length(index), length_var);
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
            if let Some(source) = source {
                for (&(argument, offset), value) in &source.fields {
                    if argument != index
                        || exit_fields
                            .iter()
                            .any(|f| f.starts_with(&format!("{offset}:")))
                    {
                        continue;
                    }
                    // A field assertion is only emitted for a complete word in the declared region.
                    if align.parse::<u64>().unwrap_or(0) >= 8
                        && offset
                            .checked_add(8)
                            .is_some_and(|end| size.parse::<u64>().is_ok_and(|len| end <= len))
                    {
                        exit_fields.push(format!("{offset}: int({})", value.render(input_name)));
                    }
                }
            }
            if !entry_fields.is_empty() || !exit_fields.is_empty() {
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
    for (base, input, stride) in dynamic_slices {
        if let Some(&length) = words.get(&input) {
            slices.push(Slice {
                base,
                length,
                stride,
            });
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
        ["pair"] => {
            if let Some(view) = source.and_then(|s| s.view.as_ref()) {
                let offset = view.offset.render(input_name);
                let length = view.length.as_ref().unwrap().render(input_name);
                text.push_str(&format!(
                    " out a0: int(p{} + ({offset})), a1: int({length})",
                    view.argument
                ));
            } else if let Some(view) = source.and_then(|s| s.view_end.as_ref()) {
                text.push_str(" out a0: u64(view_ptr), a1: u64(view_len)");
                post.push(format!(
                    "view_ptr + {}*view_len = p{} + ({})",
                    view.stride,
                    view.argument,
                    view.end.render(input_name)
                ));
            } else {
                text.push_str(" out a0: int, a1: int");
            }
        }
        ["word"] => {
            if let Some(value) = source.and_then(|s| s.result.as_ref()) {
                text.push_str(&format!(" out a0: int({})", value.render(input_name)));
            } else if let Some(value) =
                llvm_result.filter(|value| supported_expression(layout, value))
            {
                text.push_str(&format!(" out a0: int({})", value.render(input_name)));
            } else if let Some(range) = llvm_range {
                text.push_str(" out a0: u64(llvm_result)");
                post.push(format!("{} <= llvm_result < {}", range.lower, range.upper));
            } else {
                text.push_str(" out a0: int");
            }
        }
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

use crate::{
    contract_ir::{Expr, Input, Pointer, Summary, ViewEnd},
    flow::{State, address, analyze_detailed, entry},
    loops::Slice,
    memory::Regions,
};
use nocompiler_typed::{
    asm::Func,
    isa::{Instr, Reg, StOp},
    lin::{Lin, Names, Var},
};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};

pub type Rules = BTreeMap<String, BTreeMap<String, String>>;

#[derive(Clone)]
pub struct Layout {
    pub output: String,
    pub args: Vec<String>,
    pub is_unsafe: bool,
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

pub fn discover(funcs: &[Func], layouts: &BTreeMap<String, Layout>) -> Value {
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
                let (words, arrays): (Vec<_>, Vec<_>) = fields
                    .into_iter()
                    .partition(|(_, (_, kind))| *kind == "word");
                let mut pairs = words.iter().flat_map(|&(field, (offset, _))| {
                    let bound = field_growth_bound(f, Reg(register), offset);
                    arrays.iter().filter_map(move |&(array, (_, kind))| {
                        let capacity: u64 = kind.parse().ok()?;
                        (capacity > 0 && bound.is_some_and(|max| max <= capacity))
                            .then_some((field, array))
                    })
                });
                if let (Some((field, array)), None) = (pairs.next(), pairs.next()) {
                    let pair = BTreeMap::from([(field.to_owned(), array.to_owned())]);
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
    Value::Object(
        candidates
            .iter()
            .map(|(n, p)| (n.clone(), json!({"fields":p,"witnesses":witnesses[n]})))
            .collect(),
    )
}

fn field_growth_bound(func: &Func, base: Reg, offset: i128) -> Option<u64> {
    let object = Var(0);
    let field = Var(1);
    let mut start = entry();
    start.regs.insert(base, Lin::var(object));
    start.words.insert((object, offset), Lin::var(field));
    let target = Lin::var(object).add_const(offset);
    let updated = Lin::var(field).add_const(1);
    func.instrs
        .iter()
        .zip(analyze_detailed(func, start))
        .filter_map(|(point, state)| {
            let (
                Instr::Store {
                    op: StOp::Sd,
                    rs1,
                    rs2,
                    off,
                },
                Some(state),
            ) = (&point.instr, state)
            else {
                return None;
            };
            (address(&state.exact, *rs1, *off) == target && state.exact.reg(*rs2) == updated)
                .then(|| state.unsigned_max(*rs2))
        })
        .max()
}

/// A source contract independent of the register assignment.
#[derive(Default)]
pub struct SourceContract {
    raw: BTreeMap<usize, (Expr, u64, bool)>,
    view: Option<Pointer>,
    view_end: Option<ViewEnd>,
    result: Option<Expr>,
    fields: BTreeMap<(usize, u64), Expr>,
    initialized: BTreeSet<(usize, u64)>,
}

impl SourceContract {
    pub fn with_machine_raw(mut self, machine: Self, use_source: bool) -> Self {
        if !use_source {
            self = Self::default();
        }
        for (argument, (extent, align, mode)) in machine.raw {
            if !extent.terms.is_empty() {
                self.raw.entry(argument).or_insert((extent, align, mode));
            }
        }
        self
    }
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

fn tracked_borrow(layout: &Layout, argument: usize) -> bool {
    layout.args.get(argument).is_some_and(|arg| {
        let mut parts = arg.split(':');
        matches!(parts.next(), Some("struct" | "ref")) && parts.nth(2) == Some("rw")
    })
}

fn extent_covers(layout: &Layout, extent: &Expr, end: &Expr) -> bool {
    extent.add(end, -1).is_some_and(|difference| {
        difference.constant >= 0
            && difference.terms.iter().all(|(&input, &coefficient)| {
                coefficient >= 0
                    && match input {
                        Input::Length(_) => true,
                        Input::Value(index) => layout.args[index] == "uword",
                    }
            })
    })
}

pub fn infer_source(layout: &Layout, summary: &Summary) -> SourceContract {
    let mut contract = SourceContract::default();
    for (i, arg) in layout.args.iter().enumerate() {
        if arg != "ptr" {
            continue;
        }
        let mut ends = Vec::new();
        let mut align = 1;
        let mut write = false;
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
            align = align.max(access.alignment);
            write |= access.write;
            ends.push(end);
        }
        if compatible
            && let Some(end) = ends.iter().find(|extent| {
                (extent.constant > 0 || (extent.constant == 0 && !extent.terms.is_empty()))
                    && extent.terms.values().all(|&c| c > 0)
                    && ends.iter().all(|end| extent_covers(layout, extent, end))
            })
        {
            contract.raw.insert(i, (end.clone(), align, write));
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
    for &(i, offset) in &summary.initialized_words {
        if tracked_borrow(layout, i) && offset % 8 == 0 {
            contract.initialized.insert((i, offset));
        }
    }
    for (&(i, offset), value) in &summary.field_writes {
        if tracked_borrow(layout, i) && offset % 8 == 0 && supported_expression(layout, value) {
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
        "initialized_words": contract.initialized,
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
    (llvm_range, llvm_result): (Option<crate::llvm::WordRange>, Option<&Expr>),
    declared: &Rules,
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
            if !layout.is_unsafe {
                inputs.push(format!("{reg}: int"));
                continue;
            }
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
        if matches!(*kind, "struct" | "ref") {
            let (ty, fields) = fields(parts.get(4).copied().unwrap_or_default());
            let mut entry_fields = vec![];
            let mut exit_fields = vec![];
            if let Some(rules) = declared.get(ty) {
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
                for &(argument, offset) in &source.initialized {
                    if argument == index
                        && !exit_fields
                            .iter()
                            .any(|f| f.starts_with(&format!("{offset}:")))
                        && align.parse::<u64>().unwrap_or(0) >= 8
                        && offset
                            .checked_add(8)
                            .is_some_and(|end| size.parse::<u64>().is_ok_and(|len| end <= len))
                    {
                        exit_fields.push(format!("{offset}: int(init{index}_{offset})"));
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dynamic_extent_covers_fixed_prefix_with_an_unsigned_index() {
        let mut layout = Layout {
            output: "word".into(),
            args: vec!["ptr".into(), "uword".into()],
            is_unsafe: true,
        };
        let last = Expr::input(Input::Value(1))
            .scale(8)
            .unwrap()
            .add(&Expr::constant(8), 1)
            .unwrap();
        assert!(extent_covers(&layout, &last, &Expr::constant(8)));
        assert!(!extent_covers(&layout, &Expr::constant(8), &last));
        layout.args[1] = "word".into();
        assert!(!extent_covers(&layout, &last, &Expr::constant(8)));
    }

    #[test]
    fn field_growth_uses_layout_and_reachable_register_facts() {
        let source = r#"
.type update, @function
update:
    ld a1, 0(a0)
    li a2, 4
    bgeu a1, a2, .Ldone
.Lupdate:
    addi a1, a1, 1
    sd a1, 0(a0)
.Ldone:
    ret
.size update, .-update
"#;
        let layout = Layout {
            output: "unit".into(),
            is_unsafe: false,
            args: vec!["struct:40:8:rw:Vector;count@0@word;elements@8@4".into()],
        };
        let layouts = BTreeMap::from([("update".into(), layout)]);
        let program = nocompiler_typed::asm::parse(source).unwrap();
        assert_eq!(
            discover(&program.funcs, &layouts)["Vector"]["fields"],
            json!({"count": "elements"})
        );

        let unguarded = source.replace(
            "    ld a1, 0(a0)",
            "    bnez a3, .Lupdate\n    ld a1, 0(a0)",
        );
        let program = nocompiler_typed::asm::parse(&unguarded).unwrap();
        assert_eq!(discover(&program.funcs, &layouts), json!({}));
    }
}

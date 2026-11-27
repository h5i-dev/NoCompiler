use crate::flow::calls;
use nocompiler_typed::{
    asm::Func,
    isa::{IOp, Instr, Reg},
};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};

pub type Specs = BTreeMap<String, Value>;

pub fn operation(name: &str) -> Option<&str> {
    let rest = name.strip_prefix("_RNv")?;
    let rest = if let Some(hash) = rest.strip_prefix("Cs") {
        hash.split_once('_')?.1
    } else {
        rest
    };
    let rest = rest.strip_prefix("7___rustc")?;
    let digits = rest.bytes().take_while(u8::is_ascii_digit).count();
    let name = rest.get(digits..)?.strip_prefix('_')?;
    match name {
        "__rust_alloc" => Some("rust_alloc"),
        "__rust_alloc_zeroed" => Some("rust_alloc_zeroed"),
        "__rust_dealloc" => Some("rust_dealloc"),
        "__rust_realloc" => Some("rust_realloc"),
        "__rust_no_alloc_shim_is_unstable_v2" => Some("rust_no_alloc_shim_is_unstable_v2"),
        _ => None,
    }
}

pub fn discover<'a>(
    funcs: &[Func],
    shims: &[Func],
    linked: impl Iterator<Item = &'a String>,
    stack: u64,
) -> Specs {
    let references: BTreeSet<_> = funcs.iter().flat_map(calls).map(|(c, _)| c).collect();
    let mut specs = Specs::new();
    for name in linked {
        if references.contains(name.as_str())
            && let Some(op) = operation(name)
        {
            specs.insert(
                name.clone(),
                json!({"operation":op,"stack":if op.contains("no_alloc_shim"){0}else{stack}}),
            );
        }
    }
    let mut ambiguous = BTreeSet::new();
    for shim in shims {
        let Some(op) = operation(&shim.name) else {
            continue;
        };
        let count = match op {
            "rust_alloc" | "rust_alloc_zeroed" => 2,
            "rust_dealloc" => 3,
            "rust_realloc" => 4,
            _ => continue,
        };
        let Some((last, moves)) = shim.instrs.split_last() else {
            continue;
        };
        let Some((callee, true)) = crate::flow::call(&last.instr) else {
            continue;
        };
        if !references.contains(callee) || funcs.iter().any(|f| f.name == callee) {
            continue;
        }
        let mut values: BTreeMap<_, _> = (10..10 + count).map(|i| (Reg(i), Reg(i))).collect();
        let mut changed = vec![];
        let mut valid = true;
        for p in moves {
            if let Instr::IOp {
                op: IOp::Addi,
                rd,
                rs1,
                imm: 0,
            } = p.instr
                && (10..18).contains(&rd.0)
                && let Some(&value) = values.get(&rs1)
            {
                values.insert(rd, value);
                changed.push(rd);
            } else {
                valid = false;
                break;
            }
        }
        if !valid {
            continue;
        }
        let mut regs = BTreeMap::new();
        for reg in changed.into_iter().rev().chain(values.keys().copied()) {
            regs.entry(values[&reg].name()).or_insert(reg.name());
        }
        if regs.len() != usize::from(count) {
            continue;
        }
        let spec =
            json!({"operation":op,"stack":stack,"registers":regs,"forwarding_shim":shim.name});
        if let Some(previous) = specs.get(callee)
            && (previous["operation"] != spec["operation"]
                || previous["registers"] != spec["registers"])
        {
            ambiguous.insert(callee);
        }
        specs.insert(callee.to_owned(), spec);
    }
    specs.retain(|name, _| !ambiguous.contains(name.as_str()));
    specs
}

fn signature(op: &str, align: u64, spec: &Value) -> Option<String> {
    let canonical = match op {
        "allocate" => format!(
            "[n] in a0: u64(n) borrow Heap out a0: u64(p) give p != 0 => p |-> bytes[n] rw heap where {align} | p"
        ),
        "deallocate" => {
            "[p, n] in a0: int(p), a1: u64(n) take p |-> bytes[n] rw heap borrow Heap".into()
        }
        "reallocate" | "reallocate_nonnull" => {
            let base = "[p, old, n] in a0: int(p), a1: u64(old), a2: u64(n) take p |-> bytes[old] rw heap borrow Heap out a0: u64(q)";
            if op == "reallocate" {
                format!(
                    "{base} give q = 0 => p |-> bytes[old] rw heap, q != 0 => q |-> bytes[n] rw heap where {align} | q"
                )
            } else {
                format!("{base} give q |-> bytes[n] rw heap where q != 0, {align} | q")
            }
        }
        "rust_no_alloc_shim_is_unstable_v2" => "[]".into(),
        _ => {
            let alignments = [1, 2, 4, 8, 16, 32, 64];
            let supported = alignments
                .iter()
                .map(|n| format!("a = {n}"))
                .collect::<Vec<_>>()
                .join(" || ");
            let post = alignments[1..]
                .iter()
                .map(|n| format!("(a = {n} => {n} | q)"))
                .collect::<Vec<_>>()
                .join(", ");
            let limits = format!("n > 0, ({supported})");
            let r = |canonical: &str| {
                spec["registers"][canonical]
                    .as_str()
                    .filter(|s| matches!(s.as_bytes(), [b'a', b'0'..=b'7']))
                    .unwrap_or(match canonical {
                        "a0" => "a0",
                        "a1" => "a1",
                        "a2" => "a2",
                        _ => "a3",
                    })
            };
            let (a0, a1, a2, a3) = (r("a0"), r("a1"), r("a2"), r("a3"));
            match op {
                "rust_alloc" | "rust_alloc_zeroed" => format!(
                    "[n, a] in {a0}: u64(n), {a1}: u64(a) borrow Heap where {limits} out a0: u64(q) give q != 0 => q |-> bytes[n] rw heap where {post}"
                ),
                "rust_dealloc" => format!(
                    "[p, n, a] in {a0}: u64(p), {a1}: u64(n), {a2}: u64(a) borrow Heap take p |-> bytes[n] rw heap where {limits}"
                ),
                "rust_realloc" => format!(
                    "[p, old, a, n] in {a0}: u64(p), {a1}: u64(old), {a2}: u64(a), {a3}: u64(n) borrow Heap take p |-> bytes[old] rw heap where old > 0, {limits} out a0: u64(q) give q = 0 => p |-> bytes[old] rw heap, q != 0 => q |-> bytes[n] rw heap where {post}"
                ),
                _ => return None,
            }
        }
    };
    Some(canonical)
}

pub struct AllocatorContracts {
    pub annotations: BTreeMap<String, String>,
    pub budgets: BTreeMap<String, i128>,
}

pub fn contracts(
    specs: &Specs,
    linked: &BTreeMap<String, (u64, u64)>,
    selected: &BTreeSet<String>,
) -> Result<AllocatorContracts, String> {
    let mut contracts = BTreeMap::new();
    let mut budgets = BTreeMap::new();
    for (name, spec) in specs {
        if !linked.contains_key(name)
            || selected.contains(name)
            || !name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
        {
            return Err(format!(
                "allocator {name} must name a linked symbol outside the selected targets"
            ));
        }
        let Some(stack) = spec["stack"].as_u64() else {
            return Err(format!("invalid allocator stack budget for {name}"));
        };
        let align = spec
            .get("alignment")
            .map_or(Some(16), Value::as_u64)
            .filter(|a| a.is_power_of_two())
            .ok_or_else(|| format!("invalid alignment for {name}"))?;
        let op = spec["operation"]
            .as_str()
            .and_then(|op| signature(op, align, spec))
            .ok_or_else(|| format!("unknown allocator operation for {name}"))?;
        contracts.insert(
            name.clone(),
            format!("#: extern fn {name} {op} stack {stack}\n"),
        );
        budgets.insert(name.clone(), i128::from(stack));
    }
    Ok(AllocatorContracts {
        annotations: contracts,
        budgets,
    })
}

pub fn propagate(funcs: &[Func], mut uses: BTreeSet<String>) -> BTreeSet<String> {
    loop {
        let next: Vec<_> = funcs
            .iter()
            .filter(|f| !uses.contains(&f.name) && calls(f).any(|(c, _)| uses.contains(c)))
            .map(|f| f.name.clone())
            .collect();
        if next.is_empty() {
            return uses;
        }
        uses.extend(next);
    }
}

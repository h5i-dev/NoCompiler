//! Diagnostic call scope from the selected optimized assembly bodies.
use crate::{TextMap, build::Symbols, flow::call};
use nocompiler_typed::{
    asm::Func,
    isa::{Instr, RA, ZERO},
};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};

pub fn report(targets: &TextMap, funcs: &[Func], symbols: &Symbols, external: &TextMap) -> Value {
    let bodies: BTreeMap<_, _> = funcs.iter().map(|f| (f.name.as_str(), f)).collect();
    let entries = targets
        .iter()
        .map(|(path, symbol)| {
            let mut seen = BTreeSet::new();
            let mut selected = BTreeSet::new();
            let mut declared = BTreeSet::new();
            let mut unselected = BTreeSet::new();
            let mut missing = BTreeSet::new();
            let mut indirect = Vec::new();
            let mut pending = vec![symbol.as_str()];
            while let Some(name) = pending.pop() {
                if !seen.insert(name) {
                    continue;
                }
                if let Some(body) = bodies.get(name) {
                    selected.insert(name);
                    for instruction in &body.instrs {
                        if let Some((callee, _)) = call(&instruction.instr) {
                            pending.push(callee);
                        } else if let Instr::Jalr { rd, rs1, off } = instruction.instr
                            && (rd, rs1, off) != (ZERO, RA, 0)
                        {
                            indirect.push(json!({
                                "function": name, "line_in_selected_assembly": instruction.line,
                                "base_register": rs1.name(), "offset": off,
                            }));
                        }
                    }
                } else if external.contains_key(name) {
                    declared.insert(name);
                } else if symbols.contains_key(name) {
                    unselected.insert(name);
                } else {
                    missing.insert(name);
                }
            }
            (
                path.to_owned(),
                json!({
                    "selected_bodies": selected,
                    "external_contracts": declared,
                    "linked_without_selected_body_or_contract": unselected,
                    "missing_linked_symbols": missing,
                    "unresolved_indirect_sites": indirect,
                }),
            )
        })
        .collect();
    Value::Object(entries)
}

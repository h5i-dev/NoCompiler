//! `--prove`: compile the generated Lean module (the program's theorem D on the linked image)
//! with the repository's Lean checker, and read the axioms its theorem depends on. The ledger
//! records `proved` only when this succeeds with the standard axioms (ledger.rs `Proof`).

use std::path::Path;
use std::process::Command;

/// The axioms a proof in the Lean core may use (docs/isa/trust.md); anything else (`sorryAx`,
/// a user axiom, `Lean.ofReduceBool` from `native_decide`) means not proved.
pub const STANDARD_AXIOMS: [&str; 3] = ["propext", "Classical.choice", "Quot.sound"];

/// Run `lake env lean` in `lean_dir` on `module_text` followed by `#print axioms theorem`;
/// the theorem's axioms, or why it failed.
pub fn run_lean(lean_dir: &Path, module_text: &str, theorem: &str) -> Result<Vec<String>, String> {
    let file = std::env::temp_dir().join(format!("nocompiler-prove-{}.lean", std::process::id()));
    std::fs::write(&file, format!("{module_text}\n#print axioms {theorem}\n"))
        .map_err(|e| format!("{}: {e}", file.display()))?;
    let out = Command::new("lake")
        .args(["env", "lean"])
        .arg(&file)
        .current_dir(lean_dir)
        .output()
        .map_err(|e| format!("lake: {e}"))?;
    let _ = std::fs::remove_file(&file);
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    if !out.status.success() || text.lines().any(|l| l.contains(": error")) {
        let first = text
            .lines()
            .chain(String::from_utf8_lossy(&out.stderr).lines())
            .find(|l| l.contains("error"))
            .unwrap_or("lean failed")
            .to_string();
        return Err(first);
    }
    parse_axioms(&text).ok_or_else(|| "no `#print axioms` output".to_string())
}

/// The axiom list of `#print axioms` output.
pub fn parse_axioms(text: &str) -> Option<Vec<String>> {
    for line in text.lines() {
        if line.contains("does not depend on any axioms") {
            return Some(vec![]);
        }
        if let Some(i) = line.find("depends on axioms: [") {
            let rest = &line[i + "depends on axioms: [".len()..];
            let inner = rest.split(']').next()?;
            return Some(
                inner
                    .split(',')
                    .map(|a| a.trim().to_string())
                    .filter(|a| !a.is_empty())
                    .collect(),
            );
        }
    }
    None
}

/// Only the standard axioms.
pub fn standard(axioms: &[String]) -> bool {
    axioms.iter().all(|a| STANDARD_AXIOMS.contains(&a.as_str()))
}

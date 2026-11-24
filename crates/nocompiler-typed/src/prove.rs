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
    // the named theorem's line: a module may print the axioms of other theorems too
    let mine: String = text
        .lines()
        .filter(|l| l.contains(&format!("'{theorem}'")))
        .collect::<Vec<_>>()
        .join("\n");
    parse_axioms(&mine).ok_or_else(|| format!("no `#print axioms {theorem}` output"))
}

/// The certificate path (docs/typed/export.md "Certificates"): the exported module's record and
/// `def code` (cut before its search-mode theorems) go through `lean/scripts/certgen.py --split
/// --prog`, which records the search's certificates by compiled evaluation and writes the
/// program's theorem D with one kernel theorem per point (`prog_meets`, in the root namespace).
/// Returns that module's text. The certificates are hints: the kernel re-checks every one.
pub fn certify(lean_dir: &Path, module_text: &str, module: &str) -> Result<String, String> {
    let cut = module_text
        .find("set_option maxRecDepth 100000 in\ntheorem chk_")
        .ok_or("no per-function theorems in the module (needs --image and the linked code)")?;
    let input = format!(
        "{}end {module}\n\nopen {module}\nopen NoCompiler NoCompiler.Typed\n",
        &module_text[..cut]
    );
    certgen_text(lean_dir, &input)
}

/// `certgen.py --split --prog` on a module that has the records, `def code` and `def prog` (no
/// theorems): the module with the certificate tables, the kernel theorems and theorem D.
pub fn certgen_text(lean_dir: &Path, input: &str) -> Result<String, String> {
    let tmp = std::env::temp_dir();
    let id = std::process::id();
    let inp = tmp.join(format!("nocompiler-certin-{id}.lean"));
    let outp = tmp.join(format!("nocompiler-cert-{id}.lean"));
    std::fs::write(&inp, input).map_err(|e| format!("{}: {e}", inp.display()))?;
    let script = lean_dir.join("scripts").join("certgen.py");
    let out = Command::new("python3")
        .arg(&script)
        .arg(&inp)
        .arg(&outp)
        .args(["--split", "--prog"])
        .current_dir(lean_dir)
        .output()
        .map_err(|e| format!("python3: {e}"))?;
    let _ = std::fs::remove_file(&inp);
    if !out.status.success() {
        let err = String::from_utf8_lossy(&out.stderr);
        return Err(format!(
            "certgen: {}",
            err.lines().last().unwrap_or("failed")
        ));
    }
    let text = std::fs::read_to_string(&outp).map_err(|e| format!("{}: {e}", outp.display()))?;
    let _ = std::fs::remove_file(&outp);
    let _ = std::fs::remove_file(tmp.join(format!("nocompiler-cert-{id}.log.lean")));
    Ok(text)
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

//! A binary as a patch stack (docs/toolkit/design/patch-stack.md, Q-VC2): a
//! base ELF by SHA-256, ordered patches in `disasm`'s structured text, and the
//! SHA-256 of the binary they make. `build` rebuilds it: each patch assembled
//! (`text::assemble`, deterministic: tests/asm_determinism.rs) and linked into
//! the binary so far (`link::link`, swb-elf's placement).
//!
//! The file, one record per line (`#` starts a comment); paths are relative
//! to the stack file's directory:
//!
//! ```text
//! nocompiler-stack 1
//! base SHA256 PATH
//! patch SHA256 PATH
//! result SHA256
//! ```
//!
//! `1` is the version of the recipe (assembler and linker); a new version is
//! a new recipe, and its `result` must be recomputed.

use std::path::{Path, PathBuf};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stack {
    pub base: (String, PathBuf),
    pub patches: Vec<(String, PathBuf)>,
    pub result: Option<String>,
}

fn sha_hex(b: &[u8]) -> String {
    crate::sha256::hex(&crate::sha256::digest(b))
}

fn is_sha(s: &str) -> bool {
    s.len() == 64
        && s.bytes()
            .all(|c| c.is_ascii_hexdigit() && !c.is_ascii_uppercase())
}

/// Read a stack file's text.
pub fn parse(text: &str) -> Result<Stack, String> {
    let mut lines = text
        .lines()
        .enumerate()
        .map(|(i, l)| (i + 1, l.split('#').next().unwrap_or("").trim()))
        .filter(|(_, l)| !l.is_empty());
    match lines.next() {
        Some((_, "nocompiler-stack 1")) => {}
        Some((n, l)) => return Err(format!("line {n}: `{l}`: want `nocompiler-stack 1`")),
        None => return Err("empty stack file".into()),
    }
    let (mut base, mut patches, mut result) = (None, Vec::new(), None);
    for (n, l) in lines {
        let w: Vec<&str> = l.split_whitespace().collect();
        let sha = |s: &str| {
            if is_sha(s) {
                Ok(s.to_string())
            } else {
                Err(format!("line {n}: `{s}` is not a lowercase SHA-256"))
            }
        };
        match w[..] {
            ["base", s, p] if base.is_none() && patches.is_empty() => {
                base = Some((sha(s)?, PathBuf::from(p)))
            }
            ["patch", s, p] if base.is_some() && result.is_none() => {
                patches.push((sha(s)?, PathBuf::from(p)))
            }
            ["result", s] if base.is_some() && result.is_none() => result = Some(sha(s)?),
            _ => {
                return Err(format!(
                    "line {n}: `{l}`: want `base SHA PATH`, then `patch SHA PATH` lines, then `result SHA`"
                ));
            }
        }
    }
    let base = base.ok_or("no `base` line")?;
    Ok(Stack {
        base,
        patches,
        result,
    })
}

/// The stack's text (`parse`'s inverse).
pub fn render(s: &Stack) -> String {
    let mut o = format!(
        "nocompiler-stack 1\nbase {} {}\n",
        s.base.0,
        s.base.1.display()
    );
    for (h, p) in &s.patches {
        o.push_str(&format!("patch {h} {}\n", p.display()));
    }
    if let Some(r) = &s.result {
        o.push_str(&format!("result {r}\n"));
    }
    o
}

/// Rebuild the binary: the base and every patch read from `dir` and checked
/// against their SHA-256s, then each patch assembled and linked in order.
pub fn build(s: &Stack, dir: &Path) -> Result<Vec<u8>, String> {
    let read = |p: &Path| {
        std::fs::read(dir.join(p)).map_err(|e| format!("{}: {e}", dir.join(p).display()))
    };
    let mut bin = read(&s.base.1)?;
    if sha_hex(&bin) != s.base.0 {
        return Err(format!(
            "{}: SHA-256 {} is not the stack's base {}",
            s.base.1.display(),
            sha_hex(&bin),
            s.base.0
        ));
    }
    for (h, p) in &s.patches {
        let t = read(p)?;
        if &sha_hex(&t) != h {
            return Err(format!(
                "{}: SHA-256 {} is not the stack's {h}",
                p.display(),
                sha_hex(&t)
            ));
        }
        let text = String::from_utf8(t).map_err(|_| format!("{}: not UTF-8", p.display()))?;
        let o = crate::text::assemble(&text).map_err(|e| format!("{}: {e}", p.display()))?;
        let obj = crate::text::write_object(&o)?;
        bin = crate::link::link(&bin, &obj)
            .map_err(|e| format!("{}: link: {e}", p.display()))?
            .0;
    }
    Ok(bin)
}

/// The SHA-256 of a built binary, for the `result` line.
pub fn result_sha(bin: &[u8]) -> String {
    sha_hex(bin)
}

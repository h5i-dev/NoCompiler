//! Proof status per version (Q-VC3, docs/design/proof-status.md): a proofs
//! file records which theorems were proved about which binary, and `status`
//! says which of them still cover another build.
//!
//! The file, one record per line (a line starting with `#` is a comment;
//! names may hold `#`, as `module` names namesakes `f#k`); paths are relative
//! to the proofs file's directory:
//!
//! ```text
//! nocompiler-proofs 1
//! module SHA256 PATH            the binary the proofs are about
//! stack SHA256 PATH             or: a patch stack, SHA256 its result's
//! proof FUNCTION THEOREM SPEC closure KEY STATE
//! ```
//!
//! KEY is the function's closure key in that binary (`module::keys`). STATE
//! is `checked` (the Lean kernel accepted the theorem, or its reuse, about
//! that binary) or `by-key` (the closure key is unchanged from a binary where
//! it was proved, and nobody has checked the reuse). Only `checked` is ever
//! reported as proved: a key is an index, not evidence (docs/isa/ledger.md).

use crate::module::{self, Kind, Module};
use std::collections::{BTreeSet, HashMap};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum State {
    Checked,
    ByKey,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
    pub function: String,
    pub theorem: String,
    pub spec: String,
    pub closure: String,
    pub state: State,
}

/// What a proofs file is about: a binary, or a patch stack's result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Subject {
    Module(String, PathBuf),
    Stack(String, PathBuf),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proofs {
    pub subject: Subject,
    pub proofs: Vec<Proof>,
}

fn is_sha(s: &str) -> bool {
    s.len() == 64
        && s.bytes()
            .all(|c| c.is_ascii_hexdigit() && !c.is_ascii_uppercase())
}

/// Whether `text` is a proofs file (rather than `ledger --proofs`'s TSV).
pub fn is_proofs(text: &str) -> bool {
    text.lines()
        .map(str::trim)
        .find(|l| !l.is_empty() && !l.starts_with('#'))
        .is_some_and(|l| l.starts_with("nocompiler-proofs"))
}

/// Read a proofs file's text.
pub fn parse(text: &str) -> Result<Proofs, String> {
    let mut lines = text
        .lines()
        .enumerate()
        .map(|(i, l)| (i + 1, l.trim()))
        .filter(|(_, l)| !l.is_empty() && !l.starts_with('#'));
    match lines.next() {
        Some((_, "nocompiler-proofs 1")) => {}
        Some((n, l)) => return Err(format!("line {n}: `{l}`: want `nocompiler-proofs 1`")),
        None => return Err("empty proofs file".into()),
    }
    let (mut subject, mut proofs) = (None, Vec::<Proof>::new());
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
            ["module", s, p] if subject.is_none() => {
                subject = Some(Subject::Module(sha(s)?, PathBuf::from(p)))
            }
            ["stack", s, p] if subject.is_none() => {
                subject = Some(Subject::Stack(sha(s)?, PathBuf::from(p)))
            }
            ["proof", f, th, sp, "closure", k, st] if subject.is_some() => {
                let state = match st {
                    "checked" => State::Checked,
                    "by-key" => State::ByKey,
                    _ => return Err(format!("line {n}: `{st}`: want `checked` or `by-key`")),
                };
                if proofs.iter().any(|p| p.function == f && p.theorem == th) {
                    return Err(format!("line {n}: {th} about {f} listed twice"));
                }
                proofs.push(Proof {
                    function: f.into(),
                    theorem: th.into(),
                    spec: sp.into(),
                    closure: sha(k)?,
                    state,
                });
            }
            _ => {
                return Err(format!(
                    "line {n}: `{l}`: want `module SHA PATH` or `stack SHA PATH`, then `proof FUNCTION THEOREM SPEC closure KEY STATE` lines"
                ));
            }
        }
    }
    let subject = subject.ok_or("no `module` or `stack` line")?;
    Ok(Proofs { subject, proofs })
}

/// The file's text (`parse`'s inverse).
pub fn render(p: &Proofs) -> String {
    let mut o = String::from("nocompiler-proofs 1\n");
    let _ = match &p.subject {
        Subject::Module(s, f) => writeln!(o, "module {s} {}", f.display()),
        Subject::Stack(s, f) => writeln!(o, "stack {s} {}", f.display()),
    };
    for q in &p.proofs {
        let st = match q.state {
            State::Checked => "checked",
            State::ByKey => "by-key",
        };
        let _ = writeln!(
            o,
            "proof {} {} {} closure {} {st}",
            q.function, q.theorem, q.spec, q.closure
        );
    }
    o
}

/// The bytes of a binary or of a patch stack's rebuilt result, and whether
/// it was a stack. A stack is told by its first line.
pub fn load_bytes(path: &Path) -> Result<(Vec<u8>, bool), String> {
    let bytes = std::fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?;
    if !bytes.starts_with(b"nocompiler-stack") {
        return Ok((bytes, false));
    }
    let text = String::from_utf8(bytes).map_err(|_| format!("{}: not UTF-8", path.display()))?;
    let s = crate::stack::parse(&text).map_err(|e| format!("{}: {e}", path.display()))?;
    let bin = crate::stack::build(&s, path.parent().unwrap_or(Path::new(".")))?;
    Ok((bin, true))
}

/// The binary a proofs file is about, read from beside it and checked
/// against its SHA-256.
pub fn subject_bytes(p: &Proofs, proofs_path: &Path) -> Result<Vec<u8>, String> {
    let dir = proofs_path.parent().unwrap_or(Path::new("."));
    let (sha, path) = match &p.subject {
        Subject::Module(s, f) | Subject::Stack(s, f) => (s, dir.join(f)),
    };
    let (bytes, _) = load_bytes(&path)?;
    let got = crate::sha256::hex(&crate::sha256::digest(&bytes));
    if &got != sha {
        return Err(format!(
            "{}: SHA-256 {got} is not the proofs file's {sha}",
            path.display()
        ));
    }
    Ok(bytes)
}

/// What became of one proof in the new build.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Status {
    /// The closure key is unchanged, and so is every address the closure
    /// takes: `Verified.of_sub` carries the theorem once its side conditions
    /// are checked (`--lean`).
    Carries,
    /// The function's own canonical form changed (old and new SHA-256).
    Edited(String, String),
    /// Its own form is unchanged; this callee (the nearest changed one) is not.
    Callee(String),
    /// Not in the new build's module at all.
    Removed,
    /// The closure takes the address of data section D, whose contents
    /// changed. `Verified` does not depend on data (`Verified.of_sub` holds
    /// for any data), but a spec about those bytes would mean something
    /// else, so this is reported as a layout-dependent spec. In rustc
    /// builds, `.rodata` holds code addresses (vtables), which move with
    /// the code.
    Data(String),
    /// In the new build's `Module::skipped`, with the reason.
    Skipped(String),
    /// The closure takes the address of this symbol, which moved: a spec
    /// that names addresses would mean something else at the new layout.
    LayoutDependent(String),
}

impl Status {
    pub fn carries(&self) -> bool {
        *self == Status::Carries
    }
    pub fn invalidated(&self) -> bool {
        matches!(
            self,
            Status::Edited(..) | Status::Callee(_) | Status::Removed
        )
    }
    /// The status column.
    pub fn label(&self) -> String {
        match self {
            Status::Carries => "carries".into(),
            Status::Edited(..) => "invalidated: edited".into(),
            Status::Callee(c) => format!("invalidated: callee {c}"),
            Status::Removed => "invalidated: removed".into(),
            Status::Data(_) => "unknown: layout-dependent spec".into(),
            Status::Skipped(_) => "unknown: skipped".into(),
            Status::LayoutDependent(_) => "unknown: layout-dependent spec".into(),
        }
    }
    /// What follows the theorem's name on its line.
    pub fn detail(&self) -> String {
        let short = |s: &str| s[..s.len().min(8)].to_string();
        match self {
            Status::Edited(a, b) => format!("(sha256 {}.. -> {}..)", short(a), short(b)),
            Status::Skipped(r) => format!("({r})"),
            Status::LayoutDependent(s) => format!("(the address of {s} moved)"),
            Status::Data(d) => format!("(the contents of {d} changed)"),
            _ => String::new(),
        }
    }
}

/// The address of every symbol of a module: functions (skipped ones too)
/// and data sections.
fn addresses(m: &Module) -> HashMap<&str, u64> {
    m.funcs
        .iter()
        .map(|f| (f.name.as_str(), f.entry))
        .chain(m.skipped.iter().map(|f| (f.name.as_str(), f.entry)))
        .chain(m.data.iter().map(|d| (d.name.as_str(), d.addr)))
        .collect()
}

/// Each proof's status in `new`, the proofs being about `old`. An error if a
/// proof's function is not in `old`'s module or its key is not `old`'s.
pub fn status(old: &Module, new: &Module, proofs: &Proofs) -> Result<Vec<Status>, String> {
    let (ko, kn) = (module::keys(old), module::keys(new));
    let (ao, an) = (addresses(old), addresses(new));
    let idx: HashMap<&str, usize> = old
        .funcs
        .iter()
        .enumerate()
        .map(|(i, f)| (f.name.as_str(), i))
        .collect();
    let data_n: HashMap<&str, &module::RData> =
        new.data.iter().map(|d| (d.name.as_str(), d)).collect();
    let data_o: HashMap<&str, &module::RData> =
        old.data.iter().map(|d| (d.name.as_str(), d)).collect();
    let mut out = Vec::new();
    for p in &proofs.proofs {
        let f = p.function.as_str();
        let Some(&i) = idx.get(f) else {
            return Err(format!(
                "{f}: not in the module of the proofs file's binary"
            ));
        };
        if ko[f].1 != p.closure {
            return Err(format!(
                "{f}: closure key {} in the proofs file, {} in its binary",
                p.closure, ko[f].1
            ));
        }
        if let Some(s) = new.skipped.iter().find(|s| s.name == f) {
            out.push(Status::Skipped(s.reason.replace('\n', " ")));
            continue;
        }
        let Some(nk) = kn.get(f) else {
            out.push(Status::Removed);
            continue;
        };
        if nk.0 != ko[f].0 {
            // The same words and relocations but for the target of some
            // calls: the code is unchanged, what it calls is not. A patch
            // stack does this to every caller of a replaced function, whose
            // calls now reach the jump at its old entry, under another name.
            let g = &new.funcs[new.funcs.iter().position(|g| g.name == f).expect("keyed")];
            let o = &old.funcs[i];
            let retargeted = g.words == o.words
                && g.relocs.len() == o.relocs.len()
                && g.relocs.iter().zip(&o.relocs).all(|(a, b)| {
                    a.sym == b.sym
                        || (a.kind == Kind::Call && b.kind == Kind::Call && {
                            let (mut a, mut b) = (a.clone(), b.clone());
                            a.sym.clear();
                            b.sym.clear();
                            a == b
                        })
                });
            let first = o
                .relocs
                .iter()
                .zip(&g.relocs)
                .find(|(a, b)| a.sym != b.sym)
                .map(|(a, _)| a.sym.clone());
            out.push(match (retargeted, first) {
                (true, Some(x)) => Status::Callee(x),
                _ => Status::Edited(ko[f].0.clone(), nk.0.clone()),
            });
            continue;
        }
        // The closure in breadth-first order from `f`, so the nearest changed
        // callee is named.
        let mut order = vec![i];
        let mut seen: BTreeSet<usize> = order.iter().copied().collect();
        let mut k = 0;
        while k < order.len() {
            for r in &old.funcs[order[k]].relocs {
                if r.kind == Kind::Call {
                    if let Some(&j) = idx.get(r.sym.as_str()) {
                        if seen.insert(j) {
                            order.push(j);
                        }
                    }
                }
            }
            k += 1;
        }
        if nk.1 != ko[f].1 {
            let changed = order
                .iter()
                .map(|&j| old.funcs[j].name.as_str())
                .find(|g| kn.get(*g).is_none_or(|k| k.0 != ko[*g].0));
            // Equal own forms give equal call targets, so some callee differs.
            out.push(Status::Callee(changed.unwrap_or("?").to_string()));
            continue;
        }
        // Every address the closure takes (not a call), and the data it reads.
        let mut st = Status::Carries;
        'scan: for &j in &order {
            for r in &old.funcs[j].relocs {
                if r.kind != Kind::PcrelHi {
                    continue;
                }
                let s = r.sym.as_str();
                if let (Some(a), Some(b)) = (data_o.get(s), data_n.get(s)) {
                    if a.bytes != b.bytes || a.zero != b.zero || a.writable != b.writable {
                        st = Status::Data(s.to_string());
                        break 'scan;
                    }
                }
                if ao.get(s) != an.get(s) {
                    st = Status::LayoutDependent(s.to_string());
                    break 'scan;
                }
            }
        }
        out.push(st);
    }
    Ok(out)
}

/// The Lean file `status --lean` writes: both modules in chunks (namespaces
/// `{ns}.Old` and `{ns}.New`), then `module::reuse_lean_for`'s theorems for
/// the functions in `only`, in namespace `ns`.
pub fn lean(
    old: &Module,
    new: &Module,
    ns: &str,
    form: module::ReuseForm,
    only: &BTreeSet<String>,
    sources: (&str, &str),
    shas: (&str, &str),
) -> Result<String, String> {
    let body = |t: &str| -> String {
        // Drop the header comment and imports of a generated file.
        let t = t
            .split_once("import NoCompiler.ModuleChunks\n")
            .map_or(t, |x| x.1);
        t.lines()
            .filter(|l| !l.starts_with("import "))
            .collect::<Vec<_>>()
            .join("\n")
            + "\n"
    };
    let (on, nn) = (format!("{ns}.Old"), format!("{ns}.New"));
    let mut o = format!(
        "/-\nGenerated by `nocompiler status --lean` {}; do not edit.\nOld: {} (SHA-256 {})\nNew: {} (SHA-256 {})\n-/\nimport NoCompiler.ModuleChunks\n",
        env!("CARGO_PKG_VERSION"),
        sources.0,
        shas.0,
        sources.1,
        shas.1
    );
    o += &body(&module::lean_chunks(old, &on, sources.0, shas.0)?);
    o += &body(&module::lean_chunks(new, &nn, sources.1, shas.1)?);
    let (r, _, _) = module::reuse_lean_for(old, new, &on, &nn, ns, form, Some(only));
    let r = r.split_once("-/\n").map_or(r.as_str(), |x| x.1);
    o += &body(r);
    Ok(o)
}

/// The index `reuse_lean` gives `function`'s theorem (`r_i`) in `old`.
pub fn reuse_index(old: &Module, function: &str) -> Option<usize> {
    old.funcs.iter().position(|f| f.name == function)
}

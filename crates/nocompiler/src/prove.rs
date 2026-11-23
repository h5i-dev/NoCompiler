//! `nocompiler prove ELF`: one command from a binary to its theorems and a report of what
//! was not proved, and why (round 5, item 5). Thin: it runs what exists, in order:
//!
//! 0. `lake build NoCompiler` (the library the image and the generator import);
//! 1. the profile check (each function's level, and the first violation of one below L1);
//! 2. the chunk export and its compiled image (`lean/NoCompiler/VC/Bench/Art.py ELF WORK 0`);
//! 3. the generator (`Prove.py WORK 0 --specs ... --calls --loops`): one `VerifiedImg`
//!    theorem per function it can take, at the first specification that proves it;
//! 4. the report: `WORK/REPORT.md` and `WORK/report.json`, one row per function: proved (by
//!    which specification), failed (the generator's error), or not attempted (why).
//!
//! Composition into a whole-process theorem (round 5, item 2) is not a step yet.
//!
//! The scripts are found under the repository (`--root`, `NOCOMPILER_ROOT`, or where this
//! binary was built from), and `lake` on `PATH` gives the Lean environment.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;

pub struct Options {
    pub work: PathBuf,
    pub specs: String,
    pub jobs: usize,
    pub root: Option<PathBuf>,
    /// Only these functions (export identifiers) and their callees; every function when empty.
    pub only: Vec<String>,
}

/// One function's outcome.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    Proved { spec: String },
    Failed { reason: String },
    NotAttempted { reason: String },
}

pub struct Row {
    pub name: String,
    pub instrs: u64,
    pub level: String,
    pub outcome: Outcome,
    /// For a proved function: the module and the theorem (`WORK/Q<k>_<spec>.lean`, `Art.Q<k>.safe`).
    pub theorem: Option<(String, String)>,
}

fn root(o: &Options) -> PathBuf {
    o.root
        .clone()
        .or_else(|| std::env::var_os("NOCOMPILER_ROOT").map(PathBuf::from))
        .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../.."))
}

fn run(cmd: &mut Command, log: &Path) -> Result<(), String> {
    let out = cmd.output().map_err(|e| format!("{cmd:?}: {e}"))?;
    let mut text = String::from_utf8_lossy(&out.stdout).into_owned();
    text.push_str(&String::from_utf8_lossy(&out.stderr));
    std::fs::write(log, &text).map_err(|e| format!("{}: {e}", log.display()))?;
    if !out.status.success() {
        let tail: Vec<&str> = text.lines().rev().take(5).collect();
        return Err(format!(
            "{} failed (log {}): {}",
            cmd.get_program().to_string_lossy(),
            log.display(),
            tail.into_iter().rev().collect::<Vec<_>>().join(" | ")
        ));
    }
    Ok(())
}

/// The rows of a run, from the profile check and the generator's two tables.
pub fn rows(
    check: &[(String, u64, String)],
    selection: &str,
    results: &str,
    proved: &str,
) -> Vec<Row> {
    let mut thm: BTreeMap<String, (String, String)> = BTreeMap::new();
    for l in proved.lines() {
        if let [n, _, m, t] = l.split('\t').collect::<Vec<_>>()[..] {
            thm.insert(n.to_string(), (m.to_string(), t.to_string()));
        }
    }
    // The generator's names are the export's identifiers; match by name.
    let mut sel: BTreeMap<String, String> = BTreeMap::new();
    for l in selection.lines() {
        let c: Vec<&str> = l.split('\t').collect();
        if let [n, _, why] = c[..] {
            sel.insert(n.to_string(), why.to_string());
        }
    }
    // rows.tsv has a row per specification tried; the function's outcome is a success if any,
    // else its last error.
    let mut res: BTreeMap<String, Outcome> = BTreeMap::new();
    for l in results.lines() {
        let c: Vec<&str> = l.split('\t').collect();
        let [n, _, spec, rc, err] = c[..] else {
            continue;
        };
        if matches!(res.get(n), Some(Outcome::Proved { .. })) {
            continue;
        }
        let o = if rc == "0" {
            Outcome::Proved { spec: spec.into() }
        } else {
            let e = err.trim();
            Outcome::Failed {
                reason: if rc == "124" {
                    "timeout (300 s)".into()
                } else if e.is_empty() {
                    format!("exit {rc}")
                } else {
                    e.splitn(2, "error: ").last().unwrap_or(e).to_string()
                },
            }
        };
        res.insert(n.to_string(), o);
    }
    check
        .iter()
        .map(|(name, instrs, level)| {
            let id = crate::lean::ident(name);
            let outcome = match (res.get(&id), sel.get(&id)) {
                (Some(o), _) => o.clone(),
                (None, Some(why)) if why == "attempted" => Outcome::Failed {
                    reason: "attempted, no result (the generator stopped)".into(),
                },
                (None, Some(why)) => Outcome::NotAttempted {
                    reason: why.trim_start_matches("not attempted: ").to_string(),
                },
                (None, None) => Outcome::NotAttempted {
                    reason: "not exported".into(),
                },
            };
            let theorem = match outcome {
                Outcome::Proved { .. } => thm.get(&id).cloned(),
                _ => None,
            };
            Row {
                name: name.clone(),
                instrs: *instrs,
                level: level.clone(),
                outcome,
                theorem,
            }
        })
        .collect()
}

/// The report as Markdown: totals, then reasons by count, then every function.
pub fn markdown(file: &str, rows: &[Row]) -> String {
    let mut o = String::new();
    let proved = rows
        .iter()
        .filter(|r| matches!(r.outcome, Outcome::Proved { .. }))
        .count();
    let _ = writeln!(o, "# nocompiler prove {file}\n");
    let _ = writeln!(
        o,
        "{proved} of {} functions proved automatically ({} of {} instructions).\n",
        rows.len(),
        rows.iter()
            .filter(|r| matches!(r.outcome, Outcome::Proved { .. }))
            .map(|r| r.instrs)
            .sum::<u64>(),
        rows.iter().map(|r| r.instrs).sum::<u64>()
    );
    let mut why: BTreeMap<String, Vec<&Row>> = BTreeMap::new();
    for r in rows {
        let k = match &r.outcome {
            Outcome::Proved { spec } => format!("proved ({spec})"),
            Outcome::Failed { reason } => format!("failed: {}", short(reason)),
            Outcome::NotAttempted { reason } => format!("not attempted: {reason}"),
        };
        why.entry(k).or_default().push(r);
    }
    let mut ks: Vec<_> = why.iter().collect();
    ks.sort_by_key(|(k, v)| (!k.starts_with("proved"), std::cmp::Reverse(v.len())));
    let _ = writeln!(o, "| outcome | functions | e.g. |\n| --- | --- | --- |");
    for (k, v) in ks {
        let _ = writeln!(o, "| {k} | {} | `{}` |", v.len(), v[0].name);
    }
    let _ = writeln!(
        o,
        "\n| function | instructions | level | outcome |\n| --- | --- | --- | --- |"
    );
    for r in rows {
        let out = match &r.outcome {
            Outcome::Proved { spec } => match &r.theorem {
                Some((m, t)) => format!("proved ({spec}): `{t}` in {m}"),
                None => format!("proved ({spec})"),
            },
            Outcome::Failed { reason } => format!("failed: {}", short(reason)),
            Outcome::NotAttempted { reason } => format!("not attempted: {reason}"),
        };
        let _ = writeln!(o, "| `{}` | {} | {} | {out} |", r.name, r.instrs, r.level);
    }
    o
}

fn short(s: &str) -> String {
    let s = s.replace('|', "/");
    if s.chars().count() > 90 {
        s.chars().take(90).collect::<String>() + "..."
    } else {
        s
    }
}

pub fn json(rows: &[Row]) -> String {
    let q = crate::cmd::json_str;
    let items: Vec<String> = rows
        .iter()
        .map(|r| {
            let (kind, detail) = match &r.outcome {
                Outcome::Proved { spec } => ("proved", spec),
                Outcome::Failed { reason } => ("failed", reason),
                Outcome::NotAttempted { reason } => ("not_attempted", reason),
            };
            format!(
                "{{\"name\":{},\"instructions\":{},\"level\":{},\"outcome\":{},\"detail\":{},\"theorem\":{}}}",
                q(&r.name),
                r.instrs,
                q(&r.level),
                q(kind),
                q(detail),
                r.theorem.as_ref().map_or("null".to_string(), |(m, t)| {
                    format!("{{\"module\":{},\"name\":{}}}", q(m), q(t))
                })
            )
        })
        .collect();
    format!("[\n{}\n]\n", items.join(",\n"))
}

/// The whole pipeline.
pub fn prove(elf: &Path, o: &Options, out: &mut String) -> Result<Vec<Row>, String> {
    let bytes = std::fs::read(elf).map_err(|e| format!("{}: {e}", elf.display()))?;
    let bin = crate::load(&bytes)?;
    let check: Vec<(String, u64, String)> = bin
        .check()
        .into_iter()
        .map(|r| {
            let n = bin
                .funcs
                .iter()
                .find(|f| f.entry == r.entry)
                .map_or(0, |f| f.words.len() as u64);
            let level = match (&r.level, &r.result) {
                (Some(l), Ok(_)) => format!("{l:?}"),
                (l, Err(vs)) => format!(
                    "{} ({})",
                    l.map_or("below L0".to_string(), |l| format!("{l:?}")),
                    vs.first()
                        .map_or(String::new(), |v| format!("{} {}", v.rule, v.detail))
                ),
                (None, Ok(_)) => "?".into(),
            };
            (r.name, n, level)
        })
        .collect();
    let conform = check.iter().filter(|c| !c.2.contains('(')).count();
    let _ = writeln!(
        out,
        "1. check: {conform} of {} functions at L1 or above",
        check.len()
    );
    std::fs::create_dir_all(&o.work).map_err(|e| format!("{}: {e}", o.work.display()))?;
    let work = std::fs::canonicalize(&o.work).map_err(|e| format!("{}: {e}", o.work.display()))?;
    let elf = std::fs::canonicalize(elf).map_err(|e| format!("{}: {e}", elf.display()))?;
    let root = root(o);
    let bench = root.join("lean/NoCompiler/VC/Bench");
    // The library the image and the generator import: built first, since a checkout that was
    // just pulled may be ahead of its .olean files (nothing to do when they are current).
    run(
        Command::new("lake")
            .args(["build", "NoCompiler"])
            .current_dir(root.join("lean")),
        &work.join("lake.log"),
    )?;
    let exe = std::env::current_exe().map_err(|e| e.to_string())?;
    run(
        Command::new("python3")
            .arg("-I")
            .arg(bench.join("Art.py"))
            .arg(&elf)
            .arg(&work)
            .arg("0")
            .env("NOCOMPILER", &exe),
        &work.join("art.log"),
    )?;
    let _ = writeln!(
        out,
        "2. export: {} (compiled to ArtImg.olean)",
        work.join("Art.lean").display()
    );
    let mut only = Vec::new();
    if !o.only.is_empty() {
        let list = work.join("only.txt");
        let ids: Vec<String> = o.only.iter().map(|n| crate::lean::ident(n)).collect();
        std::fs::write(&list, ids.join("\n") + "\n").map_err(|e| e.to_string())?;
        only = vec!["--only".to_string(), list.to_string_lossy().into_owned()];
    }
    let _ = std::fs::remove_file(work.join("rows.tsv"));
    let _ = std::fs::remove_file(work.join("proved.tsv"));
    run(
        Command::new("python3")
            .arg("-I")
            .arg(bench.join("Prove.py"))
            .arg(&work)
            .arg("0")
            .args([
                "--specs",
                &o.specs,
                "--calls",
                "--loops",
                "--jobs",
                &o.jobs.to_string(),
            ])
            .args(&only),
        &work.join("prove.log"),
    )?;
    let read = |f: &str| std::fs::read_to_string(work.join(f)).unwrap_or_default();
    let rows = rows(
        &check,
        &read("selection.tsv"),
        &read("rows.tsv"),
        &read("proved.tsv"),
    );
    let name = elf
        .file_name()
        .map_or(String::new(), |s| s.to_string_lossy().into_owned());
    let md = markdown(&name, &rows);
    std::fs::write(work.join("REPORT.md"), &md).map_err(|e| e.to_string())?;
    std::fs::write(work.join("report.json"), json(&rows)).map_err(|e| e.to_string())?;
    let proved = rows
        .iter()
        .filter(|r| matches!(r.outcome, Outcome::Proved { .. }))
        .count();
    let _ = writeln!(
        out,
        "3. generator: {proved} of {} functions proved (theorems in {})",
        rows.len(),
        work.display()
    );
    let _ = writeln!(out, "4. report: {}", work.join("REPORT.md").display());
    Ok(rows)
}

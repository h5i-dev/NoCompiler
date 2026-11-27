//! Collect untrusted certificates from compiled Lean evaluation and render the
//! per-point kernel checks used by the proof command.
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Write as _,
    fs::{self, File},
    path::Path,
    process::{Command, Stdio},
    time::{Duration, Instant},
};

const TAG_STRIDE: usize = 1_000_000;
const ENTRY: usize = TAG_STRIDE - 1;
const DEPTH: &str = "set_option maxRecDepth 100000 in";

#[derive(Default)]
struct Table {
    certificates: Vec<String>,
    splits: Vec<String>,
    entails: Vec<String>,
}

impl Table {
    fn render(&self) -> String {
        format!(
            ".table [{}] [{}] [{}]",
            self.certificates.join(", "),
            self.splits.join(", "),
            self.entails.join(", ")
        )
    }
}

fn functions(input: &str) -> Result<Vec<(&str, usize)>, String> {
    let mut found = Vec::new();
    let mut name = None;
    for line in input.lines() {
        if let Some(f) = line
            .strip_prefix("def fn_")
            .and_then(|s| s.strip_suffix(" : Fn where"))
        {
            if name.replace(f).is_some() {
                return Err("certgen: function has no declared size".into());
            }
        } else if let Some(size) = line.strip_prefix("  size := ")
            && let Some(f) = name.take()
        {
            let n = size
                .parse::<usize>()
                .map_err(|_| format!("certgen: invalid size for {f}"))?;
            if n > ENTRY {
                return Err(format!(
                    "certgen: instruction count exceeds tag space for {f}"
                ));
            }
            found.push((f, n));
        }
    }
    if name.is_some() || found.is_empty() {
        return Err("certgen: no complete function records".into());
    }
    Ok(found)
}

fn logging_module(input: &str, funcs: &[(&str, usize)]) -> String {
    let mut out = input.to_owned();
    for (i, (f, _)) in funcs.iter().enumerate() {
        let tag = i * TAG_STRIDE;
        let _ = write!(
            out,
            r#"
def fnlog_{f} : Fn :=
  {{ fn_{f} with
    types := fn_{f}.types.map (fun p => (p.1, {{ p.2 with certs := .log ({tag} + p.1) }})),
    entryCerts := .log {entry} }}

#eval show IO Unit from do
  let t ← IO.monoMsNow
  let z := t - t
  IO.println s!"DONE {f} {{fnlog_{f}.structOk && fnlog_{f}.edge none fnlog_{f}.initTy z}} {{(List.range fnlog_{f}.size).map (fun k => fnlog_{f}.instr code (k + z))}}"
"#,
            entry = tag + ENTRY
        );
    }
    out
}

fn short(text: &str) -> String {
    text.replace("NoCompiler.Typed.", "")
}

enum Hint {
    Certificate(String),
    Split(String),
    Entails(String),
}

fn parse_hint(line: &str) -> Option<(usize, Hint)> {
    let mut parts = line.splitn(3, ' ');
    let kind = parts.next()?;
    let tag = parts.next()?.parse().ok()?;
    let body = parts.next()?;
    let hint = match kind {
        "CERT" => {
            let (count, content) = body.split_once(' ')?;
            let mut pieces = content.split(" ::: ");
            let (goal, keep, cert) = (pieces.next()?, pieces.next()?, pieces.next()?);
            if pieces.next().is_some() || !cert.trim_end().ends_with(']') {
                return None;
            }
            Hint::Certificate(format!("({}, {count}, {keep}, {cert})", short(goal)))
        }
        "SPLIT" => {
            let (index, rest) = body.split_once(' ')?;
            let (split, goal) = rest.split_at(rest.find(']')? + 1);
            Hint::Split(format!(
                "({}, {index}, {})",
                short(goal.trim_start()),
                short(split)
            ))
        }
        "ENT" => Hint::Entails(short(body)),
        _ => return None,
    };
    Some((tag, hint))
}

fn read_tables(output: &str, funcs: &[(&str, usize)]) -> Vec<BTreeMap<usize, Table>> {
    let mut tables: Vec<_> = (0..funcs.len()).map(|_| BTreeMap::new()).collect();
    let mut seen: Vec<BTreeSet<(usize, u8, String)>> =
        (0..funcs.len()).map(|_| BTreeSet::new()).collect();
    for line in output.lines() {
        let Some((tag, hint)) = parse_hint(line) else {
            continue;
        };
        let (function, point) = (tag / TAG_STRIDE, tag % TAG_STRIDE);
        let Some((_, size)) = funcs.get(function) else {
            continue;
        };
        if point != ENTRY && point >= *size {
            continue;
        }
        let (tag, text) = match hint {
            Hint::Certificate(text) => (0, text),
            Hint::Split(text) => (1, text),
            Hint::Entails(text) => (2, text),
        };
        if seen[function].insert((point, tag, text.clone())) {
            let table: &mut Table = tables[function].entry(point).or_default();
            match tag {
                0 => table.certificates.push(text),
                1 => table.splits.push(text),
                _ => table.entails.push(text),
            }
        }
    }
    tables
}

fn write_function(out: &mut String, f: &str, size: usize, tables: &BTreeMap<usize, Table>) {
    let mut rows = Vec::new();
    for (point, table) in tables.iter().filter(|(point, _)| **point != ENTRY) {
        let _ = writeln!(
            out,
            "set_option maxHeartbeats 0 in\ndef certs_{f}_{point} : CertMode := {}\n",
            table.render()
        );
        rows.push(format!("({point}, certs_{f}_{point})"));
    }
    let _ = write!(
        out,
        r#"
def certs_{f} : List (Nat × CertMode) := [{rows}]

def fnc_{f} : Fn :=
  {{ fn_{f} with
    types := fn_{f}.types.map (fun p => (p.1, {{ p.2 with certs := (certs_{f}.lookup p.1).getD (.table []) }})),
    entryCerts := {entry} }}

{DEPTH}
theorem chk_{f}_s : (fnc_{f}.structOk && fnc_{f}.edge none fnc_{f}.initTy 0) = true := by
  decide +kernel
"#,
        rows = rows.join(", "),
        entry = tables
            .get(&ENTRY)
            .map_or_else(|| Table::default().render(), Table::render),
    );
    for point in 0..size {
        let _ = writeln!(
            out,
            "\n{DEPTH}\ntheorem chk_{f}_{point} : fnc_{f}.instr code {point} = true := by decide +kernel"
        );
    }
    let _ = write!(
        out,
        "\n{DEPTH}\ntheorem chk_{f} : fnc_{f}.check code = true :=\n  Fn.check_of_parts_n _ (n := {size}) rfl chk_{f}_s "
    );
    for _ in 0..size {
        out.push_str("(rangeAll_succ ");
    }
    let _ = write!(out, "(rangeAll_zero (fnc_{f}.instr code))");
    for point in 0..size {
        let _ = write!(out, " chk_{f}_{point})");
    }
    let _ = writeln!(out, "\n\n#print axioms chk_{f}\n");
}

fn write_program(out: &mut String, input: &str) -> Result<(), String> {
    let entries = input
        .lines()
        .find_map(|line| {
            line.strip_prefix("def prog : List Fn := [")?
                .strip_suffix(']')
        })
        .ok_or("certgen: no program definition")?;
    let funcs: Vec<_> = entries
        .split(',')
        .map(|name| {
            name.trim()
                .strip_prefix("fn_")
                .ok_or("certgen: malformed program entry")
        })
        .collect::<Result<_, _>>()?;
    let instances = funcs
        .iter()
        .map(|name| format!("fnc_{name}"))
        .collect::<Vec<_>>()
        .join(", ");
    let checks = funcs
        .iter()
        .map(|name| format!("chk_{name}"))
        .collect::<Vec<_>>()
        .join(", ");
    let external = input.lines().any(|line| line.starts_with("def ext : Env"));
    let environment = if external { "ext" } else { "[]" };
    let _ = write!(
        out,
        r#"
def progc : List Fn := [{instances}]

{DEPTH}
theorem prog_checked : Prog.check code {environment} progc = true := by
  simp only [progc, Prog.check, {checks}, Bool.true_and]
  decide +kernel
"#
    );
    if external {
        out.push_str(
            r#"
theorem prog_meets_rel (T : TokEnv) (hE : ∀ e ∈ ext, Meets code e.2.2 e.1 T e.2.1) :
    ∀ e ∈ Prog.env ext progc, Meets code e.2.2 e.1 T e.2.1 :=
  Prog.check_sound progc ext hE prog_checked

#print axioms prog_meets_rel
"#,
        );
    } else {
        out.push_str(
            r#"
theorem prog_meets (T : TokEnv) :
    ∀ e ∈ Prog.env [] progc, Meets code e.2.2 e.1 T e.2.1 :=
  Prog.check_sound_closed prog_checked

#print axioms prog_meets
"#,
        );
    }
    Ok(())
}

pub fn generate(lean_dir: &Path, input: &str) -> Result<String, String> {
    let input = input.split_once("\n#eval").map_or(input, |(base, _)| base);
    if !input
        .lines()
        .any(|line| line.starts_with("def code : Code"))
    {
        return Err("certgen: no linked code definition".into());
    }
    let funcs = functions(input)?;
    let output =
        evaluate(lean_dir, &logging_module(input, &funcs)).map_err(|e| format!("certgen: {e}"))?;
    let tables = read_tables(&output, &funcs);
    let mut module = input.to_string();
    module.push('\n');
    for ((function, size), tables) in funcs.into_iter().zip(tables) {
        write_function(&mut module, function, size, &tables);
    }
    write_program(&mut module, input)?;
    Ok(module)
}

fn evaluate(lean_dir: &Path, module: &str) -> Result<String, Box<dyn std::error::Error>> {
    let tmp = tempfile::Builder::new()
        .prefix("nocompiler-cert-")
        .tempdir()?;
    let lean = tmp.path().join("Log.lean");
    let stdout = tmp.path().join("stdout");
    let stderr = tmp.path().join("stderr");
    fs::write(&lean, module)?;
    let mut command = if let Some(mem) = std::env::var("CERTGEN_MEM").ok().filter(|s| !s.is_empty())
    {
        let mut command = Command::new("systemd-run");
        command.args([
            "--user",
            "--scope",
            "--quiet",
            "-p",
            &format!("MemoryMax={mem}"),
            "-p",
            "MemorySwapMax=0",
            "lake",
        ]);
        command
    } else {
        Command::new("lake")
    };
    let timeout = match std::env::var("LEAN_TIMEOUT") {
        Ok(value) => Duration::from_secs(value.parse()?),
        Err(_) => Duration::from_secs(900),
    };
    let mut child = command
        .arg("lean")
        .arg(lean)
        .current_dir(lean_dir)
        .stdout(Stdio::from(File::create(&stdout)?))
        .stderr(Stdio::from(File::create(&stderr)?))
        .spawn()?;
    let start = Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait()? {
            break status;
        }
        if start.elapsed() >= timeout {
            let _ = child.kill();
            let _ = child.wait();
            return Err(format!(
                "Lean certificate collection timed out after {}s",
                timeout.as_secs()
            )
            .into());
        }
        std::thread::sleep(Duration::from_millis(50));
    };
    let output = format!(
        "{}\n{}",
        fs::read_to_string(stdout)?,
        fs::read_to_string(stderr)?
    );
    if let Some(error) = output.lines().find(|line| line.contains(": error")) {
        return Err(error.into());
    }
    if !status.success() {
        return Err(format!("Lean certificate collection {status}").into());
    }
    // A failed search for one point is not evidence. Keep its partial log;
    // the generated kernel theorem independently rejects any missing facts.
    Ok(output)
}

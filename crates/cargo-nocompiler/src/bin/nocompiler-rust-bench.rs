use clap::Parser;
use serde::Deserialize;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs::{self, File},
    path::{Path, PathBuf},
    process::{Command, ExitCode, Stdio},
    time::Instant,
};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error + Send + Sync>>;

#[derive(Parser)]
#[command(about = "Measure a pinned selection of Rust functions on RV64")]
struct Args {
    #[arg(long, default_value = "benchmarks/rust/manifest.json")]
    manifest: PathBuf,
    #[arg(long)]
    artifacts: PathBuf,
    #[arg(long)]
    checker: Option<PathBuf>,
    #[arg(long, default_value_t = 2, value_parser = clap::value_parser!(u64).range(1..=32))]
    jobs: u64,
    #[arg(long, default_value_t = 600, value_parser = clap::value_parser!(u64).range(1..))]
    timeout_secs: u64,
    #[arg(long)]
    no_mir_hints: bool,
    #[arg(long)]
    llvm_hints: bool,
    #[arg(long, default_value = "release")]
    profile: String,
    #[arg(long)]
    chc_solver: Option<PathBuf>,
    #[arg(long = "run")]
    run_ids: Vec<String>,
}

#[derive(Deserialize)]
struct Manifest {
    schema_version: u32,
    target: String,
    candidates: Vec<Candidate>,
    runs: Vec<Run>,
}

#[derive(Deserialize)]
struct Candidate {
    name: String,
    category: String,
    priority: bool,
}

#[derive(Deserialize)]
struct Run {
    id: String,
    manifest: PathBuf,
    binary: String,
    #[serde(rename = "crate")]
    package: Option<String>,
    version: Option<String>,
    track: String,
    targets: Vec<Target>,
}

#[derive(Deserialize)]
struct Target {
    function: String,
    source: String,
    kind: String,
    variant: Option<String>,
}

fn measure(run: &Run, root: &Path, base: &Path, checker: &Path, args: &Args) -> Result<Value> {
    let dir = root.join(&run.id);
    let crate_manifest = base.join(&run.manifest).canonicalize()?;
    let lock = fs::read(crate_manifest.with_file_name("Cargo.lock"))?;
    let lock_digest = format!("{:x}", Sha256::digest(&lock));
    let log_path = root.join(format!("{}.log", run.id));
    let log = File::create(&log_path)?;
    let elapsed = Instant::now();
    let mut command = Command::new("timeout");
    command
        .args(["--kill-after=5s", &format!("{}s", args.timeout_secs)])
        .arg(checker)
        .args([
            "check",
            "--locked",
            "--allow-assumptions",
            "--manifest-path",
        ])
        .arg(&crate_manifest)
        .args(["--profile", &args.profile])
        .args(["--bin", &run.binary, "--artifacts"])
        .arg(&dir)
        .stdout(Stdio::from(log.try_clone()?))
        .stderr(Stdio::from(log));
    if args.no_mir_hints {
        command.arg("--no-mir-hints");
    }
    if args.llvm_hints {
        command.arg("--llvm-hints");
    }
    if let Some(solver) = &args.chc_solver {
        command.arg("--chc-solver").arg(solver);
    }
    for target in &run.targets {
        command.args(["--function", &target.function]);
    }
    let status = command.status()?.code();
    let report = match fs::read(dir.join("report.json")) {
        Ok(data) => serde_json::from_slice::<Value>(&data)?,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Value::Null,
        Err(error) => return Err(error.into()),
    };
    let elapsed_ms = elapsed.elapsed().as_millis();
    let built = dir.join("verified.elf").is_file();
    let missing = match status {
        Some(124 | 137) => "timeout",
        _ if !built && fs::read_to_string(log_path)?.contains("Cargo build exit status") => {
            "compilation_failure"
        }
        _ => "tool_error",
    };
    let targets: Vec<_> = run.targets.iter().map(|target| {
        let result = &report["functions"][&target.function];
        json!({
            "function": target.function, "source": target.source, "kind": target.kind,
            "variant": target.variant,
            "result": if result.is_null() { json!({"status": missing}) } else { result.clone() },
        })
    }).collect();
    Ok(json!({
        "run": run.id, "crate": run.package, "version": run.version, "track": run.track,
        "elapsed_ms": elapsed_ms, "exit_code": status, "built": built,
        "cargo_lock_sha256": lock_digest,
        "rustc_version": report["rustc_version"], "elf_sha256": report["elf_sha256"],
        "proof_attempt": report["proof_attempt"], "targets": targets,
        "timing_ms": report["timing_ms"], "llvm_result_fallbacks": report["llvm_result_fallbacks"],
    }))
}

fn verdicts(runs: &[Value]) -> impl Iterator<Item = (&Value, &Value)> {
    runs.iter().flat_map(|run| {
        run["targets"]
            .as_array()
            .unwrap()
            .iter()
            .map(move |row| (run, row))
    })
}

fn run(args: Args) -> Result<bool> {
    let frozen = fs::read(&args.manifest)?;
    let manifest: Manifest = serde_json::from_slice(&frozen)?;
    if manifest.schema_version != 1 || manifest.target != "riscv64imac-unknown-none-elf" {
        return Err("unsupported manifest schema or target".into());
    }
    let registry: BTreeMap<_, _> = manifest
        .candidates
        .iter()
        .map(|entry| (&entry.name, entry))
        .collect();
    let mut ids = BTreeSet::new();
    if registry.len() != manifest.candidates.len()
        || manifest.runs.is_empty()
        || manifest.runs.iter().any(|run| {
            run.id.is_empty()
                || !run
                    .id
                    .bytes()
                    .all(|b| b.is_ascii_alphanumeric() || b == b'-')
                || !ids.insert(&run.id)
                || run.targets.is_empty()
                || run
                    .targets
                    .iter()
                    .map(|target| &target.function)
                    .collect::<BTreeSet<_>>()
                    .len()
                    != run.targets.len()
                || run
                    .package
                    .as_ref()
                    .is_some_and(|name| !registry.contains_key(name) || run.version.is_none())
        })
    {
        return Err("invalid candidate registry or benchmark runs".into());
    }
    if args.run_ids.iter().any(|id| !ids.contains(id)) {
        return Err("unknown --run identifier".into());
    }
    let selected: Vec<_> = manifest
        .runs
        .iter()
        .filter(|run| args.run_ids.is_empty() || args.run_ids.contains(&run.id))
        .collect();
    let checker = match &args.checker {
        Some(path) => path.canonicalize()?,
        None => std::env::current_exe()?
            .with_file_name("cargo-nocompiler")
            .canonicalize()?,
    };
    fs::create_dir(&args.artifacts)?;
    let root = args.artifacts.canonicalize()?;
    let manifest_path = args.manifest.canonicalize()?;
    let base = manifest_path.parent().ok_or("manifest has no parent")?;
    fs::write(root.join("manifest.json"), frozen)?;
    let checker_digest = format!("{:x}", Sha256::digest(fs::read(&checker)?));
    let suite_started = Instant::now();
    let next = std::sync::atomic::AtomicUsize::new(0);
    let mut results = std::thread::scope(|scope| {
        let workers: Vec<_> = (0..selected.len().min(args.jobs as usize))
            .map(|_| {
                scope.spawn(|| {
                    let mut completed = Vec::new();
                    loop {
                        let index = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        let Some(run) = selected.get(index) else {
                            break;
                        };
                        let result = measure(run, &root, base, &checker, &args)?;
                        eprintln!("{} finished in {} ms", run.id, result["elapsed_ms"]);
                        completed.push((index, result));
                    }
                    Ok::<_, Box<dyn std::error::Error + Send + Sync>>(completed)
                })
            })
            .collect();
        let mut results = Vec::new();
        for worker in workers {
            results.extend(worker.join().map_err(|_| "benchmark worker panicked")??);
        }
        Ok::<_, Box<dyn std::error::Error + Send + Sync>>(results)
    })?;
    results.sort_unstable_by_key(|(index, _)| *index);
    let results: Vec<_> = results.into_iter().map(|(_, result)| result).collect();
    let mut counts = BTreeMap::<String, BTreeMap<String, usize>>::new();
    let mut sources = BTreeMap::<_, BTreeMap<&str, usize>>::new();
    let mut symbols = BTreeSet::new();
    let mut crates = BTreeSet::new();
    for (run, row) in verdicts(&results) {
        let status = row["result"]["status"].as_str().unwrap_or("tool_error");
        let package = run["crate"].as_str();
        if let Some(package) = package {
            crates.insert(package);
        }
        *sources
            .entry((package, row["kind"].as_str(), row["source"].as_str()))
            .or_default()
            .entry(status)
            .or_default() += 1;
        if let (Some(image), Some(name)) =
            (run["elf_sha256"].as_str(), row["result"]["name"].as_str())
        {
            symbols.insert((image, name));
        }
        let category = package
            .and_then(|name| registry.get(&name.to_owned()))
            .map_or("fixture", |entry| entry.category.as_str());
        for key in [
            "all".to_owned(),
            format!("kind/{}", row["kind"].as_str().unwrap()),
            format!("track/{}", run["track"].as_str().unwrap()),
            format!("category/{category}"),
            format!("run/{}", run["run"].as_str().unwrap()),
        ] {
            *counts
                .entry(key)
                .or_default()
                .entry(status.to_owned())
                .or_default() += 1;
        }
    }
    let source_coverage: Vec<_> = sources
        .iter()
        .map(|((package, kind, source), verdict_counts)| {
            json!({"crate": package, "kind": kind, "source": source, "verdicts": verdict_counts})
        })
        .collect();
    let total: usize = counts["all"].values().sum();
    let proved = counts["all"].get("proved").copied().unwrap_or_default();
    let assumed = counts["all"]
        .get("proved_assuming")
        .copied()
        .unwrap_or_default();
    let rust_checked = proved + assumed + counts["all"].get("checked").copied().unwrap_or_default();
    fs::write(
        root.join("coverage.json"),
        serde_json::to_vec_pretty(&json!({
            "schema_version": 1, "target": manifest.target,
            "settings": {"profile": args.profile, "locked": true, "mir_hints": !args.no_mir_hints,
                "llvm_hints": args.llvm_hints, "timeout_secs": args.timeout_secs, "jobs": args.jobs,
                "chc_solver_enabled": args.chc_solver.is_some(), "frontend_sha256": checker_digest},
            "candidate_crates": registry.len(), "priority_candidates": registry.values().filter(|v| v.priority).count(),
            "measured_crates": crates, "unique_source_entries": sources.len(), "unique_symbols_in_images": symbols.len(),
            "suite_elapsed_ms": suite_started.elapsed().as_millis(),
            "requested_targets": total, "rust_checker_passed": rust_checked,
            "lean_proved": proved, "lean_proved_assuming": assumed,
            "built_runs": results.iter().filter(|run| run["built"] == true).count(),
            "requested_targets_in_linked_builds": verdicts(&results).filter(|(run, _)| run["built"] == true).count(),
            "source_coverage": source_coverage, "counts": counts, "runs": results,
        }))?,
    )?;
    println!(
        "{proved}/{total} Lean proofs, {assumed} with assumptions, {rust_checked} Rust checker passes"
    );
    println!("Artifacts {}", root.display());
    Ok(counts["all"].contains_key("tool_error"))
}

fn main() -> ExitCode {
    match run(Args::parse()) {
        Ok(has_error) => ExitCode::from(u8::from(has_error)),
        Err(error) => {
            eprintln!("Rust benchmark error: {error}");
            ExitCode::FAILURE
        }
    }
}

use clap::Parser;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{
    collections::BTreeMap,
    fs::{self, File},
    path::{Path, PathBuf},
    process::{Command, ExitCode, Stdio},
    sync::atomic::{AtomicUsize, Ordering},
};
use syn::visit::{self, Visit};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error + Send + Sync>>;
const TOOLCHAIN: &str = "+nightly-2026-09-17";
const TARGET: &str = "riscv64imac-unknown-none-elf";

#[derive(Parser)]
#[command(about = "Screen each Rust-100 candidate for unsafe syntax and RV64 builds")]
struct Args {
    #[arg(long, default_value = "benchmarks/rust/manifest.json")]
    manifest: PathBuf,
    #[arg(long)]
    artifacts: PathBuf,
    /// Reuse the versions in an earlier screening report.
    #[arg(long)]
    versions: Option<PathBuf>,
    /// Add one explicit no-default feature probe per crate from a JSON map.
    #[arg(long)]
    feature_overrides: Option<PathBuf>,
    #[arg(long, default_value_t = 6, value_parser = clap::value_parser!(u64).range(1..=16))]
    jobs: u64,
    #[arg(long, default_value_t = 150, value_parser = clap::value_parser!(u64).range(1..))]
    timeout_secs: u64,
}

#[derive(Default)]
struct Syntax {
    blocks: usize,
    functions: usize,
    unsafe_traits: usize,
    unsafe_impls: usize,
    foreign_blocks: usize,
}

impl<'ast> Visit<'ast> for Syntax {
    fn visit_expr_unsafe(&mut self, node: &'ast syn::ExprUnsafe) {
        self.blocks += 1;
        visit::visit_expr_unsafe(self, node);
    }
    fn visit_item_fn(&mut self, node: &'ast syn::ItemFn) {
        self.functions += usize::from(node.sig.unsafety.is_some());
        visit::visit_item_fn(self, node);
    }
    fn visit_impl_item_fn(&mut self, node: &'ast syn::ImplItemFn) {
        self.functions += usize::from(node.sig.unsafety.is_some());
        visit::visit_impl_item_fn(self, node);
    }
    fn visit_trait_item_fn(&mut self, node: &'ast syn::TraitItemFn) {
        self.functions += usize::from(node.sig.unsafety.is_some() && node.default.is_some());
        visit::visit_trait_item_fn(self, node);
    }
    fn visit_item_trait(&mut self, node: &'ast syn::ItemTrait) {
        self.unsafe_traits += usize::from(node.unsafety.is_some());
        visit::visit_item_trait(self, node);
    }
    fn visit_item_impl(&mut self, node: &'ast syn::ItemImpl) {
        self.unsafe_impls += usize::from(node.unsafety.is_some());
        visit::visit_item_impl(self, node);
    }
    fn visit_item_foreign_mod(&mut self, node: &'ast syn::ItemForeignMod) {
        self.foreign_blocks += 1;
        visit::visit_item_foreign_mod(self, node);
    }
}

fn scan(source: &Path) -> Result<Value> {
    let mut todo = vec![source.to_path_buf()];
    let mut syntax = Syntax::default();
    let mut parsed = 0;
    let mut failed = Vec::new();
    let mut unsafe_files = Vec::new();
    while let Some(path) = todo.pop() {
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            let path = entry.path();
            let kind = entry.file_type()?;
            if kind.is_dir() {
                if !matches!(
                    entry.file_name().to_str(),
                    Some("tests" | "benches" | "examples" | "target" | "test")
                ) {
                    todo.push(path);
                }
            } else if kind.is_file()
                && path.extension().is_some_and(|ext| ext == "rs")
                && entry.file_name() != "build.rs"
            {
                let relative = path.strip_prefix(source)?.to_path_buf();
                match fs::read_to_string(&path)
                    .ok()
                    .and_then(|text| syn::parse_file(&text).ok())
                {
                    Some(file) => {
                        let before = syntax.blocks;
                        syntax.visit_file(&file);
                        if syntax.blocks != before {
                            unsafe_files.push(relative);
                        }
                        parsed += 1;
                    }
                    None => failed.push(relative),
                }
            }
        }
    }
    unsafe_files.sort();
    failed.sort();
    Ok(
        json!({"status": "scanned", "parsed_files": parsed, "parse_failures": failed,
        "unsafe_blocks": syntax.blocks, "unsafe_functions_with_bodies": syntax.functions,
        "unsafe_traits": syntax.unsafe_traits, "unsafe_impls": syntax.unsafe_impls,
        "foreign_blocks": syntax.foreign_blocks, "files_with_unsafe_blocks": unsafe_files}),
    )
}

fn index_path(name: &str) -> String {
    match name.len() {
        1 | 2 => format!("{}/{name}", name.len()),
        3 => format!("3/{}/{name}", &name[..1]),
        _ => format!("{}/{}/{name}", &name[..2], &name[2..4]),
    }
}

fn stable_key(version: &str) -> Option<[u64; 3]> {
    let (core, _) = version.split_once('+').unwrap_or((version, ""));
    let mut parts = core.split('.');
    let key = [
        parts.next()?.parse().ok()?,
        parts.next()?.parse().ok()?,
        parts.next()?.parse().ok()?,
    ];
    parts.next().is_none().then_some(key)
}

fn curl(url: &str) -> Result<std::process::Output> {
    Ok(Command::new("curl")
        .args(["-fsSL", "--retry", "2", "--max-time", "25", url])
        .output()?)
}

fn resolve(name: &str, pinned: Option<&str>) -> Result<(String, String)> {
    let response = curl(&format!("https://index.crates.io/{}", index_path(name)))?;
    if !response.status.success() {
        return Err(format!(
            "registry index: {}",
            String::from_utf8_lossy(&response.stderr).trim()
        )
        .into());
    }
    let index = std::str::from_utf8(&response.stdout)?;
    let records: Vec<Value> = index
        .lines()
        .map(serde_json::from_str)
        .collect::<std::result::Result<_, _>>()?;
    let record = if let Some(version) = pinned {
        records.iter().find(|row| row["vers"] == version)
    } else {
        records
            .iter()
            .filter(|row| row["yanked"] == false)
            .filter_map(|row| Some((stable_key(row["vers"].as_str()?)?, row)))
            .max_by_key(|(key, _)| *key)
            .map(|(_, row)| row)
    }
    .ok_or("no requested release found in registry index")?;
    Ok((
        record["vers"].as_str().ok_or("missing version")?.to_owned(),
        record["cksum"]
            .as_str()
            .ok_or("missing archive checksum")?
            .to_owned(),
    ))
}

fn source_scan(name: &str, version: &str, digest: &str, scratch: &Path) -> Result<Value> {
    let response = curl(&format!(
        "https://static.crates.io/crates/{name}/{name}-{version}.crate"
    ))?;
    if !response.status.success() {
        return Err(format!(
            "archive: {}",
            String::from_utf8_lossy(&response.stderr).trim()
        )
        .into());
    }
    if format!("{:x}", Sha256::digest(&response.stdout)) != digest {
        return Err("published archive checksum does not match the index".into());
    }
    let archive = scratch.join("source.crate");
    fs::write(&archive, response.stdout)?;
    let source = scratch.join("source");
    fs::create_dir(&source)?;
    let unpack = Command::new("tar")
        .args(["-xzf"])
        .arg(archive)
        .args(["--strip-components=1", "-C"])
        .arg(&source)
        .output()?;
    if !unpack.status.success() {
        return Err(format!("unpack: {}", String::from_utf8_lossy(&unpack.stderr).trim()).into());
    }
    scan(&source)
}

fn build(
    name: &str,
    version: &str,
    defaults: bool,
    features: &[String],
    artifact: &Path,
    scratch: &Path,
    timeout: u64,
) -> Result<Value> {
    fs::create_dir_all(artifact)?;
    fs::create_dir(artifact.join("src"))?;
    fs::write(
        artifact.join("Cargo.toml"),
        format!(
            "[package]\nname = \"rust100-screen\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\
         [dependencies]\nsubject = {{ package = {name:?}, version = \"={version}\", default-features = {defaults}, features = {features:?} }}\n[workspace]\n"
        ),
    )?;
    fs::write(
        artifact.join("src/lib.rs"),
        "#![no_std]\nextern crate subject;\n",
    )?;
    let log = File::create(artifact.join("build.log"))?;
    let result = Command::new("timeout")
        .args([
            "--kill-after=5s",
            &format!("{timeout}s"),
            "cargo",
            TOOLCHAIN,
            "build",
            "--lib",
            "--release",
            "--target",
            TARGET,
            "--jobs",
            "1",
            "--message-format=json-render-diagnostics",
            "--color",
            "never",
            "--target-dir",
        ])
        .arg(scratch.join("target"))
        .env("CARGO_NET_RETRY", "1")
        .env("CARGO_HTTP_TIMEOUT", "25")
        .current_dir(artifact)
        .stdout(Stdio::from(log.try_clone()?))
        .stderr(Stdio::from(log))
        .status()?;
    let log = fs::read_to_string(artifact.join("build.log")).unwrap_or_default();
    let archive_name = format!("lib{}-", name.replace('-', "_"));
    let target_library = log
        .lines()
        .filter(|line| line.starts_with('{'))
        .filter_map(|line| serde_json::from_str::<Value>(line).ok())
        .filter(|row| row["reason"] == "compiler-artifact")
        .any(|row| {
            row["package_id"].as_str().is_some_and(|id| {
                id.starts_with("registry+")
                    && (id.ends_with(&format!("#{name}@{version}"))
                        || id.ends_with(&format!("/{name}#{version}")))
            }) && row["filenames"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
                .any(|file| {
                    file.contains(&format!("/{TARGET}/"))
                        && Path::new(file)
                            .file_name()
                            .and_then(|f| f.to_str())
                            .is_some_and(|f| {
                                f.ends_with(".rlib")
                                    && (f.starts_with(&archive_name)
                                        || row["target"]["kind"].as_array().is_some_and(|kinds| {
                                            kinds.iter().any(|kind| kind == "lib" || kind == "rlib")
                                        }))
                            })
                })
        });
    let status = match result.code() {
        Some(0) if target_library => "built",
        Some(0) => "no_target_library",
        Some(124 | 137) => "timeout",
        _ if log.contains("failed to download")
            || log.contains("failed to get successful HTTP response") =>
        {
            "dependency_fetch_failed"
        }
        _ if !artifact.join("Cargo.lock").is_file() => "resolution_failed",
        _ => "build_failed",
    };
    let lock = fs::read(artifact.join("Cargo.lock"))
        .ok()
        .map(|data| format!("{:x}", Sha256::digest(data)));
    let diagnostic = log
        .lines()
        .find(|line| line.starts_with("error"))
        .unwrap_or("");
    Ok(json!({"status": status, "exit_code": result.code(),
        "lock_sha256": lock, "diagnostic": diagnostic}))
}

fn screen(
    candidate: &Value,
    pin: Option<&str>,
    features: Option<&[String]>,
    artifact: &Path,
    timeout: u64,
) -> Result<Value> {
    let name = candidate["name"].as_str().ok_or("candidate has no name")?;
    let (version, digest) = match resolve(name, pin) {
        Ok(resolved) => resolved,
        Err(error) => {
            return Ok(
                json!({"candidate": candidate, "status": "registry_unresolved", "diagnostic": error.to_string()}),
            );
        }
    };
    let scratch = tempfile::Builder::new()
        .prefix("rust100-screen-")
        .tempdir_in(artifact)?;
    let source = source_scan(name, &version, &digest, scratch.path())
        .unwrap_or_else(|error| json!({"status": "source_error", "diagnostic": error.to_string()}));
    let probe = |mode, defaults, features: &[String]| {
        build(
            name,
            &version,
            defaults,
            features,
            &artifact.join(name).join(mode),
            scratch.path(),
            timeout,
        )
        .unwrap_or_else(|error| json!({"status": "tool_error", "diagnostic": error.to_string()}))
    };
    let minimal = probe("no-default", false, &[]);
    let defaults = probe("default", true, &[]);
    let explicit = features.map(|features| probe("explicit-features", false, features));
    Ok(json!({"candidate": candidate, "status": "screened",
        "version": version, "archive_sha256": digest, "source": source,
        "no-default": minimal, "default": defaults, "explicit_features": features,
        "feature_build": explicit}))
}

fn run(args: Args) -> Result<()> {
    let manifest: Value = serde_json::from_slice(&fs::read(&args.manifest)?)?;
    let candidates = manifest["candidates"]
        .as_array()
        .ok_or("missing candidates")?;
    let mut names = std::collections::BTreeSet::new();
    for candidate in candidates {
        let name = candidate["name"].as_str().ok_or("candidate has no name")?;
        if name.is_empty()
            || !name
                .bytes()
                .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-' || b == b'_')
            || !names.insert(name)
        {
            return Err("invalid or duplicated registry candidate name".into());
        }
    }
    let mut pins = BTreeMap::new();
    for row in manifest["runs"].as_array().into_iter().flatten() {
        if let (Some(name), Some(version)) = (row["crate"].as_str(), row["version"].as_str()) {
            pins.insert(name.to_owned(), version.to_owned());
        }
    }
    if let Some(path) = args.versions {
        let report: Value = serde_json::from_slice(&fs::read(path)?)?;
        for row in report["candidates"]
            .as_array()
            .ok_or("versions report has no candidates")?
        {
            if let (Some(name), Some(version)) =
                (row["candidate"]["name"].as_str(), row["version"].as_str())
            {
                pins.insert(name.to_owned(), version.to_owned());
            }
        }
    }
    let overrides: BTreeMap<String, Vec<String>> = match &args.feature_overrides {
        Some(path) => serde_json::from_slice(&fs::read(path)?)?,
        None => BTreeMap::new(),
    };
    if overrides.iter().any(|(name, features)| {
        !names.contains(name.as_str())
            || features.is_empty()
            || features.iter().any(|feature| {
                feature.is_empty()
                    || !feature
                        .bytes()
                        .all(|b| b.is_ascii_alphanumeric() || b"-_.".contains(&b))
            })
    }) {
        return Err("invalid feature overrides".into());
    }
    fs::create_dir(&args.artifacts)?;
    let root = args.artifacts.canonicalize()?;
    fs::write(
        root.join("manifest.json"),
        serde_json::to_vec_pretty(&manifest)?,
    )?;
    let next = AtomicUsize::new(0);
    let mut rows = std::thread::scope(|scope| {
        let workers: Vec<_> = (0..(args.jobs as usize).min(candidates.len())).map(|_| {
            scope.spawn(|| {
                let mut rows = Vec::new();
                loop {
                    let i = next.fetch_add(1, Ordering::Relaxed);
                    let Some(candidate) = candidates.get(i) else { break };
                    let name = candidate["name"].as_str().unwrap();
                    let row = screen(candidate, pins.get(name).map(String::as_str), overrides.get(name).map(Vec::as_slice), &root, args.timeout_secs)
                        .unwrap_or_else(|error| json!({"candidate": candidate, "status": "tool_error", "diagnostic": error.to_string()}));
                    eprintln!("{name} {} {} / {}", row["status"], row["no-default"]["status"], row["default"]["status"]);
                    rows.push((i, row));
                }
                rows
            })
        }).collect();
        workers
            .into_iter()
            .flat_map(|worker| worker.join().expect("screening worker"))
            .collect::<Vec<_>>()
    });
    rows.sort_unstable_by_key(|(index, _)| *index);
    let candidates: Vec<_> = rows.into_iter().map(|(_, row)| row).collect();
    let mut counts = BTreeMap::<&str, BTreeMap<&str, usize>>::new();
    for row in &candidates {
        for (group, status) in [
            ("registry", row["status"].as_str()),
            ("no-default", row["no-default"]["status"].as_str()),
            ("default", row["default"]["status"].as_str()),
            ("feature_build", row["feature_build"]["status"].as_str()),
        ] {
            *counts
                .entry(group)
                .or_default()
                .entry(status.unwrap_or("not_run"))
                .or_default() += 1;
        }
    }
    let unsafe_blocks = candidates
        .iter()
        .filter(|row| {
            row["source"]["unsafe_blocks"]
                .as_u64()
                .is_some_and(|n| n > 0)
        })
        .count();
    let eligible = candidates
        .iter()
        .filter(|row| {
            row["source"]["unsafe_blocks"]
                .as_u64()
                .is_some_and(|n| n > 0)
                && (row["no-default"]["status"] == "built"
                    || row["default"]["status"] == "built"
                    || row["feature_build"]["status"] == "built")
        })
        .count();
    let report = json!({"schema_version": 1, "toolchain": TOOLCHAIN, "target": TARGET,
        "timeout_secs": args.timeout_secs, "jobs": args.jobs,
        "counts": counts, "own_source_unsafe_blocks": unsafe_blocks,
        "unsafe_block_and_rv64_build": eligible, "candidates": candidates});
    fs::write(
        root.join("screening.json"),
        serde_json::to_vec_pretty(&report)?,
    )?;
    println!(
        "{} candidates, {unsafe_blocks} with unsafe blocks, {eligible} with unsafe blocks and an RV64 build",
        candidates.len()
    );
    println!("Artifacts {}", root.display());
    Ok(())
}

fn main() -> ExitCode {
    match run(Args::parse()) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("Rust screening error: {error}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn separates_unsafe_blocks_from_declarations() {
        let file = syn::parse_file(
            r#"
            // unsafe { text in a comment }
            unsafe trait Marker {}
            unsafe impl Marker for u32 {}
            unsafe fn operation() { unsafe {} }
            unsafe extern "C" { fn foreign(); }
        "#,
        )
        .unwrap();
        let mut syntax = Syntax::default();
        syntax.visit_file(&file);
        assert_eq!(syntax.blocks, 1);
        assert_eq!(syntax.functions, 1);
        assert_eq!(syntax.unsafe_traits, 1);
        assert_eq!(syntax.unsafe_impls, 1);
        assert_eq!(syntax.foreign_blocks, 1);
    }

    #[test]
    fn sparse_index_paths_and_stable_version_keys() {
        assert_eq!(index_path("im"), "2/im");
        assert_eq!(index_path("aes"), "3/a/aes");
        assert_eq!(index_path("bytecast"), "by/te/bytecast");
        assert!(stable_key("1.0.0-rc.1").is_none());
        assert!(stable_key("1.12.0+revision") > stable_key("1.9.0"));
    }
}

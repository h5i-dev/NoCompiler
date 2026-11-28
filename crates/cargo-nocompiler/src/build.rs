use crate::{Args, Result};
use serde_json::{Value, json};
use std::{
    collections::BTreeMap,
    fs,
    io::Write,
    path::{Path, PathBuf},
    process::{Command, Stdio},
};

pub const TOOLCHAIN: &str = "nightly-2026-09-17";
pub const TARGET: &str = "riscv64imac-unknown-none-elf";

pub fn flags(debug: bool) -> Vec<&'static str> {
    let mut flags = vec![
        "-C",
        "target-feature=-c,-zca",
        "-C",
        "codegen-units=1",
        "-C",
        "panic=abort",
        "-C",
        "lto=off",
        "-C",
        "link-dead-code=yes",
        "-C",
        "link-arg=--no-relax",
    ];
    if debug {
        flags.extend(["-C", "debuginfo=2", "-C", "strip=none"]);
    }
    flags
}

pub fn output(command: &mut Command) -> Result<String> {
    let result = command.output()?;
    if !result.status.success() {
        return Err(format!(
            "{command:?}: {}\n{}",
            result.status,
            String::from_utf8_lossy(&result.stderr)
        )
        .into());
    }
    Ok(String::from_utf8(result.stdout)?)
}
pub type Symbols = BTreeMap<String, (u64, u64)>;
pub struct Build {
    pub assembly: String,
    pub image: PathBuf,
    pub symbols: Symbols,
    pub version: String,
    pub llvm_hints: crate::llvm::Hints,
}
pub fn compile(args: &Args, dir: &Path) -> Result<Build> {
    let pin = format!("+{TOOLCHAIN}");
    let sysroot = output(Command::new("rustc").args([&pin, "--print", "sysroot"]))?;
    let sysroot = Path::new(sysroot.trim());
    let version = output(Command::new("rustc").args([&pin, "-vV"]))?;
    let host = version
        .lines()
        .find_map(|l| l.strip_prefix("host: "))
        .ok_or("rustc did not report a host")?;
    let driver_source = dir.join("capture.rs");
    fs::write(&driver_source, include_str!("rustc_driver.rs"))?;
    fs::write(dir.join("capture_mir.rs"), include_str!("capture_mir.rs"))?;
    fs::write(dir.join("contract_ir.rs"), include_str!("contract_ir.rs"))?;
    let driver = dir.join("capture-rustc");
    let lib = sysroot.join("lib");
    output(
        Command::new("rustc")
            .args([&pin, "--edition=2024", "-C", "opt-level=2", "-L"])
            .arg(format!("native={}", lib.display()))
            .args([
                "-C",
                &format!("link-arg=-Wl,-rpath,{}", lib.display()),
                "-o",
            ])
            .arg(&driver)
            .arg(&driver_source),
    )?;
    let assembly = dir.join("rustc.s");
    let llvm_ir = dir.join("rustc.ll");
    let mut emit = format!("--emit=asm={}", assembly.display());
    if args.llvm_hints {
        emit.push_str(&format!(",llvm-ir={}", llvm_ir.display()));
    }
    let mut command = Command::new("cargo");
    command
        .args([&pin, "rustc", "--manifest-path"])
        .arg(&args.manifest_path)
        .args(["--target", TARGET, "--target-dir"])
        .arg(dir.join("target"))
        .args([
            "--profile",
            &args.profile,
            "--bin",
            &args.bin,
            "--message-format=json",
        ]);
    if let Some(package) = &args.package {
        command.args(["--package", package]);
    }
    if !args.features.is_empty() {
        command.arg("--features").arg(args.features.join(","));
    }
    for (enabled, flag) in [
        (args.no_default_features, "--no-default-features"),
        (args.all_features, "--all-features"),
        (args.locked, "--locked"),
    ] {
        if enabled {
            command.arg(flag);
        }
    }
    let result = command
        .args(["--", "--nocompiler-capture", &emit])
        .args(flags(!args.no_source_trace))
        .env("RUSTC_WRAPPER", &driver)
        .env("RUSTC_WORKSPACE_WRAPPER", "")
        .env("RUSTC", sysroot.join("bin/rustc"))
        .env("NOCOMPILER_CAPTURE_PATH", dir)
        .env("NOCOMPILER_CAPTURE_TARGETS", args.function.join("\n"))
        .env("NOCOMPILER_RUST_SYSROOT", sysroot)
        .stderr(Stdio::inherit())
        .output()?;
    let mut executables = vec![];
    let mut artifacts = vec![];
    for line in String::from_utf8(result.stdout)?.lines() {
        let event: Value = serde_json::from_str(line)?;
        if event["reason"] == "compiler-message" {
            if let Some(msg) = event["message"]["rendered"]
                .as_str()
                .or_else(|| event["message"]["message"].as_str())
            {
                eprint!("{msg}");
            }
        } else if event["reason"] == "compiler-artifact" {
            artifacts.push(json!({
                "package_id": event["package_id"],
                "target": event["target"]["name"],
                "kind": event["target"]["kind"],
                "features": event["features"],
                "profile": event["profile"],
            }));
            if event["target"]["name"] == args.bin
                && event["target"]["kind"]
                    .as_array()
                    .is_some_and(|v| v.iter().any(|x| x == "bin"))
                && let Some(path) = event["executable"].as_str()
            {
                executables.push(path.to_owned());
            }
        }
    }
    if !result.status.success() {
        return Err(format!("Cargo build {}", result.status).into());
    }
    let [path] = executables.as_slice() else {
        return Err("Cargo did not produce exactly one selected executable".into());
    };
    crate::write_json(
        &dir.join("cargo-build.json"),
        &json!({"artifacts": artifacts}),
    )?;
    let image = dir.join("verified.elf");
    fs::copy(path, &image)?;
    let llvm_bin = sysroot.join("lib/rustlib").join(host).join("bin");
    let llvm_hints = if args.llvm_hints {
        crate::llvm::capture(sysroot, &llvm_bin, &llvm_ir, dir)?
    } else {
        crate::llvm::Hints::default()
    };
    let nm = llvm_bin.join("llvm-nm");
    let symbols = output(
        Command::new(nm)
            .args(["--defined-only", "--format=posix"])
            .arg(&image),
    )?
    .lines()
    .filter_map(|line| {
        let mut fields = line.split_whitespace();
        let name = fields.next()?;
        if !matches!(fields.next()?, "T" | "t") {
            return None;
        }
        Some((
            name.into(),
            (
                u64::from_str_radix(fields.next()?, 16).ok()?,
                u64::from_str_radix(fields.next()?, 16).ok()?,
            ),
        ))
    })
    .collect();
    Ok(Build {
        assembly: fs::read_to_string(assembly)?,
        llvm_hints,
        image,
        symbols,
        version: version.lines().next().unwrap_or_default().into(),
    })
}

pub fn trace(
    tool: &Path,
    image: &Path,
    linked: &Symbols,
    targets: &BTreeMap<String, String>,
) -> Result<Value> {
    let mut addresses = BTreeMap::<u64, Vec<&str>>::new();
    for (path, name) in targets {
        if let Some(&(start, size)) = linked.get(name) {
            let end = start.checked_add(size).ok_or("symbol range overflows")?;
            for address in (start..end).step_by(4) {
                addresses.entry(address).or_default().push(path);
            }
        }
    }
    let mut traces = BTreeMap::<String, Vec<Value>>::new();
    if addresses.is_empty() {
        return Ok(json!(traces));
    }
    let mut child = Command::new(tool)
        .args(["--inlines", "--output-style=JSON", "--obj"])
        .arg(image)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;
    let mut input = child
        .stdin
        .take()
        .ok_or("could not open symbolizer stdin")?;
    let request: String = addresses
        .keys()
        .map(|addr| format!("{addr:#x}\n"))
        .collect();
    let writer = std::thread::spawn(move || input.write_all(request.as_bytes()));
    let output = child.wait_with_output()?;
    writer
        .join()
        .map_err(|_| "symbolizer input thread failed")??;
    if !output.status.success() {
        return Err(format!("symbolizer {}", output.status).into());
    }
    for line in String::from_utf8(output.stdout)?.lines() {
        let event: Value = serde_json::from_str(line)?;
        let Some(frames) = event["Symbol"].as_array().filter(|frames| frames.len() > 1) else {
            continue;
        };
        let addr = u64::from_str_radix(
            event["Address"]
                .as_str()
                .ok_or("missing DWARF address")?
                .trim_start_matches("0x"),
            16,
        )?;
        let stack:Vec<_>=frames.iter().map(|f|json!({"function":f["FunctionName"],"file":f["FileName"],"line":f["Line"],"column":f["Column"]})).collect();
        let Some(paths) = addresses.get(&addr) else {
            return Err("unexpected DWARF address".into());
        };
        for path in paths {
            let ranges = traces.entry((*path).into()).or_default();
            if let Some(last) = ranges.last_mut()
                && last["end"] == addr
                && last["frames"].as_array() == Some(&stack)
            {
                last["end"] = json!(addr + 4);
            } else {
                ranges.push(json!({"start":addr,"end":addr+4,"frames":stack}));
            }
        }
    }
    Ok(json!(traces))
}

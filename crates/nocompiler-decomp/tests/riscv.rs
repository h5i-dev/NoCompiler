//! The decompiler on RISC-V (RV64, through the embedded SLEIGH specification).
//!
//! On the committed `examples/elf/sum.elf`, every function decompiles with
//! nothing unmodelled, the loop is a loop, the `auipc`+`jalr` calls are direct
//! calls with the callee's arguments, and a C compiler accepts the output.
//!
//! `coverage` measures a whole binary and is ignored by default because the
//! binaries worth measuring are not committed:
//!
//! ```text
//! NOCOMPILER_RV_ELF=path/to/micropython.elf \
//!   cargo test --release -p nocompiler-decomp --test riscv coverage -- --ignored --nocapture
//! ```

use std::collections::BTreeMap;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::Path;
use std::process::Command;
use std::time::Instant;

use nocompiler_analysis::{Function, Options, Program, analyze};
use nocompiler_core::Arch;
use nocompiler_format::LoadOptions;

fn load(path: &Path) -> Program {
    let data = std::fs::read(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let obj = nocompiler_format::load(&data, &LoadOptions::default()).expect("loads");
    assert!(
        matches!(&obj.arch, Arch::Sleigh(id) if id.starts_with("RISCV:LE:64")),
        "{:?}",
        obj.arch
    );
    analyze(obj, &Options::default())
}

fn committed(name: &str) -> Program {
    load(
        &Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../examples/elf")
            .join(name),
    )
}

fn decompiled(p: &Program, name: &str) -> nocompiler_api::Decompiled {
    let f = p
        .functions_by_address()
        .find(|f| f.display_name() == name)
        .unwrap_or_else(|| panic!("{name} recovered"));
    let all: Vec<&Function> = p.functions_by_address().collect();
    let unit = nocompiler_api::decompile_program(p, &all);
    unit.functions
        .into_iter()
        .find(|d| d.addr == f.entry)
        .expect("decompiled")
}

#[test]
fn sum_is_a_loop_over_an_array() {
    let p = committed("sum.elf");
    let d = decompiled(&p, "sum");
    assert_eq!(d.unmodelled, 0, "{}", d.text);
    assert_eq!(d.gotos, 0, "{}", d.text);
    assert!(d.text.contains("while ("), "{}", d.text);
    assert!(d.signature.contains("*arg0"), "a pointer: {}", d.signature);
    assert!(d.signature.contains("arg1"), "{}", d.signature);
    assert!(
        !d.signature.contains("arg2"),
        "two parameters: {}",
        d.signature
    );
}

#[test]
fn sum2_calls_sum_twice_with_its_own_arguments() {
    let p = committed("sum.elf");
    let d = decompiled(&p, "sum2");
    assert_eq!(d.unmodelled, 0, "{}", d.text);
    assert!(!d.text.contains("__callind"), "{}", d.text);
    assert!(!d.text.contains("__clobbered"), "{}", d.text);
    assert!(d.text.contains("sum((void *)arg0, arg1)"), "{}", d.text);
    assert!(d.text.contains("sum((void *)arg2, arg3)"), "{}", d.text);
    // The prologue's spills of ra and s0-s2 are not variables.
    assert!(!d.text.contains("inherited"), "{}", d.text);
}

#[test]
fn every_committed_function_decompiles_and_compiles() {
    for name in ["sum.elf", "hello.elf", "sum.link2.elf"] {
        let p = committed(name);
        let all: Vec<&Function> = p.functions_by_address().collect();
        let unit = nocompiler_api::decompile_program(&p, &all);
        assert_eq!(unit.functions.len(), all.len(), "{name}");
        for d in &unit.functions {
            assert_eq!(d.unmodelled, 0, "{name} {}: {}", d.name, d.text);
            assert!(!d.text.trim().is_empty(), "{name} {}", d.name);
        }
        if Command::new("clang").arg("--version").output().is_err() {
            eprintln!("clang is not installed; the compile check is skipped");
            continue;
        }
        let dir = std::env::temp_dir().join(format!("nocompiler-decomp-riscv-{name}"));
        std::fs::create_dir_all(&dir).unwrap();
        let src = dir.join("out.c");
        std::fs::write(&src, unit.text()).unwrap();
        let out = Command::new("clang")
            .args(["-c", "-w", "-ffreestanding", "-o"])
            .arg(dir.join("out.o"))
            .arg(&src)
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "{name}: clang rejected the output:\n{}\n{}",
            String::from_utf8_lossy(&out.stderr),
            unit.text()
        );
    }
}

/// What happened to one function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Outcome {
    /// Pseudo-C with every instruction modelled.
    Clean,
    /// Pseudo-C, with `__unmodelled` where an instruction has no IR.
    Unmodelled,
    /// The decompiler panicked.
    Panicked,
    /// Nothing came back.
    Empty,
}

#[test]
#[ignore]
fn coverage() {
    let Some(path) = std::env::var_os("NOCOMPILER_RV_ELF") else {
        eprintln!("set NOCOMPILER_RV_ELF to a RISC-V ELF");
        return;
    };
    let start = Instant::now();
    let p = load(Path::new(&path));
    let analysed = start.elapsed();
    let all: Vec<&Function> = p.functions_by_address().collect();
    let mut outcome: BTreeMap<Outcome, Vec<String>> = BTreeMap::new();
    let mut gotos = 0usize;
    let mut with_goto = 0usize;
    let mut incomplete_cfg = 0usize;
    let start = Instant::now();
    // Chunks of 64, as the command line decompiles `all`. A chunk that
    // panics is redone one function at a time to find which.
    for chunk in all.chunks(64) {
        let unit = catch_unwind(AssertUnwindSafe(|| {
            nocompiler_api::decompile_program(&p, chunk)
        }));
        let singles: Vec<(String, Option<nocompiler_api::Decompiled>)> = match unit {
            Ok(u) => {
                let mut by: BTreeMap<_, _> = u.functions.into_iter().map(|d| (d.addr, d)).collect();
                chunk
                    .iter()
                    .map(|f| (f.display_name(), by.remove(&f.entry)))
                    .collect()
            }
            Err(_) => chunk
                .iter()
                .map(|f| {
                    let one = catch_unwind(AssertUnwindSafe(|| {
                        nocompiler_api::decompile_function(&p, f)
                    }));
                    match one {
                        Ok(d) => (f.display_name(), Some(d)),
                        Err(_) => {
                            outcome
                                .entry(Outcome::Panicked)
                                .or_default()
                                .push(f.display_name());
                            (f.display_name(), None)
                        }
                    }
                })
                .filter(|(_, d)| d.is_some())
                .collect(),
        };
        for (name, d) in singles {
            let o = match &d {
                None => Outcome::Empty,
                Some(d) if d.text.trim().is_empty() => Outcome::Empty,
                Some(d) if d.unmodelled > 0 => Outcome::Unmodelled,
                Some(_) => Outcome::Clean,
            };
            if let Some(d) = &d {
                gotos += d.gotos;
                with_goto += usize::from(d.gotos > 0);
            }
            outcome.entry(o).or_default().push(name);
        }
    }
    for f in &all {
        incomplete_cfg += usize::from(!f.is_complete());
    }
    let count = |o| outcome.get(&o).map_or(0, |v| v.len());
    let produced = count(Outcome::Clean) + count(Outcome::Unmodelled);
    eprintln!(
        "{}: {} functions, analysis {:.1?}, decompile {:.1?}",
        Path::new(&path).display(),
        all.len(),
        analysed,
        start.elapsed()
    );
    eprintln!("decompiled (pseudo-C produced): {produced} / {}", all.len());
    for (o, names) in &outcome {
        let sample: Vec<&str> = names.iter().take(8).map(String::as_str).collect();
        eprintln!("  {o:?}: {} {sample:?}", names.len());
    }
    eprintln!("  functions with a goto: {with_goto} ({gotos} gotos)");
    eprintln!("  functions whose CFG is incomplete (unresolved indirect jump): {incomplete_cfg}");
}

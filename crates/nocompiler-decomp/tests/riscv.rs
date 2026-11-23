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

/// A function that returns a call's result unchanged while one branch
/// computes an address in `a1` to store through (musl's strtol shape). The
/// result is `a0`, the call's: before, the branch's last write to `a1` made
/// `a1` the result, so `f` returned the stored sum on that path and
/// `__clobbered()` on the other, and the call's result was dropped.
///
/// Fixture: tests/riscv/pass-through.c, built with the profile's flags
/// (`clang --target=riscv64-unknown-elf -march=rv64im_zba_zbb -mabi=lp64
/// -mcmodel=medany -mno-relax -O2 -ffreestanding -nostdlib -fno-pic` and
/// `ld.lld -static -e _start`).
#[test]
fn a_returned_call_result_stays_the_result() {
    let p = load(&Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/riscv/pass-through.elf"));
    let d = decompiled(&p, "f");
    assert!(!d.text.contains("__clobbered"), "{}", d.text);
    assert!(
        d.text.contains("v0 = (uint64_t)(g((void *)arg0));"),
        "{}",
        d.text
    );
    assert!(d.text.contains("return (uint64_t)(v0);"), "{}", d.text);
}

/// A call to a function returning a double leaves its result in fa0, and a
/// double argument goes out in fa0: float-call.c's square_half calls
/// `half(x)` and squares what it gives back. Before, the call read a0 and its
/// result read as `__clobbered()`. float-call.elf is built as the others but
/// with `-march=rv64imfd_zba_zbb -mabi=lp64d`.
#[test]
fn a_float_call_passes_and_returns_in_float_registers() {
    let p = load(&Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/riscv/float-call.elf"));
    let d = decompiled(&p, "square_half");
    assert!(d.text.contains(" = half(farg0);"), "{}", d.text);
    // n goes to tick in a0 untouched: still a parameter, not an inherited
    // register.
    assert!(
        d.signature
            .starts_with("double square_half(uint64_t arg0, double farg0)"),
        "{}",
        d.signature
    );
    assert!(d.text.contains("tick(arg0)"), "{}", d.text);
    assert!(!d.text.contains("__clobbered"), "{}", d.text);
    let d = decompiled(&p, "half");
    assert!(
        d.signature.starts_with("double half(double "),
        "{}",
        d.signature
    );
    // A call through a function pointer whose caller passes fa0 on: the
    // result is the float, not a clobber.
    let d = decompiled(&p, "apply");
    assert!(d.text.contains("half(v"), "{}", d.text);
    assert!(!d.text.contains("__clobbered"), "{}", d.text);
    // a1 set on one path, a0 the result: a1 is not a second argument.
    let d = decompiled(&p, "a1_scratch");
    assert!(
        d.signature
            .starts_with("uint64_t a1_scratch(uint32_t *arg0)"),
        "{}",
        d.signature
    );
    // fa1 loaded as scratch on one path reaches the return through a phi
    // with its entry value; that is not a second float argument.
    let d = decompiled(&p, "scratch_fa1");
    assert!(
        d.signature.contains("double farg0") && !d.signature.contains("farg1"),
        "{}",
        d.signature
    );
}

/// The value a return gives is the one that reaches it, not the newest
/// version of the result register: pass-through.c's len_or_fail returns
/// maybe_len's result, which it tested, and not that of `fail` on the path
/// that never returns (micropython's mp_obj_len returned a local nothing
/// assigned).
#[test]
fn a_return_gives_the_value_that_reaches_it() {
    let p = load(&Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/riscv/pass-through.elf"));
    let d = decompiled(&p, "len_or_fail");
    // fail is a loop nothing leaves, so it does not return, and the walk
    // stops after the call instead of running on into _start's code.
    assert!(
        !d.text.contains("__syscall") && !d.text.contains("while"),
        "{}",
        d.text
    );
    let assigned = d
        .text
        .lines()
        .find_map(|l| l.trim().strip_suffix(" = (uint64_t)(maybe_len(arg0));"))
        .unwrap_or_else(|| panic!("{}", d.text))
        .to_string();
    assert!(
        d.text.contains(&format!("return (uint64_t)({assigned});")),
        "{}",
        d.text
    );
}

/// A system call passes the arguments its caller set: openat takes four,
/// float-call.c's open_after sets three after a call to tick, and a3 (what
/// tick left) is not passed as a fourth; wake calls futex with three.
#[test]
fn a_system_call_passes_only_what_was_set() {
    let p = load(&Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/riscv/float-call.elf"));
    let d = decompiled(&p, "open_after");
    assert!(d.text.contains("__syscall(56, -100, arg0, v"), "{}", d.text);
    assert!(!d.text.contains("__clobbered"), "{}", d.text);
    // futex takes up to six; wake passes three, and a3..a5 (what wake was
    // entered with) are neither its parameters nor passed.
    let d = decompiled(&p, "wake");
    assert!(
        d.signature.starts_with("uint64_t wake(uint64_t arg0)"),
        "{}",
        d.signature
    );
    assert!(d.text.contains("__syscall(98, arg0, 129, 1)"), "{}", d.text);
    assert!(!d.text.contains("inherited"), "{}", d.text);
}

/// An inner loop whose exits are a return and the way back to the outer
/// loop continues at the latter: the return is written where the loop
/// branches to it, and no goto is needed (pass-through.c's first_bit, the
/// shape of mbedtls_mpi_lsb). Each return is written once. Exits that each
/// run one block and go on to the same place continue there (mal0_clear).
#[test]
fn a_returning_exit_is_not_where_a_loop_continues() {
    let p = load(&Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/riscv/pass-through.elf"));
    let d = decompiled(&p, "first_bit");
    assert!(!d.text.contains("goto "), "{}", d.text);
    assert_eq!(
        d.text.matches("return (uint64_t)(0);").count(),
        1,
        "{}",
        d.text
    );
    assert_eq!(
        d.text.matches("return (uint64_t)(v").count(),
        1,
        "{}",
        d.text
    );
    // An inner search whose "found" exit runs a loop and returns, the other
    // exit going on to the outer loop (scope_check_to_close_over's shape).
    let d = decompiled(&p, "find_in_lists");
    assert!(!d.text.contains("goto "), "{}", d.text);
    // An inner loop whose two exits each set the cursor and go back to the
    // outer loop's head (musl's mal0_clear): it continues there, and each
    // exit is written before a `break`.
    let d = decompiled(&p, "mal0_clear");
    assert!(!d.text.contains("goto "), "{}", d.text);
    assert_eq!(d.text.matches("break;").count(), 2, "{}", d.text);
}

/// A test that needs a call first, going where the test before it goes, is
/// one condition: `if (a || (v = f(x), v != 0))`. Without it the shared code
/// was either copied or reached by a goto (micropython's x509_crt_check_cn
/// had six). pass-through.c's or_call (assembly): the call is made once, in
/// the condition, and the result-0 path is the condition's false side.
#[test]
fn a_test_after_a_call_joins_the_condition_before_it() {
    let p = load(&Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/riscv/pass-through.elf"));
    let d = decompiled(&p, "or_call");
    assert!(!d.text.contains("goto "), "{}", d.text);
    assert_eq!(d.text.matches("maybe_len(").count(), 1, "{}", d.text);
    assert!(d.text.contains(" || (v"), "{}", d.text);
    assert!(d.text.contains("(maybe_len(arg0)), "), "{}", d.text);
    // The first test's way runs a block of its own first (pass_or): a
    // conditional expression, the store made once, on that side.
    let d = decompiled(&p, "pass_or");
    assert!(!d.text.contains("goto "), "{}", d.text);
    assert!(
        d.text
            .contains("(arg0->field_0 != 0) ? (arg0->field_8 = arg1, 1) : (arg2 == arg1)"),
        "{}",
        d.text
    );
    assert_eq!(
        d.text.matches("arg0->field_8 = arg1").count(),
        1,
        "{}",
        d.text
    );
}

/// Assigning what a call clobbered says nothing (the variable may hold
/// anything there, and keeping its value is one of those things), so no
/// `v = __clobbered();` is written. At f635598 musl's
/// libc-slen.elf printed 148 of them (printf_core in micropython 1221).
#[test]
fn a_clobbered_value_is_not_assigned() {
    let p = committed("libc-slen.elf");
    let all: Vec<&Function> = p.functions_by_address().collect();
    let unit = nocompiler_api::decompile_program(&p, &all);
    let n: usize = unit
        .functions
        .iter()
        .map(|d| {
            d.text
                .lines()
                .filter(|l| l.trim_end().ends_with("= __clobbered();"))
                .count()
        })
        .sum();
    assert_eq!(n, 0);
}

/// Linux's exit does not come back: pass-through.c's quit (`li a7, 93;
/// ecall`) ends there and does not run on into after_quit, which follows it
/// in memory (musl's __unmapself carried __clone's code).
#[test]
fn an_exit_system_call_does_not_return() {
    let p = load(&Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/riscv/pass-through.elf"));
    let d = decompiled(&p, "quit");
    assert!(d.signature.starts_with("void quit("), "{}", d.signature);
    assert!(!d.text.contains("+ 7"), "{}", d.text);
}

/// A jump through a 64-bit pointer loaded from memory, where no jump table
/// was read, is a tail call through a function pointer: the function's CFG is
/// complete and the jump is written as the call (pass-through.c's
/// via_pointer, the shape of micropython's fun_builtin_0_call and, through an
/// array of them, op_getitem). A jump through a 32-bit offset added to a base
/// (via_table, a switch's table with no bound) stays unresolved.
#[test]
fn a_jump_through_a_loaded_pointer_is_a_tail_call() {
    let p = load(&Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/riscv/pass-through.elf"));
    let f = |name: &str| {
        p.functions_by_address()
            .find(|f| f.display_name() == name)
            .expect("found")
    };
    assert!(f("via_pointer").cfg.is_complete());
    // An argument register (`jr a2`), a call's result through a move, and a
    // load with a null check between it and the jump.
    for name in ["via_arg", "via_result", "via_checked"] {
        assert!(f(name).cfg.is_complete(), "{name}");
    }
    assert!(!f("via_table").cfg.is_complete());
    let d = decompiled(&p, "via_pointer");
    assert!(
        d.text
            .contains("return (uint64_t)(__callind(*(uint64_t *)(arg0 + 8), arg1));"),
        "{}",
        d.text
    );
    // A jump to a constant address that is a function of the unit is that
    // function's call, by name (musl's __libc_start_main to
    // libc_start_main_stage2).
    assert!(f("via_constant").cfg.is_complete());
    let d = decompiled(&p, "via_constant");
    assert!(d.text.contains("maybe_len("), "{}", d.text);
    assert!(!d.text.contains("__callind("), "{}", d.text);
    let d = decompiled(&p, "via_table");
    assert!(d.text.contains("__indirect_branch("), "{}", d.text);
}

/// A function that leaves only by a tail call returns what the callee
/// returns, so `show` (variadic.elf) returns `sum_n`'s result; one whose tail
/// callee returns nothing, or that also returns with nothing (`if (p) tail(p);
/// return;`), returns nothing (pass-through.c's tail_void and maybe).
#[test]
fn a_tail_call_returns_what_the_callee_returns() {
    let p = load(&Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/riscv/pass-through.elf"));
    for name in ["tail_void", "maybe"] {
        let d = decompiled(&p, name);
        assert!(d.signature.starts_with("void "), "{name}: {}", d.signature);
        // Both hand their pointer on to `nothing`; tail_void never reads it.
        assert!(d.signature.contains("arg0"), "{name}: {}", d.signature);
        assert!(!d.text.contains("__clobbered"), "{name}: {}", d.text);
    }
}

/// A loop-header phi of an entry value and clobbers is not an argument:
/// musl's __lock and __lockfile take one pointer, not two doubles besides
/// (the walk gave up at a depth limit on the loop's phi cycle).
#[test]
fn a_loop_does_not_invent_float_arguments() {
    let p = committed("libc-slen.elf");
    for name in ["__lock", "__lockfile"] {
        let d = decompiled(&p, name);
        assert!(!d.signature.contains("double"), "{name}: {}", d.signature);
        assert!(
            !d.signature.contains("arg1"),
            "{name}: one argument: {}",
            d.signature
        );
    }
}

/// A variadic function spills a1-a7 for `va_start`; it takes its fixed
/// parameters and `...`, and a call passes what the caller set (before: eight
/// arguments, the last five the caller's own entry registers). Fixture:
/// tests/riscv/variadic.c, built as pass-through.c is.
#[test]
fn a_variadic_callee_gets_what_the_caller_set() {
    let p = load(&Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/riscv/variadic.elf"));
    let d = decompiled(&p, "sum_n");
    assert_eq!(
        d.signature, "uint64_t sum_n(uint64_t arg0, ...)",
        "{}",
        d.text
    );
    let d = decompiled(&p, "show");
    // show tail-calls sum_n, so it returns what sum_n returns.
    assert!(
        d.text.contains("return (uint64_t)(sum_n(2, arg0, 7));"),
        "{}",
        d.text
    );
    assert!(d.signature.starts_with("uint64_t show("), "{}", d.signature);
    assert!(!d.text.contains("inherited"), "{}", d.text);
    // And the unit is C a compiler takes.
    if Command::new("clang").arg("--version").output().is_err() {
        return;
    }
    let all: Vec<&Function> = p.functions_by_address().collect();
    let unit = nocompiler_api::decompile_program(&p, &all);
    let dir = std::env::temp_dir().join(format!(
        "nocompiler-decomp-riscv-variadic-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("out.c"), unit.text()).unwrap();
    let out = Command::new("clang")
        .args(["-c", "-w", "-ffreestanding", "-o"])
        .arg(dir.join("out.o"))
        .arg(dir.join("out.c"))
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&out.stderr),
        unit.text()
    );
}

/// A system call returns its result in a0 and leaves the rest alone: hello's
/// write loop advances by what `write` (64) returned. Before, every register
/// after the ecall read as `__clobbered()` (`v4 = __clobbered() - v2`).
#[test]
fn a_system_call_returns_its_result() {
    let p = committed("hello.elf");
    let d = decompiled(&p, "write_all");
    assert!(!d.text.contains("__clobbered"), "{}", d.text);
    assert!(d.text.contains("__syscall(64, arg0, v1, v2)"), "{}", d.text);
    assert!(d.text.contains("v2 = v2 - v0;"), "{}", d.text);
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
    let mut callind = 0usize;
    let mut clobbered = 0usize;
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
            if let (Some(d), Some(dir)) = (&d, std::env::var_os("NOCOMPILER_COVERAGE_DUMP")) {
                // The pseudo-C of every function with a defect marker, to read what each count is.
                if d.text.contains("__clobbered()") || d.text.contains("__callind(") || d.gotos > 0
                {
                    let file: String = name
                        .chars()
                        .map(|c| {
                            if c.is_ascii_alphanumeric() || c == '_' {
                                c
                            } else {
                                '_'
                            }
                        })
                        .collect();
                    let _ = std::fs::create_dir_all(&dir);
                    let _ = std::fs::write(Path::new(&dir).join(format!("{file}.c")), &d.text);
                }
            }
            if let Some(d) = &d {
                gotos += d.gotos;
                with_goto += usize::from(d.gotos > 0);
                callind += usize::from(d.text.contains("__callind("));
                clobbered += usize::from(d.text.contains("__clobbered()"));
            }
            outcome.entry(o).or_default().push(name);
        }
    }
    let mut incomplete_names: Vec<String> = Vec::new();
    for f in &all {
        if !f.is_complete() {
            incomplete_cfg += 1;
            incomplete_names.push(f.display_name());
        }
    }
    // With NOCOMPILER_COVERAGE_DUMP, also which functions those are.
    if let Some(dir) = std::env::var_os("NOCOMPILER_COVERAGE_DUMP") {
        let _ = std::fs::write(
            Path::new(&dir).join("incomplete-cfg.txt"),
            incomplete_names.join("\n") + "\n",
        );
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
    eprintln!("  functions with an unresolved indirect call (__callind): {callind}");
    eprintln!("  functions reading a register a call clobbered (__clobbered): {clobbered}");
    eprintln!("  functions whose CFG is incomplete (unresolved indirect jump): {incomplete_cfg}");
}

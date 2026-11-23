//! Calls to undefined symbols in a relocatable object reach a named stub.
//!
//! glibc's `snprintf.o` (AArch64) is two calls with nothing defined behind
//! them: `bl __vsnprintf_internal` and, on the stack-check path, the last
//! instruction of `.text`, `bl __stack_chk_fail`. With the relocation left
//! unapplied both are `bl .`, a call to itself. With a stub each `bl` lands on
//! an import thunk that carries the name, which is what lets the analysis know
//! the second one does not return.
//!
//! The archive comes from the AArch64 cross compiler (`gcc-aarch64-linux-gnu`
//! in CI's container); without it the test skips.

use std::path::PathBuf;
use std::process::Command;

use nocompiler_core::{Addr, Evidence};
use nocompiler_format::{LoadOptions, archive};

fn libc_a() -> Option<PathBuf> {
    let cc = ["aarch64-linux-gnu-gcc", "gcc"]
        .into_iter()
        .find(|c| Command::new(c).arg("--version").output().is_ok())?;
    let out = Command::new(cc)
        .arg("-print-file-name=libc.a")
        .output()
        .ok()?;
    let path = PathBuf::from(String::from_utf8(out.stdout).ok()?.trim());
    (path.is_absolute() && path.is_file()).then_some(path)
}

/// Where the `bl` at `at` goes.
fn bl_target(mem: &nocompiler_core::MemoryMap, at: Addr) -> Addr {
    let b = mem.slice(at, 4).expect("mapped");
    let word = u32::from_le_bytes([b[0], b[1], b[2], b[3]]);
    assert_eq!(word >> 26, 0b100101, "{at} is not a bl: {word:#010x}");
    let imm = ((word & 0x03ff_ffff) << 6) as i32 >> 6;
    Addr(at.get().wrapping_add((imm as i64 * 4) as u64))
}

#[test]
fn every_call_to_an_undefined_symbol_reaches_its_named_stub() {
    let Some(path) = libc_a() else {
        eprintln!("no libc.a for an AArch64 compiler; skipped");
        return;
    };
    let data = std::fs::read(&path).unwrap();
    let ar = archive::open(&data).unwrap();
    let Some((n, _)) = ar.objects().find(|(_, m)| m.name == "snprintf.o") else {
        eprintln!("{} has no snprintf.o; skipped", path.display());
        return;
    };
    let obj = ar.load_member(n, &LoadOptions::default()).unwrap();
    if obj.arch != nocompiler_core::Arch::AArch64 {
        eprintln!("{} is not AArch64; skipped", path.display());
        return;
    }
    let text = obj.section(".text").expect(".text").range;

    let stub = |name: &str| -> Addr {
        let imp = obj
            .imports
            .iter()
            .find(|im| im.name == name)
            .unwrap_or_else(|| panic!("no import {name}: {:?}", obj.imports));
        let t = imp.thunk.unwrap_or_else(|| panic!("{name} has no stub"));
        assert!(!text.contains(t), "{name}'s stub {t} is inside .text");
        let hint = obj
            .function_hints
            .iter()
            .find(|h| h.addr == t)
            .unwrap_or_else(|| panic!("no function hint at {name}'s stub {t}"));
        assert_eq!(hint.name.as_deref(), Some(format!("{name}@plt").as_str()));
        assert_eq!(hint.provenance.best, Evidence::ImportThunk);
        t
    };

    // Every `bl` in `.text`, and where it goes.
    let mut calls = Vec::new();
    let mut at = text.start();
    while at < text.end() {
        let b = obj.memory.slice(at, 4).unwrap();
        if u32::from_le_bytes([b[0], b[1], b[2], b[3]]) >> 26 == 0b100101 {
            calls.push((at, bl_target(&obj.memory, at)));
        }
        at = Addr(at.get() + 4);
    }
    let targets: Vec<Addr> = calls.iter().map(|(_, t)| *t).collect();
    assert!(
        calls.iter().all(|(at, t)| at != t),
        "a bl still calls itself: {calls:x?}"
    );
    for name in ["__vsnprintf_internal", "__stack_chk_fail"] {
        let t = stub(name);
        assert!(
            targets.contains(&t),
            "no bl reaches {name}'s stub {t}: {calls:x?}"
        );
    }
    assert_eq!(
        obj.metadata.get("elf.extern_stubs").map(String::as_str),
        Some("2"),
        "one stub per undefined callee"
    );
}

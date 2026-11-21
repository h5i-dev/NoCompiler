//! `nocompiler funcs` and `xrefs` on a RISC-V ELF go to the core, not the
//! toolkit (which has no RISC-V and answered "no functions recovered").

use std::process::Command;

#[test]
fn funcs_and_xrefs_on_a_risc_v_elf() {
    let exe = env!("CARGO_BIN_EXE_nocompiler");
    let elf = concat!(env!("CARGO_MANIFEST_DIR"), "/../../examples/elf/sum.elf");
    let out = Command::new(exe).args(["funcs", elf]).output().unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let s = String::from_utf8(out.stdout).unwrap();
    assert!(s.contains("L2    sum2"), "{s}");
    let out = Command::new(exe)
        .args(["xrefs", elf, "sum"])
        .output()
        .unwrap();
    assert!(out.status.success());
    assert_eq!(String::from_utf8(out.stdout).unwrap().lines().count(), 4);
    // sum calls nothing: what it refers to is its own loop's branches.
    let out = Command::new(exe)
        .args(["xrefs", elf, "0x11190", "--from"])
        .output()
        .unwrap();
    let s = String::from_utf8(out.stdout).unwrap();
    assert!(
        !s.is_empty() && s.lines().all(|l| l.starts_with("branch")),
        "{s}"
    );
    // An address nothing refers to (.data + 8): "no references", exit 1.
    let out = Command::new(exe)
        .args(["xrefs", elf, "0x12270"])
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(1));
}

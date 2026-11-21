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

/// `symbols --filter` and the default limit (lead 17:05, item 2): a solver's
/// client cannot take a 575 KB list.
#[test]
fn symbols_filter_and_limit() {
    let exe = env!("CARGO_BIN_EXE_nocompiler");
    let elf = concat!(env!("CARGO_MANIFEST_DIR"), "/../../examples/elf/sum.elf");
    let run = |args: &[&str]| {
        let out = Command::new(exe)
            .arg("symbols")
            .arg(elf)
            .args(args)
            .output()
            .unwrap();
        (out.status.code(), String::from_utf8(out.stdout).unwrap())
    };
    let (_, all) = run(&[]);
    assert!(all.contains("object    static  data"), "{all}");
    let (_, f) = run(&["--filter", "SUM2"]);
    assert_eq!(f.lines().count(), 1, "{f}");
    assert!(f.contains("function  static  sum2"), "{f}");
    let (_, one) = run(&["--limit", "1"]);
    let n = all.lines().count();
    assert_eq!(one.lines().count(), 2, "{one}");
    assert!(one.ends_with(&format!(
        "... {} more of {n} (--limit 0 for all, --filter NAME to narrow)\n",
        n - 1
    )));
    assert_eq!(run(&["--filter", "zzz_none"]).0, Some(1));
}

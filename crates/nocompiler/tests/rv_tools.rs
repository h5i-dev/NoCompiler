//! `funcs` and `xrefs` on RISC-V binaries (crate::rv_tools): the toolkit's
//! crates decode x86 and Arm only, so these come from the core.

use std::path::PathBuf;

fn load(name: &str) -> Vec<u8> {
    std::fs::read(
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../examples/elf")
            .join(name),
    )
    .unwrap()
}

#[test]
fn funcs_lists_every_function_with_its_level() {
    let bytes = load("sum.elf");
    let bin = nocompiler::load(&bytes).unwrap();
    let t = nocompiler::rv_tools::funcs(&bin, false);
    assert!(
        t.contains("0x11190                   36       9  L2    sum\n"),
        "{t}"
    );
    assert!(t.contains("sum2") && t.contains("_start"), "{t}");
    let j = nocompiler::rv_tools::funcs(&bin, true);
    assert!(
        j.contains("{\"addr\":70032,\"size\":36,\"insns\":9,\"level\":\"L2\",\"name\":\"sum\"}"),
        "{j}"
    );
}

#[test]
fn xrefs_finds_calls_and_addresses() {
    let bytes = load("sum.elf");
    let bin = nocompiler::load(&bytes).unwrap();
    // `sum` is called twice from sum2 and twice from _start (auipc+jalr pairs).
    let (t, n) = nocompiler::rv_tools::xrefs(&bin, "sum", false, false).unwrap();
    assert_eq!(n, 4, "{t}");
    assert!(t.contains("call      0x111d0 in sum2+0x1c"), "{t}");
    // _start forms the address of .data and calls sum.
    let (t, _) = nocompiler::rv_tools::xrefs(&bin, "_start", true, false).unwrap();
    assert!(
        t.starts_with("addr      0x12268\ncall      0x11190 in sum\n"),
        "{t}"
    );
    // By address, and an unknown name.
    assert_eq!(
        nocompiler::rv_tools::xrefs(&bin, "0x12268", false, false)
            .unwrap()
            .1,
        1
    );
    assert!(nocompiler::rv_tools::xrefs(&bin, "no_such_symbol", false, false).is_none());
    // Branches: sum's loop branches back into itself.
    let all = nocompiler::rv_tools::all_xrefs(&bin);
    assert!(
        all.iter()
            .any(|x| x.kind == "branch" && x.from >= 0x11190 && x.from < 0x111b4)
    );
}

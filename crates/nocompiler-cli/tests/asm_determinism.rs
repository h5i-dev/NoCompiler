//! `asm` is deterministic (docs/toolkit/design/patch-stack.md, the contract a
//! patch stack's rebuild relies on): the same text gives the same object
//! bytes in another directory, under another file name. (Not claimed: the
//! same code at two layouts gives the same object. `disasm` lists functions
//! in address order, so the object's sections follow the layout's order.)

use std::process::Command;

fn run(exe: &str, dir: &std::path::Path, args: &[&str]) -> std::process::Output {
    Command::new(exe)
        .args(args)
        .current_dir(dir)
        .output()
        .unwrap()
}

#[test]
fn the_same_text_gives_the_same_object() {
    let exe = env!("CARGO_BIN_EXE_nocompiler");
    let root = format!("{}/../../examples/elf", env!("CARGO_MANIFEST_DIR"));
    let tmp = std::env::temp_dir().join(format!("nc-asm-det-{}", std::process::id()));
    let (x, y) = (tmp.join("x"), tmp.join("y/deeper"));
    std::fs::create_dir_all(&x).unwrap();
    std::fs::create_dir_all(&y).unwrap();
    for elf in ["sum.link1.elf", "sum.link2.elf", "hello.elf"] {
        let text = run(exe, &x, &["disasm", &format!("{root}/{elf}")]).stdout;
        std::fs::write(x.join("a.s"), &text).unwrap();
        std::fs::write(y.join("other-name.s"), &text).unwrap();
        assert!(run(exe, &x, &["asm", "a.s", "-o", "a.o"]).status.success());
        assert!(
            run(exe, &y, &["asm", "other-name.s", "-o", "b.o"])
                .status
                .success()
        );
        let (a, b) = (
            std::fs::read(x.join("a.o")).unwrap(),
            std::fs::read(y.join("b.o")).unwrap(),
        );
        assert_eq!(
            a, b,
            "{elf}: the object depends on the directory or the file name"
        );
    }
    let _ = std::fs::remove_dir_all(&tmp);
}

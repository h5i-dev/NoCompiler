//! Patch stacks (crate::stack, Q-VC2): the committed stack rebuilds to the
//! committed SHA-256, a changed patch is refused, and the format reads back.

use std::path::PathBuf;

fn dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/stack")
}

/// The lead's test: rebuild == the committed SHA-256.
#[test]
fn the_committed_stack_rebuilds_to_its_result() {
    let text = std::fs::read_to_string(dir().join("sum.nocompiler-stack")).unwrap();
    let s = nocompiler::stack::parse(&text).unwrap();
    let bin = nocompiler::stack::build(&s, &dir()).unwrap();
    assert_eq!(Some(nocompiler::stack::result_sha(&bin)), s.result);
    // And twice gives the same bytes.
    assert_eq!(nocompiler::stack::build(&s, &dir()).unwrap(), bin);
    // The result runs sum from refine-sum-b.elf: in the new segment, the old sum redirected.
    let b = nocompiler::load(&bin).unwrap();
    assert_eq!(b.extra_exec, [".swb"]);
}

#[test]
fn a_changed_patch_is_refused() {
    let tmp = std::env::temp_dir().join(format!("nc-stack-{}", std::process::id()));
    std::fs::create_dir_all(&tmp).unwrap();
    let mut s = nocompiler::stack::parse(
        &std::fs::read_to_string(dir().join("sum.nocompiler-stack")).unwrap(),
    )
    .unwrap();
    s.base.1 = dir().join(&s.base.1);
    let text = std::fs::read_to_string(dir().join("sum-from-b.s")).unwrap();
    std::fs::write(
        tmp.join("sum-from-b.s"),
        text.replace("add a2, a2, a3", "add a2, a3, a2"),
    )
    .unwrap();
    let e = nocompiler::stack::build(&s, &tmp).unwrap_err();
    let _ = std::fs::remove_dir_all(&tmp);
    assert!(e.contains("is not the stack's"), "{e}");
}

#[test]
fn the_format() {
    let t = std::fs::read_to_string(dir().join("sum.nocompiler-stack")).unwrap();
    let s = nocompiler::stack::parse(&t).unwrap();
    assert_eq!(s.patches.len(), 1);
    assert_eq!(
        nocompiler::stack::parse(&nocompiler::stack::render(&s)).unwrap(),
        s
    );
    let bad = |t: &str| nocompiler::stack::parse(t).unwrap_err();
    assert!(bad("").contains("empty"));
    assert!(bad("nocompiler-stack 2\n").contains("want `nocompiler-stack 1`"));
    assert!(bad("nocompiler-stack 1\npatch 00 x.s\n").contains("line 2"));
    assert!(bad("nocompiler-stack 1\nbase XYZ a.elf\n").contains("not a lowercase SHA-256"));
    assert!(bad("nocompiler-stack 1\n# only a comment\n").contains("no `base` line"));
}

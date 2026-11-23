//! `link`: the whole-program checks across files (S5 over all files, declarations against
//! definitions).

use nocompiler_typed::check::{Options, Rule};
use nocompiler_typed::link::link;

fn f(name: &str, src: &str) -> (String, String) {
    (name.to_string(), src.to_string())
}

const F: &str = "#: fn f [] stack 0\n#: fn g [] stack 0\nf:\n    tail g\n";
const G: &str = "#: fn g [] stack 0\n#: fn f [] stack 0\ng:\n    tail f\n";

#[test]
fn a_cycle_across_files_is_rejected() {
    let r = link(&[f("f.s", F), f("g.s", G)], Options::default());
    assert!(!r.ok());
    assert!(r.errors.iter().any(|(_, e)| e.rule == Rule::Recursion));
    // each file alone is fine
    assert!(
        link(&[f("f.s", F)], Options::default())
            .errors
            .iter()
            .any(|(_, e)| e.rule == Rule::Sig)
    );
}

#[test]
fn declarations_must_match_and_exist() {
    let def = "#: fn h [n] in a0: int(n) out a0: int(n) stack 0\nh:\n    ret\n";
    let ok = "#: fn h [n] in a0: int(n) out a0: int(n) stack 0\n#: fn k [] frame 16 slots 8 stack 16\nk:\n    addi sp, sp, -16\n    sd ra, 8(sp)\n    call h\n    ld ra, 8(sp)\n    addi sp, sp, 16\n    ret\n";
    let r = link(&[f("h.s", def), f("k.s", ok)], Options::default());
    assert!(r.ok(), "{:?}", r.errors);
    let bad = ok.replace("out a0: int(n)", "out a0: int(n + 1)");
    let r = link(&[f("h.s", def), f("k.s", &bad)], Options::default());
    assert!(
        r.errors
            .iter()
            .any(|(_, e)| e.rule == Rule::Sig && e.msg.contains("differs"))
    );
    let r = link(&[f("k.s", ok)], Options::default());
    assert!(
        r.errors
            .iter()
            .any(|(_, e)| e.msg.contains("defined in none"))
    );
}

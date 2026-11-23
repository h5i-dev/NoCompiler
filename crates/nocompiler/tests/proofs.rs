//! Proof status per version (Q-VC3, crate::proofs, `nocompiler status`):
//! which theorems about one build still cover another.

use nocompiler::module::Module;
use nocompiler::proofs::{self, State, Status};
use std::path::PathBuf;

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn module(name: &str) -> Module {
    let bytes = std::fs::read(root().join("examples/elf").join(name)).unwrap();
    nocompiler::module::of_binary(&nocompiler::load(&bytes).unwrap()).unwrap()
}

/// A proofs file about sum.link1.elf with a (placeholder) proof per function.
fn every_function(m: &Module) -> proofs::Proofs {
    let keys = nocompiler::module::keys(m);
    let mut ps: Vec<proofs::Proof> = m
        .funcs
        .iter()
        .map(|f| proofs::Proof {
            function: f.name.clone(),
            theorem: format!("T.{}_ok", f.name),
            spec: "T.spec".into(),
            closure: keys[&f.name].1.clone(),
            state: State::Checked,
        })
        .collect();
    ps.sort_by(|a, b| a.function.cmp(&b.function));
    proofs::Proofs {
        subject: proofs::Subject::Module("0".repeat(64), "sum.link1.elf".into()),
        proofs: ps,
    }
}

fn run(
    new: &std::path::Path,
    proofs: &std::path::Path,
    o: &nocompiler::cmd::StatusOpts,
) -> (u8, String) {
    let mut out = String::new();
    let code = nocompiler::cmd::status(new, proofs, o, &mut out).unwrap();
    (code, out)
}

/// The same object at two layouts: the committed proof carries, and the
/// command says so.
#[test]
fn the_proof_of_sum_carries_to_the_other_link() {
    let p = root().join("examples/link/sum.nocompiler-proofs");
    for e in ["sum.link1.elf", "sum.link2.elf"] {
        let (code, out) = run(
            &root().join("examples/elf").join(e),
            &p,
            &Default::default(),
        );
        assert_eq!(code, 0, "{out}");
        assert_eq!(
            out,
            "sum  carries  Examples.Link.sum_relocatable\n1 proofs: 1 carries, 0 invalidated, 0 unknown\n"
        );
    }
}

/// One function edited in a module: it is `edited`, its callers name it.
#[test]
fn an_edit_invalidates_the_function_and_its_callers() {
    let a = module("sum.link1.elf");
    let p = every_function(&a);
    let mut e = a.clone();
    e.funcs.iter_mut().find(|f| f.name == "sum").unwrap().words[0] ^= 1 << 7;
    let st = proofs::status(&a, &e, &p).unwrap();
    let names: Vec<&str> = p.proofs.iter().map(|q| q.function.as_str()).collect();
    assert_eq!(names, ["_start", "sum", "sum2"]);
    assert_eq!(st[0], Status::Callee("sum".into()));
    assert!(matches!(st[1], Status::Edited(..)));
    assert_eq!(st[2], Status::Callee("sum".into()));
    assert_eq!(st[0].label(), "invalidated: callee sum");
    // Unchanged: everything carries.
    let st = proofs::status(&a, &a.clone(), &p).unwrap();
    assert!(st.iter().all(Status::carries));
    // Gone, skipped.
    let mut g = a.clone();
    g.funcs.retain(|f| f.name != "sum2");
    assert_eq!(proofs::status(&a, &g, &p).unwrap()[2], Status::Removed);
    let mut s = g.clone();
    s.skipped.push(nocompiler::module::Skipped {
        name: "sum2".into(),
        entry: 0,
        reason: "test".into(),
    });
    let st = proofs::status(&a, &s, &p).unwrap();
    assert_eq!(st[2], Status::Skipped("test".into()));
    assert!(!st[2].invalidated() && !st[2].carries());
}

/// `_start` takes a data address: at the other link the data moved, so its
/// proof is `unknown: layout-dependent spec`; `sum`, which takes none,
/// carries. Changed data contents make it unknown too.
#[test]
fn a_moved_address_makes_the_spec_unknown() {
    let (a, b) = (module("sum.link1.elf"), module("sum.link2.elf"));
    let p = every_function(&a);
    let st = proofs::status(&a, &b, &p).unwrap();
    assert!(matches!(&st[0], Status::LayoutDependent(_)), "{st:?}");
    assert_eq!(st[0].label(), "unknown: layout-dependent spec");
    assert_eq!(st[1], Status::Carries);
    let mut d = a.clone();
    let sym = match &st[0] {
        Status::LayoutDependent(s) => s.clone(),
        _ => unreachable!(),
    };
    let data = d.data.iter_mut().find(|x| x.name == sym).unwrap();
    data.bytes[0] ^= 1;
    data.zero = false;
    let st = proofs::status(&a, &d, &p).unwrap();
    assert_eq!(st[0], Status::Data(sym));
    assert_eq!(st[0].label(), "unknown: layout-dependent spec");
    assert!(!st[0].invalidated());
}

/// A caller whose only change is the name its call reaches (as after a
/// patch, through the jump at the old entry) is `callee X`, X the name the
/// old build called.
#[test]
fn a_retargeted_call_names_the_callee() {
    let a = module("sum.link1.elf");
    let p = every_function(&a);
    let mut e = a.clone();
    for f in e.funcs.iter_mut() {
        for r in f.relocs.iter_mut() {
            if r.sym == "sum" {
                r.sym = "sum_old".into();
            }
        }
    }
    let st = proofs::status(&a, &e, &p).unwrap();
    assert_eq!(st[2], Status::Callee("sum".into()), "{st:?}");
    // Another word as well: edited.
    e.funcs.iter_mut().find(|f| f.name == "sum2").unwrap().words[0] ^= 1 << 7;
    assert!(matches!(
        proofs::status(&a, &e, &p).unwrap()[2],
        Status::Edited(..)
    ));
}

/// A proofs file whose key is not its binary's is refused.
#[test]
fn a_wrong_key_is_refused() {
    let a = module("sum.link1.elf");
    let mut p = every_function(&a);
    p.proofs[1].closure = "1".repeat(64);
    let e = proofs::status(&a, &a, &p).unwrap_err();
    assert!(e.contains("in the proofs file"), "{e}");
}

/// The patch stack replacing `sum`: `sum` is edited; `_start` (an exit
/// system call, no call to `sum`) carries. `--record` keeps only `_start`,
/// `by-key`, about the stack.
#[test]
fn the_stack_edits_sum() {
    let dir = root().join("crates/nocompiler/tests/stack");
    let tmp = std::env::temp_dir().join(format!("nc-status-{}", std::process::id()));
    std::fs::create_dir_all(&tmp).unwrap();
    let rec = tmp.join("b.nocompiler-proofs");
    let (code, out) = run(
        &dir.join("sum.nocompiler-stack"),
        &dir.join("sum-base.nocompiler-proofs"),
        &nocompiler::cmd::StatusOpts {
            record: Some(&rec),
            ..Default::default()
        },
    );
    assert_eq!(code, 1);
    assert!(
        out.contains("_start  carries              Test.start_ok\n"),
        "{out}"
    );
    assert!(
        out.contains("sum     invalidated: edited  Test.sum_ok  (sha256 a3944f27.. -> "),
        "{out}"
    );
    assert!(
        out.contains("2 proofs: 1 carries, 1 invalidated, 0 unknown\n"),
        "{out}"
    );
    let r = proofs::parse(&std::fs::read_to_string(&rec).unwrap()).unwrap();
    let _ = std::fs::remove_dir_all(&tmp);
    assert!(matches!(&r.subject, proofs::Subject::Stack(s, _) if s.starts_with("e5c9b8c6")));
    assert_eq!(r.proofs.len(), 1);
    assert_eq!(
        (r.proofs[0].function.as_str(), r.proofs[0].state),
        ("_start", State::ByKey)
    );
}

/// `--lean` writes both modules and a theorem per carried proof; `--checked`
/// accepts only the compiled file of exactly that text.
#[test]
fn the_lean_file_and_checked() {
    let tmp = std::env::temp_dir().join(format!("nc-status-lean-{}", std::process::id()));
    std::fs::create_dir_all(&tmp).unwrap();
    let (new, p) = (
        root().join("examples/elf/sum.link2.elf"),
        root().join("examples/link/sum.nocompiler-proofs"),
    );
    let lean = tmp.join("S.lean");
    let (_, out) = run(
        &new,
        &p,
        &nocompiler::cmd::StatusOpts {
            lean: Some(&lean),
            ..Default::default()
        },
    );
    assert!(
        out.contains("  sum Examples.Link.sum_relocatable: NoCompilerStatus.r_1\n"),
        "{out}"
    );
    let text = std::fs::read_to_string(&lean).unwrap();
    assert_eq!(text.matches("\nimport ").count(), 1, "{text}");
    for want in [
        "namespace NoCompilerStatus.Old\n",
        "namespace NoCompilerStatus.New\n",
        "theorem r_1 {α : Type}",
    ] {
        assert!(text.contains(want), "{want}: {text}");
    }
    // Only the proofs' functions get a theorem.
    assert_eq!(text.matches("theorem ").count(), 1);
    // A stand-in for the compiled file, newer than the source.
    let olean = tmp.join("S.olean");
    std::fs::write(&olean, b"").unwrap();
    let rec = tmp.join("r.nocompiler-proofs");
    let o = nocompiler::cmd::StatusOpts {
        record: Some(&rec),
        checked: Some(&olean),
        ..Default::default()
    };
    run(&new, &p, &o);
    let r = proofs::parse(&std::fs::read_to_string(&rec).unwrap()).unwrap();
    assert_eq!(r.proofs[0].state, State::Checked);
    // Another text beside the .olean: refused.
    std::fs::write(&lean, text.replace("r_1", "r_9")).unwrap();
    std::fs::write(&olean, b"").unwrap();
    let mut out = String::new();
    let e = nocompiler::cmd::status(&new, &p, &o, &mut out).unwrap_err();
    let _ = std::fs::remove_dir_all(&tmp);
    assert!(e.contains("not the reuse file of these builds"), "{e}");
}

#[test]
fn the_format() {
    let t = std::fs::read_to_string(root().join("examples/link/sum.nocompiler-proofs")).unwrap();
    let p = proofs::parse(&t).unwrap();
    assert_eq!(proofs::parse(&proofs::render(&p)).unwrap(), p);
    assert!(proofs::is_proofs(&t));
    assert!(!proofs::is_proofs("sum\tA\tB\n"));
    let bad = |t: &str| proofs::parse(t).unwrap_err();
    assert!(bad("").contains("empty"));
    assert!(bad("nocompiler-proofs 2\n").contains("want `nocompiler-proofs 1`"));
    assert!(bad("nocompiler-proofs 1\n").contains("no `module`"));
    let m = format!("nocompiler-proofs 1\nmodule {} a.elf\n", "a".repeat(64));
    let k = "b".repeat(64);
    assert!(bad(&format!("{m}proof f T S closure {k} proved\n")).contains("want `checked`"));
    assert!(
        bad(&format!(
            "{m}proof f T S closure {k} checked\nproof f T S closure {k} by-key\n"
        ))
        .contains("twice")
    );
    // A `#` inside a name is not a comment (namesakes are `f#k`).
    let p = proofs::parse(&format!("{m}# note\nproof f#1 T S closure {k} checked\n")).unwrap();
    assert_eq!(p.proofs[0].function, "f#1");
}

/// `ledger --proofs` reads a proofs file as it reads the TSV.
#[test]
fn the_ledger_reads_a_proofs_file() {
    let mut a = String::new();
    let mut b = String::new();
    let elf = root().join("examples/elf/sum.link1.elf");
    nocompiler::cmd::ledger(&elf, Some(&root().join("examples/link/proofs.tsv")), &mut a).unwrap();
    nocompiler::cmd::ledger(
        &elf,
        Some(&root().join("examples/link/sum.nocompiler-proofs")),
        &mut b,
    )
    .unwrap();
    assert_eq!(a, b);
}

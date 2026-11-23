//! `nocompiler textconv`: the text git diffs (docs/toolkit/git-diff.md).

use std::process::Command;

fn textconv(elf: &str) -> String {
    let exe = env!("CARGO_BIN_EXE_nocompiler");
    let p = format!("{}/../../examples/elf/{elf}", env!("CARGO_MANIFEST_DIR"));
    let out = Command::new(exe).args(["textconv", &p]).output().unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).unwrap()
}

fn block<'a>(t: &'a str, name: &str) -> &'a str {
    let h = format!("\nfunc {name}  ;");
    let a = t.find(&h).unwrap() + 1;
    let b = t[a..].find("\nfunc ").map_or(t.len(), |k| a + k);
    &t[a..b]
}

/// The same object at two layouts: the same text.
#[test]
fn addresses_do_not_show() {
    assert_eq!(textconv("sum.link1.elf"), textconv("sum.link2.elf"));
}

/// Two binaries that differ in `sum` only: only `sum`'s block differs.
#[test]
fn a_one_function_change_shows_in_that_function_only() {
    let (a, b) = (textconv("refine-sum-a.elf"), textconv("refine-sum-b.elf"));
    assert_eq!(block(&a, "_start"), block(&b, "_start"));
    assert_ne!(block(&a, "sum"), block(&b, "sum"));
    // Calls and data references name their targets (sum.link1.elf's _start).
    let l = textconv("sum.link1.elf");
    assert!(
        block(&l, "_start").contains("auipc ra, 0  ; reloc call sum"),
        "{l}"
    );
    assert!(block(&l, "_start").contains("; reloc pcrel_hi data"), "{l}");
}

/// Through git itself, with the documented config: the diff names `sum` only.
#[test]
fn git_diff_shows_the_changed_function() {
    let exe = env!("CARGO_BIN_EXE_nocompiler");
    let root = format!("{}/../../examples/elf", env!("CARGO_MANIFEST_DIR"));
    let dir = std::env::temp_dir().join(format!("nc-textconv-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let git = |args: &[&str]| {
        Command::new("git")
            .args([
                "-c",
                "user.name=t",
                "-c",
                "user.email=t@t",
                "-c",
                "commit.gpgsign=false",
            ])
            .args(args)
            .current_dir(&dir)
            .output()
    };
    if git(&["init", "-q"]).is_err() {
        eprintln!("git not installed: skipping");
        return;
    }
    std::fs::write(dir.join(".gitattributes"), "*.elf diff=nocompiler\n").unwrap();
    git(&[
        "config",
        "diff.nocompiler.textconv",
        &format!("{exe} textconv"),
    ])
    .unwrap();
    git(&["config", "diff.nocompiler.xfuncname", "^func .*"]).unwrap();
    std::fs::copy(format!("{root}/refine-sum-a.elf"), dir.join("p.elf")).unwrap();
    git(&["add", "."]).unwrap();
    git(&["commit", "-q", "-m", "a"]).unwrap();
    std::fs::copy(format!("{root}/refine-sum-b.elf"), dir.join("p.elf")).unwrap();
    let out = git(&["diff", "--", "p.elf"]).unwrap();
    let d = String::from_utf8(out.stdout).unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        d.contains("-func sum  ;") && d.contains("+func sum  ;"),
        "{d}"
    );
    assert!(
        d.contains("-  add a2, a3, a2") && d.contains("+  add a2, a2, a3"),
        "{d}"
    );
    assert!(!d.contains("Binary files"), "{d}");
    let changed: Vec<&str> = d
        .lines()
        .filter(|l| l.starts_with(['+', '-']) && !l.starts_with("+++") && !l.starts_with("---"))
        .collect();
    assert_eq!(changed.len(), 4, "{d}");
}

/// `nocompiler link STACK --check` (Q-VC2): the committed stack's rebuild
/// matches its recorded result.
#[test]
fn link_check_rebuilds_the_committed_stack() {
    let exe = env!("CARGO_BIN_EXE_nocompiler");
    let stack = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../nocompiler/tests/stack/sum.nocompiler-stack"
    );
    let out = Command::new(exe)
        .args(["link", stack, "--check"])
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        String::from_utf8(out.stdout)
            .unwrap()
            .contains("matches the recorded result")
    );
}

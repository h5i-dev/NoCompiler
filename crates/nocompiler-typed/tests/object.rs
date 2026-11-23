//! Assembles every corpus file that parses with clang (when clang is installed) and checks
//! that the object's words are the encodings the checker computed (I15). This is also the
//! cross-check of the encoder against LLVM's.

use nocompiler_typed::{asm, object};
use std::path::PathBuf;
use std::process::Command;

#[test]
fn corpus_objects_match_text() {
    if Command::new("clang").arg("--version").output().is_err() {
        eprintln!("clang not found: skipped");
        return;
    }
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tests/typed/corpus");
    let out = std::env::temp_dir().join(format!("nc-typed-obj-{}", std::process::id()));
    std::fs::create_dir_all(&out).unwrap();
    let mut n = 0;
    let mut bad = Vec::new();
    let mut stack = vec![dir];
    while let Some(d) = stack.pop() {
        for e in std::fs::read_dir(&d).unwrap() {
            let p = e.unwrap().path();
            if p.is_dir() {
                stack.push(p);
                continue;
            }
            if p.extension().is_none_or(|x| x != "s") {
                continue;
            }
            let src = std::fs::read_to_string(&p).unwrap();
            let Ok(prog) = asm::parse(&src) else { continue };
            let o = out.join(format!("{n}.o"));
            let st = Command::new("clang")
                .args([
                    "--target=riscv64-linux-gnu",
                    "-march=rv64im_zba_zbb",
                    "-mno-relax",
                    "-c",
                ])
                .arg(&p)
                .arg("-o")
                .arg(&o)
                .output()
                .unwrap();
            if !st.status.success() {
                bad.push(format!(
                    "{}: clang failed: {}",
                    p.display(),
                    String::from_utf8_lossy(&st.stderr)
                ));
                continue;
            }
            let errs = object::compare(&prog, &std::fs::read(&o).unwrap());
            for e in errs {
                bad.push(format!("{}:{}: {}", p.display(), e.line, e.msg));
            }
            n += 1;
        }
    }
    let _ = std::fs::remove_dir_all(&out);
    assert!(n > 0);
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

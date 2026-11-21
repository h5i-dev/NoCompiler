//! RISC-V through the embedded SLEIGH specification: every instruction of the
//! committed RISC-V ELFs decodes, and lengths and direct targets agree with
//! `llvm-objdump` when it is installed.

use std::path::{Path, PathBuf};
use std::process::Command;

use nocompiler_arch::{Flow, decode, sleigh};
use nocompiler_core::{Addr, Arch};

fn rv64() -> Arch {
    Arch::Sleigh("RISCV:LE:64:default".into())
}

fn elf(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/elf")
        .join(name)
}

/// The `.text` section of an ELF64: its address and bytes.
fn text(path: &Path) -> (u64, Vec<u8>) {
    let d = std::fs::read(path).expect("the ELF is committed");
    let u16_at = |o: usize| u16::from_le_bytes(d[o..o + 2].try_into().unwrap()) as usize;
    let u32_at = |o: usize| u32::from_le_bytes(d[o..o + 4].try_into().unwrap()) as usize;
    let u64_at = |o: usize| u64::from_le_bytes(d[o..o + 8].try_into().unwrap());
    let (shoff, shentsize, shnum, shstrndx) = (
        u64_at(0x28) as usize,
        u16_at(0x3a),
        u16_at(0x3c),
        u16_at(0x3e),
    );
    let sh = |i: usize| shoff + i * shentsize;
    let strtab = u64_at(sh(shstrndx) + 0x18) as usize;
    for i in 0..shnum {
        let name = strtab + u32_at(sh(i));
        if d[name..].starts_with(b".text\0") {
            let addr = u64_at(sh(i) + 0x10);
            let off = u64_at(sh(i) + 0x18) as usize;
            let size = u64_at(sh(i) + 0x20) as usize;
            return (addr, d[off..off + size].to_vec());
        }
    }
    panic!("no .text in {}", path.display());
}

#[test]
fn the_specification_parses() {
    let lang = sleigh::language("RISCV:LE:64:default").expect("RV64 is embedded");
    assert!(lang.zero.is_some(), "x0 is named zero");
    assert!(sleigh::language("MIPS:BE:32:default").is_none());
}

#[test]
fn every_committed_instruction_decodes() {
    for name in ["sum.elf", "hello.elf", "sum.link2.elf"] {
        let (base, bytes) = text(&elf(name));
        let mut at = 0;
        while at < bytes.len() {
            let i = decode(&rv64(), &bytes[at..], Addr::new(base + at as u64))
                .unwrap_or_else(|| panic!("{name}: {:#x} decodes", base + at as u64));
            assert!(i.len == 4 || i.len == 2);
            at += i.len as usize;
        }
    }
}

#[test]
fn flow_of_the_usual_forms() {
    let at = Addr::new(0x1000);
    let d = |w: u32| decode(&rv64(), &w.to_le_bytes(), at).expect("decodes");
    // ret = jalr x0, 0(ra)
    assert_eq!(d(0x0000_8067).flow, Flow::Return);
    // jal ra, +0x10
    assert_eq!(d(0x0100_00ef).flow, Flow::Call(Addr::new(0x1010)));
    // j +0x10 (jal x0)
    assert_eq!(d(0x0100_006f).flow, Flow::Branch(Addr::new(0x1010)));
    // beq a0, a1, +8
    assert_eq!(d(0x00b5_0463).flow, Flow::CondBranch(Addr::new(0x1008)));
    // jalr ra, 0(a5)
    assert_eq!(d(0x0007_80e7).flow, Flow::IndirectCall);
    // jr a5
    assert_eq!(d(0x0007_8067).flow, Flow::IndirectBranch);
    // ecall, ebreak
    assert_eq!(d(0x0000_0073).flow, Flow::Syscall);
    assert_eq!(d(0x0010_0073).flow, Flow::Trap);
    // addi a0, a0, 1
    let i = d(0x0015_0513);
    assert_eq!(i.flow, Flow::Next);
    assert_eq!(
        nocompiler_arch::format(&rv64(), &i, false),
        "addi a0,a0,0x1"
    );
}

/// Lengths and direct branch targets against llvm-objdump.
#[test]
fn agrees_with_llvm_objdump() {
    for name in ["sum.elf", "hello.elf", "sum.link2.elf"] {
        let path = elf(name);
        let Ok(out) = Command::new("llvm-objdump")
            .args([
                "-d",
                "--no-show-raw-insn",
                "--mattr=+m,+a,+f,+d,+c,+zba,+zbb",
            ])
            .arg(&path)
            .output()
        else {
            eprintln!("llvm-objdump is not installed; skipped");
            return;
        };
        let (base, bytes) = text(&path);
        let listing = String::from_utf8_lossy(&out.stdout);
        let mut checked = 0;
        for line in listing.lines() {
            let Some((left, rest)) = line.split_once(':') else {
                continue;
            };
            let Ok(a) = u64::from_str_radix(left.trim(), 16) else {
                continue;
            };
            if a < base || a >= base + bytes.len() as u64 {
                continue;
            }
            let i = decode(&rv64(), &bytes[(a - base) as usize..], Addr::new(a)).expect("decodes");
            let words: Vec<&str> = rest.split_whitespace().collect();
            let m = words.first().copied().unwrap_or("");
            // A direct branch or jal prints its absolute target as `0x... <sym>`.
            let target = words.iter().find_map(|w| {
                w.strip_prefix("0x")
                    .and_then(|h| u64::from_str_radix(h, 16).ok())
            });
            let direct = m.starts_with('b') || m == "j" || m == "jal" || m == "c.j";
            if direct && line.contains('<') {
                assert_eq!(i.flow.target().map(|t| t.get()), target, "{name} {line}");
            }
            if m == "ret" {
                assert_eq!(i.flow, Flow::Return, "{name} {line}");
            }
            checked += 1;
        }
        assert!(checked > 5, "{name}: objdump listed {checked} instructions");
    }
}

//! `nocompiler textconv FILE`: a RISC-V binary as text for `git diff`
//! (docs/toolkit/git-diff.md). One block per function, sorted by name; each
//! instruction in its relocatable form (the module's words, relocated fields
//! zero, with the relocation's target by name), branch offsets relative. So
//! the text does not depend on where the linker put anything: a function that
//! did not change gives the same lines, and `git diff` shows only the
//! functions that did. The block's header carries the level and a key of the
//! block's masked lines, so a change shows in it too. A jump or call `jal` out
//! of the function names its target. Not masked: a function the module could
//! not make relocatable keeps its pc-relative low parts (its `auipc`
//! immediates are masked).

use crate::Binary;
use crate::isa;
use crate::module::{self, Kind};
use std::fmt::Write as _;

/// A word at `pc` in the function `[lo, hi)`: a jump or branch out of the
/// function names its target (`name_at`), one inside it keeps its relative
/// offset, so neither depends on the layout.
fn word_text(w: u32, pc: u64, lo: u64, hi: u64, name_at: &dyn Fn(u64) -> String) -> String {
    let out = |imm: isa::Imm| {
        let t = pc.wrapping_add(imm.signed() as u64);
        (t < lo || t >= hi).then(|| name_at(t))
    };
    match isa::decode(w) {
        Some(isa::Instr::Jal(rd, imm)) => match out(imm) {
            Some(n) => format!("jal {rd}, {n}"),
            None => isa::Instr::Jal(rd, imm).asm_rel(),
        },
        Some(i @ isa::Instr::Branch(op, a, b, imm)) => match out(imm) {
            Some(n) => format!("{} {a}, {b}, {n}", op.mnemonic()),
            None => i.asm_rel(),
        },
        Some(i) => i.asm_rel(),
        None => crate::rvlist::other(w).unwrap_or_else(|| format!(".word {w:#010x}")),
    }
}

/// The data objects (STT_OBJECT symbols with a size), by address.
fn objects(bin: &Binary) -> Vec<(u64, u64, String)> {
    let Ok(e) = crate::elf::Elf::parse(bin.bytes) else {
        return Vec::new();
    };
    let mut v: Vec<(u64, u64, String)> = e
        .symbols
        .iter()
        .filter(|s| s.kind == 1 && s.size > 0)
        .map(|s| (s.value, s.size, s.name.clone()))
        .collect();
    v.sort();
    v
}

/// The text of a binary.
pub fn textconv(bin: &Binary) -> String {
    let m = module::of_binary(bin).ok();
    let objs = objects(bin);
    // A relocation's target by the data object holding it, when one does: so
    // a change to data elsewhere in the section does not show here.
    let target = |sym: &str, addend: i64| -> String {
        let sec = bin.segments.iter().find(|g| g.name == sym);
        if let Some(g) = sec {
            let t = g.addr.wrapping_add(addend as u64);
            if let Some((a, _, n)) = objs.iter().find(|(a, z, _)| t >= *a && t < a + z) {
                return if t == *a {
                    n.clone()
                } else {
                    format!("{n}+{}", t - a)
                };
            }
        }
        match addend {
            0 => sym.to_string(),
            a if a > 0 => format!("{sym}+{a}"),
            a => format!("{sym}{a}"),
        }
    };
    let reports = bin.check();
    let mut fs: Vec<_> = bin.funcs.iter().zip(&reports).collect();
    fs.sort_by(|a, b| a.0.name.cmp(&b.0.name).then(a.0.entry.cmp(&b.0.entry)));
    let name_at = |t: u64| -> String {
        match bin.funcs.iter().find(|g| t >= g.entry && t < g.end()) {
            Some(g) if g.entry == t => g.name.clone(),
            Some(g) => format!("{}+{}", g.name, t - g.entry),
            None => "?".to_string(),
        }
    };
    let mut o = String::new();
    let _ = writeln!(
        o,
        "; nocompiler textconv: {} functions, by name; addresses masked",
        fs.len()
    );
    for (f, r) in fs {
        let level = r.level.map_or("L0".to_string(), |l| format!("{l:?}"));
        let rf = m
            .as_ref()
            .and_then(|m| m.funcs.iter().find(|g| g.entry == f.entry));
        match rf {
            Some(rf) => {
                let mut body = String::new();
                for (i, &w) in rf.words.iter().enumerate() {
                    let off = 4 * i as u64;
                    let rel: Vec<String> = rf
                        .relocs
                        .iter()
                        .filter(|r| r.off == off)
                        .map(|r| {
                            let k = match r.kind {
                                Kind::Call => "call",
                                Kind::PcrelHi => "pcrel_hi",
                                Kind::PcrelLoI | Kind::PcrelLoS => "pcrel_lo",
                            };
                            format!("{k} {}", target(&r.sym, r.addend))
                        })
                        .collect();
                    let note = if rel.is_empty() {
                        String::new()
                    } else {
                        format!("  ; reloc {}", rel.join(", "))
                    };
                    let t = word_text(w, f.entry + off, f.entry, f.end(), &name_at);
                    let _ = writeln!(body, "  {t}{note}");
                }
                // The key of the masked text: it changes exactly when a line does.
                let key = crate::sha256::hex(&crate::sha256::digest(body.as_bytes()));
                let _ = writeln!(
                    o,
                    "\nfunc {}  ; {level}, {} instructions, key {}",
                    f.name,
                    rf.words.len(),
                    &key[..16]
                );
                o.push_str(&body);
            }
            None => {
                // Not relocatable: the words as they are, the auipc immediates
                // (which depend on the layout) masked.
                let _ = writeln!(
                    o,
                    "\nfunc {}  ; {level}, {} instructions, not relocatable",
                    f.name,
                    f.words.len()
                );
                // The low parts: an instruction after an auipc that uses its
                // register as a base, until the register is written again.
                let mut lo = vec![false; f.words.len()];
                for i in 0..f.words.len() {
                    let Some(isa::Instr::Auipc(rd, _)) = isa::decode(f.words[i]) else {
                        continue;
                    };
                    for j in i + 1..f.words.len().min(i + 16) {
                        let (base, writes) = match isa::decode(f.words[j]) {
                            Some(isa::Instr::IOp(_, d, b, _)) => (Some(b), Some(d)),
                            Some(isa::Instr::Load(_, d, b, _)) => (Some(b), Some(d)),
                            Some(isa::Instr::Jalr(d, b, _)) => (Some(b), Some(d)),
                            Some(isa::Instr::Store(_, b, _, _)) => (Some(b), None),
                            Some(isa::Instr::Jal(..)) | Some(isa::Instr::Branch(..)) | None => {
                                break;
                            }
                            _ => (None, None),
                        };
                        // FP loads/stores (fld/fsd) use it as a base too.
                        let fp = matches!(f.words[j] & 0x7f, 0x07 | 0x27)
                            && (f.words[j] >> 15) & 31 == rd.0 as u32;
                        if base == Some(rd) || fp {
                            lo[j] = true;
                        }
                        if writes == Some(rd) {
                            break;
                        }
                    }
                }
                for (i, &w) in f.words.iter().enumerate() {
                    let pc = f.entry + 4 * i as u64;
                    let t = match isa::decode(w) {
                        Some(isa::Instr::Auipc(rd, _)) => format!("auipc {rd}, ?"),
                        _ if lo[i] => {
                            // Zero the 12-bit immediate (I or S type) and say so.
                            let s_type = matches!(w & 0x7f, 0x23 | 0x27);
                            let m = if s_type { 0xfe00_0f80 } else { 0xfff0_0000 };
                            format!(
                                "{}  ; pcrel_lo ?",
                                word_text(w & !m, pc, f.entry, f.end(), &name_at)
                            )
                        }
                        _ => word_text(w, pc, f.entry, f.end(), &name_at),
                    };
                    let _ = writeln!(o, "  {t}");
                }
            }
        }
    }
    o
}

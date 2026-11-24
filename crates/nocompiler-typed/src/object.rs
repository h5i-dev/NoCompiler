//! Text versus object (decision I15): the words in the assembled ELF relocatable object
//! must be the encodings of the instructions the checker read, so what is checked is what
//! runs. Calls to symbols are matched against the object's relocations.

use crate::asm::Program;
use crate::check::{CheckError, Rule};
use crate::isa::{Instr, Target, encode_words};
use std::collections::BTreeMap;

struct Sec {
    name: String,
    ty: u32,
    addr: u64,
    off: usize,
    size: usize,
    link: u32,
    info: u32,
}

struct Elf<'a> {
    d: &'a [u8],
    secs: Vec<Sec>,
}

fn u16_at(d: &[u8], o: usize) -> Option<u16> {
    Some(u16::from_le_bytes(d.get(o..o + 2)?.try_into().ok()?))
}
fn u32_at(d: &[u8], o: usize) -> Option<u32> {
    Some(u32::from_le_bytes(d.get(o..o + 4)?.try_into().ok()?))
}
fn u64_at(d: &[u8], o: usize) -> Option<u64> {
    Some(u64::from_le_bytes(d.get(o..o + 8)?.try_into().ok()?))
}
fn cstr(d: &[u8], o: usize) -> Option<String> {
    let s = d.get(o..)?;
    let e = s.iter().position(|b| *b == 0)?;
    Some(String::from_utf8_lossy(&s[..e]).into_owned())
}

impl<'a> Elf<'a> {
    fn parse(d: &'a [u8]) -> Result<Elf<'a>, String> {
        Self::parse_kind(d, false)
    }

    fn parse_kind(d: &'a [u8], linked: bool) -> Result<Elf<'a>, String> {
        if d.get(0..4) != Some(b"\x7fELF") || d.get(4) != Some(&2) || d.get(5) != Some(&1) {
            return Err("not a little-endian ELF64 file".into());
        }
        if u16_at(d, 0x12) != Some(243) {
            return Err("not a RISC-V object".into());
        }
        let ty = u16_at(d, 0x10);
        if !linked && ty != Some(1) {
            return Err("not a relocatable object (ET_REL)".into());
        }
        if linked && ty != Some(2) && ty != Some(3) {
            return Err("not a linked executable (ET_EXEC or ET_DYN)".into());
        }
        let bad = || "truncated ELF".to_string();
        let shoff = u64_at(d, 0x28).ok_or_else(bad)? as usize;
        let shentsize = u16_at(d, 0x3a).ok_or_else(bad)? as usize;
        let shnum = u16_at(d, 0x3c).ok_or_else(bad)? as usize;
        let shstrndx = u16_at(d, 0x3e).ok_or_else(bad)? as usize;
        let mut raw = Vec::new();
        for i in 0..shnum {
            let h = shoff + i * shentsize;
            raw.push((
                u32_at(d, h).ok_or_else(bad)?,
                u32_at(d, h + 4).ok_or_else(bad)?,
                u64_at(d, h + 16).ok_or_else(bad)?,
                u64_at(d, h + 24).ok_or_else(bad)? as usize,
                u64_at(d, h + 32).ok_or_else(bad)? as usize,
                u32_at(d, h + 40).ok_or_else(bad)?,
                u32_at(d, h + 44).ok_or_else(bad)?,
            ));
        }
        let stro = raw.get(shstrndx).ok_or_else(bad)?.3;
        let secs = raw
            .into_iter()
            .map(|(n, ty, addr, off, size, link, info)| Sec {
                name: cstr(d, stro + n as usize).unwrap_or_default(),
                ty,
                addr,
                off,
                size,
                link,
                info,
            })
            .collect();
        Ok(Elf { d, secs })
    }

    /// (name, section index, value)
    fn symbols(&self) -> Vec<(String, usize, u64)> {
        let mut out = Vec::new();
        for s in self.secs.iter().filter(|s| s.ty == 2) {
            let str_off = self.secs.get(s.link as usize).map(|t| t.off).unwrap_or(0);
            for k in 0..s.size / 24 {
                let e = s.off + k * 24;
                let (Some(n), Some(sh), Some(v)) = (
                    u32_at(self.d, e),
                    u16_at(self.d, e + 6),
                    u64_at(self.d, e + 8),
                ) else {
                    continue;
                };
                out.push((
                    cstr(self.d, str_off + n as usize).unwrap_or_default(),
                    sh as usize,
                    v,
                ));
            }
        }
        out
    }

    /// Relocations applying to section `target`: offset → (type, symbol name).
    fn relocs(&self, target: usize, syms: &[(String, usize, u64)]) -> BTreeMap<u64, (u32, String)> {
        let mut out = BTreeMap::new();
        for s in self
            .secs
            .iter()
            .filter(|s| s.ty == 4 && s.info as usize == target)
        {
            for k in 0..s.size / 24 {
                let e = s.off + k * 24;
                let (Some(off), Some(info)) = (u64_at(self.d, e), u64_at(self.d, e + 8)) else {
                    continue;
                };
                let ty = (info & 0xffff_ffff) as u32;
                if ty == 51 {
                    continue; // R_RISCV_RELAX: a hint, the bytes are unchanged
                }
                let sym = syms
                    .get((info >> 32) as usize)
                    .map(|s| s.0.clone())
                    .unwrap_or_default();
                out.insert(off, (ty, sym));
            }
        }
        out
    }
}

/// The addresses of the named symbols of a linked RISC-V ELF (for the export with
/// `--image`, export.md "Linked image"). Undefined symbols (section 0) are left out.
pub fn symbol_addresses(bytes: &[u8]) -> Result<BTreeMap<String, u64>, String> {
    let elf = Elf::parse_kind(bytes, true)?;
    Ok(elf
        .symbols()
        .into_iter()
        .filter(|(n, sh, _)| !n.is_empty() && *sh != 0)
        .map(|(n, _, v)| (n, v))
        .collect())
}

/// The sizes (`st_size`) of the defined symbols of an ELF: a function's code range in a linked
/// image is its address and this size.
pub fn symbol_sizes(bytes: &[u8]) -> Result<BTreeMap<String, u64>, String> {
    let elf = Elf::parse_kind(bytes, true)?;
    let mut out = BTreeMap::new();
    for s in elf.secs.iter().filter(|s| s.ty == 2) {
        let str_off = elf.secs.get(s.link as usize).map(|t| t.off).unwrap_or(0);
        for k in 0..s.size / 24 {
            let e = s.off + k * 24;
            let (Some(n), Some(sh), Some(sz)) = (
                u32_at(bytes, e),
                u16_at(bytes, e + 6),
                u64_at(bytes, e + 16),
            ) else {
                continue;
            };
            let name = cstr(bytes, str_off + n as usize).unwrap_or_default();
            if !name.is_empty() && sh != 0 {
                out.insert(name, sz);
            }
        }
    }
    Ok(out)
}

/// The `.text` section of a linked RISC-V ELF: its address and its 32-bit words (the code
/// image the Lean checker runs on).
pub fn text_words(bytes: &[u8]) -> Result<(u64, Vec<u32>), String> {
    let elf = Elf::parse_kind(bytes, true)?;
    let sec = elf
        .secs
        .iter()
        .find(|s| s.name == ".text")
        .ok_or("no .text section")?;
    let data = bytes
        .get(sec.off..sec.off + sec.size)
        .ok_or("truncated .text")?;
    Ok((
        sec.addr,
        data.chunks_exact(4)
            .map(|w| u32::from_le_bytes([w[0], w[1], w[2], w[3]]))
            .collect(),
    ))
}

/// Compares every function's instructions with the object's bytes.
pub fn compare(prog: &Program, bytes: &[u8]) -> Vec<CheckError> {
    let mut errs = Vec::new();
    let e = |line, msg: String| CheckError {
        rule: Rule::Object,
        line,
        msg,
    };
    let elf = match Elf::parse(bytes) {
        Ok(x) => x,
        Err(m) => return vec![e(0, m)],
    };
    let syms = elf.symbols();
    for f in &prog.funcs {
        let Some(si) = elf.secs.iter().position(|s| s.name == f.section) else {
            errs.push(e(
                f.line,
                format!("section {} of '{}' is not in the object", f.section, f.name),
            ));
            continue;
        };
        let sec = &elf.secs[si];
        let relocs = elf.relocs(si, &syms);
        let Some(first) = f.instrs.first() else {
            continue;
        };
        match syms.iter().find(|s| s.0 == f.name) {
            Some(s) if s.1 == si && s.2 == first.addr => {}
            Some(s) => {
                errs.push(e(
                    f.line,
                    format!(
                        "'{}' is at {}+{:#x} in the object, the text puts it at {}+{:#x}",
                        f.name,
                        elf.secs.get(s.1).map(|x| x.name.as_str()).unwrap_or("?"),
                        s.2,
                        f.section,
                        first.addr
                    ),
                ));
                continue;
            }
            None => {} // a local label without a symbol: positions still compared
        }
        for pi in &f.instrs {
            let off = match &pi.instr {
                Instr::Jal { target, .. }
                | Instr::Branch { target, .. }
                | Instr::CallPair { target, .. } => {
                    match target {
                        Target::Local(t) => Some(f.instrs[*t].addr as i64 - pi.addr as i64),
                        Target::Symbol(name) => match relocs.get(&pi.addr) {
                            Some((_, sym)) if sym == name => None,
                            Some((_, sym)) => {
                                errs.push(e(pi.line, format!("relocation at {:#x} is for '{sym}', the text says '{name}'", pi.addr)));
                                continue;
                            }
                            None => match syms.iter().find(|s| s.0 == *name && s.1 == si) {
                                Some(s) => Some(s.2 as i64 - pi.addr as i64),
                                None => {
                                    errs.push(e(
                                        pi.line,
                                        format!("no relocation or local symbol for '{name}'"),
                                    ));
                                    continue;
                                }
                            },
                        },
                    }
                }
                _ => None,
            };
            let Some(words) = encode_words(&pi.instr, off) else {
                errs.push(e(
                    pi.line,
                    "instruction cannot be encoded (offset out of range)".into(),
                ));
                continue;
            };
            for (k, w) in words.iter().enumerate() {
                let a = pi.addr as usize + 4 * k;
                let got = if a + 4 <= sec.size {
                    u32_at(elf.d, sec.off + a)
                } else {
                    None
                };
                if got != Some(*w) {
                    errs.push(e(pi.line, format!("object word at {}+{a:#x} is {}, the checked instruction encodes as {w:#010x}", f.section, got.map(|g| format!("{g:#010x}")).unwrap_or("missing".into()))));
                }
            }
        }
    }
    // data symbols: the bytes the checker took fields from must be the object's
    for (name, d) in &prog.data {
        let Some(si) = elf.secs.iter().position(|s| s.name == d.section) else {
            errs.push(e(
                d.line,
                format!(
                    "data section {} of '{name}' is not in the object",
                    d.section
                ),
            ));
            continue;
        };
        let sec = &elf.secs[si];
        if sec.ty == 8 {
            // SHT_NOBITS: zeros
            if d.bytes.iter().any(|b| b.is_some_and(|b| b != 0)) {
                errs.push(e(
                    d.line,
                    format!("'{name}' is in a NOBITS section but has non-zero bytes"),
                ));
            }
            continue;
        }
        for (j, b) in d.bytes.iter().enumerate() {
            let Some(b) = b else { continue };
            let at = d.offset as usize + j;
            let got = if at < sec.size {
                elf.d.get(sec.off + at).copied()
            } else {
                None
            };
            if got != Some(*b) {
                errs.push(e(d.line, format!("data byte {}+{at:#x} of '{name}' is {got:?} in the object, {b:#04x} in the text", d.section)));
                break;
            }
        }
    }
    errs
}

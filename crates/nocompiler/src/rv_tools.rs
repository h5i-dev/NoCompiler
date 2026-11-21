//! The reading tools on a RISC-V binary: `funcs` and `xrefs` (the toolkit's
//! crates decode x86 and Arm only). Functions are the symbol table's
//! (`Binary::funcs`); references come from decoding each function's words and,
//! for `auipc` pairs, from the module's recovered relocations
//! (`module::of_binary`), so a call through `auipc`+`jalr` and a pc-relative
//! address name their real target.

use crate::Binary;
use crate::isa::{self, Instr};
use crate::module::{self, Kind};
use std::fmt::Write as _;

/// One reference: what kind, the instruction's address, the target.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Xref {
    /// `call` (jal ra, or an auipc+jalr call pair), `jump` (another jal),
    /// `branch`, or `addr` (an auipc pair forming an address: data or code).
    pub kind: &'static str,
    pub from: u64,
    pub to: u64,
}

/// Every reference in the binary's functions, by source address.
pub fn all_xrefs(bin: &Binary) -> Vec<Xref> {
    let m = module::of_binary(bin).ok();
    let addr = |s: &str| -> Option<u64> {
        let m = m.as_ref()?;
        m.funcs
            .iter()
            .find(|f| f.name == s)
            .map(|f| f.entry)
            .or_else(|| m.skipped.iter().find(|f| f.name == s).map(|f| f.entry))
            .or_else(|| m.data.iter().find(|d| d.name == s).map(|d| d.addr))
    };
    let mut out = Vec::new();
    for f in &bin.funcs {
        let rf = m
            .as_ref()
            .and_then(|m| m.funcs.iter().find(|g| g.entry == f.entry));
        // Direct jumps and branches, from the words.
        for (i, &w) in f.words.iter().enumerate() {
            let pc = f.entry + 4 * i as u64;
            match isa::decode(w) {
                Some(Instr::Jal(rd, imm)) => out.push(Xref {
                    kind: if rd == isa::RA { "call" } else { "jump" },
                    from: pc,
                    to: pc.wrapping_add(imm.signed() as u64),
                }),
                Some(Instr::Branch(_, _, _, imm)) => out.push(Xref {
                    kind: "branch",
                    from: pc,
                    to: pc.wrapping_add(imm.signed() as u64),
                }),
                _ => {}
            }
        }
        match rf {
            // The auipc pairs, as the module recovered them.
            Some(rf) => {
                for r in &rf.relocs {
                    let kind = match r.kind {
                        Kind::Call => "call",
                        Kind::PcrelHi => "addr",
                        Kind::PcrelLoI | Kind::PcrelLoS => continue,
                    };
                    if let Some(a) = addr(&r.sym) {
                        out.push(Xref {
                            kind,
                            from: f.entry + r.off,
                            to: a.wrapping_add(r.addend as u64),
                        });
                    }
                }
            }
            // A function the module could not recover: an auipc with the next
            // instruction using it (jalr: a call; addi or a load/store: an address).
            None => {
                for i in 0..f.words.len().saturating_sub(1) {
                    let pc = f.entry + 4 * i as u64;
                    let Some(Instr::Auipc(rd, hi)) = isa::decode(f.words[i]) else {
                        continue;
                    };
                    let hi = ((hi.value << 12) as i32) as i64;
                    let (kind, lo) = match isa::decode(f.words[i + 1]) {
                        Some(Instr::Jalr(_, rs, lo)) if rs == rd => ("call", lo.signed()),
                        Some(Instr::IOp(_, _, rs, lo)) if rs == rd => ("addr", lo.signed()),
                        Some(Instr::Load(_, _, rs, lo)) if rs == rd => ("addr", lo.signed()),
                        Some(Instr::Store(_, rs, _, lo)) if rs == rd => ("addr", lo.signed()),
                        _ => continue,
                    };
                    out.push(Xref {
                        kind,
                        from: pc,
                        to: pc.wrapping_add((hi + lo) as u64),
                    });
                }
            }
        }
    }
    out.sort_by_key(|x| (x.from, x.to));
    out
}

/// The function whose words hold `a`.
pub fn func_at<'b>(bin: &'b Binary, a: u64) -> Option<&'b crate::profile::Func> {
    bin.funcs.iter().find(|f| a >= f.entry && a < f.end())
}

/// An address (`0x…` or decimal) or a symbol: a function, or a section.
pub fn resolve(bin: &Binary, target: &str) -> Option<u64> {
    let t = target.trim();
    if let Some(h) = t.strip_prefix("0x").or_else(|| t.strip_prefix("0X")) {
        return u64::from_str_radix(h, 16).ok();
    }
    if let Ok(v) = t.parse::<u64>() {
        return Some(v);
    }
    bin.funcs
        .iter()
        .find(|f| f.name == t)
        .map(|f| f.entry)
        .or_else(|| bin.segments.iter().find(|g| g.name == t).map(|g| g.addr))
}

fn json_str(s: &str) -> String {
    crate::cmd::json_str(s)
}

/// `funcs`: every function, its size, instructions and level.
pub fn funcs(bin: &Binary, json: bool) -> String {
    let reports = bin.check();
    let mut fs: Vec<_> = bin.funcs.iter().zip(&reports).collect();
    fs.sort_by_key(|(f, _)| f.entry);
    let level = |r: &crate::Report| match r.level {
        Some(l) => format!("{l:?}"),
        None => "L0".to_string(),
    };
    let mut o = String::new();
    if json {
        let rows: Vec<String> = fs
            .iter()
            .map(|(f, r)| {
                format!(
                    "{{\"addr\":{},\"size\":{},\"insns\":{},\"level\":{},\"name\":{}}}",
                    f.entry,
                    4 * f.words.len(),
                    f.words.len(),
                    json_str(&level(r)),
                    json_str(&f.name)
                )
            })
            .collect();
        let _ = writeln!(o, "[{}]", rows.join(","));
        return o;
    }
    let _ = writeln!(
        o,
        "{:<20}{:>8}  {:>6}  {:<6}name",
        "address", "size", "insns", "level"
    );
    for (f, r) in fs {
        let _ = writeln!(
            o,
            "{:<20}{:>8}  {:>6}  {:<6}{}",
            format!("{:#x}", f.entry),
            4 * f.words.len(),
            f.words.len(),
            level(r),
            f.name
        );
    }
    o
}

/// `xrefs TARGET [--from]`: what refers to TARGET (or, with `from`, what the
/// instructions at TARGET, or in the function TARGET names, refer to).
/// `None` when TARGET is neither an address nor a symbol.
pub fn xrefs(bin: &Binary, target: &str, from: bool, json: bool) -> Option<(String, usize)> {
    let a = resolve(bin, target)?;
    let all = all_xrefs(bin);
    let name_of = |x: u64| {
        func_at(bin, x)
            .map(|f| {
                if f.entry == x {
                    f.name.clone()
                } else {
                    format!("{}+{:#x}", f.name, x - f.entry)
                }
            })
            .unwrap_or_default()
    };
    let hits: Vec<&Xref> = if from {
        // From a function's whole body when TARGET is its entry.
        match func_at(bin, a).filter(|f| f.entry == a) {
            Some(f) => all
                .iter()
                .filter(|x| x.from >= f.entry && x.from < f.end())
                .collect(),
            None => all.iter().filter(|x| x.from == a).collect(),
        }
    } else {
        all.iter().filter(|x| x.to == a).collect()
    };
    let mut o = String::new();
    if json {
        let rows: Vec<String> = hits
            .iter()
            .map(|x| {
                format!(
                    "{{\"kind\":{},\"from\":{},\"to\":{},\"from_name\":{},\"to_name\":{}}}",
                    json_str(x.kind),
                    x.from,
                    x.to,
                    json_str(&name_of(x.from)),
                    json_str(&name_of(x.to))
                )
            })
            .collect();
        let _ = writeln!(o, "[{}]", rows.join(","));
    } else {
        for x in &hits {
            let (other, n) = if from {
                (x.to, name_of(x.to))
            } else {
                (x.from, name_of(x.from))
            };
            let n = if n.is_empty() {
                String::new()
            } else {
                format!(" in {n}")
            };
            let _ = writeln!(o, "{:<10}{other:#x}{n}", x.kind);
        }
    }
    Some((o, hits.len()))
}

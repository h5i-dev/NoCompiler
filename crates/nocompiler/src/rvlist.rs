//! Decoding for reading only: what `disasm` prints for a word. Words of the
//! profile (RV64IM + Zba + Zbb, `isa::decode`) print as the profile prints
//! them; F, D, A, Zicsr, `fence` and `ebreak` words print as an assembler
//! would. This gives NO semantics: nothing here is checked, exported to Lean,
//! or used by a proof; a word outside the profile still puts its function
//! below L1.

use crate::isa::{self, Reg};

const FREG: [&str; 32] = [
    "ft0", "ft1", "ft2", "ft3", "ft4", "ft5", "ft6", "ft7", "fs0", "fs1", "fa0", "fa1", "fa2",
    "fa3", "fa4", "fa5", "fa6", "fa7", "fs2", "fs3", "fs4", "fs5", "fs6", "fs7", "fs8", "fs9",
    "fs10", "fs11", "ft8", "ft9", "ft10", "ft11",
];

fn bits(w: u32, lo: u32, len: u32) -> u32 {
    (w >> lo) & ((1u32 << len) - 1)
}
fn x(w: u32, lo: u32) -> String {
    Reg(bits(w, lo, 5) as u8).to_string()
}
fn f(w: u32, lo: u32) -> &'static str {
    FREG[bits(w, lo, 5) as usize]
}
fn sext(v: u32, n: u32) -> i64 {
    let v = v as i64;
    if v & (1 << (n - 1)) != 0 {
        v - (1 << n)
    } else {
        v
    }
}
fn imm_i(w: u32) -> i64 {
    sext(bits(w, 20, 12), 12)
}
fn imm_s(w: u32) -> i64 {
    sext(bits(w, 7, 5) | bits(w, 25, 7) << 5, 12)
}

fn csr_name(c: u32) -> String {
    match c {
        0x001 => "fflags".into(),
        0x002 => "frm".into(),
        0x003 => "fcsr".into(),
        0xc00 => "cycle".into(),
        0xc01 => "time".into(),
        0xc02 => "instret".into(),
        _ => format!("{c:#x}"),
    }
}

/// The word `w` at `pc`, as text.
pub fn text(w: u32, pc: u64) -> String {
    if let Some(i) = isa::decode(w) {
        return i.asm(pc);
    }
    other(w).unwrap_or_else(|| format!(".word {w:#010x}"))
}

/// A word outside the profile, if it is one this decoder reads.
pub fn other(w: u32) -> Option<String> {
    let op = w & 0x7f;
    let f3 = bits(w, 12, 3);
    let f7 = bits(w, 25, 7);
    let rs2 = bits(w, 20, 5);
    let sd = |s: u32| if s & 1 == 1 { "d" } else { "s" };
    Some(match op {
        // LOAD-FP / STORE-FP
        0x07 if f3 == 2 || f3 == 3 => {
            format!(
                "fl{} {}, {}({})",
                if f3 == 2 { "w" } else { "d" },
                f(w, 7),
                imm_i(w),
                x(w, 15)
            )
        }
        0x27 if f3 == 2 || f3 == 3 => {
            format!(
                "fs{} {}, {}({})",
                if f3 == 2 { "w" } else { "d" },
                f(w, 20),
                imm_s(w),
                x(w, 15)
            )
        }
        // fused multiply-add
        0x43 | 0x47 | 0x4b | 0x4f if bits(w, 25, 2) < 2 => {
            let m = match op {
                0x43 => "fmadd",
                0x47 => "fmsub",
                0x4b => "fnmsub",
                _ => "fnmadd",
            };
            format!(
                "{m}.{} {}, {}, {}, {}",
                sd(bits(w, 25, 2)),
                f(w, 7),
                f(w, 15),
                f(w, 20),
                f(w, 27)
            )
        }
        // OP-FP
        0x53 => {
            let t = sd(f7);
            let (rd, a, b) = (f(w, 7), f(w, 15), f(w, 20));
            match f7 >> 1 {
                0x00 => format!("fadd.{t} {rd}, {a}, {b}"),
                0x02 => format!("fsub.{t} {rd}, {a}, {b}"),
                0x04 => format!("fmul.{t} {rd}, {a}, {b}"),
                0x06 => format!("fdiv.{t} {rd}, {a}, {b}"),
                0x16 if rs2 == 0 => format!("fsqrt.{t} {rd}, {a}"),
                0x08 => {
                    let m = ["fsgnj", "fsgnjn", "fsgnjx"].get(f3 as usize)?;
                    format!("{m}.{t} {rd}, {a}, {b}")
                }
                0x0a => {
                    let m = ["fmin", "fmax"].get(f3 as usize)?;
                    format!("{m}.{t} {rd}, {a}, {b}")
                }
                0x10 if f7 == 0x20 && rs2 == 1 => format!("fcvt.s.d {rd}, {a}"),
                0x10 if f7 == 0x21 && rs2 == 0 => format!("fcvt.d.s {rd}, {a}"),
                0x28 => {
                    let m = match f3 {
                        2 => "feq",
                        1 => "flt",
                        0 => "fle",
                        _ => return None,
                    };
                    format!("{m}.{t} {}, {a}, {b}", x(w, 7))
                }
                0x30 => {
                    let i = ["w", "wu", "l", "lu"].get(rs2 as usize)?;
                    format!("fcvt.{i}.{t} {}, {a}", x(w, 7))
                }
                0x34 => {
                    let i = ["w", "wu", "l", "lu"].get(rs2 as usize)?;
                    format!("fcvt.{t}.{i} {rd}, {}", x(w, 15))
                }
                0x38 if rs2 == 0 && f3 == 0 => {
                    format!(
                        "fmv.x.{} {}, {a}",
                        if f7 & 1 == 1 { "d" } else { "w" },
                        x(w, 7)
                    )
                }
                0x38 if rs2 == 0 && f3 == 1 => format!("fclass.{t} {}, {a}", x(w, 7)),
                0x3c if rs2 == 0 && f3 == 0 => {
                    format!(
                        "fmv.{}.x {rd}, {}",
                        if f7 & 1 == 1 { "d" } else { "w" },
                        x(w, 15)
                    )
                }
                _ => return None,
            }
        }
        // AMO
        0x2f if f3 == 2 || f3 == 3 => {
            let s = if f3 == 2 { "w" } else { "d" };
            let ord = match bits(w, 25, 2) {
                0 => "",
                1 => ".rl",
                2 => ".aq",
                _ => ".aqrl",
            };
            let (rd, a, b) = (x(w, 7), x(w, 15), x(w, 20));
            match bits(w, 27, 5) {
                0x02 if rs2 == 0 => format!("lr.{s}{ord} {rd}, ({a})"),
                0x03 => format!("sc.{s}{ord} {rd}, {b}, ({a})"),
                k => {
                    let m = match k {
                        0x01 => "amoswap",
                        0x00 => "amoadd",
                        0x04 => "amoxor",
                        0x0c => "amoand",
                        0x08 => "amoor",
                        0x10 => "amomin",
                        0x14 => "amomax",
                        0x18 => "amominu",
                        0x1c => "amomaxu",
                        _ => return None,
                    };
                    format!("{m}.{s}{ord} {rd}, {b}, ({a})")
                }
            }
        }
        // SYSTEM
        0x73 => match f3 {
            0 if w == 0x0010_0073 => "ebreak".into(),
            1..=3 | 5..=7 => {
                let m = [
                    "", "csrrw", "csrrs", "csrrc", "", "csrrwi", "csrrsi", "csrrci",
                ][f3 as usize];
                let src = if f3 >= 5 {
                    bits(w, 15, 5).to_string()
                } else {
                    x(w, 15)
                };
                format!("{m} {}, {}, {src}", x(w, 7), csr_name(bits(w, 20, 12)))
            }
            _ => return None,
        },
        // MISC-MEM
        0x0f => match f3 {
            0 => "fence".into(),
            1 => "fence.i".into(),
            _ => return None,
        },
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The words are what `clang --target=riscv64 -march=rv64g` (clang 15)
    /// assembles for the text on the right.
    #[test]
    fn reads_what_the_profile_does_not() {
        assert_eq!(text(0x0084_3507, 0), "fld fa0, 8(s0)");
        assert_eq!(text(0xf204_0553, 0), "fmv.d.x fa0, s0");
        assert_eq!(text(0x00a4_3427, 0), "fsd fa0, 8(s0)");
        assert_eq!(text(0x02b5_7553, 0), "fadd.d fa0, fa0, fa1");
        assert_eq!(text(0xe205_0553, 0), "fmv.x.d a0, fa0");
        assert_eq!(text(0xa2b5_2553, 0), "feq.d a0, fa0, fa1");
        assert_eq!(text(0xd225_7553, 0), "fcvt.d.l fa0, a0");
        assert_eq!(text(0x1005_272f, 0), "lr.w a4, (a0)");
        assert_eq!(text(0x0010_0073, 0), "ebreak");
        assert_eq!(text(0x6ac5_f543, 0), "fmadd.d fa0, fa1, fa2, fa3");
        assert_eq!(text(0x06b6_352f, 0), "amoadd.d.aqrl a0, a1, (a2)");
        assert_eq!(text(0x0030_2573, 0), "csrrs a0, fcsr, zero");
        assert_eq!(text(0x5a05_f553, 0), "fsqrt.d fa0, fa1");
        assert_eq!(text(0xc205_9553, 0), "fcvt.w.d a0, fa1");
        assert_eq!(text(0xe205_9553, 0), "fclass.d a0, fa1");
        assert_eq!(text(0x0030_0513, 0), "addi a0, zero, 3"); // the profile's own
        assert_eq!(text(0xffff_ffff, 0), ".word 0xffffffff");
    }
}

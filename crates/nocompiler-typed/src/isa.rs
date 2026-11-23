//! The instruction profile (RV64IM + Zba + Zbb, no C), the same set as
//! `lean/NoCompiler/Isa.lean`, with its encoding and a reference evaluator used for
//! constant folding.

use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Reg(pub u8);

pub const ZERO: Reg = Reg(0);
pub const RA: Reg = Reg(1);
pub const SP: Reg = Reg(2);
pub const GP: Reg = Reg(3);
pub const TP: Reg = Reg(4);
pub const A0: Reg = Reg(10);
pub const A1: Reg = Reg(11);
pub const A2: Reg = Reg(12);
pub const A7: Reg = Reg(17);

const ABI: [&str; 32] = [
    "zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0", "s1", "a0", "a1", "a2", "a3", "a4",
    "a5", "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11", "t3", "t4",
    "t5", "t6",
];

impl Reg {
    pub fn parse(s: &str) -> Option<Reg> {
        if let Some(i) = ABI.iter().position(|n| *n == s) {
            return Some(Reg(i as u8));
        }
        if s == "fp" {
            return Some(Reg(8));
        }
        let n: u8 = s.strip_prefix('x')?.parse().ok()?;
        (n < 32 && !s[1..].starts_with('0') || s == "x0").then_some(Reg(n))
    }
    pub fn name(self) -> &'static str {
        ABI[self.0 as usize]
    }
    /// `s0`–`s11`.
    pub fn is_saved(self) -> bool {
        matches!(self.0, 8 | 9 | 18..=27)
    }
    /// Registers a callee must give back unchanged (I7): `sp`, `gp`, `tp`, `s0`–`s11`.
    /// `ra` is checked separately (it is where control returns to).
    pub fn is_preserved(self) -> bool {
        self == SP || self == GP || self == TP || self.is_saved()
    }
    pub fn all() -> impl Iterator<Item = Reg> {
        (0..32).map(Reg)
    }
}

impl fmt::Display for Reg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BrOp {
    Beq,
    Bne,
    Blt,
    Bge,
    Bltu,
    Bgeu,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LdOp {
    Lb,
    Lh,
    Lw,
    Ld,
    Lbu,
    Lhu,
    Lwu,
}

impl LdOp {
    pub fn width(self) -> u32 {
        match self {
            LdOp::Lb | LdOp::Lbu => 1,
            LdOp::Lh | LdOp::Lhu => 2,
            LdOp::Lw | LdOp::Lwu => 4,
            LdOp::Ld => 8,
        }
    }
    pub fn signed(self) -> bool {
        matches!(self, LdOp::Lb | LdOp::Lh | LdOp::Lw)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StOp {
    Sb,
    Sh,
    Sw,
    Sd,
}

impl StOp {
    pub fn width(self) -> u32 {
        match self {
            StOp::Sb => 1,
            StOp::Sh => 2,
            StOp::Sw => 4,
            StOp::Sd => 8,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IOp {
    Addi,
    Slti,
    Sltiu,
    Xori,
    Ori,
    Andi,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShOp {
    Slli,
    Srli,
    Srai,
    Rori,
    SlliUw,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShWOp {
    Slliw,
    Srliw,
    Sraiw,
    Roriw,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ROp {
    Add,
    Sub,
    Sll,
    Slt,
    Sltu,
    Xor,
    Srl,
    Sra,
    Or,
    And,
    Mul,
    Mulh,
    Mulhsu,
    Mulhu,
    Div,
    Divu,
    Rem,
    Remu,
    Sh1add,
    Sh2add,
    Sh3add,
    Andn,
    Orn,
    Xnor,
    Max,
    Maxu,
    Min,
    Minu,
    Rol,
    Ror,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RWOp {
    Addw,
    Subw,
    Sllw,
    Srlw,
    Sraw,
    Mulw,
    Divw,
    Divuw,
    Remw,
    Remuw,
    AddUw,
    Sh1addUw,
    Sh2addUw,
    Sh3addUw,
    Rolw,
    Rorw,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UOp {
    Clz,
    Ctz,
    Cpop,
    Clzw,
    Ctzw,
    Cpopw,
    SextB,
    SextH,
    ZextH,
    Rev8,
    OrcB,
}

/// An instruction with its control target as an instruction index (filled in by the
/// parser) or a symbol (a function, resolved by the checker or the linker).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Target {
    Local(usize),
    Symbol(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Instr {
    Lui {
        rd: Reg,
        imm: u32,
    },
    Auipc {
        rd: Reg,
        imm: u32,
    },
    Jal {
        rd: Reg,
        target: Target,
    },
    Jalr {
        rd: Reg,
        rs1: Reg,
        off: i64,
    },
    Branch {
        op: BrOp,
        rs1: Reg,
        rs2: Reg,
        target: Target,
    },
    Load {
        op: LdOp,
        rd: Reg,
        rs1: Reg,
        off: i64,
    },
    /// `rs1` is the base, `rs2` the value stored (as in Isa.lean).
    Store {
        op: StOp,
        rs1: Reg,
        rs2: Reg,
        off: i64,
    },
    IOp {
        op: IOp,
        rd: Reg,
        rs1: Reg,
        imm: i64,
    },
    Addiw {
        rd: Reg,
        rs1: Reg,
        imm: i64,
    },
    Shift {
        op: ShOp,
        rd: Reg,
        rs1: Reg,
        sh: u32,
    },
    ShiftW {
        op: ShWOp,
        rd: Reg,
        rs1: Reg,
        sh: u32,
    },
    ROp {
        op: ROp,
        rd: Reg,
        rs1: Reg,
        rs2: Reg,
    },
    RWOp {
        op: RWOp,
        rd: Reg,
        rs1: Reg,
        rs2: Reg,
    },
    UOp {
        op: UOp,
        rd: Reg,
        rs1: Reg,
    },
    Ecall,
    Unimp,
    /// `call f` / `tail f`: `auipc tmp, %pcrel_hi(f)` then `jalr rd, %pcrel_lo(f)(tmp)`,
    /// two words. With `-mno-relax` this pair is what runs; it jumps to `f` and writes
    /// `tmp` and `rd` (decision I21).
    CallPair {
        rd: Reg,
        tmp: Reg,
        target: Target,
    },
}

impl Instr {
    /// Number of 32-bit words.
    pub fn words(&self) -> usize {
        if matches!(self, Instr::CallPair { .. }) {
            2
        } else {
            1
        }
    }
    /// The register written, if any (never `x0`).
    pub fn rd(&self) -> Option<Reg> {
        let r = match self {
            Instr::Lui { rd, .. }
            | Instr::Auipc { rd, .. }
            | Instr::Jal { rd, .. }
            | Instr::Jalr { rd, .. }
            | Instr::Load { rd, .. }
            | Instr::IOp { rd, .. }
            | Instr::Addiw { rd, .. }
            | Instr::Shift { rd, .. }
            | Instr::ShiftW { rd, .. }
            | Instr::ROp { rd, .. }
            | Instr::RWOp { rd, .. }
            | Instr::UOp { rd, .. } => *rd,
            Instr::Ecall => A0,
            Instr::CallPair { rd, tmp, .. } => {
                if *rd != ZERO {
                    *rd
                } else {
                    *tmp
                }
            }
            Instr::Branch { .. } | Instr::Store { .. } | Instr::Unimp => return None,
        };
        (r != ZERO).then_some(r)
    }
}

fn r_ty(f7: u32, rs2: Reg, rs1: Reg, f3: u32, rd: Reg, opc: u32) -> u32 {
    f7 << 25 | (rs2.0 as u32) << 20 | (rs1.0 as u32) << 15 | f3 << 12 | (rd.0 as u32) << 7 | opc
}
fn i_ty(imm: u32, rs1: Reg, f3: u32, rd: Reg, opc: u32) -> u32 {
    (imm & 0xfff) << 20 | (rs1.0 as u32) << 15 | f3 << 12 | (rd.0 as u32) << 7 | opc
}

pub fn rop_code(op: ROp) -> (u32, u32) {
    use ROp::*;
    match op {
        Add => (0x00, 0),
        Sub => (0x20, 0),
        Sll => (0x00, 1),
        Slt => (0x00, 2),
        Sltu => (0x00, 3),
        Xor => (0x00, 4),
        Srl => (0x00, 5),
        Sra => (0x20, 5),
        Or => (0x00, 6),
        And => (0x00, 7),
        Mul => (0x01, 0),
        Mulh => (0x01, 1),
        Mulhsu => (0x01, 2),
        Mulhu => (0x01, 3),
        Div => (0x01, 4),
        Divu => (0x01, 5),
        Rem => (0x01, 6),
        Remu => (0x01, 7),
        Sh1add => (0x10, 2),
        Sh2add => (0x10, 4),
        Sh3add => (0x10, 6),
        Andn => (0x20, 7),
        Orn => (0x20, 6),
        Xnor => (0x20, 4),
        Max => (0x05, 6),
        Maxu => (0x05, 7),
        Min => (0x05, 4),
        Minu => (0x05, 5),
        Rol => (0x30, 1),
        Ror => (0x30, 5),
    }
}

pub fn rwop_code(op: RWOp) -> (u32, u32) {
    use RWOp::*;
    match op {
        Addw => (0x00, 0),
        Subw => (0x20, 0),
        Sllw => (0x00, 1),
        Srlw => (0x00, 5),
        Sraw => (0x20, 5),
        Mulw => (0x01, 0),
        Divw => (0x01, 4),
        Divuw => (0x01, 5),
        Remw => (0x01, 6),
        Remuw => (0x01, 7),
        AddUw => (0x04, 0),
        Sh1addUw => (0x10, 2),
        Sh2addUw => (0x10, 4),
        Sh3addUw => (0x10, 6),
        Rolw => (0x30, 1),
        Rorw => (0x30, 5),
    }
}

/// The 32-bit encoding, given the byte offset of each control target from this
/// instruction (`None` for a symbol the linker resolves: the field is 0, as in an object
/// file with a relocation).
pub fn encode(i: &Instr, target_off: Option<i64>) -> Option<u32> {
    let off = target_off.unwrap_or(0);
    Some(match i {
        Instr::Lui { rd, imm } => (imm & 0xfffff) << 12 | (rd.0 as u32) << 7 | 0x37,
        Instr::Auipc { rd, imm } => (imm & 0xfffff) << 12 | (rd.0 as u32) << 7 | 0x17,
        Instr::Jal { rd, .. } => {
            if !(-(1 << 20)..(1 << 20)).contains(&off) || off % 2 != 0 {
                return None;
            }
            let o = off as u32;
            ((o >> 20) & 1) << 31
                | ((o >> 1) & 0x3ff) << 21
                | ((o >> 11) & 1) << 20
                | ((o >> 12) & 0xff) << 12
                | (rd.0 as u32) << 7
                | 0x6f
        }
        Instr::Jalr { rd, rs1, off } => i_ty(imm12(*off)?, *rs1, 0, *rd, 0x67),
        Instr::Branch { op, rs1, rs2, .. } => {
            if !(-(1 << 12)..(1 << 12)).contains(&off) || off % 2 != 0 {
                return None;
            }
            let f3 = match op {
                BrOp::Beq => 0,
                BrOp::Bne => 1,
                BrOp::Blt => 4,
                BrOp::Bge => 5,
                BrOp::Bltu => 6,
                BrOp::Bgeu => 7,
            };
            let o = off as u32;
            ((o >> 12) & 1) << 31
                | ((o >> 5) & 0x3f) << 25
                | (rs2.0 as u32) << 20
                | (rs1.0 as u32) << 15
                | f3 << 12
                | ((o >> 1) & 0xf) << 8
                | ((o >> 11) & 1) << 7
                | 0x63
        }
        Instr::Load { op, rd, rs1, off } => {
            let f3 = match op {
                LdOp::Lb => 0,
                LdOp::Lh => 1,
                LdOp::Lw => 2,
                LdOp::Ld => 3,
                LdOp::Lbu => 4,
                LdOp::Lhu => 5,
                LdOp::Lwu => 6,
            };
            i_ty(imm12(*off)?, *rs1, f3, *rd, 0x03)
        }
        Instr::Store { op, rs1, rs2, off } => {
            let f3 = match op {
                StOp::Sb => 0,
                StOp::Sh => 1,
                StOp::Sw => 2,
                StOp::Sd => 3,
            };
            let o = imm12(*off)?;
            ((o >> 5) & 0x7f) << 25
                | (rs2.0 as u32) << 20
                | (rs1.0 as u32) << 15
                | f3 << 12
                | (o & 0x1f) << 7
                | 0x23
        }
        Instr::IOp { op, rd, rs1, imm } => {
            let f3 = match op {
                IOp::Addi => 0,
                IOp::Slti => 2,
                IOp::Sltiu => 3,
                IOp::Xori => 4,
                IOp::Ori => 6,
                IOp::Andi => 7,
            };
            i_ty(imm12(*imm)?, *rs1, f3, *rd, 0x13)
        }
        Instr::Addiw { rd, rs1, imm } => i_ty(imm12(*imm)?, *rs1, 0, *rd, 0x1b),
        Instr::Shift { op, rd, rs1, sh } => {
            if *sh >= 64 {
                return None;
            }
            let (top6, f3, opc) = match op {
                ShOp::Slli => (0x00, 1, 0x13),
                ShOp::Srli => (0x00, 5, 0x13),
                ShOp::Srai => (0x10, 5, 0x13),
                ShOp::Rori => (0x18, 5, 0x13),
                ShOp::SlliUw => (0x02, 1, 0x1b),
            };
            i_ty(top6 << 6 | sh, *rs1, f3, *rd, opc)
        }
        Instr::ShiftW { op, rd, rs1, sh } => {
            if *sh >= 32 {
                return None;
            }
            let (f7, f3) = match op {
                ShWOp::Slliw => (0x00, 1),
                ShWOp::Srliw => (0x00, 5),
                ShWOp::Sraiw => (0x20, 5),
                ShWOp::Roriw => (0x30, 5),
            };
            i_ty(f7 << 5 | sh, *rs1, f3, *rd, 0x1b)
        }
        Instr::ROp { op, rd, rs1, rs2 } => {
            let (f7, f3) = rop_code(*op);
            r_ty(f7, *rs2, *rs1, f3, *rd, 0x33)
        }
        Instr::RWOp { op, rd, rs1, rs2 } => {
            let (f7, f3) = rwop_code(*op);
            r_ty(f7, *rs2, *rs1, f3, *rd, 0x3b)
        }
        Instr::UOp { op, rd, rs1 } => match op {
            UOp::Clz => i_ty(0x600, *rs1, 1, *rd, 0x13),
            UOp::Ctz => i_ty(0x601, *rs1, 1, *rd, 0x13),
            UOp::Cpop => i_ty(0x602, *rs1, 1, *rd, 0x13),
            UOp::SextB => i_ty(0x604, *rs1, 1, *rd, 0x13),
            UOp::SextH => i_ty(0x605, *rs1, 1, *rd, 0x13),
            UOp::Rev8 => i_ty(0x6b8, *rs1, 5, *rd, 0x13),
            UOp::OrcB => i_ty(0x287, *rs1, 5, *rd, 0x13),
            UOp::Clzw => i_ty(0x600, *rs1, 1, *rd, 0x1b),
            UOp::Ctzw => i_ty(0x601, *rs1, 1, *rd, 0x1b),
            UOp::Cpopw => i_ty(0x602, *rs1, 1, *rd, 0x1b),
            UOp::ZextH => r_ty(0x04, ZERO, *rs1, 4, *rd, 0x3b),
        },
        Instr::Ecall => 0x0000_0073,
        Instr::Unimp => 0xc000_1073,
        Instr::CallPair { .. } => return None,
    })
}

/// The words of an instruction, `target_off` as in [`encode`] (from the first word).
pub fn encode_words(i: &Instr, target_off: Option<i64>) -> Option<Vec<u32>> {
    if let Instr::CallPair { rd, tmp, .. } = i {
        let off = target_off.unwrap_or(0);
        let hi = (off + 0x800) >> 12;
        let lo = off - (hi << 12);
        let au = Instr::Auipc {
            rd: *tmp,
            imm: (hi as u32) & 0xfffff,
        };
        let jr = Instr::Jalr {
            rd: *rd,
            rs1: *tmp,
            off: lo,
        };
        return Some(vec![encode(&au, None)?, encode(&jr, None)?]);
    }
    Some(vec![encode(i, target_off)?])
}

fn imm12(x: i64) -> Option<u32> {
    (-2048..2048).contains(&x).then_some((x as u32) & 0xfff)
}

fn sext32(x: u64) -> u64 {
    x as u32 as i32 as i64 as u64
}

/// The value written to `rd` by a computational instruction, given its source operand
/// values (RISC-V unprivileged spec, as in Machine.lean). `None` for instructions that
/// are not computational.
pub fn eval(i: &Instr, r1: u64, r2: u64) -> Option<u64> {
    Some(match i {
        Instr::Lui { imm, .. } => sext32((*imm as u64) << 12),
        Instr::IOp { op, imm, .. } => {
            let b = *imm as u64;
            match op {
                IOp::Addi => r1.wrapping_add(b),
                IOp::Slti => ((r1 as i64) < *imm) as u64,
                IOp::Sltiu => (r1 < b) as u64,
                IOp::Xori => r1 ^ b,
                IOp::Ori => r1 | b,
                IOp::Andi => r1 & b,
            }
        }
        Instr::Addiw { imm, .. } => sext32(r1.wrapping_add(*imm as u64)),
        Instr::Shift { op, sh, .. } => match op {
            ShOp::Slli => r1 << sh,
            ShOp::Srli => r1 >> sh,
            ShOp::Srai => ((r1 as i64) >> sh) as u64,
            ShOp::Rori => r1.rotate_right(*sh),
            ShOp::SlliUw => (r1 & 0xffff_ffff) << sh,
        },
        Instr::ShiftW { op, sh, .. } => {
            let w = r1 as u32;
            match op {
                ShWOp::Slliw => sext32((w << sh) as u64),
                ShWOp::Srliw => sext32((w >> sh) as u64),
                ShWOp::Sraiw => ((w as i32) >> sh) as i64 as u64,
                ShWOp::Roriw => sext32(w.rotate_right(*sh) as u64),
            }
        }
        Instr::ROp { op, .. } => rop(*op, r1, r2),
        Instr::RWOp { op, .. } => rwop(*op, r1, r2),
        Instr::UOp { op, .. } => match op {
            UOp::Clz => r1.leading_zeros() as u64,
            UOp::Ctz => r1.trailing_zeros() as u64,
            UOp::Cpop => r1.count_ones() as u64,
            UOp::Clzw => (r1 as u32).leading_zeros() as u64,
            UOp::Ctzw => (r1 as u32).trailing_zeros() as u64,
            UOp::Cpopw => (r1 as u32).count_ones() as u64,
            UOp::SextB => r1 as u8 as i8 as i64 as u64,
            UOp::SextH => r1 as u16 as i16 as i64 as u64,
            UOp::ZextH => r1 & 0xffff,
            UOp::Rev8 => r1.swap_bytes(),
            UOp::OrcB => {
                let mut out = 0u64;
                for k in 0..8 {
                    if (r1 >> (8 * k)) & 0xff != 0 {
                        out |= 0xff << (8 * k);
                    }
                }
                out
            }
        },
        _ => return None,
    })
}

pub fn rop(op: ROp, a: u64, b: u64) -> u64 {
    use ROp::*;
    let (sa, sb) = (a as i64, b as i64);
    match op {
        Add => a.wrapping_add(b),
        Sub => a.wrapping_sub(b),
        Sll => a << (b & 63),
        Slt => (sa < sb) as u64,
        Sltu => (a < b) as u64,
        Xor => a ^ b,
        Srl => a >> (b & 63),
        Sra => (sa >> (b & 63)) as u64,
        Or => a | b,
        And => a & b,
        Mul => a.wrapping_mul(b),
        Mulh => ((sa as i128 * sb as i128) >> 64) as u64,
        Mulhsu => ((sa as i128 * b as i128) >> 64) as u64,
        Mulhu => ((a as u128 * b as u128) >> 64) as u64,
        Div => {
            if b == 0 {
                u64::MAX
            } else {
                sa.wrapping_div(sb) as u64
            }
        }
        Divu => a.checked_div(b).unwrap_or(u64::MAX),
        Rem => {
            if b == 0 {
                a
            } else {
                sa.wrapping_rem(sb) as u64
            }
        }
        Remu => a.checked_rem(b).unwrap_or(a),
        Sh1add => (a << 1).wrapping_add(b),
        Sh2add => (a << 2).wrapping_add(b),
        Sh3add => (a << 3).wrapping_add(b),
        Andn => a & !b,
        Orn => a | !b,
        Xnor => !(a ^ b),
        Max => sa.max(sb) as u64,
        Maxu => a.max(b),
        Min => sa.min(sb) as u64,
        Minu => a.min(b),
        Rol => a.rotate_left((b & 63) as u32),
        Ror => a.rotate_right((b & 63) as u32),
    }
}

pub fn rwop(op: RWOp, a: u64, b: u64) -> u64 {
    use RWOp::*;
    let (wa, wb) = (a as u32, b as u32);
    let (sa, sb) = (wa as i32, wb as i32);
    let s = |x: u32| x as i32 as i64 as u64;
    match op {
        Addw => s(wa.wrapping_add(wb)),
        Subw => s(wa.wrapping_sub(wb)),
        Sllw => s(wa << (wb & 31)),
        Srlw => s(wa >> (wb & 31)),
        Sraw => (sa >> (wb & 31)) as i64 as u64,
        Mulw => s(wa.wrapping_mul(wb)),
        Divw => {
            if wb == 0 {
                u64::MAX
            } else {
                sa.wrapping_div(sb) as i64 as u64
            }
        }
        Divuw => wa.checked_div(wb).map(s).unwrap_or(u64::MAX),
        Remw => {
            if wb == 0 {
                sa as i64 as u64
            } else {
                sa.wrapping_rem(sb) as i64 as u64
            }
        }
        Remuw => {
            if wb == 0 {
                s(wa)
            } else {
                s(wa % wb)
            }
        }
        AddUw => (wa as u64).wrapping_add(b),
        Sh1addUw => ((wa as u64) << 1).wrapping_add(b),
        Sh2addUw => ((wa as u64) << 2).wrapping_add(b),
        Sh3addUw => ((wa as u64) << 3).wrapping_add(b),
        Rolw => s(wa.rotate_left(wb & 31)),
        Rorw => s(wa.rotate_right(wb & 31)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn known_encodings() {
        // from llvm-mc -triple riscv64 -mattr=+m,+zba,+zbb -show-encoding
        let a0 = A0;
        let a1 = A1;
        let a2 = A2;
        let add = Instr::ROp {
            op: ROp::Add,
            rd: a2,
            rs1: Reg(13),
            rs2: a2,
        };
        assert_eq!(encode(&add, None), Some(0x00c6_8633));
        let ld = Instr::Load {
            op: LdOp::Ld,
            rd: Reg(13),
            rs1: a0,
            off: 0,
        };
        assert_eq!(encode(&ld, None), Some(0x0005_3683));
        let addi = Instr::IOp {
            op: IOp::Addi,
            rd: a1,
            rs1: a1,
            imm: -1,
        };
        assert_eq!(encode(&addi, None), Some(0xfff5_8593));
        let ret = Instr::Jalr {
            rd: ZERO,
            rs1: RA,
            off: 0,
        };
        assert_eq!(encode(&ret, None), Some(0x0000_8067));
        let sd = Instr::Store {
            op: StOp::Sd,
            rs1: SP,
            rs2: RA,
            off: 72,
        };
        assert_eq!(encode(&sd, None), Some(0x0411_3423));
        let bne = Instr::Branch {
            op: BrOp::Bne,
            rs1: a1,
            rs2: ZERO,
            target: Target::Local(0),
        };
        assert_eq!(encode(&bne, Some(-16)), Some(0xfe05_98e3));
        let jal = Instr::Jal {
            rd: ZERO,
            target: Target::Local(0),
        };
        assert_eq!(encode(&jal, Some(8)), Some(0x0080_006f));
        let sh3 = Instr::ROp {
            op: ROp::Sh3add,
            rd: a0,
            rs1: a1,
            rs2: a0,
        };
        assert_eq!(encode(&sh3, None), Some(0x20a5_e533));
        let minu = Instr::ROp {
            op: ROp::Minu,
            rd: a0,
            rs1: a0,
            rs2: a1,
        };
        assert_eq!(encode(&minu, None), Some(0x0ab5_5533));
    }

    #[test]
    fn registers() {
        assert_eq!(Reg::parse("a0"), Some(A0));
        assert_eq!(Reg::parse("x10"), Some(A0));
        assert_eq!(Reg::parse("fp"), Some(Reg(8)));
        assert_eq!(Reg::parse("x32"), None);
        assert_eq!(Reg::parse("x01"), None);
        assert_eq!(Reg::parse("x0"), Some(ZERO));
    }
}

//! Lifting for the architectures `nocompiler-arch` decodes through a SLEIGH
//! specification: the specification's p-code, mapped onto the IR.
//!
//! The IR is p-code-shaped, so most of this is a renaming. What the mapping
//! has to add:
//!
//! - **The zero register.** RISC-V's `x0` reads as zero and ignores writes.
//!   The specification names it as an ordinary register, so a read becomes
//!   the constant and a write is dropped here.
//! - **Calls.** The IR's call defines the result register and is followed by
//!   an `Undefine` of every caller-saved register, the way the hand-written
//!   lifters do it, so dataflow does not carry a value across a call that the
//!   callee was free to overwrite.
//! - **Register layout.** The floating point registers move to a 16-byte
//!   stride, because the convention code assumes vector registers are 16
//!   bytes apart. Everything else keeps the specification's offsets.
//! - **Extensions the specification leaves `unimpl`.** Ghidra's RISC-V spec
//!   gives the bit-manipulation extensions (Zba, Zbb) no semantics. They are
//!   lifted here from the encoding, using the ratified encodings.
//!
//! An instruction whose p-code branches inside itself (to a p-code label) has
//! no IR form, because the IR's branches go to machine addresses. It is
//! reported as unimplemented rather than approximated.

use std::collections::HashMap;

use nocompiler_arch::sleigh::{self as arch_sleigh, Language};
use nocompiler_arch::{Insn, Operand};
use nocompiler_sleigh::pcode::{self as pc, Opcode};

use super::{Builder, Lifted, MAX_TEMPS};
use crate::op::{Op, Varnode};

/// The register-space offset of RISC-V's `pc`.
pub const RISCV_PC: u64 = 0x1000;
const GPR_BASE: u64 = 0x2000;
const SPEC_FPR_BASE: u64 = 0x3000;
const FPR_BASE: u64 = 0x3000;

/// The IR offset of integer register `x{n}`.
pub const fn gpr_offset(n: u8) -> u64 {
    GPR_BASE + 8 * n as u64
}

/// The IR offset of floating point register `f{n}`.
pub const fn fpr_offset(n: u8) -> u64 {
    FPR_BASE + 16 * n as u64
}

/// The IR offset of the stack pointer, `x2`.
pub const fn sp_offset() -> u64 {
    gpr_offset(2)
}

/// The IR offset of the return address register, `x1`.
pub const fn ra_offset() -> u64 {
    gpr_offset(1)
}

/// Whether `arch` is RISC-V RV64 through the embedded specification.
pub fn is_riscv64(arch: &nocompiler_core::Arch) -> bool {
    matches!(arch, nocompiler_core::Arch::Sleigh(id) if arch_sleigh::is_riscv64(id))
}

/// The instruction's encoding, which the SLEIGH decoder leaves in the last
/// operand because [`Insn`] does not carry its bytes.
fn encoding(i: &Insn) -> Option<Vec<u8>> {
    match i.operands().last() {
        Some(Operand::UImm(w)) => Some(w.to_le_bytes()[..i.len as usize].to_vec()),
        _ => None,
    }
}

struct Map<'a> {
    lang: &'a Language,
    b: Builder,
    temps: HashMap<u64, u64>,
}

impl Map<'_> {
    fn register(&self, offset: u64, size: u8) -> Varnode {
        if (SPEC_FPR_BASE..SPEC_FPR_BASE + 32 * 8).contains(&offset) {
            let rel = offset - SPEC_FPR_BASE;
            return Varnode::register(FPR_BASE + rel / 8 * 16 + rel % 8, size);
        }
        Varnode::register(offset, size)
    }

    fn is_zero(&self, v: &pc::Varnode) -> bool {
        v.space == pc::Space::Register && Some(v.offset) == self.lang.zero
    }

    /// An input: the zero register reads as zero.
    fn input(&mut self, v: &pc::Varnode) -> Option<Varnode> {
        if self.is_zero(v) {
            return Some(Varnode::constant(0, v.size));
        }
        self.place(v)
    }

    fn place(&mut self, v: &pc::Varnode) -> Option<Varnode> {
        Some(match v.space {
            pc::Space::Const => Varnode::constant(v.offset, v.size),
            pc::Space::Register => self.register(v.offset, v.size),
            pc::Space::Ram => Varnode {
                space: crate::op::Space::Ram,
                offset: v.offset,
                size: v.size,
            },
            pc::Space::Unique => {
                let n = self.temps.len() as u64;
                let id = *self.temps.entry(v.offset).or_insert(n);
                if id >= MAX_TEMPS {
                    return None;
                }
                Varnode::temp(id, v.size)
            }
        })
    }
}

fn opcode(op: Opcode) -> Option<Op> {
    use Opcode as P;
    Some(match op {
        P::Copy => Op::Copy,
        P::Load => Op::Load,
        P::Store => Op::Store,
        P::Branch => Op::Branch,
        P::CBranch => Op::CBranch,
        P::BranchInd => Op::BranchInd,
        P::Call => Op::Call,
        P::CallInd => Op::CallInd,
        P::Return => Op::Return,
        P::IntAdd => Op::IntAdd,
        P::IntSub => Op::IntSub,
        P::IntMul => Op::IntMul,
        P::IntDiv => Op::IntDiv,
        P::IntSDiv => Op::IntSDiv,
        P::IntRem => Op::IntRem,
        P::IntSRem => Op::IntSRem,
        P::IntMulHigh => Op::IntMulHigh,
        P::IntSMulHigh => Op::IntSMulHigh,
        P::IntAnd => Op::IntAnd,
        P::IntOr => Op::IntOr,
        P::IntXor => Op::IntXor,
        P::IntNot => Op::IntNot,
        P::IntNegate => Op::IntNegate,
        P::IntLeft => Op::IntLeft,
        P::IntRight => Op::IntRight,
        P::IntSRight => Op::IntSRight,
        P::IntEqual => Op::IntEqual,
        P::IntNotEqual => Op::IntNotEqual,
        P::IntLess => Op::IntLess,
        P::IntSLess => Op::IntSLess,
        P::IntLessEqual => Op::IntLessEqual,
        P::IntSLessEqual => Op::IntSLessEqual,
        P::IntCarry => Op::IntCarry,
        P::IntSCarry => Op::IntSCarry,
        P::IntSBorrow => Op::IntSBorrow,
        P::IntZExt => Op::IntZExt,
        P::IntSExt => Op::IntSExt,
        P::PopCount => Op::PopCount,
        P::LzCount => Op::LzCount,
        P::BoolAnd => Op::BoolAnd,
        P::BoolOr => Op::BoolOr,
        P::BoolXor => Op::BoolXor,
        P::BoolNot => Op::BoolNot,
        P::FloatAdd => Op::FloatAdd,
        P::FloatSub => Op::FloatSub,
        P::FloatMul => Op::FloatMul,
        P::FloatDiv => Op::FloatDiv,
        P::FloatNeg => Op::FloatNeg,
        P::FloatAbs => Op::FloatAbs,
        P::FloatSqrt => Op::FloatSqrt,
        P::FloatEqual => Op::FloatEqual,
        P::FloatNotEqual => Op::FloatNotEqual,
        P::FloatLess => Op::FloatLess,
        P::FloatLessEqual => Op::FloatLessEqual,
        P::FloatNan => Op::FloatNan,
        P::FloatTrunc => Op::FloatTrunc,
        P::FloatRound => Op::FloatRound,
        P::FloatCeil => Op::FloatCeil,
        P::FloatFloor => Op::FloatFloor,
        P::IntToFloat => Op::IntToFloat,
        P::FloatToInt => Op::FloatToInt,
        P::FloatConvert => Op::FloatConvert,
        P::Piece => Op::Piece,
        P::SubPiece => Op::SubPiece,
        P::Other | P::Unimplemented => return None,
    })
}

/// Lift one instruction decoded by the SLEIGH language `id`.
pub fn lift(id: &str, insn: &Insn) -> Lifted {
    let b = Builder::new(insn.addr);
    let (Some(lang), Some(bytes)) = (arch_sleigh::language(id), encoding(insn)) else {
        return b.unimplemented();
    };
    if bytes.len() == 8
        && let Some(p) = arch_sleigh::riscv_pair(&bytes, insn.addr)
    {
        return lift_pair(b, &p, insn);
    }
    let Some(full) = arch_sleigh::decode_full(lang, &bytes, insn.addr) else {
        return b.unimplemented();
    };
    let mut m = Map {
        lang,
        b,
        temps: HashMap::new(),
    };
    if !full.pcode.is_complete() || full.pcode.ops.iter().any(|o| o.relative) {
        let word = u32::from_le_bytes(
            [bytes.as_slice(), &[0; 4]].concat()[..4]
                .try_into()
                .unwrap_or([0; 4]),
        );
        return match riscv_bitmanip(&mut m.b, word) {
            Some(()) => m.b.finish(true),
            None => m.b.unimplemented(),
        };
    }
    let abi = crate::abi::lp64d();
    let result = Varnode::register(abi.results[0], 8);
    for op in &full.pcode.ops {
        let Some(ir) = opcode(op.op) else {
            // A named operation with no semantics: fences and hints change
            // nothing the IR models; ecall and ebreak are already in the
            // instruction's flow. Anything else is honestly unknown.
            match op.note.as_deref() {
                Some("fence") | Some("fence.i") | Some("ecall") | Some("ebreak") => {
                    if op.note.as_deref() == Some("ecall") {
                        // Linux reads a7 and a0-a5 and writes a0; every other
                        // register keeps its value (crate::syscall).
                        let a = &abi.integer_arguments;
                        let mut ins = vec![
                            Varnode::constant(crate::syscall::SYSCALL, 8),
                            Varnode::register(a[7], 8),
                        ];
                        ins.extend(a[..6].iter().map(|r| Varnode::register(*r, 8)));
                        m.b.emit(Op::Call, Some(result), &ins);
                    }
                    continue;
                }
                _ => return m.b.unimplemented(),
            }
        };
        if op.out.as_ref().is_some_and(|o| m.is_zero(o)) {
            continue;
        }
        let mut ins = Vec::with_capacity(op.ins.len());
        for v in &op.ins {
            match m.input(v) {
                Some(v) => ins.push(v),
                None => return m.b.unimplemented(),
            }
        }
        let out = match &op.out {
            Some(o) => match m.place(o) {
                Some(v) => Some(v),
                None => return m.b.unimplemented(),
            },
            None => None,
        };
        match ir {
            Op::Call | Op::CallInd => {
                m.b.emit(ir, Some(result), &ins);
                for r in &abi.caller_saved {
                    if *r != abi.results[0] {
                        m.b.emit(Op::Undefine, Some(Varnode::register(*r, 8)), &[]);
                    }
                }
            }
            _ => m.b.emit(ir, out, &ins),
        }
    }
    let mut lifted = m.b.finish(true);
    peephole(&mut lifted.ops);
    lifted
}

/// A fused `auipc` + `jalr` (see [`arch_sleigh::riscv_pair`]).
fn lift_pair(mut b: Builder, p: &arch_sleigh::Pair, insn: &Insn) -> Lifted {
    let abi = crate::abi::lp64d();
    b.emit(
        Op::Copy,
        Some(Varnode::register(gpr_offset(p.scratch), 8)),
        &[Varnode::constant(p.scratch_value, 8)],
    );
    let target = Varnode::constant(p.target, 8);
    if p.link {
        b.emit(
            Op::Copy,
            Some(Varnode::register(ra_offset(), 8)),
            &[Varnode::constant(insn.next().get(), 8)],
        );
        let result = Varnode::register(abi.results[0], 8);
        b.emit(Op::Call, Some(result), &[target]);
        for r in &abi.caller_saved {
            if *r != abi.results[0] {
                b.emit(Op::Undefine, Some(Varnode::register(*r, 8)), &[]);
            }
        }
    } else {
        b.emit(Op::Branch, None, &[target]);
    }
    b.finish(true)
}

/// Tidy one instruction's operations the way the hand-written lifters write
/// them: constants inline rather than copied into a temporary first, and a
/// result written straight to its register rather than through one.
///
/// This is not an optimisation for its own sake: passes that pattern-match
/// on the IR, such as stack slot promotion, look for `sp + constant` and do
/// not see it through a temporary.
fn peephole(ops: &mut Vec<crate::op::IrOp>) {
    use crate::op::Space;
    let is_temp = |v: &Varnode| v.space == Space::Unique;
    // Temporaries are numbered, not laid out in bytes, so two of them alias
    // only when they are the same one; `overlaps` would say u0:8 meets u1:8.
    let same = |a: Varnode, b: Varnode| {
        if is_temp(&a) || is_temp(&b) {
            a.space == b.space && a.offset == b.offset
        } else {
            a.overlaps(b)
        }
    };
    // Forward-substitute `t = Copy c` (c a constant) and `t = Copy u` (u a
    // temporary) into later uses, until either is redefined.
    let mut i = 0;
    while i < ops.len() {
        let op = ops[i];
        if op.op == Op::Copy
            && let (Some(t), Some(src)) = (op.out, op.input(0))
            && is_temp(&t)
            && (src.is_const() || is_temp(&src))
            && src.size == t.size
        {
            for later in ops.iter_mut().skip(i + 1) {
                later.map_inputs(|v| if v == t { src } else { v });
                if later
                    .out
                    .is_some_and(|o| same(o, t) || (is_temp(&src) && same(o, src)))
                {
                    break;
                }
            }
        }
        i += 1;
    }
    // `t = X ...; r = Copy t` with t used nowhere else becomes `r = X ...`.
    let uses = |ops: &[crate::op::IrOp], t: Varnode| {
        ops.iter()
            .flat_map(|o| o.inputs().iter())
            .filter(|v| same(**v, t))
            .count()
    };
    let mut i = 0;
    while i + 1 < ops.len() {
        let (a, c) = (ops[i], ops[i + 1]);
        if c.op == Op::Copy
            && let (Some(t), Some(src), Some(r)) = (a.out, c.input(0), c.out)
            && is_temp(&t)
            && src == t
            && t.size == r.size
            && uses(ops, t) == 1
            && !a.op.is_branch()
        {
            ops[i].out = Some(r);
            ops.remove(i + 1);
            continue;
        }
        i += 1;
    }
    // Copies into temporaries nothing reads any more.
    let mut i = 0;
    while i < ops.len() {
        if ops[i].op == Op::Copy
            && let Some(t) = ops[i].out
            && is_temp(&t)
            && uses(ops, t) == 0
        {
            ops.remove(i);
            continue;
        }
        i += 1;
    }
}

/// The RISC-V bit-manipulation instructions (Zba, Zbb) that Ghidra's
/// specification leaves without semantics, from their ratified encodings.
/// `None` for anything else.
fn riscv_bitmanip(b: &mut Builder, w: u32) -> Option<()> {
    let opcode = w & 0x7f;
    let rd = ((w >> 7) & 31) as u8;
    let f3 = (w >> 12) & 7;
    let rs1 = ((w >> 15) & 31) as u8;
    let rs2 = ((w >> 20) & 31) as u8;
    let f7 = w >> 25;
    let imm = w >> 20;
    let x = |n: u8| {
        if n == 0 {
            Varnode::constant(0, 8)
        } else {
            Varnode::register(gpr_offset(n), 8)
        }
    };
    let c = |v: u64| Varnode::constant(v, 8);
    let (a, s) = (x(rs1), x(rs2));
    let low32 = |b: &mut Builder, v: Varnode| {
        let t = b.eval(Op::SubPiece, 4, &[v, Varnode::constant(0, 4)]);
        b.eval(Op::IntZExt, 8, &[t])
    };
    let sext32 = |b: &mut Builder, v: Varnode| {
        let t = b.eval(Op::SubPiece, 4, &[v, Varnode::constant(0, 4)]);
        b.eval(Op::IntSExt, 8, &[t])
    };
    let rotl = |b: &mut Builder, v: Varnode, n: Varnode, bits: u64| {
        let n = b.eval(Op::IntAnd, 8, &[n, c(bits - 1)]);
        let l = b.eval(Op::IntLeft, 8, &[v, n]);
        let back = b.eval(Op::IntSub, 8, &[c(bits), n]);
        let back = b.eval(Op::IntAnd, 8, &[back, c(bits - 1)]);
        let r = b.eval(Op::IntRight, 8, &[v, back]);
        // n = 0 shifts right by 0 too; or-ing v with itself is still v.
        b.eval(Op::IntOr, 8, &[l, r])
    };
    let rotr = |b: &mut Builder, v: Varnode, n: Varnode, bits: u64| {
        let neg = b.eval(Op::IntSub, 8, &[c(bits), n]);
        rotl(b, v, neg, bits)
    };
    let select = |b: &mut Builder, cond: Varnode, t: Varnode, f: Varnode| {
        let wide = b.eval(Op::IntZExt, 8, &[cond]);
        let mask = b.eval(Op::IntNegate, 8, &[wide]);
        let keep = b.eval(Op::IntAnd, 8, &[t, mask]);
        let inv = b.eval(Op::IntNot, 8, &[mask]);
        let other = b.eval(Op::IntAnd, 8, &[f, inv]);
        b.eval(Op::IntOr, 8, &[keep, other])
    };
    let ctz = |b: &mut Builder, v: Varnode, bits: u64| {
        // popcount(~v & (v - 1)) counts the trailing zeros, and is `bits` for 0.
        let v = if bits == 32 {
            let hi = c(0xffff_ffff_0000_0000);
            b.eval(Op::IntOr, 8, &[v, hi])
        } else {
            v
        };
        let m1 = b.eval(Op::IntSub, 8, &[v, c(1)]);
        let inv = b.eval(Op::IntNot, 8, &[v]);
        let t = b.eval(Op::IntAnd, 8, &[inv, m1]);
        b.eval(Op::PopCount, 8, &[t])
    };
    let value = match (opcode, f3, f7) {
        // OP
        (0x33, 7, 0x20) => {
            let n = b.eval(Op::IntNot, 8, &[s]);
            b.eval(Op::IntAnd, 8, &[a, n])
        }
        (0x33, 6, 0x20) => {
            let n = b.eval(Op::IntNot, 8, &[s]);
            b.eval(Op::IntOr, 8, &[a, n])
        }
        (0x33, 4, 0x20) => {
            let t = b.eval(Op::IntXor, 8, &[a, s]);
            b.eval(Op::IntNot, 8, &[t])
        }
        (0x33, 4..=7, 0x05) => {
            let less = match f3 {
                4 | 6 => b.eval(Op::IntSLess, 1, &[a, s]),
                _ => b.eval(Op::IntLess, 1, &[a, s]),
            };
            // min picks a when a < b, max picks b.
            if f3 == 4 || f3 == 5 {
                select(b, less, a, s)
            } else {
                select(b, less, s, a)
            }
        }
        (0x33, 2 | 4 | 6, 0x10) => {
            let sh = b.eval(Op::IntLeft, 8, &[a, c((f3 / 2) as u64)]);
            b.eval(Op::IntAdd, 8, &[sh, s])
        }
        (0x33, 1, 0x30) => rotl(b, a, s, 64),
        (0x33, 5, 0x30) => rotr(b, a, s, 64),
        // OP-IMM
        (0x13, 1, _) if imm == 0x600 => b.eval(Op::LzCount, 8, &[a]),
        (0x13, 1, _) if imm == 0x601 => ctz(b, a, 64),
        (0x13, 1, _) if imm == 0x602 => b.eval(Op::PopCount, 8, &[a]),
        (0x13, 1, _) if imm == 0x604 || imm == 0x605 => {
            let size = if imm == 0x604 { 1 } else { 2 };
            let t = b.eval(Op::SubPiece, size, &[a, Varnode::constant(0, 4)]);
            b.eval(Op::IntSExt, 8, &[t])
        }
        (0x13, 5, _) if imm == 0x6b8 => {
            // rev8
            let mut acc = c(0);
            for i in 0..8u64 {
                let byte = b.eval(Op::IntRight, 8, &[a, c(8 * i)]);
                let byte = b.eval(Op::IntAnd, 8, &[byte, c(0xff)]);
                let placed = b.eval(Op::IntLeft, 8, &[byte, c(56 - 8 * i)]);
                acc = b.eval(Op::IntOr, 8, &[acc, placed]);
            }
            acc
        }
        (0x13, 5, _) if imm == 0x287 => {
            // orc.b
            let mut acc = c(0);
            for i in 0..8u64 {
                let mask = c(0xff << (8 * i));
                let byte = b.eval(Op::IntAnd, 8, &[a, mask]);
                let set = b.eval(Op::IntNotEqual, 1, &[byte, c(0)]);
                let wide = b.eval(Op::IntZExt, 8, &[set]);
                let full = b.eval(Op::IntMul, 8, &[wide, mask]);
                acc = b.eval(Op::IntOr, 8, &[acc, full]);
            }
            acc
        }
        (0x13, 5, _) if imm >> 6 == 0x18 => rotr(b, a, c((imm & 63) as u64), 64),
        // OP-32
        (0x3b, 0, 0x04) => {
            let z = low32(b, a);
            b.eval(Op::IntAdd, 8, &[z, s])
        }
        (0x3b, 4, 0x04) if rs2 == 0 => {
            let t = b.eval(Op::SubPiece, 2, &[a, Varnode::constant(0, 4)]);
            b.eval(Op::IntZExt, 8, &[t])
        }
        (0x3b, 2 | 4 | 6, 0x10) => {
            let z = low32(b, a);
            let sh = b.eval(Op::IntLeft, 8, &[z, c((f3 / 2) as u64)]);
            b.eval(Op::IntAdd, 8, &[sh, s])
        }
        (0x3b, 1 | 5, 0x30) => {
            let z = low32(b, a);
            let dup = b.eval(Op::IntLeft, 8, &[z, c(32)]);
            let both = b.eval(Op::IntOr, 8, &[z, dup]);
            let r = if f3 == 1 {
                rotl(b, both, s, 64)
            } else {
                rotr(b, both, s, 64)
            };
            // Rotating the doubled word by n < 32 leaves the rotated word in
            // both halves, so the low half is the answer either way.
            sext32(b, r)
        }
        // OP-IMM-32
        (0x1b, 1, _) if imm >> 6 == 0x02 => {
            let z = low32(b, a);
            b.eval(Op::IntLeft, 8, &[z, c((imm & 63) as u64)])
        }
        (0x1b, 1, _) if imm == 0x600 => {
            let t = b.eval(Op::SubPiece, 4, &[a, Varnode::constant(0, 4)]);
            b.eval(Op::LzCount, 8, &[t])
        }
        (0x1b, 1, _) if imm == 0x601 => ctz(b, a, 32),
        (0x1b, 1, _) if imm == 0x602 => {
            let t = b.eval(Op::SubPiece, 4, &[a, Varnode::constant(0, 4)]);
            b.eval(Op::PopCount, 8, &[t])
        }
        (0x1b, 5, 0x30) => {
            let z = low32(b, a);
            let dup = b.eval(Op::IntLeft, 8, &[z, c(32)]);
            let both = b.eval(Op::IntOr, 8, &[z, dup]);
            let r = rotr(b, both, c((imm & 31) as u64), 64);
            sext32(b, r)
        }
        _ => return None,
    };
    if rd != 0 {
        b.emit(Op::Copy, Some(x(rd)), &[value]);
    }
    Some(())
}

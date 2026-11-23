import LPS.Riscv.Prelude

/-!
# LPS `theories/Riscv/Instr.v` (f1006fe8): the RV64GC base instruction AST

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Riscv/Instr.v` at f1006fe8, the whole file. Immediates keep their encoded width with
the sign bit (I/S 12, B 13, U 20, J 21); compressed instructions expand into this AST (DecodeC).
The `EqDecision` instances are `DecidableEq` derivations.
-/

namespace LPS

inductive aluop where
  | ALU_ADD | ALU_SUB | ALU_SLL | ALU_SLT | ALU_SLTU
  | ALU_XOR | ALU_SRL | ALU_SRA | ALU_OR | ALU_AND
  deriving DecidableEq, Repr

inductive mulop where
  | M_MUL | M_MULH | M_MULHSU | M_MULHU
  | M_DIV | M_DIVU | M_REM | M_REMU
  deriving DecidableEq, Repr

inductive branch_cond where
  | BC_EQ | BC_NE | BC_LT | BC_GE | BC_LTU | BC_GEU
  deriving DecidableEq, Repr

inductive msize where
  | SZ1 | SZ2 | SZ4 | SZ8
  deriving DecidableEq, Repr

inductive amoop where
  | AMO_SWAP | AMO_ADD | AMO_XOR | AMO_AND | AMO_OR
  | AMO_MIN | AMO_MAX | AMO_MINU | AMO_MAXU
  deriving DecidableEq, Repr

inductive awidth where
  | AW | AD
  deriving DecidableEq, Repr

inductive csrop where
  | CSR_RW | CSR_RS | CSR_RC
  deriving DecidableEq, Repr

inductive ffmt where
  | FMT_S | FMT_D
  deriving DecidableEq, Repr

inductive fariop where
  | F_ADD | F_SUB | F_MUL | F_DIV
  deriving DecidableEq, Repr
inductive fmaop where
  | F_MADD | F_MSUB | F_NMSUB | F_NMADD
  deriving DecidableEq, Repr
inductive fsgnop where
  | F_SGNJ | F_SGNJN | F_SGNJX
  deriving DecidableEq, Repr
inductive fminmaxop where
  | F_MIN | F_MAX
  deriving DecidableEq, Repr
inductive fcmpop where
  | F_EQ | F_LT | F_LE
  deriving DecidableEq, Repr

inductive fcvt_ty where
  | FC_W | FC_WU | FC_L | FC_LU
  | FC_S | FC_D
  deriving DecidableEq, Repr

inductive fmvdir where
  | FMV_X_F | FMV_F_X
  deriving DecidableEq, Repr

inductive instr where
  -- RV32I / RV64I
  | Lui (rd : reg) (imm : bv 20)
  | Auipc (rd : reg) (imm : bv 20)
  | Jal (rd : reg) (imm : bv 21)
  | Jalr (rd rs1 : reg) (imm : bv 12)
  | Branch (c : branch_cond) (rs1 rs2 : reg) (imm : bv 13)
  | Load (sz : msize) (signed : Bool) (rd rs1 : reg) (imm : bv 12)
  | Store (sz : msize) (rs1 rs2 : reg) (imm : bv 12)
  | OpImm (op : aluop) (rd rs1 : reg) (imm : bv 12)
  | ShiftImm (op : aluop) (rd rs1 : reg) (shamt : bv 6)
  | Op (op : aluop) (rd rs1 rs2 : reg)
  | OpImm32 (rd rs1 : reg) (imm : bv 12)
  | ShiftImm32 (op : aluop) (rd rs1 : reg) (shamt : bv 5)
  | Op32 (op : aluop) (rd rs1 rs2 : reg)
  | Fence (fm : bv 4) (pred succ : bv 4) (rd rs1 : reg)
  | FenceI (rd rs1 : reg) (imm : bv 12)
  | Ecall
  | Ebreak
  -- M
  | Mul (op : mulop) (rd rs1 rs2 : reg)
  | Mul32 (op : mulop) (rd rs1 rs2 : reg)
  -- A
  | Lr (w : awidth) (aq rl : Bool) (rd rs1 : reg)
  | Sc (w : awidth) (aq rl : Bool) (rd rs1 rs2 : reg)
  | Amo (op : amoop) (w : awidth) (aq rl : Bool) (rd rs1 rs2 : reg)
  -- Zicsr
  | Csr (op : csrop) (rd rs1 : reg) (csr : bv 12)
  | CsrI (op : csrop) (rd : reg) (uimm : bv 5) (csr : bv 12)
  -- F/D loads/stores
  | FLoad (fmt : ffmt) (rd rs1 : reg) (imm : bv 12)
  | FStore (fmt : ffmt) (rs1 rs2 : reg) (imm : bv 12)
  -- F/D computation
  | Fma (op : fmaop) (fmt : ffmt) (rd rs1 rs2 rs3 : reg) (rm : bv 3)
  | Fari (op : fariop) (fmt : ffmt) (rd rs1 rs2 : reg) (rm : bv 3)
  | Fsqrt (fmt : ffmt) (rd rs1 : reg) (rm : bv 3)
  | Fsgnj (op : fsgnop) (fmt : ffmt) (rd rs1 rs2 : reg)
  | Fminmax (op : fminmaxop) (fmt : ffmt) (rd rs1 rs2 : reg)
  | Fcmp (op : fcmpop) (fmt : ffmt) (rd rs1 rs2 : reg)
  | Fcvt (dst src : fcvt_ty) (rd rs1 : reg) (rm : bv 3)
  | Fmv (dir : fmvdir) (fmt : ffmt) (rd rs1 : reg)
  | Fclass (fmt : ffmt) (rd rs1 : reg)
  deriving DecidableEq, Repr

/-- Instr.v:131. -/
def msize_bytes (sz : msize) : Int :=
  match sz with
  | .SZ1 => 1 | .SZ2 => 2 | .SZ4 => 4 | .SZ8 => 8

end LPS

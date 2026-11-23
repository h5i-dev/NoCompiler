import LPS.Riscv.Sem2

/-! Spot checks for `LPS.Riscv.Sem`/`Sem2`: one instruction on a concrete core. `eff` has function
fields (no decidable equality), so each check projects the outcome. -/

open LPS instr aluop mulop awidth eff core

/-- sp = 0x1000, a1 = 0x0000000100000002, a2 = 2, pc = 0x400. -/
def c0 : core :=
  Core (bvmap_set (2#5) (0x1000#64) (bvmap_set (11#5) (0x0000000100000002#64)
          (bvmap_set (12#5) (2#64) bvmap_empty)))
       bvmap_empty 0x400#64 0#32 none

def done_reg (r : reg) : eff → Option (word × word)
  | EDone c => some (rget c r, c_pc c)
  | _ => none

-- addi sp, sp, -32: sp = 0xfe0, pc = 0x404
example : done_reg 2#5 (exec 4#64 (OpImm ALU_ADD 2#5 2#5 (Z_to_bv 12 (-32))) c0)
    = some (0xfe0#64, 0x404#64) := by decide +kernel
-- divw a0, a1, a2 truncates operands first: 2 / 2 = 1 (Sem.v:481-489)
example : done_reg 10#5 (exec 4#64 (instr.Mul32 M_DIV 10#5 11#5 12#5) c0)
    = some (1#64, 0x404#64) := by decide +kernel
-- div by zero: all ones
example : done_reg 10#5 (exec 4#64 (instr.Mul M_DIVU 10#5 11#5 0#5) c0)
    = some (0xffffffffffffffff#64, 0x404#64) := by decide +kernel
-- writes to x0 are discarded
example : done_reg 0#5 (exec 2#64 (OpImm ALU_ADD 0#5 2#5 (Z_to_bv 12 5)) c0)
    = some (0#64, 0x402#64) := by decide +kernel
-- jal ra, +16 links pc + 4
example : done_reg 1#5 (exec 4#64 (Jal 1#5 (Z_to_bv 21 16)) c0) = some (0x404#64, 0x410#64) := by
  decide +kernel
-- ld a0, 8(sp): issues a 64-bit load at 0x1008; answering 0x55 retires a0 = 0x55
example : (match exec 4#64 (Load .SZ8 true 10#5 2#5 (Z_to_bv 12 8)) c0 with
           | ELoad 64 a k => some (a, done_reg 10#5 (k 0x55#64))
           | _ => none) = some (0x1008#64, some (0x55#64, 0x404#64)) := by decide +kernel
-- lr.w at a misaligned address faults, pc not advanced
example : (match exec 4#64 (Lr AW false false 10#5 11#5) (with_regs (bvmap_set (11#5) (0x1002#64)) c0) with
           | EFault c => some (c_pc c) | _ => none) = some 0x400#64 := by decide +kernel
-- ecall: EEcall with pc advanced
example : (match exec 4#64 Ecall c0 with | EEcall c => some (c_pc c) | _ => none) = some 0x404#64 := by
  decide +kernel
-- unimp = csrrw x0, cycle, x0: defined-illegal (read-only CSR written)
example : (match exec 4#64 (Csr .CSR_RW 0#5 0#5 0xc00#12) c0 with
           | EDefinedIllegal c => some (c_pc c) | _ => none) = some 0x400#64 := by decide +kernel
-- fadd.d with reserved rm 5: EIllegal with pc advanced
example : (match exec 4#64 (Fari .F_ADD .FMT_D 1#5 2#5 3#5 5#3) c0 with
           | EIllegal c => some (c_pc c) | _ => none) = some 0x404#64 := by decide +kernel
-- fdiv.s 1/3 accrues NX into fcsr and NaN-boxes the result
example : (match exec 4#64 (Fari .F_DIV .FMT_S 1#5 2#5 3#5 0#3)
             (with_fregs (fun m => bvmap_set (2#5) (nan_box 0x3F800000#32)
                (bvmap_set (3#5) (nan_box 0x40400000#32) m)) c0) with
           | EDone c => some (fget c 1#5, c_fcsr c) | _ => none)
    = some (0xffffffff3EAAAAAB#64, 1#32) := by decide +kernel

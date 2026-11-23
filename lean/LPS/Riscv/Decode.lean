import LPS.Riscv.Instr

/-!
# LPS `theories/Riscv/Decode.v` (f1006fe8): the 32-bit RV64IMAFD_Zicsr_Zifencei decoder

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Riscv/Decode.v` at f1006fe8. `decode w = none` means "not a valid 32-bit
instruction" (the intent there is to match binutils objdump; the policy notes are kept inline).
Immediates are kept at their encoded width, sign bit included; no sign extension happens here.

What changed and why: the section variable `w` of the field definitions is an explicit first
argument (as Rocq's section discharge makes it); `match` on a `Z` with literal patterns is a `match`
on `Int` literals (same arms, same order, first match wins as in Rocq); `decide (x = c)` and
`bool_decide (x = c)` are `decide (x = c)`; `(0 : bv 1)` is `0#1`. The `Goal` sanity checks
(Decode.v:325-380) are in `Examples/LPS/Test/DecodeTest.lean`.
-/

namespace LPS

open aluop mulop branch_cond msize amoop awidth csrop ffmt fariop fmaop fsgnop fminmaxop fcmpop
  fcvt_ty fmvdir instr

/-! ## Fields (Decode.v:12-35) -/

/-- Decode.v:16. -/
def f_rd (w : bv 32) : reg := bits 7 5 w
/-- Decode.v:17. -/
def f_rs1 (w : bv 32) : reg := bits 15 5 w
/-- Decode.v:18. -/
def f_rs2 (w : bv 32) : reg := bits 20 5 w
/-- Decode.v:19. -/
def f_rs3 (w : bv 32) : reg := bits 27 5 w

/-- Decode.v:22. -/
def imm_i (w : bv 32) : bv 12 := bits 20 12 w
/-- Decode.v:23. -/
def imm_s (w : bv 32) : bv 12 := bv_concat 12 (bits 25 7 w) (bits 7 5 w)
/-- Decode.v:24. -/
def imm_b (w : bv 32) : bv 13 :=
  bv_concat 13 (bits 31 1 w)
    (bv_concat 12 (bits 7 1 w)
      (bv_concat 11 (bits 25 6 w)
        (bv_concat 5 (bits 8 4 w) (0#1))))
/-- Decode.v:29. -/
def imm_u (w : bv 32) : bv 20 := bits 12 20 w
/-- Decode.v:30. -/
def imm_j (w : bv 32) : bv 21 :=
  bv_concat 21 (bits 31 1 w)
    (bv_concat 20 (bits 12 8 w)
      (bv_concat 12 (bits 20 1 w)
        (bv_concat 11 (bits 21 10 w) (0#1))))

/-! ## The decoder (Decode.v:37-323) -/

/-- Decode.v:37. -/
def decode (w : bv 32) : Option instr :=
  let opc := bv_unsigned (bits 0 7 w)
  let rd  := f_rd w
  let f3  := bv_unsigned (bits 12 3 w)
  let rs1 := f_rs1 w
  let rs2 := f_rs2 w
  let f7  := bv_unsigned (bits 25 7 w)
  let rm  : bv 3 := bits 12 3 w
  match opc with
  -- Words whose low two bits are not 11 fall through to `none` below,
  -- as do the 48-bit-and-up prefixes (bits[4:2] = 111).
  | 0x37 => some (Lui rd (imm_u w))
  | 0x17 => some (Auipc rd (imm_u w))
  | 0x6F => some (Jal rd (imm_j w))
  | 0x67 => if decide (f3 = 0) then some (Jalr rd rs1 (imm_i w)) else none
  | 0x63 => -- BRANCH
    let br c := some (Branch c rs1 rs2 (imm_b w))
    match f3 with
    | 0 => br BC_EQ  | 1 => br BC_NE
    | 4 => br BC_LT  | 5 => br BC_GE
    | 6 => br BC_LTU | 7 => br BC_GEU
    | _ => none
  | 0x03 => -- LOAD; funct3 = 7 (an "ldu") does not exist
    let ld sz sg := some (Load sz sg rd rs1 (imm_i w))
    match f3 with
    | 0 => ld SZ1 true  | 1 => ld SZ2 true
    | 2 => ld SZ4 true  | 3 => ld SZ8 true
    | 4 => ld SZ1 false | 5 => ld SZ2 false | 6 => ld SZ4 false
    | _ => none
  | 0x23 => -- STORE
    let st sz := some (Store sz rs1 rs2 (imm_s w))
    match f3 with
    | 0 => st SZ1 | 1 => st SZ2 | 2 => st SZ4 | 3 => st SZ8
    | _ => none
  | 0x13 => -- OP-IMM; RV64 shifts have 6-bit shamt (bit 25 may be set)
    let oi op := some (OpImm op rd rs1 (imm_i w))
    let sh := bits 20 6 w
    match f3 with
    | 0 => oi ALU_ADD | 2 => oi ALU_SLT | 3 => oi ALU_SLTU
    | 4 => oi ALU_XOR | 6 => oi ALU_OR  | 7 => oi ALU_AND
    | 1 => -- slli: bits[31:26] must be 000000
      if decide (bv_unsigned (bits 26 6 w) = 0)
      then some (ShiftImm ALU_SLL rd rs1 sh) else none
    | 5 =>
      match bv_unsigned (bits 26 6 w) with
      | 0x00 => some (ShiftImm ALU_SRL rd rs1 sh)
      | 0x10 => some (ShiftImm ALU_SRA rd rs1 sh)
      | _ => none
    | _ => none
  | 0x1B => -- OP-IMM-32; 5-bit shamt, bit 25 must be 0 (checked via funct7)
    let sh5 := bits 20 5 w
    match f3 with
    | 0 => some (OpImm32 rd rs1 (imm_i w))
    | 1 => if decide (f7 = 0)
           then some (ShiftImm32 ALU_SLL rd rs1 sh5) else none
    | 5 =>
      match f7 with
      | 0x00 => some (ShiftImm32 ALU_SRL rd rs1 sh5)
      | 0x20 => some (ShiftImm32 ALU_SRA rd rs1 sh5)
      | _ => none
    | _ => none
  | 0x33 => -- OP: funct7 checked exactly (0x00 / 0x20 / 0x01 = M)
    let op o := some (Op o rd rs1 rs2)
    let ml o := some (instr.Mul o rd rs1 rs2)
    match f7, f3 with
    | 0x00, 0 => op ALU_ADD | 0x20, 0 => op ALU_SUB
    | 0x00, 1 => op ALU_SLL
    | 0x00, 2 => op ALU_SLT | 0x00, 3 => op ALU_SLTU
    | 0x00, 4 => op ALU_XOR
    | 0x00, 5 => op ALU_SRL | 0x20, 5 => op ALU_SRA
    | 0x00, 6 => op ALU_OR  | 0x00, 7 => op ALU_AND
    | 0x01, 0 => ml M_MUL    | 0x01, 1 => ml M_MULH
    | 0x01, 2 => ml M_MULHSU | 0x01, 3 => ml M_MULHU
    | 0x01, 4 => ml M_DIV    | 0x01, 5 => ml M_DIVU
    | 0x01, 6 => ml M_REM    | 0x01, 7 => ml M_REMU
    | _, _ => none
  | 0x3B => -- OP-32; the M subset here is only mulw/divw/divuw/remw/remuw
    let op o := some (Op32 o rd rs1 rs2)
    let ml o := some (Mul32 o rd rs1 rs2)
    match f7, f3 with
    | 0x00, 0 => op ALU_ADD | 0x20, 0 => op ALU_SUB
    | 0x00, 1 => op ALU_SLL
    | 0x00, 5 => op ALU_SRL | 0x20, 5 => op ALU_SRA
    | 0x01, 0 => ml M_MUL
    | 0x01, 4 => ml M_DIV   | 0x01, 5 => ml M_DIVU
    | 0x01, 6 => ml M_REM   | 0x01, 7 => ml M_REMU
    | _, _ => none
  | 0x0F => -- MISC-MEM (Decode.v:133-138: binutils' fence / fence.tso / fence.i rules)
    match f3 with
    | 0 =>
      if decide (bv_unsigned rd = 0)
         && decide (bv_unsigned rs1 = 0)
         && (decide (bv_unsigned (bits 28 4 w) = 0)
             || decide (bv_unsigned (bits 20 12 w) = 0x833))
      then some (Fence (bits 28 4 w) (bits 24 4 w) (bits 20 4 w) rd rs1)
      else none
    | 1 =>
      if decide (bv_unsigned w = 0x0000100F)
      then some (FenceI rd rs1 (imm_i w)) else none
    | _ => none
  | 0x73 => -- SYSTEM
    match f3 with
    | 0 => -- Only ecall/ebreak; privileged instructions are out of scope (Decode.v:154-158).
      match bv_unsigned w with
      | 0x00000073 => some Ecall
      | 0x00100073 => some Ebreak
      | _ => none
    | 1 => some (Csr CSR_RW rd rs1 (bits 20 12 w))
    | 2 => some (Csr CSR_RS rd rs1 (bits 20 12 w))
    | 3 => some (Csr CSR_RC rd rs1 (bits 20 12 w))
    | 5 => some (CsrI CSR_RW rd rs1 (bits 20 12 w))
    | 6 => some (CsrI CSR_RS rd rs1 (bits 20 12 w))
    | 7 => some (CsrI CSR_RC rd rs1 (bits 20 12 w))
    | _ => none  -- funct3 = 4
  | 0x2F => -- AMO
    let aq := bit 26 w
    let rl := bit 25 w
    let go aw :=
      let am o := some (Amo o aw aq rl rd rs1 rs2)
      match bv_unsigned (bits 27 5 w) with
      | 0x00 => am AMO_ADD
      | 0x01 => am AMO_SWAP
      | 0x02 => -- lr: rs2 must be 0 (binutils rejects rs2 <> 0)
        if decide (bv_unsigned rs2 = 0)
        then some (Lr aw aq rl rd rs1) else none
      | 0x03 => some (Sc aw aq rl rd rs1 rs2)
      | 0x04 => am AMO_XOR
      | 0x08 => am AMO_OR
      | 0x0C => am AMO_AND
      | 0x10 => am AMO_MIN
      | 0x14 => am AMO_MAX
      | 0x18 => am AMO_MINU
      | 0x1C => am AMO_MAXU
      | _ => none
    match f3 with | 2 => go AW | 3 => go AD | _ => none
  | 0x07 => -- LOAD-FP: flw/fld only
    match f3 with
    | 2 => some (FLoad FMT_S rd rs1 (imm_i w))
    | 3 => some (FLoad FMT_D rd rs1 (imm_i w))
    | _ => none
  | 0x27 => -- STORE-FP
    match f3 with
    | 2 => some (FStore FMT_S rs1 rs2 (imm_s w))
    | 3 => some (FStore FMT_D rs1 rs2 (imm_s w))
    | _ => none
  | 0x43 | 0x47 | 0x4B | 0x4F => -- FMA group; fmt = bits[26:25]
    let mo := match opc with
              | 0x43 => F_MADD  | 0x47 => F_MSUB
              | 0x4B => F_NMSUB | _    => F_NMADD
    -- POLICY: rm kept raw; the reserved rm values 5/6 still decode here.
    match bv_unsigned (bits 25 2 w) with
    | 0 => some (Fma mo FMT_S rd rs1 rs2 (f_rs3 w) rm)
    | 1 => some (Fma mo FMT_D rd rs1 rs2 (f_rs3 w) rm)
    | _ => none  -- fmt 10/11 illegal (no Q/H)
  | 0x53 => -- OP-FP: funct7 dispatch.  rm kept raw (POLICY: reserved rm values 5/6 accepted).
    let cvt_int :=  -- integer fcvt_ty selected by the rs2 field
      match bv_unsigned rs2 with
      | 0 => some FC_W | 1 => some FC_WU
      | 2 => some FC_L | 3 => some FC_LU
      | _ => none
    match f7 with
    | 0x00 => some (Fari F_ADD FMT_S rd rs1 rs2 rm)
    | 0x01 => some (Fari F_ADD FMT_D rd rs1 rs2 rm)
    | 0x04 => some (Fari F_SUB FMT_S rd rs1 rs2 rm)
    | 0x05 => some (Fari F_SUB FMT_D rd rs1 rs2 rm)
    | 0x08 => some (Fari F_MUL FMT_S rd rs1 rs2 rm)
    | 0x09 => some (Fari F_MUL FMT_D rd rs1 rs2 rm)
    | 0x0C => some (Fari F_DIV FMT_S rd rs1 rs2 rm)
    | 0x0D => some (Fari F_DIV FMT_D rd rs1 rs2 rm)
    | 0x2C => if decide (bv_unsigned rs2 = 0)
              then some (Fsqrt FMT_S rd rs1 rm) else none
    | 0x2D => if decide (bv_unsigned rs2 = 0)
              then some (Fsqrt FMT_D rd rs1 rm) else none
    | 0x10 | 0x11 =>
      let fmt := if decide (f7 = 0x10) then FMT_S else FMT_D
      match f3 with
      | 0 => some (Fsgnj F_SGNJ fmt rd rs1 rs2)
      | 1 => some (Fsgnj F_SGNJN fmt rd rs1 rs2)
      | 2 => some (Fsgnj F_SGNJX fmt rd rs1 rs2)
      | _ => none
    | 0x14 | 0x15 =>
      let fmt := if decide (f7 = 0x14) then FMT_S else FMT_D
      match f3 with
      | 0 => some (Fminmax F_MIN fmt rd rs1 rs2)
      | 1 => some (Fminmax F_MAX fmt rd rs1 rs2)
      | _ => none
    | 0x50 | 0x51 => -- fcmp: feq/flt/fle = funct3 2/1/0
      let fmt := if decide (f7 = 0x50) then FMT_S else FMT_D
      match f3 with
      | 2 => some (Fcmp F_EQ fmt rd rs1 rs2)
      | 1 => some (Fcmp F_LT fmt rd rs1 rs2)
      | 0 => some (Fcmp F_LE fmt rd rs1 rs2)
      | _ => none
    | 0x60 => -- fcvt.{w,wu,l,lu}.s
      match cvt_int with
      | some dst => some (Fcvt dst FC_S rd rs1 rm) | none => none
    | 0x61 => -- fcvt.{w,wu,l,lu}.d
      match cvt_int with
      | some dst => some (Fcvt dst FC_D rd rs1 rm) | none => none
    | 0x68 => -- fcvt.s.{w,wu,l,lu}
      match cvt_int with
      | some src => some (Fcvt FC_S src rd rs1 rm) | none => none
    | 0x69 => -- fcvt.d.{w,wu,l,lu}; fcvt.d.w/wu are exact: binutils rejects rm <> 0 (Decode.v:274-278)
      match cvt_int with
      | some FC_W | some FC_WU =>
        if decide (f3 = 0)
        then match cvt_int with
             | some src => some (Fcvt FC_D src rd rs1 rm)
             | none => none
        else none
      | some src => some (Fcvt FC_D src rd rs1 rm)
      | none => none
    | 0x20 => -- fcvt.s.d (rs2 = 1); rs2 = 0 would be fcvt.s.s: illegal
      if decide (bv_unsigned rs2 = 1)
      then some (Fcvt FC_S FC_D rd rs1 rm) else none
    | 0x21 => -- fcvt.d.s (rs2 = 0); exact, so binutils rejects rm <> 0 (Decode.v:293-295)
      if decide (bv_unsigned rs2 = 0) && decide (f3 = 0)
      then some (Fcvt FC_D FC_S rd rs1 rm) else none
    | 0x70 => -- fmv.x.w (f3 = 0) / fclass.s (f3 = 1); rs2 must be 0
      if decide (bv_unsigned rs2 = 0) then
        match f3 with
        | 0 => some (Fmv FMV_X_F FMT_S rd rs1)
        | 1 => some (Fclass FMT_S rd rs1)
        | _ => none
      else none
    | 0x71 => -- fmv.x.d / fclass.d
      if decide (bv_unsigned rs2 = 0) then
        match f3 with
        | 0 => some (Fmv FMV_X_F FMT_D rd rs1)
        | 1 => some (Fclass FMT_D rd rs1)
        | _ => none
      else none
    | 0x78 => -- fmv.w.x
      if decide (bv_unsigned rs2 = 0) && decide (f3 = 0)
      then some (Fmv FMV_F_X FMT_S rd rs1) else none
    | 0x79 => -- fmv.d.x
      if decide (bv_unsigned rs2 = 0) && decide (f3 = 0)
      then some (Fmv FMV_F_X FMT_D rd rs1) else none
    | _ => none
  | _ => none

end LPS

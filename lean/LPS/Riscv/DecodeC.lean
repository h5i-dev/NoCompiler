import LPS.Riscv.Decode

/-!
# LPS `theories/Riscv/DecodeC.v` (f1006fe8): the RV64C compressed (16-bit) decoder

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Riscv/DecodeC.v` at f1006fe8. Compressed instructions get their own AST `cinstr`
(fields at encoded width, immediates stored scaled) and are expanded into the base `instr` by
`expand_c`. The binutils policy notes of DecodeC.v:10-24 hold unchanged (HINTs decode; shamt-0
shifts decode; 0x0000 is `none`; reserved encodings are `none` except c.addi16sp nzimm = 0).

What changed and why: `EqDecision cinstr` is `deriving DecidableEq`; `match .., decide P with
| .., left _ | .., right _` is a match on the `Bool` `decide P` (`true`/`false`); `(1 : bv 2)` is
`1#2`; `decide`/`bool_decide` are `decide`. The `Goal` sanity checks (DecodeC.v:278-332) are in
`Examples/LPS/Test/DecodeTest.lean`.
-/

namespace LPS

open aluop msize ffmt branch_cond instr

/-- DecodeC.v:29. Map a 3-bit compressed register field to x8..x15. -/
def creg (r : bv 3) : reg := bv_concat 5 (1#2) r

/-- DecodeC.v:31. -/
inductive cinstr : Type where
  -- Quadrant 0
  | CAddi4spn (rd' : bv 3) (nzuimm : bv 10)     -- addi rd', x2, nzuimm
  | CFld (rd' rs1' : bv 3) (uimm : bv 8)
  | CLw  (rd' rs1' : bv 3) (uimm : bv 7)
  | CLd  (rd' rs1' : bv 3) (uimm : bv 8)
  | CFsd (rs1' rs2' : bv 3) (uimm : bv 8)
  | CSw  (rs1' rs2' : bv 3) (uimm : bv 7)
  | CSd  (rs1' rs2' : bv 3) (uimm : bv 8)
  -- Quadrant 1
  | CAddi (rd : reg) (imm : bv 6)               -- c.nop = CAddi x0 0
  | CAddiw (rd : reg) (imm : bv 6)
  | CLi (rd : reg) (imm : bv 6)
  | CAddi16sp (imm : bv 10)                     -- addi x2, x2, imm (×16)
  | CLui (rd : reg) (imm : bv 6)
  | CSrli (rd' : bv 3) (shamt : bv 6)
  | CSrai (rd' : bv 3) (shamt : bv 6)
  | CAndi (rd' : bv 3) (imm : bv 6)
  | CSub (rd' rs2' : bv 3) | CXor (rd' rs2' : bv 3)
  | COr  (rd' rs2' : bv 3) | CAnd (rd' rs2' : bv 3)
  | CSubw (rd' rs2' : bv 3) | CAddw (rd' rs2' : bv 3)
  | CJ (imm : bv 12)
  | CBeqz (rs1' : bv 3) (imm : bv 9)
  | CBnez (rs1' : bv 3) (imm : bv 9)
  -- Quadrant 2
  | CSlli (rd : reg) (shamt : bv 6)
  | CFldsp (rd : reg) (uimm : bv 9)
  | CLwsp (rd : reg) (uimm : bv 8)
  | CLdsp (rd : reg) (uimm : bv 9)
  | CJr (rs1 : reg)
  | CMv (rd rs2 : reg)
  | CEbreak
  | CJalr (rs1 : reg)
  | CAdd (rd rs2 : reg)
  | CFsdsp (rs2 : reg) (uimm : bv 9)
  | CSwsp (rs2 : reg) (uimm : bv 8)
  | CSdsp (rs2 : reg) (uimm : bv 9)
  deriving DecidableEq, Repr

open cinstr

/-- DecodeC.v:72. -/
def decode16 (h : bv 16) : Option cinstr :=
  let f3 := bv_unsigned (bits 13 3 h)
  let r1c := bits 7 3 h   -- rs1'/rd'
  let r2c := bits 2 3 h   -- rs2'/rd'
  let rd  := bits 7 5 h   -- full-width rd/rs1
  let rs2 := bits 2 5 h   -- full-width rs2
  -- Common immediates
  let imm6 : bv 6 := bv_concat 6 (bits 12 1 h) (bits 2 5 h)
  let uimm_d : bv 8 :=  -- c.fld/c.ld/c.fsd/c.sd: ×8
    bv_concat 8 (bits 5 2 h) (bv_concat 6 (bits 10 3 h) (0#3))
  let uimm_w : bv 7 :=  -- c.lw/c.sw: ×4
    bv_concat 7 (bits 5 1 h)
      (bv_concat 6 (bits 10 3 h) (bv_concat 3 (bits 6 1 h) (0#2)))
  match bv_unsigned (bits 0 2 h), f3 with
  -- ---- Quadrant 0 ----
  | 0, 0 =>
    -- c.addi4spn; nzuimm = 0 is reserved (covers the all-zero halfword 0x0000)
    let nzuimm : bv 10 :=
      bv_concat 10 (bits 7 4 h)
        (bv_concat 6 (bits 11 2 h)
          (bv_concat 4 (bits 5 1 h)
            (bv_concat 3 (bits 6 1 h) (0#2))))
    if decide (bv_unsigned nzuimm = 0) then none
    else some (CAddi4spn r2c nzuimm)
  | 0, 1 => some (CFld r2c r1c uimm_d)
  | 0, 2 => some (CLw r2c r1c uimm_w)
  | 0, 3 => some (CLd r2c r1c uimm_d)   -- RV64: c.ld, not c.flw
  | 0, 5 => some (CFsd r1c r2c uimm_d)
  | 0, 6 => some (CSw r1c r2c uimm_w)
  | 0, 7 => some (CSd r1c r2c uimm_d)
  -- ---- Quadrant 1 ----
  | 1, 0 => some (CAddi rd imm6)        -- incl. c.nop and hints
  | 1, 1 => -- RV64: c.addiw (RV32's c.jal); rd = 0 reserved
    if decide (bv_unsigned rd = 0) then none else some (CAddiw rd imm6)
  | 1, 2 => some (CLi rd imm6)          -- rd = 0 is a hint; decode it
  | 1, 3 =>
    if decide (bv_unsigned rd = 2) then
      -- c.addi16sp: nzimm[9|8:7|6|5|4] at h[12|4:3|5|2|6], ×16; nzimm = 0 decoded (binutils 2.40)
      let imm : bv 10 :=
        bv_concat 10 (bits 12 1 h)
          (bv_concat 9 (bits 3 2 h)
            (bv_concat 7 (bits 5 1 h)
              (bv_concat 6 (bits 2 1 h)
                (bv_concat 5 (bits 6 1 h) (0#4)))))
      some (CAddi16sp imm)
    else
      -- c.lui; imm = 0 reserved.  rd = 0 is a hint — decoded.
      if decide (bv_unsigned imm6 = 0) then none else some (CLui rd imm6)
  | 1, 4 =>
    match bv_unsigned (bits 10 2 h) with
    | 0 => some (CSrli r1c imm6)  -- shamt = 0 is a hint; decode it
    | 1 => some (CSrai r1c imm6)
    | 2 => some (CAndi r1c imm6)
    | _ => -- 3: register-register group
      match bit 12 h, bv_unsigned (bits 5 2 h) with
      | false, 0 => some (CSub r1c r2c)
      | false, 1 => some (CXor r1c r2c)
      | false, 2 => some (COr r1c r2c)
      | false, _ => some (CAnd r1c r2c)
      | true, 0 => some (CSubw r1c r2c)
      | true, 1 => some (CAddw r1c r2c)
      | true, _ => none  -- reserved
  | 1, 5 => -- c.j: imm[11|4|9:8|10|6|7|3:1|5] at h[12|11|10:9|8|7|6|5:3|2]
    some (CJ (bv_concat 12 (bits 12 1 h)
      (bv_concat 11 (bits 8 1 h)
        (bv_concat 10 (bits 9 2 h)
          (bv_concat 8 (bits 6 1 h)
            (bv_concat 7 (bits 7 1 h)
              (bv_concat 6 (bits 2 1 h)
                (bv_concat 5 (bits 11 1 h)
                  (bv_concat 4 (bits 3 3 h) (0#1))))))))))
  | 1, 6 | 1, 7 => -- c.beqz/c.bnez: imm[8|4:3|7:6|2:1|5] at h[12|11:10|6:5|4:3|2]
    let imm : bv 9 :=
      bv_concat 9 (bits 12 1 h)
        (bv_concat 8 (bits 5 2 h)
          (bv_concat 6 (bits 2 1 h)
            (bv_concat 5 (bits 10 2 h)
              (bv_concat 3 (bits 3 2 h) (0#1)))))
    if decide (f3 = 6) then some (CBeqz r1c imm) else some (CBnez r1c imm)
  -- ---- Quadrant 2 ----
  | 2, 0 => some (CSlli rd imm6)        -- rd = 0 / shamt = 0: hints
  | 2, 1 => -- c.fldsp: uimm[5|4:3|8:6] at h[12|6:5|4:2], ×8
    some (CFldsp rd (bv_concat 9 (bits 2 3 h)
      (bv_concat 6 (bits 12 1 h) (bv_concat 5 (bits 5 2 h) (0#3)))))
  | 2, 2 => -- c.lwsp: uimm[5|4:2|7:6] at h[12|6:4|3:2], ×4; rd = 0 reserved
    if decide (bv_unsigned rd = 0) then none
    else some (CLwsp rd (bv_concat 8 (bits 2 2 h)
      (bv_concat 6 (bits 12 1 h) (bv_concat 5 (bits 4 3 h) (0#2)))))
  | 2, 3 => -- c.ldsp; rd = 0 reserved
    if decide (bv_unsigned rd = 0) then none
    else some (CLdsp rd (bv_concat 9 (bits 2 3 h)
      (bv_concat 6 (bits 12 1 h) (bv_concat 5 (bits 5 2 h) (0#3)))))
  | 2, 4 =>
    match bit 12 h, decide (bv_unsigned rs2 = 0) with
    | false, true => -- c.jr; rs1 = 0 reserved
      if decide (bv_unsigned rd = 0) then none else some (CJr rd)
    | false, false => some (CMv rd rs2)   -- rd = 0 hint; decode
    | true, true =>
      if decide (bv_unsigned rd = 0) then some CEbreak
      else some (CJalr rd)
    | true, false => some (CAdd rd rs2)   -- rd = 0 hint; decode
  | 2, 5 => -- c.fsdsp: uimm[5:3|8:6] at h[12:10|9:7], ×8
    some (CFsdsp rs2 (bv_concat 9 (bits 7 3 h)
      (bv_concat 6 (bits 10 3 h) (0#3))))
  | 2, 6 => -- c.swsp: uimm[5:2|7:6] at h[12:9|8:7], ×4
    some (CSwsp rs2 (bv_concat 8 (bits 7 2 h)
      (bv_concat 6 (bits 9 4 h) (0#2))))
  | 2, 7 => -- c.sdsp
    some (CSdsp rs2 (bv_concat 9 (bits 7 3 h)
      (bv_concat 6 (bits 10 3 h) (0#3))))
  -- Quadrant 3 = low bits 11: a 32-bit instruction, not compressed.
  | _, _ => none

/-! ## Expansion into the base AST (DecodeC.v:194-238) -/

/-- DecodeC.v:196. -/
def x0 : reg := 0
/-- DecodeC.v:197. -/
def x1 : reg := 1
/-- DecodeC.v:198. -/
def x2 : reg := 2

/-- DecodeC.v:200. -/
def expand_c (c : cinstr) : instr :=
  match c with
  | CAddi4spn rd' nzuimm => OpImm ALU_ADD (creg rd') x2 (zext 12 nzuimm)
  | CFld rd' rs1' uimm => FLoad FMT_D (creg rd') (creg rs1') (zext 12 uimm)
  | CLw rd' rs1' uimm => Load SZ4 true (creg rd') (creg rs1') (zext 12 uimm)
  | CLd rd' rs1' uimm => Load SZ8 true (creg rd') (creg rs1') (zext 12 uimm)
  | CFsd rs1' rs2' uimm => FStore FMT_D (creg rs1') (creg rs2') (zext 12 uimm)
  | CSw rs1' rs2' uimm => Store SZ4 (creg rs1') (creg rs2') (zext 12 uimm)
  | CSd rs1' rs2' uimm => Store SZ8 (creg rs1') (creg rs2') (zext 12 uimm)
  | CAddi rd imm => OpImm ALU_ADD rd rd (sext 12 imm)
  | CAddiw rd imm => OpImm32 rd rd (sext 12 imm)
  | CLi rd imm => OpImm ALU_ADD rd x0 (sext 12 imm)
  | CAddi16sp imm => OpImm ALU_ADD x2 x2 (sext 12 imm)  -- imm is ×16 already
  | CLui rd imm => Lui rd (sext 20 imm)   -- 6-bit nzimm sexts into U-imm
  | CSrli rd' sh => ShiftImm ALU_SRL (creg rd') (creg rd') sh
  | CSrai rd' sh => ShiftImm ALU_SRA (creg rd') (creg rd') sh
  | CAndi rd' imm => OpImm ALU_AND (creg rd') (creg rd') (sext 12 imm)
  | CSub rd' rs2' => Op ALU_SUB (creg rd') (creg rd') (creg rs2')
  | CXor rd' rs2' => Op ALU_XOR (creg rd') (creg rd') (creg rs2')
  | COr rd' rs2' => Op ALU_OR (creg rd') (creg rd') (creg rs2')
  | CAnd rd' rs2' => Op ALU_AND (creg rd') (creg rd') (creg rs2')
  | CSubw rd' rs2' => Op32 ALU_SUB (creg rd') (creg rd') (creg rs2')
  | CAddw rd' rs2' => Op32 ALU_ADD (creg rd') (creg rd') (creg rs2')
  | CJ imm => Jal x0 (sext 21 imm)
  | CBeqz rs1' imm => Branch BC_EQ (creg rs1') x0 (sext 13 imm)
  | CBnez rs1' imm => Branch BC_NE (creg rs1') x0 (sext 13 imm)
  | CSlli rd sh => ShiftImm ALU_SLL rd rd sh
  | CFldsp rd uimm => FLoad FMT_D rd x2 (zext 12 uimm)
  | CLwsp rd uimm => Load SZ4 true rd x2 (zext 12 uimm)
  | CLdsp rd uimm => Load SZ8 true rd x2 (zext 12 uimm)
  | CJr rs1 => Jalr x0 rs1 0
  | CMv rd rs2 => Op ALU_ADD rd x0 rs2
  | CEbreak => Ebreak
  | CJalr rs1 => Jalr x1 rs1 0
  | CAdd rd rs2 => Op ALU_ADD rd rd rs2
  | CFsdsp rs2 uimm => FStore FMT_D x2 rs2 (zext 12 uimm)
  | CSwsp rs2 uimm => Store SZ4 x2 rs2 (zext 12 uimm)
  | CSdsp rs2 uimm => Store SZ8 x2 rs2 (zext 12 uimm)

/-- DecodeC.v:242. Decode either width from a 32-bit fetch; returns the length in bytes (2 or 4). -/
def decode_any (w : bv 32) : Option (instr × Int) :=
  if decide (bv_unsigned (bits 0 2 w) = 3) then
    match decode w with
    | some i => some (i, 4)
    | none => none
  else
    match decode16 (bits 0 16 w) with
    | some c => some (expand_c c, 2)
    | none => none

/-- DecodeC.v:275. Architecturally defined-illegal: bits [15:0] all zero (upper half ignored). -/
def is_defined_illegal (w : bv 32) : Bool :=
  decide (bv_unsigned (bits 0 16 w) = 0)

end LPS

import LPS.Riscv.Sem

/-!
# LPS `theories/Riscv/Sem.v` (f1006fe8), part 2: `exec` and `step`

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Riscv/Sem.v` at f1006fe8, lines 431-704. Same case structure, same order of
arms; the conventions are those of `LPS/Riscv/Sem.lean`. Two spelling changes: Rocq applies a
`match` returning `eff → eff` to the continuation (`(match wd with AW => EStore 32 a .. | ..) k`);
here that `match` carries the type ascription `(.. : eff → eff)`. `let '(v, fl) := ..` is
`let (v, fl) := ..`.
-/

namespace LPS

open aluop mulop branch_cond msize amoop awidth csrop ffmt fariop fmaop fminmaxop fcmpop fcvt_ty
  fmvdir instr eff core

/-- Sem.v:437. Execute one decoded instruction, including the pc update; `sz` is the encoded size
    (2 or 4), which is both the pc advance and the jal/jalr link offset. -/
def exec (sz : word) (i : instr) (c : core) : eff :=
  let pc := c_pc c
  let npc := pc + sz
  let cn := with_pc npc c   -- pc advanced past the instruction
  match i with
  -- RV64I
  | Lui rd imm =>
    EDone (rset rd (sext 64 (bv_concat 32 imm (Z_to_bv 12 0))) cn)
  | Auipc rd imm =>
    EDone (rset rd (pc + sext 64 (bv_concat 32 imm (Z_to_bv 12 0))) cn)
  | Jal rd imm =>
    EDone (rset rd npc (with_pc (pc + sext 64 imm) c))
  | Jalr rd rs1 imm =>
    -- Target computed before the link write: rd may equal rs1.
    let a := rget c rs1
    EDone (rset rd npc (with_pc (bv_and (a + sext 64 imm) (bv_not w1)) c))
  | Branch bc rs1 rs2 imm =>
    EDone (with_pc (if branch_taken bc (rget c rs1) (rget c rs2)
                    then pc + sext 64 imm else npc) c)
  | Load msz sgn rd rs1 imm =>
    load_val msz sgn (rget c rs1 + sext 64 imm)
      (fun v => EDone (rset rd v cn))
  | Store msz rs1 rs2 imm =>
    let a := rget c rs1 + sext 64 imm
    store_val msz a (rget c rs2) (EDone (inval_resv a cn))
  | OpImm op rd rs1 imm =>
    EDone (rset rd (alu64 op (rget c rs1) (sext 64 imm)) cn)
  | ShiftImm op rd rs1 shamt =>
    EDone (rset rd (alu64 op (rget c rs1) (zext 64 shamt)) cn)
  | Op op rd rs1 rs2 =>
    EDone (rset rd (alu64 op (rget c rs1) (rget c rs2)) cn)
  | OpImm32 rd rs1 imm =>
    EDone (rset rd (sext 64 (alu32 ALU_ADD (low32 (rget c rs1)) (sext 32 imm))) cn)
  | ShiftImm32 op rd rs1 shamt =>
    EDone (rset rd (sext 64 (alu32 op (low32 (rget c rs1)) (zext 32 shamt))) cn)
  | Op32 op rd rs1 rs2 =>
    EDone (rset rd (sext 64 (alu32 op (low32 (rget c rs1)) (low32 (rget c rs2)))) cn)
  | Fence _ _ _ _ _ | FenceI _ _ _ =>
    EDone cn   -- single hart: fences are no-ops
  | Ecall => EEcall cn
  | Ebreak => EEbreak cn
  -- M
  | instr.Mul op rd rs1 rs2 =>
    EDone (rset rd (mul_div op (rget c rs1) (rget c rs2)) cn)
  -- Operands are truncated to 32 bits BEFORE the divide, per the ISA (Sem.v:481-489).
  | Mul32 op rd rs1 rs2 =>
    EDone (rset rd (sext 64 (mul_div op (low32 (rget c rs1)) (low32 (rget c rs2)))) cn)
  -- A: sequential single-hart model, composed from plain memory ops.
  | Lr wd _ _ rd rs1 =>
    let a := rget c rs1
    if !(amo_aligned wd a) then EFault c
    else match wd with
    | AW => ELoad 32 a (fun v =>
              EDone (with_resv (some a) (rset rd (sext 64 v) cn)))
    | AD => ELoad 64 a (fun v =>
              EDone (with_resv (some a) (rset rd v cn)))
  | Sc wd _ _ rd rs1 rs2 =>
    let a := rget c rs1
    -- Alignment first, before the reservation.
    if !(amo_aligned wd a) then EFault c
    else
    let ok := match c_resv c with
              | some r => bv_unsigned r == bv_unsigned a
              | none => false
    let c1 := with_resv none cn
    if ok then
      (match wd with
       | AW => EStore 32 a (low32 (rget c rs2))
       | AD => EStore 64 a (rget c rs2) : eff → eff) (EDone (rset rd w0 c1))
    else EDone (rset rd w1 c1)
  | Amo op wd _ _ rd rs1 rs2 =>
    let a := rget c rs1
    if !(amo_aligned wd a) then EFault c
    else
    let src := rget c rs2
    let c1 := inval_resv a cn
    match wd with
    | AW => ELoad 32 a (fun old =>
              EStore 32 a (amo_val op old (low32 src))
                (EDone (rset rd (sext 64 old) c1)))
    | AD => ELoad 64 a (fun old =>
              EStore 64 a (amo_val op old src)
                (EDone (rset rd old c1)))
  -- Zicsr.  The architectural read-only check runs on the PRE-state core `c`.
  | Csr op rd rs1 csr =>
    let writes := match op with | CSR_RW => true | _ => !(is_x0 rs1)
    if csr_write_illegal writes csr then EDefinedIllegal c
    else exec_csr op rd (rget c rs1) writes csr cn
  | CsrI op rd uimm csr =>
    let writes :=
      match op with
      | CSR_RW => true
      | _ => !(bv_unsigned uimm == 0)
    if csr_write_illegal writes csr then EDefinedIllegal c
    else exec_csr op rd (zext 64 uimm) writes csr cn
  -- F/D data movement.
  | FLoad fmt rd rs1 imm =>
    let a := rget c rs1 + sext 64 imm
    match fmt with
    | FMT_S => ELoad 32 a (fun v => EDone (fset rd (nan_box v) cn))
    | FMT_D => ELoad 64 a (fun v => EDone (fset rd v cn))
  | FStore fmt rs1 rs2 imm =>
    let a := rget c rs1 + sext 64 imm
    let v := fget c rs2
    (match fmt with
     | FMT_S => EStore 32 a (low32 v)
     | FMT_D => EStore 64 a v : eff → eff) (EDone (inval_resv a cn))
  | Fmv dir fmt rd rs1 =>
    EDone (match dir, fmt with
           | FMV_X_F, FMT_S => rset rd (sext 64 (low32 (fget c rs1))) cn
           | FMV_X_F, FMT_D => rset rd (fget c rs1) cn
           | FMV_F_X, FMT_S => fset rd (nan_box (low32 (rget c rs1))) cn
           | FMV_F_X, FMT_D => fset rd (rget c rs1) cn)
  | Fsgnj op fmt rd rs1 rs2 =>
    let a := fget c rs1
    let b := fget c rs2
    EDone (match fmt with
           | FMT_S => fset rd (nan_box (sgnj_val op (unbox_s a) (unbox_s b))) cn
           | FMT_D => fset rd (sgnj_val op a b) cn)
  -- F/D arithmetic: resolve rm (reserved = EIllegal, pc advanced), read, Fpu, write, accrue.
  | Fari op fmt rd rs1 rs2 rm =>
    match resolve_rm rm cn with
    | none => EIllegal cn
    | some md =>
      let f := fp_format fmt
      let a := fread c fmt rs1
      let b := fread c fmt rs2
      let (v, fl) :=
        match op with
        | F_ADD => fp_add f md a b
        | F_SUB => fp_sub f md a b
        | F_MUL => fp_mul f md a b
        | F_DIV => fp_div f md a b
      EDone (fwrite fmt rd v (accrue fl cn))
  | Fsqrt fmt rd rs1 rm =>
    match resolve_rm rm cn with
    | none => EIllegal cn
    | some md =>
      let (v, fl) := fp_sqrt (fp_format fmt) md (fread c fmt rs1)
      EDone (fwrite fmt rd v (accrue fl cn))
  -- The four fused forms share one kernel; negation is a sign-bit flip of an operand.
  | Fma op fmt rd rs1 rs2 rs3 rm =>
    match resolve_rm rm cn with
    | none => EIllegal cn
    | some md =>
      let f := fp_format fmt
      let a := fread c fmt rs1
      let b := fread c fmt rs2
      let z := fread c fmt rs3
      let (a', z') :=
        match op with
        | F_MADD => (a, z)
        | F_MSUB => (a, fp_neg f z)
        | F_NMSUB => (fp_neg f a, z)
        | F_NMADD => (fp_neg f a, fp_neg f z)
      let (v, fl) := fp_fma f md a' b z'
      EDone (fwrite fmt rd v (accrue fl cn))
  | Fminmax op fmt rd rs1 rs2 =>
    let (v, fl) :=
      fp_minmax (fp_format fmt) (match op with | F_MIN => false | F_MAX => true)
                (fread c fmt rs1) (fread c fmt rs2)
    EDone (fwrite fmt rd v (accrue fl cn))
  -- The compares and fclass write an INTEGER register.
  | Fcmp op fmt rd rs1 rs2 =>
    let f := fp_format fmt
    let a := fread c fmt rs1
    let b := fread c fmt rs2
    let (v, fl) :=
      match op with
      | F_EQ => fp_eq f a b
      | F_LT => fp_lt f a b
      | F_LE => fp_le f a b
    EDone (rset rd (if v then w1 else w0) (accrue fl cn))
  | Fclass fmt rd rs1 =>
    EDone (rset rd (Z_to_bv 64 (fp_class (fp_format fmt) (fread c fmt rs1))) cn)
  -- fcvt: (dst, src) picks the direction; the dead combinations are EIllegal.
  | Fcvt dst src rd rs1 rm =>
    match resolve_rm rm cn with
    | none => EIllegal cn
    | some md =>
      let ity (t : fcvt_ty) : Option (Bool × Int) :=
        match t with
        | FC_W => some (true, 32) | FC_WU => some (false, 32)
        | FC_L => some (true, 64) | FC_LU => some (false, 64)
        | _ => none
      let fty (t : fcvt_ty) : Option ffmt :=
        match t with | FC_S => some FMT_S | FC_D => some FMT_D | _ => none
      match fty dst, fty src with
      | some df, some sf =>            -- float -> float
        let (v, fl) :=
          fp_convert (fp_format sf) (fp_format df) md (fread c sf rs1)
        EDone (fwrite df rd v (accrue fl cn))
      | none, some sf =>               -- float -> integer
        match ity dst with
        | none => EIllegal cn
        | some (sgn, bits) =>
          let (v, fl) := fp_to_int (fp_format sf) md sgn bits (fread c sf rs1)
          EDone (rset rd (if bits == 32 then sext 64 (Z_to_bv 32 v)
                          else Z_to_bv 64 v)
                      (accrue fl cn))
      | some df, none =>               -- integer -> float
        match ity src with
        | none => EIllegal cn
        | some (sgn, bits) =>
          let (v, fl) :=
            fp_of_int (fp_format df) md sgn bits (bv_unsigned (rget c rs1))
          EDone (fwrite df rd v (accrue fl cn))
      | none, none => EIllegal cn

/-- Sem.v:699. Fetch, decode, dispatch; an undecodable word is `EIllegal` with pc NOT advanced. -/
def step (decode_any : bv 32 → Option (instr × Int)) (c : core) : eff :=
  ELoad 32 (c_pc c) (fun w32 =>
    match decode_any w32 with
    | some (i, isz) => exec (Z_to_bv 64 isz) i c
    | none => EIllegal c)

end LPS

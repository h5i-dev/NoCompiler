import LPS.Common.PropExec2

/-!
# LPS `theories/Common/PropExec.v` (f1006fe8), part 3: value bridges

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/PropExec.v` at f1006fe8, lines 505-1031: the `bv` expressions `Sem.exec`
produces equal the `v_*` normal forms (ALU, shift amounts, RV64 word ops, M extension, upper
immediates, jalr). Conventions as in `PropExec1.lean`. Added (not in the source): the bit facts
`Nat.and_one_eq_mod`, `Nat.xor_and_one`, `Nat.or_one`, `Z.land_ones6`/`Z.land_ones5`, `Z.land_m2`,
`Z.shiftlZ_nonneg`, `bv_wrap_sub_idemp`, `bv_wrap_mul_idemp` and the literal values of
`bv_half_modulus`/`bv_modulus`, which the Rocq proofs get from Stdlib's `Z` bit library.
-/

namespace LPS
open RiscvSemantics aluop mulop

/-! ## Bit facts on naturals and `Z.land` (local) -/

theorem Nat.and_one_eq_mod (m : Nat) : m &&& 1 = m % 2 := Nat.and_two_pow_sub_one_eq_mod m 1

theorem Nat.xor_and_one (m : Nat) : m ^^^ (m &&& 1) = m - m % 2 := by
  rw [Nat.and_one_eq_mod]
  have h2 : (m ^^^ m % 2) / 2 = m / 2 := by
    rw [Nat.xor_div_two, show m % 2 / 2 = 0 by omega, Nat.xor_zero]
  have h1 : (m ^^^ m % 2) % 2 ≠ 1 := by
    rw [Ne, Nat.xor_mod_two_eq_one]; simp
  omega

theorem Nat.or_one (m : Nat) : m ||| 1 = m - m % 2 + 1 := by
  have hm : m = 2 ^ 1 * (m / 2) ||| m % 2 := by
    rw [← Nat.two_pow_add_eq_or_of_lt (by omega) (m / 2)]; omega
  have h1 : 2 ^ 1 * (m / 2) ||| 1 = 2 ^ 1 * (m / 2) + 1 :=
    (Nat.two_pow_add_eq_or_of_lt (by decide) (m / 2)).symm
  have hr : m % 2 ||| 1 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one m with h | h <;> rw [h] <;> rfl
  rw [hm, Nat.or_assoc, hr, h1, ← hm]; omega

theorem Z.land_ones6 (z : Int) (h : 0 ≤ z) : Z.land z 63 = z % 64 := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
  rw [show (63 : Int) = ((2 ^ 6 - 1 : Nat) : Int) from rfl, Z.land_natCast, Nat.and_two_pow_sub_one_eq_mod]
  push_cast; rfl

theorem Z.land_ones5 (z : Int) (h : 0 ≤ z) : Z.land z 31 = z % 32 := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
  rw [show (31 : Int) = ((2 ^ 5 - 1 : Nat) : Int) from rfl, Z.land_natCast, Nat.and_two_pow_sub_one_eq_mod]
  push_cast; rfl

/-- `Z.land z (-2)` clears bit 0. -/
theorem Z.land_m2 (z : Int) : Z.land z (-2) = z - z % 2 := by
  cases z with
  | ofNat m =>
    show ((m ^^^ (m &&& 1) : Nat) : Int) = (m : Int) - (m : Int) % 2
    rw [Nat.xor_and_one]; push_cast; omega
  | negSucc m =>
    show Int.negSucc (m ||| 1) = _
    rw [Nat.or_one, Int.negSucc_eq]; push_cast; omega

theorem Z.shiftlZ_nonneg (z k : Int) (hk : 0 ≤ k) : Z.shiftlZ z k = z * ((2 ^ k.toNat : Nat) : Int) := by
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  rfl

theorem bv_wrap_sub_idemp (n : Nat) (x y : Int) : bv_wrap n (bv_wrap n x - bv_wrap n y) = bv_wrap n (x - y) := by
  unfold bv_wrap; rw [Int.sub_emod (x % _), Int.emod_emod, Int.emod_emod, ← Int.sub_emod]

theorem bv_wrap_mul_idemp (n : Nat) (x y : Int) : bv_wrap n (bv_wrap n x * bv_wrap n y) = bv_wrap n (x * y) := by
  unfold bv_wrap; rw [Int.mul_emod (x % _), Int.emod_emod, Int.emod_emod, ← Int.mul_emod]

theorem bv_wrap_mul_idemp_l (n : Nat) (x y : Int) : bv_wrap n (bv_wrap n x * y) = bv_wrap n (x * y) := by
  unfold bv_wrap; rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]

theorem bv_half_modulus_64 : bv_half_modulus 64 = 2 ^ 63 := by decide
theorem bv_half_modulus_32 : bv_half_modulus 32 = 2 ^ 31 := by decide
theorem bv_half_modulus_20 : bv_half_modulus 20 = 2 ^ 19 := by decide
theorem bv_half_modulus_12 : bv_half_modulus 12 = 2 ^ 11 := by decide
theorem bv_modulus_64 : bv_modulus 64 = 2 ^ 64 := rfl
theorem bv_modulus_32 : bv_modulus 32 = 2 ^ 32 := rfl
theorem bv_modulus_20 : bv_modulus 20 = 2 ^ 20 := rfl

/-! ## Value bridges (PropExec.v:505-618) -/

theorem b_addsext (a : word) {n : Nat} (imm : bv n) : a + sext 64 imm = v_addi a (bv_signed imm) := by
  apply bv_eq; unfold v_addi sext
  rw [bv_add_unsigned, bv_sign_extend_unsigned, Z_to_bv_unsigned, bv_wrap_add_idemp_r]

theorem b_npc4 (p : word) : p + Z_to_bv 64 4 = v_addi p 4 := by
  apply bv_eq; unfold v_addi
  rw [bv_add_unsigned, Z_to_bv_unsigned, Z_to_bv_unsigned, bv_wrap_add_idemp_r]

theorem alu_addi (a : word) {n : Nat} (imm : bv n) : alu64 ALU_ADD a (sext 64 imm) = v_addi a (bv_signed imm) :=
  b_addsext a imm

theorem alu_andi (a : word) {n : Nat} (imm : bv n) : alu64 ALU_AND a (sext 64 imm) = v_andi a (bv_signed imm) := by
  show Z_to_bv 64 (Z.land (bv_unsigned a) (bv_unsigned (sext 64 imm))) = _
  rw [sext, bv_sign_extend_unsigned]; rfl

theorem alu_ori (a : word) {n : Nat} (imm : bv n) : alu64 ALU_OR a (sext 64 imm) = v_ori a (bv_signed imm) := by
  show Z_to_bv 64 (Z.lor (bv_unsigned a) (bv_unsigned (sext 64 imm))) = _
  rw [sext, bv_sign_extend_unsigned]; rfl

theorem alu_xori (a : word) {n : Nat} (imm : bv n) : alu64 ALU_XOR a (sext 64 imm) = v_xori a (bv_signed imm) := by
  show Z_to_bv 64 (Z.lxor (bv_unsigned a) (bv_unsigned (sext 64 imm))) = _
  rw [sext, bv_sign_extend_unsigned]; rfl

theorem alu_slti (a : word) (imm : bv 12) : alu64 ALU_SLT a (sext 64 imm) = v_slti a (bv_signed imm) := by
  show (if bv_lts a (sext 64 imm) then Z_to_bv 64 1 else Z_to_bv 64 0) = _
  unfold bv_lts v_slti zsig sext
  rw [bv_sign_extend_signed 64 imm (by decide) (by decide)]

theorem alu_sltiu (a : word) {n : Nat} (imm : bv n) : alu64 ALU_SLTU a (sext 64 imm) = v_sltiu a (bv_signed imm) := by
  show (if bv_ltu a (sext 64 imm) then Z_to_bv 64 1 else Z_to_bv 64 0) = _
  unfold bv_ltu v_sltiu sext
  rw [bv_sign_extend_unsigned]

theorem alu_add (a b : word) : alu64 ALU_ADD a b = v_add a b := by
  apply bv_eq; show bv_unsigned (a + b) = _; unfold v_add; rw [bv_add_unsigned, Z_to_bv_unsigned]

theorem alu_sub (a b : word) : alu64 ALU_SUB a b = v_sub a b := by
  apply bv_eq; show bv_unsigned (a - b) = _; unfold v_sub; rw [bv_sub_unsigned, Z_to_bv_unsigned]

theorem alu_slt (a b : word) : alu64 ALU_SLT a b = v_slt a b := rfl
theorem alu_sltu (a b : word) : alu64 ALU_SLTU a b = v_sltu a b := rfl
theorem alu_and (a b : word) : alu64 ALU_AND a b = v_and a b := rfl
theorem alu_or (a b : word) : alu64 ALU_OR a b = v_or a b := rfl
theorem alu_xor (a b : word) : alu64 ALU_XOR a b = v_xor a b := rfl

/-! ## Shift amount views (PropExec.v:620-698) -/

theorem shamt6_mask (s : bv 6) : bv_unsigned (bv_and (zext 64 s) (Z_to_bv 64 63)) = bv_unsigned s := by
  have Hs := u6_range s
  unfold bv_and zext
  rw [bv_zero_extend_unsigned 64 s (by decide), Z_to_bv_small 64 63 (by decide) (by decide),
    Z.land_ones6 _ Hs.1, Int.emod_eq_of_lt Hs.1 Hs.2]
  exact Z_to_bv_small 64 _ Hs.1 (by rw [bv_modulus_64]; omega)

theorem regamt64_mask (b : word) : bv_unsigned (bv_and b (Z_to_bv 64 63)) = Z.modulo (bv_unsigned b) 64 := by
  have Hb := u64_range b
  unfold bv_and
  rw [Z_to_bv_small 64 63 (by decide) (by decide), Z.land_ones6 _ Hb.1, Z.modulo,
    Int.fmod_eq_emod_of_nonneg _ (by decide)]
  exact Z_to_bv_small 64 _ (by omega) (by rw [bv_modulus_64]; omega)

theorem alu_slli (a : word) (s : bv 6) : alu64 ALU_SLL a (zext 64 s) = v_slli a (bv_unsigned s) := by
  show Z_to_bv 64 (Z.shiftlZ (bv_unsigned a) (bv_unsigned (bv_and (zext 64 s) (Z_to_bv 64 63)))) = _
  rw [shamt6_mask]; rfl

theorem alu_srli (a : word) (s : bv 6) : alu64 ALU_SRL a (zext 64 s) = v_srli a (bv_unsigned s) := by
  show Z_to_bv 64 (Z.shiftrZ (bv_unsigned a) (bv_unsigned (bv_and (zext 64 s) (Z_to_bv 64 63)))) = _
  rw [shamt6_mask]; rfl

theorem alu_srai (a : word) (s : bv 6) : alu64 ALU_SRA a (zext 64 s) = v_srai a (bv_unsigned s) := by
  show Z_to_bv 64 (Z.shiftrZ (bv_signed a) (bv_unsigned (bv_and (zext 64 s) (Z_to_bv 64 63)))) = _
  rw [shamt6_mask]; rfl

theorem alu_sll (a b : word) : alu64 ALU_SLL a b = v_sll a b := by
  show Z_to_bv 64 (Z.shiftlZ (bv_unsigned a) (bv_unsigned (bv_and b (Z_to_bv 64 63)))) = _
  rw [regamt64_mask]; rfl

theorem alu_srl (a b : word) : alu64 ALU_SRL a b = v_srl a b := by
  show Z_to_bv 64 (Z.shiftrZ (bv_unsigned a) (bv_unsigned (bv_and b (Z_to_bv 64 63)))) = _
  rw [regamt64_mask]; rfl

theorem alu_sra (a b : word) : alu64 ALU_SRA a b = v_sra a b := by
  show Z_to_bv 64 (Z.shiftrZ (bv_signed a) (bv_unsigned (bv_and b (Z_to_bv 64 63)))) = _
  rw [regamt64_mask]; rfl

/-! ## W-op (32-bit) bridges (PropExec.v:700-857) -/

theorem low32_unsigned (a : word) : bv_unsigned (low32 a) = bv_wrap 32 (bv_unsigned a) :=
  bv_extract0_unsigned 32 a

theorem low32_signed (a : word) : bv_signed (low32 a) = bv_swrap 32 (bv_unsigned a) :=
  bv_extract0_signed 32 a

/-- The 32-bit shift amount views. -/
theorem shamt5_mask (s : bv 5) : bv_unsigned (bv_and (zext 32 s) (Z_to_bv 32 31)) = bv_unsigned s := by
  have Hs := u5_range s
  unfold bv_and zext
  rw [bv_zero_extend_unsigned 32 s (by decide), Z_to_bv_small 32 31 (by decide) (by decide),
    Z.land_ones5 _ Hs.1, Int.emod_eq_of_lt Hs.1 Hs.2]
  exact Z_to_bv_small 32 _ Hs.1 (by rw [bv_modulus_32]; omega)

theorem regamt32_mask (b : word) : bv_unsigned (bv_and (low32 b) (Z_to_bv 32 31)) = Z.modulo (bv_unsigned b) 32 := by
  have Hb := u64_range b
  unfold bv_and
  rw [Z_to_bv_small 32 31 (by decide) (by decide), low32_unsigned, bv_wrap32_mod,
    Z.land_ones5 _ (by omega), Z.modulo, Int.fmod_eq_emod_of_nonneg _ (by decide)]
  rw [Z_to_bv_small 32 _ (by omega) (by rw [bv_modulus_32]; omega)]
  omega

/-- sign extension of a 32-bit result, at the unsigned level -/
theorem sext32_unsigned (v : bv 32) : bv_unsigned (sext 64 v) = bv_wrap 64 (bv_swrap 32 (bv_unsigned v)) := by
  unfold sext; rw [bv_sign_extend_unsigned, bv_signed_swrap]

theorem w_addiw (a : word) (imm : bv 12) :
    sext 64 (alu32 ALU_ADD (low32 a) (sext 32 imm)) = v_addiw a (bv_signed imm) := by
  unfold sext bv_sign_extend v_addiw; apply congrArg (Z_to_bv 64)
  show bv_signed (low32 a + sext 32 imm) = _
  rw [bv_signed_swrap, bv_add_unsigned, low32_unsigned, sext, bv_sign_extend_unsigned, bv_swrap_wrap',
    bv_swrap_add_idemp_l, bv_swrap_add_idemp_r]

theorem w_slliw (a : word) (s : bv 5) :
    sext 64 (alu32 ALU_SLL (low32 a) (zext 32 s)) = v_slliw a (bv_unsigned s) := by
  unfold sext bv_sign_extend v_slliw; apply congrArg (Z_to_bv 64)
  show bv_signed (Z_to_bv 32 (Z.shiftlZ (bv_unsigned (low32 a)) (bv_unsigned (bv_and (zext 32 s) (Z_to_bv 32 31)))))
    = _
  rw [bv_signed_Z_to_bv, shamt5_mask, low32_unsigned]
  apply bv_swrap_congr
  have Hs := (u5_range s).1
  rw [Z.shiftlZ_nonneg _ _ Hs, Z.shiftlZ_nonneg _ _ Hs, bv_wrap_mul_idemp_l]

theorem w_srliw (a : word) (s : bv 5) :
    sext 64 (alu32 ALU_SRL (low32 a) (zext 32 s)) = v_srliw a (bv_unsigned s) := by
  unfold sext bv_sign_extend v_srliw; apply congrArg (Z_to_bv 64)
  show bv_signed (Z_to_bv 32 (Z.shiftrZ (bv_unsigned (low32 a)) (bv_unsigned (bv_and (zext 32 s) (Z_to_bv 32 31)))))
    = _
  rw [bv_signed_Z_to_bv, shamt5_mask, low32_unsigned]

theorem w_sraiw (a : word) (s : bv 5) :
    sext 64 (alu32 ALU_SRA (low32 a) (zext 32 s)) = v_sraiw a (bv_unsigned s) := by
  unfold sext bv_sign_extend v_sraiw; apply congrArg (Z_to_bv 64)
  show bv_signed (Z_to_bv 32 (Z.shiftrZ (bv_signed (low32 a)) (bv_unsigned (bv_and (zext 32 s) (Z_to_bv 32 31)))))
    = _
  rw [bv_signed_Z_to_bv, shamt5_mask, low32_signed]

theorem w_addw (a b : word) : sext 64 (alu32 ALU_ADD (low32 a) (low32 b)) = v_addw a b := by
  unfold sext bv_sign_extend v_addw; apply congrArg (Z_to_bv 64)
  show bv_signed (low32 a + low32 b) = _
  rw [bv_signed_swrap, bv_add_unsigned, low32_unsigned, low32_unsigned, bv_swrap_wrap', bv_swrap_add_idemp_l,
    bv_swrap_add_idemp_r]

theorem w_subw (a b : word) : sext 64 (alu32 ALU_SUB (low32 a) (low32 b)) = v_subw a b := by
  unfold sext bv_sign_extend v_subw; apply congrArg (Z_to_bv 64)
  show bv_signed (low32 a - low32 b) = _
  rw [bv_signed_swrap, bv_sub_unsigned, low32_unsigned, low32_unsigned, bv_swrap_wrap']
  exact bv_swrap_congr _ _ _ (bv_wrap_sub_idemp _ _ _)

theorem w_sllw (a b : word) : sext 64 (alu32 ALU_SLL (low32 a) (low32 b)) = v_sllw a b := by
  unfold sext bv_sign_extend v_sllw; apply congrArg (Z_to_bv 64)
  show bv_signed (Z_to_bv 32 (Z.shiftlZ (bv_unsigned (low32 a)) (bv_unsigned (bv_and (low32 b) (Z_to_bv 32 31)))))
    = _
  rw [bv_signed_Z_to_bv, regamt32_mask, low32_unsigned]
  apply bv_swrap_congr
  have Hs : 0 ≤ Z.modulo (bv_unsigned b) 32 := by
    rw [Z.modulo, Int.fmod_eq_emod_of_nonneg _ (by decide)]; exact Int.emod_nonneg _ (by decide)
  rw [Z.shiftlZ_nonneg _ _ Hs, Z.shiftlZ_nonneg _ _ Hs, bv_wrap_mul_idemp_l]

theorem w_srlw (a b : word) : sext 64 (alu32 ALU_SRL (low32 a) (low32 b)) = v_srlw a b := by
  unfold sext bv_sign_extend v_srlw; apply congrArg (Z_to_bv 64)
  show bv_signed (Z_to_bv 32 (Z.shiftrZ (bv_unsigned (low32 a)) (bv_unsigned (bv_and (low32 b) (Z_to_bv 32 31)))))
    = _
  rw [bv_signed_Z_to_bv, regamt32_mask, low32_unsigned]

theorem w_sraw (a b : word) : sext 64 (alu32 ALU_SRA (low32 a) (low32 b)) = v_sraw a b := by
  unfold sext bv_sign_extend v_sraw; apply congrArg (Z_to_bv 64)
  show bv_signed (Z_to_bv 32 (Z.shiftrZ (bv_signed (low32 a)) (bv_unsigned (bv_and (low32 b) (Z_to_bv 32 31)))))
    = _
  rw [bv_signed_Z_to_bv, regamt32_mask, low32_signed]

/-! ## M-extension bridges (PropExec.v:859-946) -/

theorem m_mul (a b : word) : mul_div M_MUL a b = v_mul a b := by
  apply bv_eq; show bv_unsigned (a * b) = _; unfold v_mul; rw [bv_mul_unsigned, Z_to_bv_unsigned]

theorem m_mulh (a b : word) : mul_div M_MULH a b = v_mulh a b := rfl
theorem m_mulhsu (a b : word) : mul_div M_MULHSU a b = v_mulhsu a b := rfl
theorem m_mulhu (a b : word) : mul_div M_MULHU a b = v_mulhu a b := rfl
theorem m_div (a b : word) : mul_div M_DIV a b = v_div a b := rfl
theorem m_rem (a b : word) : mul_div M_REM a b = v_rem a b := rfl

theorem w_mulw (a b : word) : sext 64 (mul_div M_MUL (low32 a) (low32 b)) = v_mulw a b := by
  unfold sext bv_sign_extend v_mulw; apply congrArg (Z_to_bv 64)
  show bv_signed (low32 a * low32 b) = _
  rw [bv_signed_swrap, bv_mul_unsigned, low32_unsigned, low32_unsigned, bv_swrap_wrap']
  exact bv_swrap_congr _ _ _ (bv_wrap_mul_idemp _ _ _)

/-- the div0 scrutinee of the 32-bit division family -/
theorem div0_32 (b : word) : (bv_unsigned (low32 b) == 0) = (bv_wrap 32 (bv_unsigned b) == 0) := by
  rw [low32_unsigned]

theorem sext_m1_32 : sext 64 (Z_to_bv 32 (-1)) = Z_to_bv 64 (-1) := by
  unfold sext bv_sign_extend
  rw [bv_signed_Z_to_bv, bv_swrap_small 32 (-1) (by rw [bv_half_modulus_32]; decide)
    (by rw [bv_half_modulus_32]; decide)]

theorem w_divw (a b : word) : sext 64 (mul_div M_DIV (low32 a) (low32 b)) = v_divw a b := by
  simp only [mul_div, v_divw, div0_32]
  split
  · exact sext_m1_32
  · unfold sext bv_sign_extend bv_quots
    rw [bv_signed_Z_to_bv, low32_signed, low32_signed]

theorem w_remw (a b : word) : sext 64 (mul_div M_REM (low32 a) (low32 b)) = v_remw a b := by
  simp only [mul_div, v_remw, div0_32]
  split
  · unfold sext bv_sign_extend; rw [low32_signed]
  · unfold sext bv_sign_extend bv_rems
    rw [bv_signed_Z_to_bv, low32_signed, low32_signed]

theorem w_divuw (a b : word) : sext 64 (mul_div M_DIVU (low32 a) (low32 b)) = v_divuw a b := by
  simp only [mul_div, v_divuw, div0_32]
  split
  · exact sext_m1_32
  · unfold sext bv_sign_extend bv_divu
    rw [bv_signed_Z_to_bv, low32_unsigned, low32_unsigned]

theorem w_remuw (a b : word) : sext 64 (mul_div M_REMU (low32 a) (low32 b)) = v_remuw a b := by
  simp only [mul_div, v_remuw, div0_32]
  split
  · unfold sext bv_sign_extend; rw [low32_signed]
  · unfold sext bv_sign_extend bv_modu
    rw [bv_signed_Z_to_bv, low32_unsigned, low32_unsigned]

/-! ## Upper-immediate and jalr bridges (PropExec.v:948-1029) -/

theorem bv_swrap_hi (n : Nat) (z : Int) (Hn : n ≠ 0) (Hlo : bv_half_modulus n ≤ z) (Hhi : z < bv_modulus n) :
    bv_swrap n z = z - bv_modulus n := by
  have Htw := bv_half_modulus_twice n Hn
  unfold bv_swrap
  rw [bv_wrap_eq, show z + bv_half_modulus n = (z + bv_half_modulus n - bv_modulus n) + bv_modulus n * 1 by omega,
    Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
  omega

theorem b_lui (imm : bv 20) :
    sext 64 (bv_concat 32 imm (Z_to_bv 12 0)) = v_lui (Z.shiftl (bv_signed imm) 12) := by
  unfold sext bv_sign_extend v_lui bv_concat; apply congrArg (Z_to_bv 64)
  rw [bv_signed_Z_to_bv, Z_to_bv_small 12 0 (by decide) (by decide), Z.lor_0_r, bv_signed_swrap]
  have Hr := bv_unsigned_range imm
  rw [bv_modulus_20] at Hr
  unfold Z.shiftl
  have e : ((2 ^ 12 : Nat) : Int) = 4096 := rfl
  rw [e]
  by_cases Hlt : bv_unsigned imm < 2 ^ 19
  · rw [bv_swrap_small 32 _ (by rw [bv_half_modulus_32]; omega) (by rw [bv_half_modulus_32]; omega),
      bv_swrap_small 20 _ (by rw [bv_half_modulus_20]; omega) (by rw [bv_half_modulus_20]; omega)]
  · rw [bv_swrap_hi 32 _ (by decide) (by rw [bv_half_modulus_32]; omega) (by rw [bv_modulus_32]; omega),
      bv_swrap_hi 20 _ (by decide) (by rw [bv_half_modulus_20]; omega) (by rw [bv_modulus_20]; omega),
      bv_modulus_32, bv_modulus_20]
    omega

theorem b_auipc (p : word) (imm : bv 20) :
    p + sext 64 (bv_concat 32 imm (Z_to_bv 12 0)) = v_auipc p (Z.shiftl (bv_signed imm) 12) := by
  rw [b_lui]; apply bv_eq; unfold v_lui v_auipc
  rw [bv_add_unsigned, Z_to_bv_unsigned, Z_to_bv_unsigned, bv_wrap_add_idemp_r, Int.add_comm]

theorem Z_land_m2_wrap (z : Int) : Z.land (bv_wrap 64 z) (bv_wrap 64 (-2)) = bv_wrap 64 (Z.land z (-2)) := by
  rw [bv_wrap64_mod, bv_wrap64_mod, bv_wrap64_mod, Z.land_m2,
    show (-2 : Int) % 2 ^ 64 = ((2 ^ 64 - 2 : Nat) : Int) by decide]
  have H := Int.emod_nonneg z (show (2 : Int) ^ 64 ≠ 0 by decide)
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le H
  rw [hm, Z.land_natCast]
  have hlt : m < 2 ^ 64 := by have := Int.emod_lt_of_pos z (show (0 : Int) < 2 ^ 64 by decide); omega
  have key : m &&& (2 ^ 64 - 2) = m - m % 2 := by
    rw [show 2 ^ 64 - 2 = 2 ^ 1 * (2 ^ 63 - 1) from rfl]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and]
    cases i with
    | zero =>
      simp only [Nat.testBit_zero, Nat.mul_mod_right, Nat.zero_ne_one, decide_false, Bool.and_false]
      simp; omega
    | succ i =>
      rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
        show 2 ^ 1 * (2 ^ 63 - 1) / 2 = 2 ^ 63 - 1 from rfl, Nat.testBit_two_pow_sub_one,
        show (m - m % 2) / 2 = m / 2 by omega]
      by_cases hi : i < 63
      · simp [hi]
      · simp only [hi, decide_false, Bool.and_false]
        exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by omega : m / 2 < 2 ^ 63)
          (Nat.pow_le_pow_right (by decide) (by omega)))).symm
  rw [key]; push_cast; omega

theorem b_jalr (a : word) (imm : bv 12) :
    bv_and (a + sext 64 imm) (bv_not (Z_to_bv 64 1)) = jalr_tgt a (bv_signed imm) := by
  rw [b_addsext]
  unfold bv_and bv_not jalr_tgt jalr_tgtZ v_addi
  rw [Z_to_bv_unsigned, Z_to_bv_unsigned, Z_to_bv_small 64 1 (by decide) (by decide),
    show Z.lnot 1 = -2 from rfl, Z_land_m2_wrap, Z_to_bv_wrap]

end LPS

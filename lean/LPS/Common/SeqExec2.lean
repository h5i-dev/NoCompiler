import LPS.Common.SeqExec1

/-!
# LPS `theories/Common/SeqExec.v` (f1006fe8), part 2: M extension, narrow stores, `rdn` composition

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/SeqExec.v` at f1006fe8, SeqExec.v:590-1072 (`Section WithFP4`): `v_divu`/`v_remu`
and their bridges and step lemmas, `step_lw_zero`, the byte store `step_sb`/`step_sb256`, the
narrow-store byte identities (`Zmod_pow2_div8`, `Z_to_le_bytes_wrap`, `store_bytes_low16`/`low32`),
`step_sw_val`/`_at`, `step_sh_val`/`_at`, the value simplifications (`v_divu_small`, `v_remu_small`,
`v_subw_small`, `land_d48`, `lor_small_add`, `v_ori_lor`, `v_addi_m`) and the generic `rdn`
composition/extraction lemmas (`rdn_app`, `rdn_nth`, `rdn_skipn`, `rdn_firstn`).

Conventions as SeqExec1. Rocq's `/`, `mod` on `Z` are `Z.div`, `Z.modulo`; `2 ^ m` with a `Z`
exponent is `Z.pow 2 m` (`Zmod_pow2_div8`); `(8 * Z.of_nat n <= Z.of_N m)` is over `Int` with `m : Nat`.
Lean-only helpers: `bv_wrap_bv_wrap` (stdpp's, `n ≤ m`) and `emod_mul_ediv256` (the `Int` division
identity behind `Zmod_pow2_div8`, which the Rocq proof gets bitwise).
-/

namespace LPS
open RiscvSemantics instr aluop mulop branch_cond msize core

/-! ### M extension -/

def v_divu (x y : word) : word := Z_to_bv 64 (Z.div (bv_unsigned x) (bv_unsigned y))
def v_remu (x y : word) : word := Z_to_bv 64 (Z.modulo (bv_unsigned x) (bv_unsigned y))

/-- `Sem.mul_div M_DIVU` agrees with `v_divu` away from the divide-by-zero case. -/
theorem m_divu : ∀ a b : word, bv_unsigned b ≠ 0 → mul_div M_DIVU a b = v_divu a b := by
  intro a b Hb
  simp only [mul_div, beq_iff_eq, Hb, ↓reduceIte]
  rfl

theorem m_remu : ∀ a b : word, bv_unsigned b ≠ 0 → mul_div M_REMU a b = v_remu a b := by
  intro a b Hb
  simp only [mul_div, beq_iff_eq, Hb, ↓reduceIte]
  rfl

theorem step_divu [FPState] : ∀ segs regs pc mem rom w (rd rs1 rs2 : reg),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (instr.Mul M_DIVU rd rs1 rs2, 4) →
    bv_unsigned (getr regs rs2) ≠ 0 →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_divu (getr regs rs1) (getr regs rs2)))
      (v_addi pc 4) mem rom) := by
  intro segs regs pc mem rom w rd rs1 rs2 Hf He Hd Hnz
  rw [step_mul_gen segs regs pc mem rom w _ rd rs1 rs2 Hf He Hd, m_divu _ _ Hnz]

theorem step_remu [FPState] : ∀ segs regs pc mem rom w (rd rs1 rs2 : reg),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (instr.Mul M_REMU rd rs1 rs2, 4) →
    bv_unsigned (getr regs rs2) ≠ 0 →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_remu (getr regs rs1) (getr regs rs2)))
      (v_addi pc 4) mem rom) := by
  intro segs regs pc mem rom w rd rs1 rs2 Hf He Hd Hnz
  rw [step_mul_gen segs regs pc mem rom w _ rd rs1 rs2 Hf He Hd, m_remu _ _ Hnz]

theorem step_lw_zero [FPState] : ∀ segs regs pc mem rom w (rd rs : reg) (imm : bv 12),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Load SZ4 true rd rs imm, 4) →
    bv_eqb rd 0 = false →
    rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4
      = some [Z_to_bv 8 0, Z_to_bv 8 0, Z_to_bv 8 0, Z_to_bv 8 0] →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4) mem rom) := by
  intro segs regs pc mem rom w rd rs imm Hf He Hd Hrd Hr
  have Hval : v_lw (Z_to_bv 64 0) = Z_to_bv 64 0 := by decide
  rw [step_lw segs regs pc mem rom w rd rs imm _ (Z_to_bv 64 0) Hf He Hd Hr rfl, Hrd, Hval]
  rfl

/-! ### Narrow-store byte identities -/

/-- stdpp's `bv_wrap_bv_wrap` (for `n ≤ m`). -/
theorem bv_wrap_bv_wrap (n m : Nat) (z : Int) (h : n ≤ m) : bv_wrap n (bv_wrap m z) = bv_wrap n z := by
  unfold bv_wrap
  apply Int.emod_emod_of_dvd
  exact Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 h)

/-- `(z mod 256 N) / 256 = (z / 256) mod N`. -/
theorem emod_mul_ediv256 (z N : Int) (hN : 0 < N) : z % (256 * N) / 256 = z / 256 % N := by
  have hq := Int.emod_add_mul_ediv (z / 256) N
  have hz := Int.emod_add_mul_ediv z 256
  have h0 := Int.emod_nonneg z (by decide : (256 : Int) ≠ 0)
  have h1 := Int.emod_lt_of_pos z (by decide : (0 : Int) < 256)
  have h2 := Int.emod_nonneg (z / 256) (Int.ne_of_gt hN)
  have h3 := Int.emod_lt_of_pos (z / 256) hN
  have hm : z % (256 * N) = z % 256 + 256 * (z / 256 % N) := by
    have := (Int.ediv_emod_unique (a := z) (b := 256 * N) (r := z % 256 + 256 * (z / 256 % N))
      (q := z / 256 / N) (by omega)).2 ⟨by rw [Int.mul_assoc]; omega, by omega, by omega⟩
    exact this.2
  rw [hm]
  exact ((Int.ediv_emod_unique (by decide : (0 : Int) < 256)).2 ⟨by omega, h0, h1⟩).1

theorem Zmod_pow2_div8 : ∀ z m : Int, 8 ≤ m →
    Z.div (Z.modulo z (Z.pow 2 m)) (2 ^ 8) = Z.modulo (Z.div z (2 ^ 8)) (Z.pow 2 (m - 8)) := by
  intro z m Hm
  obtain ⟨k, rfl⟩ : ∃ k : Nat, m = (k : Int) + 8 := ⟨(m - 8).toNat, by omega⟩
  have hp1 : Z.pow 2 ((k : Int) + 8) = 256 * 2 ^ k := by
    unfold Z.pow
    simp only [show ¬ ((k : Int) + 8 < 0) by omega, ↓reduceIte]
    rw [show ((k : Int) + 8).toNat = k + 8 by omega, Int.pow_add, Int.mul_comm]; rfl
  have hp2 : Z.pow 2 ((k : Int) + 8 - 8) = 2 ^ k := by
    unfold Z.pow; simp only [show ¬ ((k : Int) + 8 - 8 < 0) by omega, ↓reduceIte]
    rw [show ((k : Int) + 8 - 8).toNat = k by omega]
  have hpos : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
  rw [hp1, hp2]
  unfold Z.div Z.modulo
  rw [Int.fmod_eq_emod_of_nonneg _ (by omega), Int.fdiv_eq_ediv_of_nonneg _ (by decide),
    Int.fdiv_eq_ediv_of_nonneg _ (by decide), Int.fmod_eq_emod_of_nonneg _ (by omega)]
  exact emod_mul_ediv256 z _ hpos

theorem Z_to_le_bytes_wrap : ∀ (n m : Nat) (z : Int), 8 * (n : Int) ≤ (m : Int) →
    Z_to_le_bytes n (bv_wrap m z) = Z_to_le_bytes n z := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro m z Hm
    simp only [Z_to_le_bytes]
    congr 1
    · apply bv_eq
      rw [Z_to_bv_unsigned, Z_to_bv_unsigned, bv_wrap_bv_wrap 8 m z (by omega)]
    · obtain ⟨k, rfl⟩ : ∃ k : Nat, m = k + 8 := ⟨m - 8, by omega⟩
      have hsh : ∀ x : Int, Z.shiftr x 8 = x / 256 := by
        intro x; unfold Z.shiftr; rw [Int.shiftRight_eq_div_pow]; rfl
      have hw : Z.shiftr (bv_wrap (k + 8) z) 8 = bv_wrap k (Z.shiftr z 8) := by
        rw [hsh, hsh]; unfold bv_wrap
        rw [show ((2 ^ (k + 8) : Nat) : Int) = 256 * ((2 ^ k : Nat) : Int) by push_cast; rw [Int.pow_add, Int.mul_comm]; rfl]
        exact emod_mul_ediv256 z _ (Int.natCast_pos.mpr (Nat.two_pow_pos k))
      rw [hw]
      exact ih k _ (by push_cast at Hm ⊢; omega)

/-- The `sh` store value: 2 bytes of the 16-bit truncation are the 2 bytes of the full word. -/
theorem store_bytes_low16 : ∀ u : word, Z_to_le_bytes 2 (bv_unsigned (bv_extract 0 16 u)) = word_to_le_bytes 2 u := by
  intro u
  unfold word_to_le_bytes
  rw [bv_extract0_unsigned]
  exact Z_to_le_bytes_wrap 2 16 _ (by decide)

/-- The `sw` store value: 4 bytes of `low32` are the 4 bytes of the full word. -/
theorem store_bytes_low32 : ∀ u : word, Z_to_le_bytes 4 (bv_unsigned (low32 u)) = word_to_le_bytes 4 u := by
  intro u
  unfold low32 word_to_le_bytes
  rw [bv_extract0_unsigned]
  exact Z_to_le_bytes_wrap 4 32 _ (by decide)

/-! ### Byte, word and halfword stores -/

/-- Store byte: the stored list is the exact single little-endian byte of rs2. -/
theorem step_sb [FPState] : ∀ segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Store SZ1 rs1 rs2 imm, 4) →
    RiscvSemantics.store_ok segs mem (v_addi (getr regs rs1) (bv_signed imm)) 1 = true →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst regs (v_addi pc 4)
      (wbytes mem (v_addi (getr regs rs1) (bv_signed imm)) (word_to_le_bytes 1 (getr regs rs2))) rom) := by
  intro segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok
  have Hsb : ∀ u : word, Z_to_le_bytes 1 (bv_unsigned (bv_extract 0 8 u)) = word_to_le_bytes 1 u := by
    intro u; unfold word_to_le_bytes; rw [bv_extract0_unsigned]; exact Z_to_le_bytes_wrap 1 8 _ (by decide)
  simp only [RiscvSemantics.step, step_accesses, ms_pc, mkst, decode_exec_accesses, exec,
    drop_access_report, rget_getr, with_pc, b_npc4, b_addsext, Bool.false_eq_true,
    ↓reduceIte, Hfetch, Hecall, Hdecode]
  simp only [store_val, interp_eff_accesses, width_bytes, Hok, ↓reduceIte, write_to_mem_wbytes, Hsb]
  rfl

/-- `Sb` with any stored byte value: identical to `step_sb`. -/
theorem step_sb256 [FPState] : ∀ segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Store SZ1 rs1 rs2 imm, 4) →
    RiscvSemantics.store_ok segs mem (v_addi (getr regs rs1) (bv_signed imm)) 1 = true →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst regs (v_addi pc 4)
      (wbytes mem (v_addi (getr regs rs1) (bv_signed imm)) (word_to_le_bytes 1 (getr regs rs2))) rom) :=
  step_sb

/-- Collapse the singleton `word_to_le_bytes` list to the literal byte. -/
theorem N_to_le_bytes_1_small : ∀ v : word, word_to_le_bytes 1 v = [Z_to_bv 8 (bv_unsigned v)] := fun _ => rfl

/-- Store word, stored VALUE exposed. -/
theorem step_sw_val [FPState] : ∀ segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Store SZ4 rs1 rs2 imm, 4) →
    RiscvSemantics.store_ok segs mem (v_addi (getr regs rs1) (bv_signed imm)) 4 = true →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst regs (v_addi pc 4)
      (wbytes mem (v_addi (getr regs rs1) (bv_signed imm)) (word_to_le_bytes 4 (getr regs rs2))) rom) := by
  intro segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok
  simp only [RiscvSemantics.step, step_accesses, ms_pc, mkst, decode_exec_accesses, exec,
    drop_access_report, rget_getr, with_pc, b_npc4, b_addsext, Bool.false_eq_true,
    ↓reduceIte, Hfetch, Hecall, Hdecode]
  simp only [store_val, interp_eff_accesses, width_bytes, Hok, ↓reduceIte, write_to_mem_wbytes,
    store_bytes_low32]
  rfl

theorem step_sw_at [FPState] : ∀ segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Store SZ4 rs1 rs2 imm, 4) →
    v_addi (getr regs rs1) (bv_signed imm) = a →
    getr regs rs2 = v →
    RiscvSemantics.store_ok segs mem a 4 = true →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 4 v)) rom) := by
  intro segs regs pc mem rom w rs1 rs2 imm a v Hf He Hd Ha Hv Hok
  rw [step_sw_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd (by rw [Ha]; exact Hok), Ha, Hv]

/-- Store halfword, stored VALUE exposed. -/
theorem step_sh_val [FPState] : ∀ segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Store SZ2 rs1 rs2 imm, 4) →
    RiscvSemantics.store_ok segs mem (v_addi (getr regs rs1) (bv_signed imm)) 2 = true →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst regs (v_addi pc 4)
      (wbytes mem (v_addi (getr regs rs1) (bv_signed imm)) (word_to_le_bytes 2 (getr regs rs2))) rom) := by
  intro segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok
  simp only [RiscvSemantics.step, step_accesses, ms_pc, mkst, decode_exec_accesses, exec,
    drop_access_report, rget_getr, with_pc, b_npc4, b_addsext, Bool.false_eq_true,
    ↓reduceIte, Hfetch, Hecall, Hdecode]
  simp only [store_val, interp_eff_accesses, width_bytes, Hok, ↓reduceIte, write_to_mem_wbytes,
    store_bytes_low16]
  rfl

theorem step_sh_at [FPState] : ∀ segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Store SZ2 rs1 rs2 imm, 4) →
    v_addi (getr regs rs1) (bv_signed imm) = a →
    getr regs rs2 = v →
    RiscvSemantics.store_ok segs mem a 2 = true →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 2 v)) rom) := by
  intro segs regs pc mem rom w rs1 rs2 imm a v Hf He Hd Ha Hv Hok
  rw [step_sh_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd (by rw [Ha]; exact Hok), Ha, Hv]

/-! ### Value simplification -/

theorem v_divu_small : ∀ x y : word, 0 < bv_unsigned y →
    bv_unsigned (v_divu x y) = Z.div (bv_unsigned x) (bv_unsigned y) := by
  intro x y Hy
  have hx := u64_range x
  unfold v_divu Z.div
  rw [Z_to_bv_unsigned, Int.fdiv_eq_ediv_of_nonneg _ (by omega)]
  apply bv_wrap_small
  · exact Int.ediv_nonneg hx.1 (by omega)
  · rw [bv_modulus_64]
    exact Int.lt_of_le_of_lt (Int.ediv_le_self _ hx.1) hx.2

theorem v_remu_small : ∀ x y : word, 0 < bv_unsigned y →
    bv_unsigned (v_remu x y) = Z.modulo (bv_unsigned x) (bv_unsigned y) := by
  intro x y Hy
  have hy := u64_range y
  unfold v_remu Z.modulo
  rw [Z_to_bv_unsigned, Int.fmod_eq_emod_of_nonneg _ (by omega)]
  apply bv_wrap_small
  · exact Int.emod_nonneg _ (by omega)
  · rw [bv_modulus_64]
    exact Int.lt_trans (Int.emod_lt_of_pos _ Hy) hy.2

theorem v_subw_small : ∀ x y : word, bv_unsigned y ≤ bv_unsigned x →
    bv_unsigned x - bv_unsigned y < 2 ^ 31 →
    bv_unsigned (v_subw x y) = bv_unsigned x - bv_unsigned y := by
  intro x y Hle Hlt
  unfold v_subw
  rw [Z_to_bv_unsigned, bv_swrap_small 32 _ (by rw [bv_half_modulus_32]; omega)
    (by rw [bv_half_modulus_32]; omega)]
  exact bv_wrap_small 64 _ (by omega) (by rw [bv_modulus_64]; omega)

theorem land_d48 : ∀ d : Int, 0 ≤ d → d < 16 → Z.land d 48 = 0 := by
  intro d Hd0 Hd
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le Hd0
  rw [show (48 : Int) = ((48 : Nat) : Int) from rfl, Z.land_natCast]
  have : m &&& 48 = 0 := (by decide : ∀ m < 16, m &&& 48 = 0) m (by omega)
  rw [this]; rfl

theorem lor_small_add : ∀ d : Int, 0 ≤ d → d < 16 → Z.lor d 48 = d + 48 := by
  intro d Hd0 Hd
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le Hd0
  rw [show (48 : Int) = ((48 : Nat) : Int) from rfl, Z.lor_natCast]
  have : m ||| 48 = m + 48 := (by decide : ∀ m < 16, m ||| 48 = m + 48) m (by omega)
  rw [this]; rfl

theorem v_ori_lor : ∀ d : word, bv_unsigned d < 16 → v_ori d 48 = Z_to_bv 64 (bv_unsigned d + 48) := by
  intro d Hd
  unfold v_ori
  rw [show bv_wrap 64 48 = 48 from rfl, lor_small_add _ (u64_range d).1 Hd]

/-! ### `rdn` composition/extraction -/

theorem rdn_app : ∀ segs mem n1 n2 (a : word) bs1 bs2,
    rdn segs mem a n1 = some bs1 →
    rdn segs mem (a + nat_to_word n1) n2 = some bs2 →
    rdn segs mem a (n1 + n2) = some (bs1 ++ bs2) := by
  intro segs mem n1
  induction n1 with
  | zero =>
    intro n2 a bs1 bs2 H1 H2
    simp only [rdn, Option.some.injEq] at H1
    subst H1
    rw [word_add_0] at H2
    simpa using H2
  | succ n1 ih =>
    intro n2 a bs1 bs2 H1 H2
    rw [show n1 + 1 + n2 = (n1 + n2) + 1 by omega]
    simp only [rdn] at H1 ⊢
    split at H1
    · next b hb =>
      split at H1
      · next rest hr =>
        simp only [Option.some.injEq] at H1
        subst H1
        have H2' : rdn segs mem (a + 1 + nat_to_word n1) n2 = some bs2 := by
          rw [word1_nat, nat_to_word_add_merge, Nat.add_comm]; exact H2
        rw [ih n2 (a + 1) rest bs2 hr H2']
        rfl
      · exact absurd H1 (by simp)
    · exact absurd H1 (by simp)

theorem rdn_nth : ∀ segs mem n (a : word) bs j,
    rdn segs mem a n = some bs → j < n →
    rdn segs mem (a + nat_to_word j) 1 = some [bs.getD j (Z_to_bv 8 0)] := by
  intro segs mem n
  induction n with
  | zero => intro _ _ _ _ Hj; omega
  | succ n ih =>
    intro a bs j H Hj
    simp only [rdn] at H
    split at H
    · next b hb =>
      split at H
      · next rest hr =>
        simp only [Option.some.injEq] at H
        subst H
        cases j with
        | zero => rw [word_add_0]; simp only [rdn, hb]; rfl
        | succ j =>
          have := ih (a + 1) rest j hr (by omega)
          rw [word1_nat, nat_to_word_add_merge, Nat.add_comm] at this
          simpa using this
      · exact absurd H (by simp)
    · exact absurd H (by simp)

/-- `addi` with a negative immediate (holds by conversion; the hypotheses are kept for the call sites). -/
theorem v_addi_m : ∀ (x : word) (k : Int), k ≤ bv_unsigned x → 0 < k →
    v_addi x (-k) = Z_to_bv 64 (bv_unsigned x - k) := by
  intro x k _ _; unfold v_addi; rw [Int.sub_eq_add_neg]

theorem rdn_skipn : ∀ segs mem n (a : word) bs k,
    rdn segs mem a n = some bs → k ≤ n →
    rdn segs mem (a + nat_to_word k) (n - k) = some (bs.drop k) := by
  intro segs mem n
  induction n with
  | zero =>
    intro a bs k H Hk
    obtain rfl : k = 0 := by omega
    rw [word_add_0]; exact H
  | succ n ih =>
    intro a bs k H Hk
    cases k with
    | zero => rw [word_add_0]; exact H
    | succ k =>
      simp only [rdn] at H
      split at H
      · next b hb =>
        split at H
        · next rest hr =>
          simp only [Option.some.injEq] at H
          subst H
          have := ih (a + 1) rest k hr (by omega)
          rw [word1_nat, nat_to_word_add_merge, Nat.add_comm] at this
          rw [show n + 1 - (k + 1) = n - k by omega]
          simpa using this
        · exact absurd H (by simp)
      · exact absurd H (by simp)

theorem rdn_firstn : ∀ segs mem n (a : word) bs k,
    rdn segs mem a n = some bs → k ≤ n →
    rdn segs mem a k = some (bs.take k) := by
  intro segs mem n
  induction n with
  | zero =>
    intro a bs k H Hk
    obtain rfl : k = 0 := by omega
    rfl
  | succ n ih =>
    intro a bs k H Hk
    simp only [rdn] at H
    split at H
    · next b hb =>
      split at H
      · next rest hr =>
        simp only [Option.some.injEq] at H
        subst H
        cases k with
        | zero => rfl
        | succ k =>
          simp only [rdn, hb, ih (a + 1) rest k hr (by omega)]
          rfl
      · exact absurd H (by simp)
    · exact absurd H (by simp)

end LPS

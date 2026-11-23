import LPS.LinuxProcessSem.BvBase

/-!
# LPS `theories/Common/NumPrint.v` (f1006fe8): unsigned decimal printing

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/NumPrint.v` at f1006fe8 (shared proof library): `udec v`, the ASCII decimal digits of
`v`, most significant first, by a fuel-bounded recursion (fuel 24, enough for any 64-bit value), and its
lemmas: the fuel does not matter once it covers the digits (`udec_aux_fuel`), one digit, the step
`udec v = udec (v / 10) ++ [last digit]`, and the length bounds. `Z.div`/`Z.modulo` are the shim's floor
division and modulus (Rocq's `/`, `mod` on `Z`).
-/

namespace LPS

def udec_aux (v : Int) : Nat → List byte
  | 0 => []
  | f + 1 => if v == 0 then [] else udec_aux (Z.div v 10) f ++ [Z_to_bv 8 (48 + Z.modulo v 10)]

def udec (v : Int) : List byte := if v == 0 then [Z_to_bv 8 48] else udec_aux v 24

theorem div10_nonneg {v : Int} (h : 0 ≤ v) : 0 ≤ Z.div v 10 := by
  unfold Z.div; rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]; omega

theorem div10_lt {v : Int} (f : Nat) (h0 : 0 ≤ v) (h : v < 10 ^ (f + 1)) : Z.div v 10 < 10 ^ f := by
  unfold Z.div; rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]
  rw [Int.pow_succ] at h
  exact Int.ediv_lt_of_lt_mul (by decide) h

theorem udec_aux_fuel : ∀ (f g : Nat) (v : Int), 0 ≤ v → v < 10 ^ f → f ≤ g → udec_aux v g = udec_aux v f
  | 0, g, v, h0, h, _ => by
    have : v = 0 := by simp at h; omega
    subst this
    cases g <;> simp [udec_aux]
  | f + 1, g + 1, v, h0, h, hfg => by
    simp only [udec_aux]
    by_cases hv : v = 0
    · simp [hv]
    · simp only [hv, beq_iff_eq, ite_false]
      rw [udec_aux_fuel f g (Z.div v 10) (div10_nonneg h0) (div10_lt f h0 h) (by omega)]
  | _ + 1, 0, _, _, _, hfg => by omega

theorem pow10_20_gt : (2 : Int) ^ 64 < 10 ^ 20 := by decide

theorem udec_aux_S (f : Nat) (v : Int) :
    udec_aux v (f + 1) = if v == 0 then [] else udec_aux (Z.div v 10) f ++ [Z_to_bv 8 (48 + Z.modulo v 10)] := rfl

theorem mod10_small {v : Int} (h0 : 0 ≤ v) (h : v < 10) : Z.modulo v 10 = v := by
  unfold Z.modulo; rw [Int.fmod_eq_emod_of_nonneg _ (by omega), Int.emod_eq_of_lt h0 h]

theorem div10_small {v : Int} (h0 : 0 ≤ v) (h : v < 10) : Z.div v 10 = 0 := by
  unfold Z.div; rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]; exact Int.ediv_eq_zero_of_lt h0 h

theorem udec_single (v : Int) (h : 1 ≤ v ∧ v ≤ 9) : udec v = [Z_to_bv 8 (48 + v)] := by
  have hv : (v == 0) = false := by simp; omega
  unfold udec
  rw [hv, if_neg (by simp), udec_aux_fuel 1 24 v (by omega) (by simp; omega) (by omega), udec_aux_S, hv,
    if_neg (by simp), div10_small (by omega) (by omega), mod10_small (by omega) (by omega)]
  rfl

theorem udec_step (v : Int) (h10 : 10 ≤ v) (h64 : v < 2 ^ 64) :
    udec v = udec (Z.div v 10) ++ [Z_to_bv 8 (48 + Z.modulo v 10)] := by
  have hv : (v == 0) = false := by simp; omega
  have hd0 : 0 ≤ Z.div v 10 := div10_nonneg (by omega)
  have hd : (Z.div v 10 == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    unfold Z.div; rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]; omega
  unfold udec
  rw [hv, hd, if_neg (by simp), if_neg (by simp), show (24 : Nat) = 23 + 1 from rfl, udec_aux_S, hv,
    if_neg (by simp)]
  congr 1
  apply udec_aux_fuel 23 23 _ hd0 _ (Nat.le_refl _) |>.trans
  symm; apply udec_aux_fuel 23 24 _ hd0 _ (by omega)
  all_goals
    have : v < 10 ^ 24 := by have := pow10_20_gt; omega
    exact div10_lt 23 (by omega) this

theorem udec_aux_len : ∀ (f : Nat) (v : Int), (udec_aux v f).length ≤ f
  | 0, _ => by simp [udec_aux]
  | f + 1, v => by
    simp only [udec_aux]
    split
    · simp
    · simp only [List.length_append, List.length_singleton]; have := udec_aux_len f (Z.div v 10); omega

theorem udec_len_le (v : Int) (h0 : 0 ≤ v) (h : v < 2 ^ 64) : (udec v).length ≤ 20 := by
  unfold udec
  split
  · simp
  · rw [udec_aux_fuel 20 24 v h0 (by have := pow10_20_gt; omega) (by omega)]; exact udec_aux_len 20 v

theorem udec_len_pos (v : Int) : 1 ≤ (udec v).length := by
  unfold udec
  split
  · simp
  · rename_i hv
    rw [show (24 : Nat) = 23 + 1 from rfl, udec_aux_S, if_neg hv]
    simp

end LPS

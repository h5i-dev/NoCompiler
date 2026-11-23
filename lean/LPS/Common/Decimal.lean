import LPS.Common.NumPrint

/-!
# LPS `theories/Common/Decimal.v` (f1006fe8): decimal rendering as numbers

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/Decimal.v` at f1006fe8 (shared proof library): `udecZ` / `sdecZ`, the ASCII codes
of a number's (signed) decimal rendering as a list of `Z`, its lemmas, and the bridge to `NumPrint.udec`
(`udecZ_udec`). The Rocq `Example`s are `example`s here, by `decide`.
-/

namespace LPS

def udigits_aux (v : Int) : Nat → List Int
  | 0 => []
  | f + 1 => if v == 0 then [] else udigits_aux (Z.div v 10) f ++ [48 + Z.modulo v 10]

def dec_fuel : Nat := 24

def udecZ (v : Int) : List Int := if v == 0 then [48] else udigits_aux v dec_fuel

def sdecZ (v : Int) : List Int := if v < 0 then 45 :: udecZ (-v) else udecZ v

def to_bytes (l : List Int) : List byte := l.map (Z_to_bv 8)

example : sdecZ 0 = [48] := by decide
example : sdecZ 7 = [55] := by decide
example : sdecZ (-3) = [45, 51] := by decide
example : sdecZ 1024 = [49, 48, 50, 52] := by decide
example : sdecZ (-12) = [45, 49, 50] := by decide
example : udecZ 67108864 = [54, 55, 49, 48, 56, 56, 54, 52] := by decide

theorem udigits_aux_S (f : Nat) (v : Int) :
    udigits_aux v (f + 1) = if v == 0 then [] else udigits_aux (Z.div v 10) f ++ [48 + Z.modulo v 10] := rfl

theorem udigits_aux_fuel : ∀ (f g : Nat) (v : Int), 0 ≤ v → v < 10 ^ f → f ≤ g →
    udigits_aux v g = udigits_aux v f
  | 0, g, v, _, h, _ => by
    have : v = 0 := by simp at h; omega
    subst this
    cases g <;> simp [udigits_aux]
  | f + 1, g + 1, v, h0, h, hfg => by
    simp only [udigits_aux]
    by_cases hv : v = 0
    · simp [hv]
    · simp only [hv, beq_iff_eq, ite_false]
      rw [udigits_aux_fuel f g (Z.div v 10) (div10_nonneg h0) (div10_lt f h0 h) (by omega)]
  | _ + 1, 0, _, _, _, hfg => by omega

theorem udecZ_0 : udecZ 0 = [48] := rfl

theorem udecZ_single (v : Int) (h : 1 ≤ v ∧ v ≤ 9) : udecZ v = [48 + v] := by
  have hv : (v == 0) = false := by simp; omega
  unfold udecZ dec_fuel
  rw [hv, if_neg (by simp), udigits_aux_fuel 1 24 v (by omega) (by simp; omega) (by omega), udigits_aux_S, hv,
    if_neg (by simp), div10_small (by omega) (by omega), mod10_small (by omega) (by omega)]
  rfl

theorem pow10_20_gt' : (2 : Int) ^ 64 < 10 ^ 20 := pow10_20_gt

theorem udecZ_step (v : Int) (h10 : 10 ≤ v) (h64 : v < 2 ^ 64) :
    udecZ v = udecZ (Z.div v 10) ++ [48 + Z.modulo v 10] := by
  have hv : (v == 0) = false := by simp; omega
  have hd0 : 0 ≤ Z.div v 10 := div10_nonneg (by omega)
  have hd : (Z.div v 10 == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    unfold Z.div; rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]; omega
  unfold udecZ dec_fuel
  rw [hv, hd, if_neg (by simp), if_neg (by simp), show (24 : Nat) = 23 + 1 from rfl, udigits_aux_S, hv,
    if_neg (by simp)]
  congr 1
  apply udigits_aux_fuel 23 23 _ hd0 _ (Nat.le_refl _) |>.trans
  symm; apply udigits_aux_fuel 23 24 _ hd0 _ (by omega)
  all_goals
    have : v < 10 ^ 24 := by have := pow10_20_gt; omega
    exact div10_lt 23 (by omega) this

theorem udigits_aux_len : ∀ (f : Nat) (v : Int), (udigits_aux v f).length ≤ f
  | 0, _ => by simp [udigits_aux]
  | f + 1, v => by
    simp only [udigits_aux]
    split
    · simp
    · simp only [List.length_append, List.length_singleton]; have := udigits_aux_len f (Z.div v 10); omega

theorem udecZ_len_le (v : Int) (h0 : 0 ≤ v) (h : v < 2 ^ 64) : (udecZ v).length ≤ 20 := by
  unfold udecZ dec_fuel
  split
  · simp
  · rw [udigits_aux_fuel 20 24 v h0 (by have := pow10_20_gt; omega) (by omega)]; exact udigits_aux_len 20 v

theorem udecZ_len_pos (v : Int) : 1 ≤ (udecZ v).length := by
  unfold udecZ dec_fuel
  split
  · simp
  · rename_i hv
    rw [show (24 : Nat) = 23 + 1 from rfl, udigits_aux_S, if_neg hv]
    simp

theorem mod10_range {v : Int} : 0 ≤ Z.modulo v 10 ∧ Z.modulo v 10 < 10 := by
  unfold Z.modulo
  exact ⟨Int.fmod_nonneg_of_pos _ (by decide), Int.fmod_lt_of_pos _ (by decide)⟩

theorem udigits_aux_digits : ∀ (f : Nat) (v : Int), 0 ≤ v → ∀ d ∈ udigits_aux v f, 48 ≤ d ∧ d ≤ 57
  | 0, _, _ => by simp [udigits_aux]
  | f + 1, v, hv => by
    simp only [udigits_aux]
    split
    · simp
    · intro d hd
      rcases List.mem_append.1 hd with hd | hd
      · exact udigits_aux_digits f _ (div10_nonneg hv) d hd
      · simp only [List.mem_singleton] at hd; subst hd; have := @mod10_range v; omega

theorem udecZ_digits (v : Int) (hv : 0 ≤ v) : ∀ d ∈ udecZ v, 48 ≤ d ∧ d ≤ 57 := by
  unfold udecZ
  split
  · simp
  · exact udigits_aux_digits _ v hv

theorem sdecZ_nonneg (v : Int) (hv : 0 ≤ v) : sdecZ v = udecZ v := by
  unfold sdecZ; rw [if_neg (by omega)]

theorem sdecZ_neg (v : Int) (hv : v < 0) : sdecZ v = 45 :: udecZ (-v) := by
  unfold sdecZ; rw [if_pos hv]

theorem sdecZ_len_pos (v : Int) : 1 ≤ (sdecZ v).length := by
  unfold sdecZ
  split
  · simp
  · exact udecZ_len_pos v

theorem sdecZ_range (v : Int) : ∀ d ∈ sdecZ v, 0 ≤ d ∧ d < 256 := by
  unfold sdecZ
  split
  · intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · omega
    · have := udecZ_digits (-v) (by omega) d hd; omega
  · intro d hd; have := udecZ_digits v (by omega) d hd; omega

theorem udigits_aux_udec_aux : ∀ (f : Nat) (v : Int), to_bytes (udigits_aux v f) = udec_aux v f
  | 0, _ => rfl
  | f + 1, v => by
    simp only [udigits_aux, udec_aux]
    split
    · rfl
    · simp only [to_bytes, List.map_append, List.map_cons, List.map_nil] at *
      rw [← udigits_aux_udec_aux f]; rfl

theorem udecZ_udec (v : Int) : to_bytes (udecZ v) = udec v := by
  unfold udecZ udec dec_fuel
  split
  · rfl
  · exact udigits_aux_udec_aux 24 v

end LPS

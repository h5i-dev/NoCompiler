import NoCompiler.Lib.Fill

/-!
# Library: bit-level idioms on 64-bit words

The bit operations compilers emit for arithmetic, as arithmetic: alignment tested with a low
mask, rounding down with the complement mask (and up, by adding first), a byte of a word by shift
and truncation, and a word assembled from a shifted high part or-ed with a low part. Namespace
`NoCompiler.Lib`. Round 7, B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

/-- The bits of the low mask `2^k - 1`. -/
theorem getElem_mask {k i : Nat} (hk : k ≤ 64) (hi : i < 64) :
    (BitVec.ofNat 64 (2 ^ k - 1))[i] = decide (i < k) := by
  rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := Nat.pow_le_pow_right (by decide : 0 < 2) hk; omega),
    Nat.testBit_two_pow_sub_one]

/-- Alignment to `2^k`, tested with the low mask. -/
theorem aligned_iff_and (x : Word) {k : Nat} (hk : k ≤ 64) :
    aligned x (2 ^ k) ↔ x &&& BitVec.ofNat 64 (2 ^ k - 1) = 0 := by
  rw [aligned, eq_zero_iff, and_mask x k hk]

/-- The complement mask clears the low `k` bits: a shift right then left. -/
theorem and_not_mask (x : Word) {k : Nat} (hk : k ≤ 64) :
    x &&& ~~~BitVec.ofNat 64 (2 ^ k - 1) = (x >>> k) <<< k := by
  ext i hi
  rw [BitVec.getElem_and, BitVec.getElem_not, getElem_mask hk hi, BitVec.getElem_shiftLeft]
  by_cases h : i < k
  · simp [h]
  · simp only [h, decide_false, Bool.not_false, Bool.and_true]
    rw [BitVec.getElem_ushiftRight]; congr 1; omega

/-- Shifting right then left by `k` rounds down to a multiple of `2^k`. -/
theorem toNat_shiftRight_shiftLeft (x : Word) (k : Nat) :
    ((x >>> k) <<< k).toNat = x.toNat - x.toNat % 2 ^ k := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have h1 := Nat.mod_add_div x.toNat (2 ^ k)
  have h2 : x.toNat / 2 ^ k * 2 ^ k ≤ x.toNat := Nat.div_mul_le_self _ _
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h2 x.isLt)]
  rw [Nat.mul_comm] at h1; omega

/-- Rounding down to `2^k` with the complement mask. -/
theorem toNat_and_not_mask (x : Word) {k : Nat} (hk : k ≤ 64) :
    (x &&& ~~~BitVec.ofNat 64 (2 ^ k - 1)).toNat = x.toNat - x.toNat % 2 ^ k := by
  rw [and_not_mask x hk, toNat_shiftRight_shiftLeft]

/-- What the complement mask leaves is aligned. -/
theorem aligned_and_not_mask (x : Word) {k : Nat} (hk : k ≤ 64) :
    aligned (x &&& ~~~BitVec.ofNat 64 (2 ^ k - 1)) (2 ^ k) := by
  unfold aligned
  rw [toNat_and_not_mask x hk, Nat.sub_mod_eq_zero_of_mod_eq (Nat.mod_mod _ _).symm]

/-- What the complement mask leaves is at most the word and less than `2^k` below it. -/
theorem and_not_mask_le (x : Word) {k : Nat} (hk : k ≤ 64) :
    (x &&& ~~~BitVec.ofNat 64 (2 ^ k - 1)).toNat ≤ x.toNat ∧
      x.toNat < (x &&& ~~~BitVec.ofNat 64 (2 ^ k - 1)).toNat + 2 ^ k := by
  rw [toNat_and_not_mask x hk]
  have := Nat.mod_lt x.toNat (Nat.two_pow_pos k)
  have := Nat.mod_le x.toNat (2 ^ k)
  omega

/-- Rounding up to `2^k`: add `2^k - 1`, then clear the low bits (when the sum does not wrap). -/
theorem toNat_align_up (x : Word) {k : Nat} (hk : k ≤ 64) (h : x.toNat + (2 ^ k - 1) < 2 ^ 64) :
    ((x + BitVec.ofNat 64 (2 ^ k - 1)) &&& ~~~BitVec.ofNat 64 (2 ^ k - 1)).toNat =
      (x.toNat + (2 ^ k - 1)) - (x.toNat + (2 ^ k - 1)) % 2 ^ k := by
  rw [toNat_and_not_mask _ hk, toNat_add_ofNat h]

/-- A byte of a word: shift right by `8 i`, keep 8 bits. -/
theorem toNat_byte (x : Word) (i : Nat) :
    ((x >>> (8 * i)).setWidth 8).toNat = x.toNat / 256 ^ i % 256 := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

/-- A word assembled from a high part shifted left by `k` and a low part below `2^k`. -/
theorem toNat_shiftLeft_or (hi lo : Word) {k : Nat} (hlo : lo.toNat < 2 ^ k)
    (h : hi.toNat * 2 ^ k + lo.toNat < 2 ^ 64) :
    (hi <<< k ||| lo).toNat = hi.toNat * 2 ^ k + lo.toNat := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega), ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hlo]

/-- Or-ing two words with no common bits is adding them. -/
theorem or_eq_add_of_and_eq_zero (x y : Word) (h : x &&& y = 0) : x ||| y = x + y :=
  (BitVec.add_eq_or_of_and_eq_zero x y h).symm

end NoCompiler.Lib

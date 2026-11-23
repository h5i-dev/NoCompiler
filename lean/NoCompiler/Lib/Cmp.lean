import NoCompiler.Lib.Count

/-!
# Library: comparison results and min/max

`slt`/`sltu`/`slti`/`sltiu` write `bool64 b` (1 or 0); compilers then branch on it being zero, or
add it, or mask with it. Its value, when it is zero, and its algebra (`xori 1` negates); and the
Zbb `minu`/`maxu`/`min`/`max` results as the smaller or larger value. Namespace
`NoCompiler.Lib`. Round 7, B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

theorem toNat_bool64 (b : Bool) : (bool64 b).toNat = if b then 1 else 0 := by
  cases b <;> rfl

theorem bool64_true : bool64 true = 1 := rfl
theorem bool64_false : bool64 false = 0 := rfl

/-- The comparison result is zero exactly when the comparison is false (`beqz`/`bnez` after it). -/
theorem bool64_eq_zero_iff (b : Bool) : bool64 b = 0 ↔ b = false := by
  cases b <;> decide

theorem bool64_ne_zero_iff (b : Bool) : bool64 b ≠ 0 ↔ b = true := by
  cases b <;> decide

/-- `xori r, r, 1` on a comparison result negates it (`sgeu` from `sltu`). -/
theorem bool64_xor_one (b : Bool) : bool64 b ^^^ 1 = bool64 (!b) := by
  cases b <;> decide

/-- `neg` of a comparison result is all ones or zero: the mask compilers build for a select. -/
theorem neg_bool64 (b : Bool) : -bool64 b = if b then BitVec.allOnes 64 else 0 := by
  cases b <;> decide

/-- Masking with that: `x &&& -bool64 b` is `x` or `0`. -/
theorem and_neg_bool64 (x : Word) (b : Bool) : x &&& -bool64 b = if b then x else 0 := by
  cases b
  · simp [neg_bool64]
  · rw [neg_bool64]; simp only [ite_true]; exact BitVec.and_allOnes

/-- `sltu x, y` as a number. -/
theorem toNat_sltu (x y : Word) : (bool64 (BitVec.ult x y)).toNat = if x.toNat < y.toNat then 1 else 0 := by
  rw [toNat_bool64, ult_iff]; by_cases h : x.toNat < y.toNat <;> simp [h]

/-- `sltu x, 1` (`seqz`): 1 exactly when `x` is zero. -/
theorem sltu_one_iff (x : Word) : BitVec.ult x 1 = true ↔ x = 0 := by
  rw [ult_iff, eq_zero_iff]; simp

/-- `sltu 0, x` (`snez`): 1 exactly when `x` is not zero. -/
theorem sltu_zero_iff (x : Word) : BitVec.ult 0 x = true ↔ x ≠ 0 := by
  rw [ult_iff, ne_iff_toNat]; simp; omega

/-- `minu` is the unsigned minimum. -/
theorem toNat_minu (x y : Word) :
    (if BitVec.ult x y then x else y).toNat = min x.toNat y.toNat := by
  rw [ult_iff]; by_cases h : x.toNat < y.toNat <;> simp [h] <;> omega

/-- `maxu` is the unsigned maximum. -/
theorem toNat_maxu (x y : Word) :
    (if BitVec.ult x y then y else x).toNat = max x.toNat y.toNat := by
  rw [ult_iff]; by_cases h : x.toNat < y.toNat <;> simp [h] <;> omega

/-- `min` is the signed minimum. -/
theorem toInt_min (x y : Word) :
    (if BitVec.slt x y then x else y).toInt = min x.toInt y.toInt := by
  rw [slt_iff_toInt]; by_cases h : x.toInt < y.toInt <;> simp [h] <;> omega

/-- `max` is the signed maximum. -/
theorem toInt_max (x y : Word) :
    (if BitVec.slt x y then y else x).toInt = max x.toInt y.toInt := by
  rw [slt_iff_toInt]; by_cases h : x.toInt < y.toInt <;> simp [h] <;> omega

end NoCompiler.Lib

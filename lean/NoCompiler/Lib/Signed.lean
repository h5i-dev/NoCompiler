import NoCompiler.Lib.Div

/-!
# Library: signed words

Two's complement as natural numbers: a word's signed value is its value below `2^63` and its
value minus `2^64` from there; the sign bit; signed comparison of words of either sign; the
arithmetic shift of a non-negative word as division; negation; and the syscall-return idiom
(a result in `[2^64 - 4095, 2^64)` is `-errno`, `__syscall_ret`'s unsigned test `x > -4096`).
Namespace `NoCompiler.Lib`. Round 7, B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

/-- The sign bit is set exactly from `2^63` on. -/
theorem msb_iff (x : Word) : x.msb = true ↔ 2 ^ 63 ≤ x.toNat := by
  rw [BitVec.msb_eq_decide]; simp

/-- The signed value of a word below `2^63`. -/
theorem toInt_of_lt {x : Word} (h : x.toNat < 2 ^ 63) : x.toInt = x.toNat :=
  BitVec.toInt_eq_toNat_of_lt (by omega)

/-- The signed value of a word from `2^63` on. -/
theorem toInt_of_ge {x : Word} (h : 2 ^ 63 ≤ x.toNat) : x.toInt = (x.toNat : Int) - 2 ^ 64 := by
  rw [BitVec.toInt_eq_toNat_cond]
  have : ¬ (2 * x.toNat < 2 ^ 64) := by omega
  simp [this]

/-- Signed less-than is less-than of the signed values. -/
theorem slt_iff_toInt (x y : Word) : BitVec.slt x y = decide (x.toInt < y.toInt) := by
  simp [BitVec.slt]

/-- A negative word is signed-less than a non-negative one. -/
theorem slt_of_neg_nonneg {x y : Word} (hx : 2 ^ 63 ≤ x.toNat) (hy : y.toNat < 2 ^ 63) :
    BitVec.slt x y = true := by
  rw [slt_iff_toInt, toInt_of_ge hx, toInt_of_lt hy]
  have := x.isLt; simp; omega

/-- Two negative words compare as their values do. -/
theorem slt_of_neg_neg {x y : Word} (hx : 2 ^ 63 ≤ x.toNat) (hy : 2 ^ 63 ≤ y.toNat) :
    BitVec.slt x y = decide (x.toNat < y.toNat) := by
  rw [slt_iff_toInt, toInt_of_ge hx, toInt_of_ge hy]
  simp

/-- The arithmetic shift of a non-negative word divides. -/
theorem toNat_sshiftRight_of_lt (x : Word) (k : Nat) (h : x.toNat < 2 ^ 63) :
    (x.sshiftRight k).toNat = x.toNat / 2 ^ k := by
  have hm : x.msb = false := by
    rw [BitVec.msb_eq_decide]; simp; omega
  rw [BitVec.sshiftRight_eq_of_msb_false hm, toNat_ushiftRight]

/-- Negation of a non-zero word. -/
theorem toNat_neg_of_ne {x : Word} (h : x ≠ 0) : (-x).toNat = 2 ^ 64 - x.toNat := by
  rw [BitVec.toNat_neg]
  have h0 : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
  have := x.isLt
  exact Nat.mod_eq_of_lt (by omega)

/-- `-k` for a constant `0 < k < 2^64`. -/
theorem toNat_neg_ofNat {k : Nat} (h0 : 0 < k) (h : k < 2 ^ 64) :
    (-BitVec.ofNat 64 k).toNat = 2 ^ 64 - k := by
  rw [toNat_neg_of_ne, toNat_ofNat_of_lt h]
  intro e; have := congrArg BitVec.toNat e; rw [toNat_ofNat_of_lt h] at this; simp at this; omega

/-- The syscall-return idiom: a result is `-e` for an errno `1 ≤ e ≤ 4095` exactly when it is
    unsigned-greater than `-4096`. -/
theorem errno_iff (x : Word) :
    BitVec.ult (-BitVec.ofNat 64 4096) x = true ↔
      ∃ e, 1 ≤ e ∧ e ≤ 4095 ∧ x = -BitVec.ofNat 64 e := by
  rw [ult_iff, toNat_neg_ofNat (by decide) (by decide)]
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨2 ^ 64 - x.toNat, by have := x.isLt; omega, by omega, ?_⟩
    apply BitVec.eq_of_toNat_eq
    have := x.isLt
    rw [toNat_neg_ofNat (by omega) (by omega)]; omega
  · rintro ⟨e, h1, h2, rfl⟩
    rw [toNat_neg_ofNat (by omega) (by omega)]; omega

end NoCompiler.Lib

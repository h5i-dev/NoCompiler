import NoCompiler.Lib.Mul

/-!
# Library: range tests

Compilers test `lo ≤ x < lo + n` with one subtraction and one unsigned comparison
(`addi t, x, -lo; sltiu t, t, n`): `(x - lo) <u n`. This is `isdigit`, `isalpha`, `isspace`, a
switch's table bound and an array index check. The test as the two comparisons, its negation, and
the instances for `'0'..'9'`, `'a'..'z'` and `'A'..'Z'`. Namespace `NoCompiler.Lib`. Round 7,
B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

/-- The one-comparison range test. -/
theorem sub_ult_iff (x : Word) {lo n : Nat} (hlo : lo < 2 ^ 64) (hn : lo + n < 2 ^ 64) :
    BitVec.ult (x - BitVec.ofNat 64 lo) (BitVec.ofNat 64 n) = true ↔
      lo ≤ x.toNat ∧ x.toNat < lo + n := by
  rw [ult_iff, decide_eq_true_eq, BitVec.toNat_sub, toNat_ofNat_of_lt hlo,
    toNat_ofNat_of_lt (by omega)]
  have := x.isLt
  constructor
  · intro h
    by_cases hl : lo ≤ x.toNat
    · rw [show 2 ^ 64 - lo + x.toNat = (x.toNat - lo) + 2 ^ 64 by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)] at h
      exact ⟨hl, by omega⟩
    · rw [Nat.mod_eq_of_lt (by omega)] at h
      omega
  · rintro ⟨h1, h2⟩
    rw [show 2 ^ 64 - lo + x.toNat = (x.toNat - lo) + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
    omega

/-- The test failing: below `lo` or at least `lo + n`. -/
theorem sub_ult_false_iff (x : Word) {lo n : Nat} (hlo : lo < 2 ^ 64) (hn : lo + n < 2 ^ 64) :
    BitVec.ult (x - BitVec.ofNat 64 lo) (BitVec.ofNat 64 n) = false ↔
      x.toNat < lo ∨ lo + n ≤ x.toNat := by
  have := sub_ult_iff x hlo hn
  constructor
  · intro h; rw [h] at this; simp at this; omega
  · intro h
    cases e : BitVec.ult (x - BitVec.ofNat 64 lo) (BitVec.ofNat 64 n)
    · rfl
    · have := this.1 e; omega

/-- A byte value is a decimal digit (`isdigit`): `(c - '0') <u 10`. -/
theorem isdigit_iff (x : Word) :
    BitVec.ult (x - BitVec.ofNat 64 48) (BitVec.ofNat 64 10) = true ↔ 48 ≤ x.toNat ∧ x.toNat < 58 :=
  sub_ult_iff x (by decide) (by decide)

/-- Lower case (`islower`): `(c - 'a') <u 26`. -/
theorem islower_iff (x : Word) :
    BitVec.ult (x - BitVec.ofNat 64 97) (BitVec.ofNat 64 26) = true ↔ 97 ≤ x.toNat ∧ x.toNat < 123 :=
  sub_ult_iff x (by decide) (by decide)

/-- Upper case (`isupper`): `(c - 'A') <u 26`. -/
theorem isupper_iff (x : Word) :
    BitVec.ult (x - BitVec.ofNat 64 65) (BitVec.ofNat 64 26) = true ↔ 65 ≤ x.toNat ∧ x.toNat < 91 :=
  sub_ult_iff x (by decide) (by decide)

/-- An index check: `i <u n` for a word bound is `i < n` as numbers. -/
theorem index_ok_iff (i n : Word) : BitVec.ult i n = true ↔ i.toNat < n.toNat := by
  rw [ult_iff]; simp

/-- The digit's value after the test: `x - '0'` is the digit. -/
theorem digit_value {x : Word} (h : 48 ≤ x.toNat) : (x - BitVec.ofNat 64 48).toNat = x.toNat - 48 :=
  toNat_sub_of_le (by rw [toNat_ofNat_of_lt (by decide)]; exact h)

end NoCompiler.Lib

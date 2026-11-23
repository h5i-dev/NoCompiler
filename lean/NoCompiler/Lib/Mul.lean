import NoCompiler.Lib.Shift

/-!
# Library: multiplication

`mul` without wrap is the product; by a constant; and the overflow test compilers emit for
`calloc`-style size computations (`mulhu x y` is zero exactly when `x * y` fits in 64 bits, and
then `mul x y` is the product). Namespace `NoCompiler.Lib`. Round 7, B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

/-- A product that does not wrap. -/
theorem toNat_mul_of_lt {x y : Word} (h : x.toNat * y.toNat < 2 ^ 64) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]

/-- A product by a constant that does not wrap. -/
theorem toNat_mul_ofNat {x : Word} {k : Nat} (hk : k < 2 ^ 64) (h : x.toNat * k < 2 ^ 64) :
    (x * BitVec.ofNat 64 k).toNat = x.toNat * k := by
  rw [toNat_mul_of_lt (by rw [toNat_ofNat_of_lt hk]; exact h), toNat_ofNat_of_lt hk]

/-- The overflow test: the high half of the product is zero exactly when it fits. -/
theorem mulhUU_eq_zero_iff (x y : Word) : mulhUU x y = 0 ↔ x.toNat * y.toNat < 2 ^ 64 := by
  rw [eq_zero_iff, toNat_mulhUU, Nat.div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact absurd h (by decide)
    · exact h
  · exact fun h => .inr h

/-- No overflow: then `mul` is the product. -/
theorem toNat_mul_of_mulhUU {x y : Word} (h : mulhUU x y = 0) : (x * y).toNat = x.toNat * y.toNat :=
  toNat_mul_of_lt ((mulhUU_eq_zero_iff x y).1 h)

/-- Multiplication by a power of two is a shift. -/
theorem mul_two_pow_eq_shiftLeft (x : Word) (k : Nat) : x * BitVec.ofNat 64 (2 ^ k) = x <<< k := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, toNat_shiftLeft, Nat.mul_mod, Nat.mod_mod,
    ← Nat.mul_mod]

/-- An element offset `i * w` within an array of `n` elements of `w` bytes, `w * n < 2^64`, does
    not wrap. -/
theorem toNat_mul_index {i : Word} {w n : Nat} (hi : i.toNat < n) (hn : w * n < 2 ^ 64) :
    (i * BitVec.ofNat 64 w).toNat = w * i.toNat := by
  have hw : w < 2 ^ 64 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · omega
    · exact Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right w h) hn
  have : i.toNat * w < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left w (Nat.le_of_lt hi)) hn
  rw [toNat_mul_ofNat hw this, Nat.mul_comm]

end NoCompiler.Lib

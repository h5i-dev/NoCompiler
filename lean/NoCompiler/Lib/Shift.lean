import NoCompiler.Lib.Cmp
import NoCompiler.Lib.Sext

/-!
# Library: shifts

The shifts as RISC-V does them: `sll`/`srl`/`sra` use the shift amount modulo 64, so an amount
below 64 is used as it is; `slli` by `k` multiplies by `2^k` and does not wrap below `2^(64-k)`;
`srli` divides; `slli.uw` (Zba) shifts the low half; a shift by 0 is the identity; and
`(x <<< k) >>> k` keeps the low bits. Namespace `NoCompiler.Lib`. Round 7, B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

/-- A register shift amount below 64 is used as it is. -/
theorem shamt_of_lt {y : Word} (h : y.toNat < 64) : y.toNat % 64 = y.toNat := Nat.mod_eq_of_lt h

/-- ... and a constant amount `k < 64`. -/
theorem shamt_ofNat {k : Nat} (h : k < 64) : (BitVec.ofNat 64 k).toNat % 64 = k := by
  rw [toNat_ofNat_of_lt (by omega), Nat.mod_eq_of_lt h]

/-- A shift left that does not wrap multiplies. -/
theorem toNat_shiftLeft_of_lt (x : Word) {k : Nat} (h : x.toNat * 2 ^ k < 2 ^ 64) :
    (x <<< k).toNat = x.toNat * 2 ^ k := by
  rw [toNat_shiftLeft, Nat.mod_eq_of_lt h]

/-- Scaling an index by 8 (`slli 3`) below `2^61`. -/
theorem toNat_shiftLeft_3 (x : Word) (h : x.toNat < 2 ^ 61) : (x <<< 3).toNat = 8 * x.toNat := by
  rw [toNat_shiftLeft_of_lt x (by omega), Nat.mul_comm]

/-- Scaling an index by 4 (`slli 2`) below `2^62`. -/
theorem toNat_shiftLeft_2 (x : Word) (h : x.toNat < 2 ^ 62) : (x <<< 2).toNat = 4 * x.toNat := by
  rw [toNat_shiftLeft_of_lt x (by omega), Nat.mul_comm]

/-- A shift by 0 is the identity. -/
theorem shiftLeft_zero' (x : Word) : x <<< 0 = x := by simp
theorem ushiftRight_zero' (x : Word) : x >>> 0 = x := by simp

/-- Shift left then right by `k` keeps the low `64 - k` bits. -/
theorem toNat_shiftLeft_ushiftRight (x : Word) {k : Nat} (hk : k ≤ 64) :
    ((x <<< k) >>> k).toNat = x.toNat % 2 ^ (64 - k) := by
  rw [toNat_ushiftRight, toNat_shiftLeft]
  have e : 2 ^ 64 = 2 ^ (64 - k) * 2 ^ k := by rw [← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (Nat.two_pow_pos k)]

/-- `slli.uw` (Zba): the low half, shifted. -/
theorem toNat_slliuw (x : Word) {k : Nat} (h : x.toNat % 2 ^ 32 * 2 ^ k < 2 ^ 64) :
    (zext32 x <<< k).toNat = x.toNat % 2 ^ 32 * 2 ^ k := by
  rw [toNat_shiftLeft_of_lt _ (by rw [toNat_zext32]; exact h), toNat_zext32]

/-- An index scaled by `slli k` and added to a base: the address of element `i` of an array of
    `2^k`-byte elements. -/
theorem base_add_shiftLeft (base x : Word) {k : Nat} (h : x.toNat * 2 ^ k < 2 ^ 64) :
    base + (x <<< k) = base + BitVec.ofNat 64 (2 ^ k * x.toNat) := by
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [toNat_shiftLeft_of_lt x h, toNat_ofNat_of_lt (by rw [Nat.mul_comm]; exact h), Nat.mul_comm]

end NoCompiler.Lib

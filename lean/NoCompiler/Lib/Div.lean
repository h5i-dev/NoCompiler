import NoCompiler.Lib.Rw

/-!
# Library: division

Unsigned division by a constant as compilers emit it (Granlund-Montgomery): `mulhu` by a magic
constant `M`, then a shift right by `s`, is `x / d` when `M * d = 2^(64+s) + e` with `e <= 2^s`
(`udiv_magic`; for gcc's `x / 10`, `M = 0xCCCCCCCCCCCCCCCD`, `s = 3`, `e = 2`, every side condition
by `decide`). Then the remainder from the quotient (`x - q * d`), and `divu`/`remu` by a non-zero
word and by zero. Namespace `NoCompiler.Lib`. Round 7, B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

/-- Division by a constant as a multiplication and a shift: when `M * d = 2^N + e` with
    `e <= 2^(N-64)` (`N >= 64`), `x * M / 2^N = x / d` for every `x < 2^64`. -/
theorem div_magic {x d M N e : Nat} (hd : 0 < d) (hx : x < 2 ^ 64) (hN : 64 ≤ N)
    (hM : M * d = 2 ^ N + e) (he : e ≤ 2 ^ (N - 64)) : x * M / 2 ^ N = x / d := by
  have hp : 2 ^ N = 2 ^ 64 * 2 ^ (N - 64) := by rw [← Nat.pow_add]; congr 1; omega
  have hxe : x * e < 2 ^ N := by
    rw [hp]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left x he)
      (Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos (N - 64)))
  have key : x * M * d = x * 2 ^ N + x * e := by rw [Nat.mul_assoc, hM, Nat.mul_add]
  have hx' := Nat.div_add_mod x d
  have hr := Nat.mod_lt x hd
  generalize x / d = q at *
  generalize x % d = r at *
  apply Nat.div_eq_of_lt_le
  · apply Nat.le_of_mul_le_mul_right _ hd
    rw [key]
    have h1 : q * 2 ^ N * d = (d * q) * 2 ^ N := by ac_rfl
    have h2 : (d * q) * 2 ^ N ≤ x * 2 ^ N := Nat.mul_le_mul_right _ (by omega)
    omega
  · apply Nat.lt_of_mul_lt_mul_right (a := d)
    rw [key]
    have h1 : (q + 1) * 2 ^ N * d = (d * q + d) * 2 ^ N := by
      rw [Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.add_mul]; ac_rfl
    have h2 : x * 2 ^ N + 2 ^ N ≤ (d * q + d) * 2 ^ N := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    omega

/-- `mulhu` is the high half of the product. -/
theorem toNat_mulhUU (x y : Word) : (mulhUU x y).toNat = x.toNat * y.toNat / 2 ^ 64 := by
  unfold mulhUU
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_setWidth,
    BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (by decide)),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le y.isLt (by decide)), Nat.shiftRight_eq_div_pow]
  have hp : x.toNat * y.toNat < 2 ^ 128 := by
    have := Nat.mul_lt_mul_of_lt_of_le x.isLt (Nat.le_of_lt y.isLt) (by decide : 0 < 2 ^ 64)
    simpa [← Nat.pow_add] using this
  rw [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt]
  exact Nat.div_lt_of_lt_mul (by simpa [← Nat.pow_add] using hp)

/-- Unsigned division by a constant `d` as compiled: `mulhu` by the magic `M`, then shift right
    by `s`, where `M * d = 2^(64+s) + e` and `e ≤ 2^s`. -/
theorem udiv_magic (x : Word) {d M s e : Nat} (hd : 0 < d) (hM64 : M < 2 ^ 64)
    (hM : M * d = 2 ^ (64 + s) + e) (he : e ≤ 2 ^ s) :
    (mulhUU x (BitVec.ofNat 64 M) >>> s).toNat = x.toNat / d := by
  rw [BitVec.toNat_ushiftRight, toNat_mulhUU, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hM64,
    Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  exact div_magic hd x.isLt (by omega) hM (by simpa using he)

/-- The remainder from the quotient, as compiled after a division by a constant:
    `x - q * d` with `q = x / d`. -/
theorem urem_of_udiv (x q : Word) {d : Nat} (hq : q.toNat = x.toNat / d) (hd : d < 2 ^ 64) :
    (x - q * BitVec.ofNat 64 d).toNat = x.toNat % d := by
  have hqd : q.toNat * d ≤ x.toNat := by rw [hq]; exact Nat.div_mul_le_self _ _
  have hmul : (q * BitVec.ofNat 64 d).toNat = q.toNat * d := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hqd x.isLt)
  rw [BitVec.toNat_sub, hmul]
  have := Nat.mod_add_div x.toNat d
  rw [hq] at hqd ⊢
  rw [show 2 ^ 64 - x.toNat / d * d + x.toNat = (x.toNat - x.toNat / d * d) + 2 ^ 64 by
    have := x.isLt; omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := x.isLt; omega)]
  rw [Nat.mul_comm] at this; omega

/-- `divu` by a non-zero word. -/
theorem toNat_rvDivu (x y : Word) (hy : y ≠ 0) : (rvDivu x y).toNat = x.toNat / y.toNat := by
  unfold rvDivu; split
  · rename_i h; exact absurd h hy
  · exact BitVec.toNat_udiv

/-- `remu` by a non-zero word. -/
theorem toNat_rvRemu (x y : Word) (hy : y ≠ 0) : (rvRemu x y).toNat = x.toNat % y.toNat := by
  unfold rvRemu; split
  · rename_i h; exact absurd h hy
  · exact BitVec.toNat_umod

/-- `divu` / `remu` by zero: all ones, and the dividend (RISC-V). -/
theorem rvDivu_zero (x : Word) : rvDivu x 0 = BitVec.allOnes 64 := by simp [rvDivu]
theorem rvRemu_zero (x : Word) : rvRemu x 0 = x := by simp [rvRemu]

end NoCompiler.Lib

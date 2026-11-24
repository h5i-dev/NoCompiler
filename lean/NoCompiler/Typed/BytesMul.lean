import NoCompiler.Typed.Bytes

/-!
# The byte broadcast of `mulhu`

Compiled `memset` builds its fill word by `mulhu (b << 56) 0x0101010101010100`: the high 64
bits of the product are byte `b` repeated in bytes `0 … 6`. `mulhUU_toNat` states `mulhu` in
`Nat` (the route that stays cheap: unfolding the 128-bit product with `simp` does not), and each
byte follows from a digit decomposition of `0x01010101010101` (`digit_gen`).
-/
namespace NoCompiler.Typed.Bytes
open NoCompiler

theorem mulhUU_toNat (x y : Word) : (mulhUU x y).toNat = x.toNat * y.toNat / 2 ^ 64 := by
  have hx := x.isLt; have hy := y.isLt
  have hxy : x.toNat * y.toNat < 2 ^ 128 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_of_lt hy) (by decide)) (by decide)
  unfold mulhUU
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_setWidth,
    BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans hx (by decide)),
    Nat.mod_eq_of_lt (Nat.lt_trans hy (by decide)), Nat.mod_eq_of_lt hxy, Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact hxy))

theorem shl56_toNat (w : Word) : (w <<< 56).toNat = w.toNat % 256 * 2 ^ 56 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show (2 : Nat) ^ 64 = 256 * 2 ^ 56 by decide,
    Nat.mul_mod_mul_right]

theorem broadcast_toNat (w : Word) :
    (mulhUU (w <<< 56) 0x0101010101010100#64).toNat = w.toNat % 256 * 0x01010101010101 := by
  rw [mulhUU_toNat, shl56_toNat, show (0x0101010101010100#64 : Word).toNat = 0x0101010101010100 from rfl,
    Nat.mul_assoc, show (2 : Nat) ^ 56 * 0x0101010101010100 = 0x01010101010101 * 2 ^ 64 by decide,
    ← Nat.mul_assoc, Nat.mul_div_cancel _ (by decide)]

theorem digit_gen (b Ki Ri t m : Nat) (hb : b < 256)
    (hK : (0x01010101010101 : Nat) = Ki * 2 ^ m + Ri) (hR : 255 * Ri < 2 ^ m)
    (hKi : Ki = 1 + 256 * t) : b * 0x01010101010101 / 2 ^ m % 256 = b := by
  rw [hK, hKi]
  have h1 : b * ((1 + 256 * t) * 2 ^ m + Ri) = b * Ri + (b * (1 + 256 * t)) * 2 ^ m := by
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.add_comm]
  have hbR : b * Ri < 2 ^ m :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right Ri (by omega : b ≤ 255)) hR
  rw [h1, Nat.add_mul_div_right _ _ (Nat.two_pow_pos m), Nat.div_eq_of_lt hbR,
    Nat.zero_add, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hb]

theorem byte_broadcast (w : Word) {i : Nat} (hi : i < 7) :
    byte (mulhUU (w <<< 56) 0x0101010101010100#64) i = byte w 0 := by
  rw [byte_eq, byte_eq, broadcast_toNat]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  have hb : w.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
  rw [show (2 : Nat) ^ 8 = 256 from rfl]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
    h | h | h | h | h | h | h <;> subst h
  · exact digit_gen _ 282578800148737 0 1103823438081 _ hb (by decide) (by decide) (by decide)
  · exact digit_gen _ 1103823438081 1 4311810305 _ hb (by decide) (by decide) (by decide)
  · exact digit_gen _ 4311810305 257 16843009 _ hb (by decide) (by decide) (by decide)
  · exact digit_gen _ 16843009 65793 65793 _ hb (by decide) (by decide) (by decide)
  · exact digit_gen _ 65793 16843009 257 _ hb (by decide) (by decide) (by decide)
  · exact digit_gen _ 257 4311810305 1 _ hb (by decide) (by decide) (by decide)
  · exact digit_gen _ 1 1103823438081 0 _ hb (by decide) (by decide) (by decide)

/-- A word whose bytes `0 … 6` are zero is its top byte shifted back up. -/
theorem eq_shl_of_low_zero {x : Word} (h : ∀ i < 7, byte x i = 0#8) : x = (x >>> 56) <<< 56 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hx := x.isLt
  -- the low 56 bits are the low bytes
  have hlow : x.toNat % 2 ^ 56 = 0 := by
    have hb : ∀ i < 7, x.toNat / 2 ^ (8 * i) % 256 = 0 := by
      intro i hi
      have := h i hi
      rw [byte_eq] at this
      have := congrArg BitVec.toNat this
      simpa [BitVec.toNat_ofNat] using this
    have h0 := hb 0 (by decide); have h1 := hb 1 (by decide); have h2 := hb 2 (by decide)
    have h3 := hb 3 (by decide); have h4 := hb 4 (by decide); have h5 := hb 5 (by decide)
    have h6 := hb 6 (by decide)
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one] at h0
    omega
  have e := Nat.mod_add_div x.toNat (2 ^ 56)
  rw [hlow, Nat.zero_add] at e
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- The broadcast of a word whose low bytes are zero: its byte `7` in bytes `0 … 6`. -/
theorem byte_broadcast' {x : Word} (h : ∀ i < 7, byte x i = 0#8) {i : Nat} (hi : i < 7) :
    byte (mulhUU x 0x0101010101010100#64) i = byte x 7 := by
  have hx := eq_shl_of_low_zero h
  calc byte (mulhUU x 0x0101010101010100#64) i
      = byte (mulhUU ((x >>> 56) <<< 56) 0x0101010101010100#64) i := by rw [← hx]
    _ = byte (x >>> 56) 0 := byte_broadcast _ hi
    _ = byte x 7 := by
      have := byte_ushiftRight x (i := 0) (b := 7) (by decide)
      simpa using this

end NoCompiler.Typed.Bytes

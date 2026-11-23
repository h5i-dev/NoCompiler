import NoCompiler.Lib.Word

/-!
# Library: sign and zero extension

The values of `sext32`, `zext32`, `w32` (the 32-bit `*w` operations) and the sign-extending loads
(`lb`, `lh`, `lw`: `(BitVec.ofNat w k).signExtend 64`) as natural numbers: the value itself when
the sign bit is clear, the value plus `2^64 - 2^w` when it is set. Namespace `NoCompiler.Lib`.
Round 7, B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

/-- Sign extension from `w` bits of a value with the sign bit clear. -/
theorem toNat_signExtend_of_lt {w : Nat} (x : BitVec w) (hw : w ≤ 64) (h : x.toNat < 2 ^ (w - 1)) :
    (x.signExtend 64).toNat = x.toNat := by
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.msb_eq_decide]
  have hx := x.isLt
  have : x.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hw)
  simp [Nat.not_le.2 h, Nat.mod_eq_of_lt this]

/-- Sign extension from `w` bits of a value with the sign bit set. -/
theorem toNat_signExtend_of_ge {w : Nat} (x : BitVec w) (hw : w ≤ 64) (h : 2 ^ (w - 1) ≤ x.toNat) :
    (x.signExtend 64).toNat = x.toNat + (2 ^ 64 - 2 ^ w) := by
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.msb_eq_decide]
  have hx := x.isLt
  have : x.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hw)
  simp [h, Nat.mod_eq_of_lt this]

/-- A sign-extending load (`lb`, `lh`, `lw`) of a value with the sign bit clear. -/
theorem toNat_signExtend_ofNat_of_lt {w k : Nat} (hw : 0 < w) (hw' : w ≤ 64) (h : k < 2 ^ (w - 1)) :
    ((BitVec.ofNat w k).signExtend 64).toNat = k := by
  have hk : k < 2 ^ w := Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega))
  rw [toNat_signExtend_of_lt _ hw' (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]; exact h),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

/-- A sign-extending load of a value with the sign bit set. -/
theorem toNat_signExtend_ofNat_of_ge {w k : Nat} (hw' : w ≤ 64) (h : 2 ^ (w - 1) ≤ k)
    (hk : k < 2 ^ w) : ((BitVec.ofNat w k).signExtend 64).toNat = k + (2 ^ 64 - 2 ^ w) := by
  rw [toNat_signExtend_of_ge _ hw' (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]; exact h),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

/-- `sext32` of a word whose low half has the sign bit clear. -/
theorem toNat_sext32_of_lt (x : Word) (h : x.toNat % 2 ^ 32 < 2 ^ 31) :
    (sext32 x).toNat = x.toNat % 2 ^ 32 := by
  unfold sext32
  rw [toNat_signExtend_of_lt _ (by decide) (by simpa [BitVec.toNat_setWidth] using h),
    BitVec.toNat_setWidth]

/-- `sext32` of a word whose low half has the sign bit set. -/
theorem toNat_sext32_of_ge (x : Word) (h : 2 ^ 31 ≤ x.toNat % 2 ^ 32) :
    (sext32 x).toNat = x.toNat % 2 ^ 32 + (2 ^ 64 - 2 ^ 32) := by
  unfold sext32
  rw [toNat_signExtend_of_ge _ (by decide) (by simpa [BitVec.toNat_setWidth] using h),
    BitVec.toNat_setWidth]

/-- `sext32` leaves a word below 2^31 as it is. -/
theorem sext32_of_lt {x : Word} (h : x.toNat < 2 ^ 31) : sext32 x = x := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_sext32_of_lt x (by omega)]; omega

/-- `zext32` is the low half. -/
theorem toNat_zext32 (x : Word) : (zext32 x).toNat = x.toNat % 2 ^ 32 := by
  unfold zext32
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))

/-- `zext32` leaves a word below 2^32 as it is. -/
theorem zext32_of_lt {x : Word} (h : x.toNat < 2 ^ 32) : zext32 x = x := by
  apply BitVec.eq_of_toNat_eq; rw [toNat_zext32]; omega

/-- A 32-bit operation (`addw`, `subw`, ...) whose 32-bit result has the sign bit clear. -/
theorem toNat_w32_of_lt (f : BitVec 32 → BitVec 32 → BitVec 32) (x y : Word)
    (h : (f (x.setWidth 32) (y.setWidth 32)).toNat < 2 ^ 31) :
    (w32 f x y).toNat = (f (x.setWidth 32) (y.setWidth 32)).toNat :=
  toNat_signExtend_of_lt _ (by decide) h

/-- `addw` of two words whose low halves sum below 2^31. -/
theorem toNat_addw_of_lt (x y : Word) (h : x.toNat % 2 ^ 32 + y.toNat % 2 ^ 32 < 2 ^ 31) :
    (w32 (· + ·) x y).toNat = x.toNat % 2 ^ 32 + y.toNat % 2 ^ 32 := by
  have e : (x.setWidth 32 + y.setWidth 32).toNat = x.toNat % 2 ^ 32 + y.toNat % 2 ^ 32 := by
    rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_setWidth]; omega
  rw [toNat_w32_of_lt _ _ _ (by rw [e]; exact h), e]

end NoCompiler.Lib

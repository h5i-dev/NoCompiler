import NoCompiler.Lib.Bytes

/-!
# Library: words

Generic facts about 64-bit words (`Word := BitVec 64`) in the forms machine code produces them:
`toNat` of a sum or difference without wrap, unsigned comparisons as `toNat` comparisons, masks
as remainders, shifts by constants as multiplication and division, and alignment. Namespace
`NoCompiler.Lib`. Round 7, B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

/-! ## Sums and differences -/

/-- A sum that does not wrap. -/
theorem toNat_add_of_lt {x y : Word} (h : x.toNat + y.toNat < 2 ^ 64) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

/-- A word plus a constant that does not wrap. -/
theorem toNat_add_ofNat {x : Word} {k : Nat} (h : x.toNat + k < 2 ^ 64) :
    (x + BitVec.ofNat 64 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    Nat.mod_eq_of_lt h]

/-- A difference that does not wrap. -/
theorem toNat_sub_of_le {x y : Word} (h : y.toNat ≤ x.toNat) :
    (x - y).toNat = x.toNat - y.toNat := by
  rw [BitVec.toNat_sub]; have := x.isLt; have := y.isLt
  rw [show 2 ^ 64 - y.toNat + x.toNat = (x.toNat - y.toNat) + 2 ^ 64 by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- `a + k - a = k` for a constant. -/
theorem add_ofNat_sub_self (a : Word) (k : Nat) : a + BitVec.ofNat 64 k - a = BitVec.ofNat 64 k := by
  bv_omega

/-- Offsets add up. -/
theorem add_ofNat_add_ofNat (a : Word) (j k : Nat) :
    a + BitVec.ofNat 64 j + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (j + k) := by
  apply BitVec.eq_of_toNat_eq; simp; omega

theorem add_one_add_ofNat (a : Word) (k : Nat) :
    a + 1 + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (k + 1) := by
  apply BitVec.eq_of_toNat_eq; simp; omega

/-- Two offsets from the same base are equal exactly when the offsets are (below 2^64). -/
theorem add_ofNat_inj {a : Word} {j k : Nat} (hj : j < 2 ^ 64) (hk : k < 2 ^ 64) :
    a + BitVec.ofNat 64 j = a + BitVec.ofNat 64 k ↔ j = k := by
  constructor
  · intro h
    have := congrArg (fun x => (x - a).toNat) h
    simp only [add_ofNat_sub_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hk] at this
    exact this
  · rintro rfl; rfl

/-! ## Comparisons -/

theorem ult_iff (x y : Word) : BitVec.ult x y = decide (x.toNat < y.toNat) := by
  simp [BitVec.ult]

theorem ule_iff (x y : Word) : BitVec.ule x y = decide (x.toNat ≤ y.toNat) := by
  simp [BitVec.ule]

theorem lt_iff_toNat {x y : Word} : x < y ↔ x.toNat < y.toNat := BitVec.lt_def

theorem le_iff_toNat {x y : Word} : x ≤ y ↔ x.toNat ≤ y.toNat := BitVec.le_def

theorem eq_iff_toNat {x y : Word} : x = y ↔ x.toNat = y.toNat :=
  ⟨fun h => h ▸ rfl, BitVec.eq_of_toNat_eq⟩

theorem ne_iff_toNat {x y : Word} : x ≠ y ↔ x.toNat ≠ y.toNat := by
  rw [Ne, eq_iff_toNat]

/-- A word is zero exactly when its value is. -/
theorem eq_zero_iff (x : Word) : x = 0 ↔ x.toNat = 0 := by
  rw [eq_iff_toNat]; simp

/-- A constant below 2^64 has itself as value. -/
theorem toNat_ofNat_of_lt {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k).toNat = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Signed less-than of two words below 2^63 is unsigned less-than. -/
theorem slt_of_small {x y : Word} (hx : x.toNat < 2 ^ 63) (hy : y.toNat < 2 ^ 63) :
    BitVec.slt x y = decide (x.toNat < y.toNat) := by
  rw [BitVec.slt, BitVec.toInt_eq_toNat_of_lt (by omega), BitVec.toInt_eq_toNat_of_lt (by omega)]
  simp

/-! ## Masks and shifts -/

/-- A low mask is a remainder. -/
theorem and_mask (x : Word) (k : Nat) (hk : k ≤ 64) :
    (x &&& BitVec.ofNat 64 (2 ^ k - 1)).toNat = x.toNat % 2 ^ k := by
  have hp : 2 ^ k - 1 < 2 ^ 64 := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hk; omega
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp, Nat.and_two_pow_sub_one_eq_mod]

/-- Shifting left by a constant multiplies (below 2^64). -/
theorem toNat_shiftLeft (x : Word) (k : Nat) : (x <<< k).toNat = x.toNat * 2 ^ k % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- Shifting right by a constant divides. -/
theorem toNat_ushiftRight (x : Word) (k : Nat) : (x >>> k).toNat = x.toNat / 2 ^ k := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-! ## Alignment -/

theorem aligned_iff (a : Word) (n : Nat) : aligned a n ↔ a.toNat % n = 0 := Iff.rfl

/-- Adding a multiple of the alignment keeps it (when the sum does not wrap, or the alignment
    divides 2^64). -/
theorem aligned_add_ofNat {a : Word} {n k : Nat} (ha : aligned a n) (hk : k % n = 0)
    (hn : n ∣ 2 ^ 64) : aligned (a + BitVec.ofNat 64 k) n := by
  unfold aligned at *
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ hn, Nat.add_mod, ha,
    Nat.mod_mod_of_dvd _ hn, hk]
  simp

/-- Zero is aligned. -/
theorem aligned_zero (n : Nat) : aligned (0 : Word) n := by simp [aligned]

end NoCompiler.Lib

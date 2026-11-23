import NoCompiler.Auto
import NoCompiler.Lib.Bits

/-!
# Libc library: word arithmetic

Generic `BitVec 64` / byte lemmas used by the libc proofs (Examples/Libc): `ofNat` comparisons, sign
extensions of or-ed flags, bit tests, the byte and shift-merge facts of word copies, `bool64`. Moved from
A's files (QUEUE-D P1, lead 2026-11-22T12:16:41Z).
-/

namespace NoCompiler.Libc
open NoCompiler

-- from Examples/Libc/StdioWrite.lean
theorem sext_or_32 (x : BitVec 32) : (x.signExtend 64 ||| 32#64).toNat % 2 ^ 32 = (x ||| 32#32).toNat := by
  have h : ((x.signExtend 64 ||| 32#64).setWidth 32) = x ||| 32#32 := by
    ext i hi
    rw [BitVec.getElem_setWidth, BitVec.getLsbD_or, BitVec.getElem_or, BitVec.getLsbD_eq_getElem (by omega),
      BitVec.getElem_signExtend]
    simp only [hi, dite_true]
    congr 1
  rw [← h, BitVec.toNat_setWidth]

-- from Examples/Libc/StdioWrite.lean
theorem ofNat_ne_of_lt {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
  intro e; apply h
  have := congrArg BitVec.toNat e
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

-- from Examples/Libc/StdioWrite.lean
theorem ofNat_ne_neg_one {a : Nat} (ha : a < 2 ^ 63) : BitVec.ofNat 64 a ≠ -1 := by
  intro e
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
  simp at this; omega

-- from Examples/Libc/StdioWrite.lean
theorem slt_ofNat_zero {r : Nat} (h : r < 2 ^ 63) : (BitVec.ofNat 64 r).slt 0 = false := by
  simp only [BitVec.slt, BitVec.toInt, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]; simp; omega

-- from Examples/Libc/StdioWrite.lean
theorem ult_ofNat_false {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = false := by
  simp only [BitVec.ult, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega)]; simp; omega

-- from Examples/Libc/StdioWrite.lean
theorem ult_ofNat_true {a b : Nat} (h : a < b) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = true := by
  simp only [BitVec.ult, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hb]; simp; omega

-- from Examples/Libc/StdioWrite.lean
theorem ofNat_sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  have e : BitVec.ofNat 64 a = BitVec.ofNat 64 (a - b) + BitVec.ofNat 64 b := by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel h]
  rw [e, BitVec.add_sub_cancel]

-- from Examples/Libc/StdioWrite.lean
theorem bool64_false' : bool64 false = 0#64 := rfl

-- from Examples/Libc/StdioWrite.lean
theorem bool64_true' : bool64 true = 1#64 := rfl

-- from Examples/Libc/StdioWrite.lean
theorem add_ofNat_add (x : Word) (a b : Nat) : x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

-- from Examples/Libc/Memcpy.lean
/-- The `i`-th byte a store of `V` writes. -/
theorem byte_of_word (V : BitVec 64) (i : Nat) : BitVec.ofNat 8 (V.toNat >>> i) = (V >>> i).setWidth 8 := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ushiftRight]

/-! Byte arithmetic for the lemmas below, so that they need no `bv_decide` (B, round 7). -/

theorem toNat_append_byte {n : Nat} (x : BitVec n) (y : Byte) : (x ++ y).toNat = x.toNat * 256 + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

theorem toNat_word4 (b0 b1 b2 b3 : Byte) :
    ((b3 ++ b2 ++ b1 ++ b0).signExtend 64 : BitVec 64).toNat % 2 ^ 32 =
      b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat := by
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, toNat_append_byte, toNat_append_byte, toNat_append_byte]
  have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt
  split <;> simp <;> omega

theorem byte_of_word4 (V : BitVec 64) (b : Byte) (k : Nat) (hk : k < 4)
    (h : V.toNat % 2 ^ 32 / 256 ^ k % 256 = b.toNat) : (V >>> (8 * k)).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_mul]
  rw [← h]
  have e : (2 : Nat) ^ 8 = 256 := rfl
  rw [e]
  rcases k with _ | _ | _ | _ | k <;> simp <;> omega

theorem toNat_or_low (A y : Word) {s : Nat} (hy : y.toNat < 2 ^ s) (hA : A.toNat % 2 ^ s = 0) :
    (A ||| y).toNat = A.toNat + y.toNat := by
  rw [BitVec.toNat_or]
  have e : A.toNat = (A.toNat / 2 ^ s) <<< s := by
    rw [Nat.shiftLeft_eq]; exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hA)).symm
  rw [e, ← Nat.shiftLeft_add_eq_or_of_lt hy]

theorem shiftLeft_mod (X : Word) {s : Nat} (hs : s ≤ 64) : (X <<< s).toNat % 2 ^ s = 0 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hs), Nat.mul_mod_left]

theorem toNat_lo (W : Word) {r : Nat} (hr : 1 ≤ r) (hr' : r ≤ 32) :
    ((W.setWidth 32 >>> r).signExtend 64 : Word).toNat = W.toNat % 2 ^ 32 / 2 ^ r := by
  have hlt : (W.setWidth 32 >>> r).toNat < 2 ^ 31 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_setWidth]
    have : 2 ^ 32 ≤ 2 ^ 31 * 2 ^ r := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
    exact Nat.div_lt_of_lt_mul (by have := Nat.mod_lt W.toNat (Nat.two_pow_pos 32); omega)
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.msb_eq_decide]
  simp only [show ¬ (2 ^ (32 - 1) ≤ (W.setWidth 32 >>> r).toNat) by simpa using Nat.not_le.2 hlt, decide_false,
    Bool.false_eq_true, ite_false, Nat.add_zero]
  rw [Nat.mod_eq_of_lt (by omega), BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_setWidth]

-- from Examples/Libc/Memcpy.lean
/-- The bytes of a word copied as is (`lw`, `sw`). -/
theorem word_bytes (b0 b1 b2 b3 : Byte) :
    let V : BitVec 64 := (b3 ++ b2 ++ b1 ++ b0).signExtend 64
    V.setWidth 8 = b0 ∧ (V >>> 8).setWidth 8 = b1 ∧ (V >>> 16).setWidth 8 = b2 ∧ (V >>> 24).setWidth 8 = b3 := by
  intro V
  have hv := toNat_word4 b0 b1 b2 b3
  have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using byte_of_word4 V b0 0 (by decide) (by simp [V] at hv ⊢; omega)
  · exact byte_of_word4 V b1 1 (by decide) (by simp [V] at hv ⊢; omega)
  · exact byte_of_word4 V b2 2 (by decide) (by simp [V] at hv ⊢; omega)
  · exact byte_of_word4 V b3 3 (by decide) (by simp [V] at hv ⊢; omega)

-- from Examples/Libc/Memcpy.lean
/-- The byte copied by `lb`, `sb`. -/
theorem byte_byte (b : Byte) : ((BitVec.ofNat 8 b.toNat).signExtend 64 : BitVec 64).setWidth 8 = b := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  ext i hi
  rw [BitVec.getElem_setWidth, BitVec.getLsbD_eq_getElem (by omega), BitVec.getElem_signExtend]
  simp [hi]

-- from Examples/Libc/Memcpy.lean
/-- The shift merges of the misaligned loops: dest off by 1 (shift 8), 2 (16), 3 (24) from source words. -/
theorem merge8 (w0 w1 w2 w3 x0 x1 x2 x3 : Byte) :
    let W : BitVec 64 := (w3 ++ w2 ++ w1 ++ w0).signExtend 64
    let X : BitVec 64 := (x3 ++ x2 ++ x1 ++ x0).signExtend 64
    let V := (X <<< 8) ||| ((W.setWidth 32 >>> 24).signExtend 64)
    V.setWidth 8 = w3 ∧ (V >>> 8).setWidth 8 = x0 ∧ (V >>> 16).setWidth 8 = x1 ∧ (V >>> 24).setWidth 8 = x2 := by
  intro W X V
  have hW : W.toNat % 2 ^ 32 = w0.toNat + 256 * w1.toNat + 65536 * w2.toNat + 16777216 * w3.toNat :=
    toNat_word4 w0 w1 w2 w3
  have hX : X.toNat % 2 ^ 32 = x0.toNat + 256 * x1.toNat + 65536 * x2.toNat + 16777216 * x3.toNat :=
    toNat_word4 x0 x1 x2 x3
  have hlo := toNat_lo W (r := 24) (by decide) (by decide)
  have hV : V.toNat = (X <<< 8).toNat + (W.toNat % 2 ^ 32 / 2 ^ 24) := by
    rw [← hlo]; exact toNat_or_low _ _ (by rw [hlo]; omega) (shiftLeft_mod X (by decide))
  have hS : (X <<< 8).toNat = X.toNat * 2 ^ 8 % 2 ^ 64 := by rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have := w0.isLt; have := w1.isLt; have := w2.isLt; have := w3.isLt
  have := x0.isLt; have := x1.isLt; have := x2.isLt; have := x3.isLt
  have hV32 : V.toNat % 2 ^ 32 = w3.toNat + 256 * x0.toNat + 65536 * x1.toNat + 16777216 * x2.toNat := by
    rw [hV, hS]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using byte_of_word4 V w3 0 (by decide) (by simp; omega)
  · exact byte_of_word4 V x0 1 (by decide) (by simp; omega)
  · exact byte_of_word4 V x1 2 (by decide) (by simp; omega)
  · exact byte_of_word4 V x2 3 (by decide) (by simp; omega)

-- from Examples/Libc/Memcpy.lean
theorem merge16 (w0 w1 w2 w3 x0 x1 x2 x3 : Byte) :
    let W : BitVec 64 := (w3 ++ w2 ++ w1 ++ w0).signExtend 64
    let X : BitVec 64 := (x3 ++ x2 ++ x1 ++ x0).signExtend 64
    let V := (X <<< 16) ||| ((W.setWidth 32 >>> 16).signExtend 64)
    V.setWidth 8 = w2 ∧ (V >>> 8).setWidth 8 = w3 ∧ (V >>> 16).setWidth 8 = x0 ∧ (V >>> 24).setWidth 8 = x1 := by
  intro W X V
  have hW : W.toNat % 2 ^ 32 = w0.toNat + 256 * w1.toNat + 65536 * w2.toNat + 16777216 * w3.toNat :=
    toNat_word4 w0 w1 w2 w3
  have hX : X.toNat % 2 ^ 32 = x0.toNat + 256 * x1.toNat + 65536 * x2.toNat + 16777216 * x3.toNat :=
    toNat_word4 x0 x1 x2 x3
  have hlo := toNat_lo W (r := 16) (by decide) (by decide)
  have hV : V.toNat = (X <<< 16).toNat + (W.toNat % 2 ^ 32 / 2 ^ 16) := by
    rw [← hlo]; exact toNat_or_low _ _ (by rw [hlo]; omega) (shiftLeft_mod X (s := 16) (by decide))
  have hS : (X <<< 16).toNat = X.toNat * 2 ^ 16 % 2 ^ 64 := by rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have := w0.isLt; have := w1.isLt; have := w2.isLt; have := w3.isLt
  have := x0.isLt; have := x1.isLt; have := x2.isLt; have := x3.isLt
  have hV32 : V.toNat % 2 ^ 32 = w2.toNat + 256 * w3.toNat + 65536 * x0.toNat + 16777216 * x1.toNat := by
    rw [hV, hS]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using byte_of_word4 V w2 0 (by decide) (by simp; omega)
  · exact byte_of_word4 V w3 1 (by decide) (by simp; omega)
  · exact byte_of_word4 V x0 2 (by decide) (by simp; omega)
  · exact byte_of_word4 V x1 3 (by decide) (by simp; omega)

-- from Examples/Libc/Memcpy.lean
theorem merge24 (w0 w1 w2 w3 x0 x1 x2 x3 : Byte) :
    let W : BitVec 64 := (w3 ++ w2 ++ w1 ++ w0).signExtend 64
    let X : BitVec 64 := (x3 ++ x2 ++ x1 ++ x0).signExtend 64
    let V := (X <<< 24) ||| ((W.setWidth 32 >>> 8).signExtend 64)
    V.setWidth 8 = w1 ∧ (V >>> 8).setWidth 8 = w2 ∧ (V >>> 16).setWidth 8 = w3 ∧ (V >>> 24).setWidth 8 = x0 := by
  intro W X V
  have hW : W.toNat % 2 ^ 32 = w0.toNat + 256 * w1.toNat + 65536 * w2.toNat + 16777216 * w3.toNat :=
    toNat_word4 w0 w1 w2 w3
  have hX : X.toNat % 2 ^ 32 = x0.toNat + 256 * x1.toNat + 65536 * x2.toNat + 16777216 * x3.toNat :=
    toNat_word4 x0 x1 x2 x3
  have hlo := toNat_lo W (r := 8) (by decide) (by decide)
  have hV : V.toNat = (X <<< 24).toNat + (W.toNat % 2 ^ 32 / 2 ^ 8) := by
    rw [← hlo]; exact toNat_or_low _ _ (by rw [hlo]; omega) (shiftLeft_mod X (s := 24) (by decide))
  have hS : (X <<< 24).toNat = X.toNat * 2 ^ 24 % 2 ^ 64 := by rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have := w0.isLt; have := w1.isLt; have := w2.isLt; have := w3.isLt
  have := x0.isLt; have := x1.isLt; have := x2.isLt; have := x3.isLt
  have hV32 : V.toNat % 2 ^ 32 = w1.toNat + 256 * w2.toNat + 65536 * w3.toNat + 16777216 * x0.toNat := by
    rw [hV, hS]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using byte_of_word4 V w1 0 (by decide) (by simp; omega)
  · exact byte_of_word4 V w2 1 (by decide) (by simp; omega)
  · exact byte_of_word4 V w3 2 (by decide) (by simp; omega)
  · exact byte_of_word4 V x0 3 (by decide) (by simp; omega)

-- from Examples/Libc/Memcpy.lean
theorem and_bitK (x : Word) (b : Nat) (hb : b < 64) (hm : BitVec.twoPow 64 b ≠ 0) :
    (x &&& BitVec.twoPow 64 b = 0) ↔ x.toNat / 2 ^ b % 2 = 0 := by
  rw [BitVec.and_twoPow]
  split
  · rename_i h
    rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq] at h
    simp only [decide_eq_true_eq] at h
    constructor
    · intro e; exact absurd e hm
    · intro e; omega
  · rename_i h
    rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq] at h
    simp only [decide_eq_true_eq] at h
    constructor
    · intro _; omega
    · intro _; rfl

-- from Examples/Libc/Memcpy.lean
theorem and_bit1 (x : Word) : (x &&& 1#64 = 0) ↔ x.toNat % 2 = 0 := by
  rw [show (1#64 : Word) = BitVec.twoPow 64 0 by decide]; have := and_bitK x 0 (by omega) (by decide); simpa using this

-- from Examples/Libc/Memcpy.lean
theorem and_bit2 (x : Word) : (x &&& 2#64 = 0) ↔ x.toNat / 2 % 2 = 0 := by
  rw [show (2#64 : Word) = BitVec.twoPow 64 1 by decide]; have := and_bitK x 1 (by omega) (by decide); simpa using this

-- from Examples/Libc/Memcpy.lean
theorem and_bit4 (x : Word) : (x &&& 4#64 = 0) ↔ x.toNat / 4 % 2 = 0 := by
  rw [show (4#64 : Word) = BitVec.twoPow 64 2 by decide]; have := and_bitK x 2 (by omega) (by decide); simpa using this

-- from Examples/Libc/Memcpy.lean
theorem and_bit8 (x : Word) : (x &&& 8#64 = 0) ↔ x.toNat / 8 % 2 = 0 := by
  rw [show (8#64 : Word) = BitVec.twoPow 64 3 by decide]; have := and_bitK x 3 (by omega) (by decide); simpa using this

-- from Examples/Libc/Memcpy.lean
theorem and_bit16 (x : Word) : (x &&& 16#64 = 0) ↔ x.toNat / 16 % 2 = 0 := by
  rw [show (16#64 : Word) = BitVec.twoPow 64 4 by decide]; have := and_bitK x 4 (by omega) (by decide); simpa using this

-- from Examples/Libc/Memcpy.lean
theorem bne_of_bit {x m : Word} (h : x &&& m ≠ 0) : (x &&& m != 0) = true := by simpa using h

-- from Examples/Libc/Memcpy.lean
theorem bne_of_nbit {x m : Word} (h : x &&& m = 0) : (x &&& m != 0) = false := by simpa using h

-- from Examples/Libc/Memcpy.lean
theorem beq_of_bit {x m : Word} (h : x &&& m ≠ 0) : (x &&& m == 0) = false := by simpa using h

-- from Examples/Libc/Memcpy.lean
theorem beq_of_nbit {x m : Word} (h : x &&& m = 0) : (x &&& m == 0) = true := by simpa using h

-- from Examples/Libc/Memcpy.lean
theorem add_ofNat_assoc (a : Word) (c j : Nat) : a + BitVec.ofNat 64 c + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (c + j) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

-- from Examples/Libc/Memcpy.lean
theorem and3_mod (x : BitVec 64) : (x &&& 3#64).toNat = x.toNat % 4 := by
  rw [BitVec.toNat_and]
  have : (3#64 : BitVec 64).toNat = 2 ^ 2 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

-- from Examples/Libc/Memcpy.lean
theorem al_of_mod (d : Word) (c j : Nat) (h : (d + BitVec.ofNat 64 c).toNat % 4 + j = 4) :
    aligned (d + BitVec.ofNat 64 (c + j)) 4 := by
  rw [← add_ofNat_assoc]; unfold aligned; bv_omega

-- from Examples/Libc/Memcpy.lean
theorem and3_beq (x : Word) (j : Nat) (hj : j < 4) : (x &&& 3#64 == BitVec.ofNat 64 j) = decide (x.toNat % 4 = j) := by
  by_cases h : x.toNat % 4 = j
  · simp only [h, decide_true, beq_iff_eq]; apply BitVec.eq_of_toNat_eq; rw [and3_mod, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]; intro e
    apply h; have := congrArg BitVec.toNat e; rw [and3_mod, BitVec.toNat_ofNat] at this; omega

-- from Examples/Libc/Memcpy.lean
theorem and3_eq0 (x : Word) : (x &&& 3#64 == 0) = decide (x.toNat % 4 = 0) := by
  have := and3_beq x 0 (by omega); simpa using this

-- from Examples/Libc/Memcpy.lean
theorem bool64_or_ne (a b : Bool) : (bool64 a ||| bool64 b != 0) = (a || b) := by cases a <;> cases b <;> decide

-- from Examples/Libc/Memcpy.lean
theorem bool64_and_ne (a b : Bool) : (bool64 a &&& bool64 b != 0) = (a && b) := by cases a <;> cases b <;> decide

-- from Examples/Libc/Memcpy.lean
theorem ult_and3_one (x : Word) : BitVec.ult (x &&& 3#64) 1#64 = decide (x.toNat % 4 = 0) := by
  simp only [BitVec.ult, and3_mod]; have : (1#64 : Word).toNat = 1 := rfl; rw [this]; by_cases h : x.toNat % 4 = 0 <;> simp [h] <;> omega

-- from Examples/Libc/Memcpy.lean
theorem ult_one (x : Word) : BitVec.ult x 1#64 = decide (x.toNat = 0) := by
  simp only [BitVec.ult]; have : (1#64 : Word).toNat = 1 := rfl; rw [this]; by_cases h : x.toNat = 0 <;> simp [h] <;> omega

-- from Examples/Libc/Memcpy.lean
theorem ult_zero_and3 (x : Word) : BitVec.ult (0 : Word) (x &&& 3#64) = decide (x.toNat % 4 ≠ 0) := by
  simp only [BitVec.ult, and3_mod]; have : (0 : Word).toNat = 0 := rfl; rw [this]; by_cases h : x.toNat % 4 = 0 <;> simp [h] <;> omega

-- from Examples/Libc/Memcpy.lean
theorem ult_zero' (x : Word) : BitVec.ult (0 : Word) x = decide (x.toNat ≠ 0) := by
  simp only [BitVec.ult]; have : (0 : Word).toNat = 0 := rfl; rw [this]; by_cases h : x.toNat = 0 <;> simp [h] <;> omega

/-! ## Bit facts of the libc paths, without `bv_decide` (B, round 9): masks, sign extensions, shifts -/

theorem sext_or_16_setWidth (x : BitVec 32) : ((x.signExtend 64 ||| 16#64).setWidth 32) = x ||| 16#32 := by
  ext i hi
  rw [BitVec.getElem_setWidth, BitVec.getLsbD_or, BitVec.getElem_or, BitVec.getLsbD_eq_getElem (by omega),
    BitVec.getElem_signExtend]
  simp only [hi, dite_true]
  congr 1

theorem ofNat8_signExtend_toNat (b : BitVec 8) : BitVec.ofNat 8 ((BitVec.ofNat 8 b.toNat).signExtend 64).toNat = b := by
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  ext i hi
  rw [BitVec.getElem_setWidth, BitVec.getLsbD_eq_getElem (by omega), BitVec.getElem_signExtend]
  simp [hi]

theorem and_mask16_umod16 (sp : Word) : (sp &&& 0xfffffffffffffff0#64) % 16#64 = 0#64 := by
  have e : (0xfffffffffffffff0#64 : Word) = ~~~BitVec.ofNat 64 (2 ^ 4 - 1) := by decide
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, e, Lib.toNat_and_not_mask sp (by decide)]
  simp; omega

theorem and_mask16_of_mod {x : Word} (h : x.toNat % 16 = 0) : x &&& 0xfffffffffffffff0#64 = x := by
  have e : (0xfffffffffffffff0#64 : Word) = ~~~BitVec.ofNat 64 (2 ^ 4 - 1) := by decide
  apply BitVec.eq_of_toNat_eq
  rw [e, Lib.toNat_and_not_mask x (by decide)]
  simp; omega

theorem shl2_add_shl1 (q : Word) : ((q <<< 2) + q) <<< 1 = q * 10#64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_mul, Nat.shiftLeft_eq]
  simp; omega

theorem ofNat_or_and4_eq_zero (r : Nat) (hr : r < 2 ^ 32) (c : BitVec 32) (hc : c &&& 4#32 = 0) (h : BitVec.ofNat 64 r &&& 4#64 = 0) :
    BitVec.ofNat 64 (BitVec.ofNat 32 r ||| c).toNat &&& 4#64 = 0 := by
  have h' := congrArg BitVec.toNat h
  have hc' := congrArg BitVec.toNat hc
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_ofNat] at h' hc' ⊢
  rw [Nat.mod_eq_of_lt (by omega : r < 2 ^ 64)] at h'
  rw [Nat.mod_eq_of_lt hr]
  have hor : (r ||| c.toNat) < 2 ^ 64 := Nat.lt_of_lt_of_le (Nat.or_lt_two_pow (by omega) (by have := c.isLt; omega)) (by decide)
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.or_lt_two_pow hr c.isLt) (by decide)), Nat.and_or_distrib_right]
  simp_all

theorem sshiftRight_shl59_getElem (x : Word) (i : Nat) (hi : i < 64) : ((x <<< 59).sshiftRight 63)[i] = x[4] := by
  rw [BitVec.getElem_sshiftRight]
  split
  · obtain rfl : i = 0 := by omega
    rw [BitVec.getElem_shiftLeft]; simp
  · rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft]; simp

theorem and16_eq_zero_iff (x : Word) : x &&& 16#64 = 0 ↔ x[4] = false := by
  constructor
  · intro h
    have := congrArg (fun y : Word => y[4]) h
    simpa using this
  · intro h
    ext i hi
    rw [BitVec.getElem_and]
    by_cases e : i = 4
    · subst e; simp [h]
    · rw [BitVec.getElem_eq_testBit_toNat (16#64), BitVec.toNat_ofNat,
        show (16 : Nat) % 2 ^ 64 = 2 ^ 4 by decide, Nat.testBit_two_pow]
      simp [Ne.symm e]

theorem sshiftRight_shl59 (x : Word) : (x <<< 59).sshiftRight 63 = (if x &&& 16#64 = 0 then 0 else -1) := by
  split <;> rename_i h
  · ext i hi; rw [sshiftRight_shl59_getElem x i hi, (and16_eq_zero_iff x).1 h]; simp
  · ext i hi
    rw [sshiftRight_shl59_getElem x i hi]
    have : x[4] = true := by
      cases e : x[4]
      · exact absurd ((and16_eq_zero_iff x).2 e) h
      · rfl
    rw [this, show (-1 : Word) = BitVec.allOnes 64 by decide, BitVec.getElem_allOnes]

end NoCompiler.Libc

import NoCompiler.Machine

/-
Bytes of words, for value invariants on top of the type check (docs/typed/value-tracker.md):
byte `i` of a shifted word, of an `or`, and of a loaded value.
-/

namespace NoCompiler.Typed.Bytes
open NoCompiler

/-- Byte `i` (little-endian) of a word. -/
def byte (w : Word) (i : Nat) : Byte := (w >>> (8 * i)).setWidth 8

theorem byte_shiftLeft (w : Word) {i b : Nat} (hi : i < 8) :
    byte (w <<< (8 * b)) i = if i < b then 0#8 else byte w (i - b) := by
  unfold byte
  split
  · ext j hj
    simp
    intro _ _; omega
  · ext j hj
    simp
    have e : 8 * i + j - 8 * b = 8 * (i - b) + j := by omega
    have h1 : 8 * i + j < 64 := by omega
    have h2 : ¬ 8 * i + j < 8 * b := by omega
    simp [e, h1, h2]

theorem byte_ushiftRight (w : Word) {i b : Nat} (hi : i < 8) :
    byte (w >>> (8 * b)) i = if i + b < 8 then byte w (i + b) else 0#8 := by
  unfold byte
  split
  · ext j hj
    simp
    have e : 8 * b + (8 * i + j) = 8 * (i + b) + j := by omega
    simp [e]
  · ext j hj
    simp
    exact BitVec.getLsbD_of_ge w _ (by omega)

theorem byte_or (x y : Word) (i : Nat) : byte (x ||| y) i = byte x i ||| byte y i := by
  unfold byte
  ext j hj
  simp

theorem byte_or_zero_left {x y : Word} {i : Nat} (h : byte x i = 0#8) :
    byte (x ||| y) i = byte y i := by rw [byte_or, h]; simp

theorem byte_or_zero_right {x y : Word} {i : Nat} (h : byte y i = 0#8) :
    byte (x ||| y) i = byte x i := by rw [byte_or, h]; simp

end NoCompiler.Typed.Bytes

namespace NoCompiler.Typed.Bytes
open NoCompiler

theorem byte_eq (w : Word) (i : Nat) : byte w i = BitVec.ofNat 8 (w.toNat / 2 ^ (8 * i)) := by
  apply BitVec.eq_of_toNat_eq
  simp [byte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem readLE_lt (m : Word → Byte) (a : Word) : ∀ n, readLE m a n < 256 ^ n
  | 0 => by simp [readLE]
  | n + 1 => by
    have := readLE_lt m (a + 1) n
    have := (m a).isLt
    simp only [readLE, Nat.pow_succ]; omega

theorem readLE_digit (m : Word → Byte) : ∀ (n : Nat) (a : Word) (i : Nat), i < n →
    readLE m a n / 256 ^ i % 256 = (m (a + BitVec.ofNat 64 i)).toNat
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, a, 0, _ => by
    have := (m a).isLt
    have e0 : a + BitVec.ofNat 64 0 = a := by simp
    rw [e0]
    simp only [readLE, Nat.pow_zero, Nat.div_one]
    omega
  | n + 1, a, i + 1, h => by
    have ih := readLE_digit m n (a + 1) i (by omega)
    have hb := (m a).isLt
    have e : readLE m a (n + 1) / 256 ^ (i + 1) = readLE m (a + 1) n / 256 ^ i := by
      rw [show readLE m a (n + 1) = (m a).toNat + 256 * readLE m (a + 1) n from rfl, Nat.pow_succ,
        Nat.mul_comm (256 ^ i) 256, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by decide),
        Nat.div_eq_of_lt hb, Nat.zero_add]
    rw [e, ih]
    congr 2
    bv_omega

theorem byte_ofNat_readLE (m : Word → Byte) (a : Word) {n i : Nat} (hn : n ≤ 8) (hi : i < n) :
    byte (BitVec.ofNat 64 (readLE m a n)) i = m (a + BitVec.ofNat 64 i) := by
  have hlt := readLE_lt m a n
  have h64 : 256 ^ n ≤ 2 ^ 64 := by
    calc 256 ^ n ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) hn
      _ = 2 ^ 64 := by decide
  rw [byte_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e : (2 : Nat) ^ (8 * i) = 256 ^ i := by rw [Nat.pow_mul]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, e]
  exact readLE_digit m n a i hi

end NoCompiler.Typed.Bytes

namespace NoCompiler.Typed.Bytes
open NoCompiler

theorem byte_signExtend8 (x : BitVec 8) : byte (x.signExtend 64) 0 = x := by
  unfold byte
  ext j hj
  simp [BitVec.getLsbD_signExtend, hj]
  omega

theorem byte_signExtend32 (y : BitVec 32) {i : Nat} (hi : i < 4) :
    byte (y.signExtend 64) i = byte (y.setWidth 64) i := by
  unfold byte
  ext j hj
  have h : 8 * i + j < 32 := by omega
  simp [BitVec.getLsbD_signExtend, h]

theorem setWidth_ofNat32 {X : Nat} (hX : X < 2 ^ 32) :
    (BitVec.ofNat 32 X).setWidth 64 = BitVec.ofNat 64 X := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hX]

/-- `srliw` by `8b` (b ≥ 1): the low word's bytes shift down and the upper word is zero. -/
theorem byte_srliw (x : Word) {i b : Nat} (hi : i < 8) (hb : 1 ≤ b) (hb4 : b ≤ 3) :
    byte (((x.setWidth 32) >>> (8 * b)).signExtend 64) i =
      if i + b < 4 then byte x (i + b) else 0#8 := by
  unfold byte
  split
  · ext j hj
    simp [BitVec.getLsbD_signExtend, hj]
    have e : 8 * b + (8 * i + j) = 8 * (i + b) + j := by omega
    have h1 : 8 * i + j < 32 := by omega
    have h2 : 8 * (i + b) + j < 32 := by omega
    simp [h1, h2, e]
    intro _; omega
  · ext j hj
    simp [BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last]
    intro _
    split <;> (intro h; omega)

theorem writeLE_apply (m : Word → Byte) (a : Word) (v : Nat) {n : Nat} (hn : n < 2 ^ 64) (p : Word) :
    writeLE m a v n p = if (p - a).toNat < n then BitVec.ofNat 8 (v / 256 ^ (p - a).toNat) else m p := by
  induction n generalizing a v with
  | zero => simp [writeLE]
  | succ n ih =>
    by_cases hpa : p = a
    · subst hpa; simp [writeLE]
    · simp only [writeLE, hpa, ite_false]
      rw [ih (a + 1) (v / 256) (by omega)]
      have hs : (p - (a + 1)).toNat + 1 = (p - a).toNat := by
        have : (p - a).toNat ≠ 0 := by
          intro h; apply hpa; have := BitVec.eq_of_toNat_eq (x := p - a) (y := 0) (by simpa using h); bv_omega
        have e : p - (a + 1) = (p - a) - 1 := by bv_omega
        rw [e]; bv_omega
      by_cases h1 : (p - (a + 1)).toNat < n
      · rw [if_pos h1, if_pos (by omega), ← hs, Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
      · rw [if_neg h1, if_neg (by omega)]

end NoCompiler.Typed.Bytes

import NoCompiler.Lib.Ret

/-!
# Library: little-endian values

`readLE m a n` as a number: the bytes split at any point (`j + k` bytes are the first `j` and
`256^j` times the rest), the first byte and the rest, and the loads `read8/16/32/64` as the value
read (it fits, so `toNat` is the value itself), with `read64` split into its 32-bit halves and
`read32` / `read8` as the low bytes of a wider read. Namespace `NoCompiler.Lib`. Round 7, B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

/-- One byte, then the rest. -/
theorem readLE_succ' (m : Word → Byte) (a : Word) (n : Nat) :
    readLE m a (n + 1) = (m a).toNat + 256 * readLE m (a + 1) n := rfl

/-- `j + k` bytes: the first `j`, then `256^j` times the next `k`. -/
theorem readLE_add (m : Word → Byte) (a : Word) (j k : Nat) :
    readLE m a (j + k) = readLE m a j + 256 ^ j * readLE m (a + BitVec.ofNat 64 j) k := by
  induction j generalizing a with
  | zero => simp [readLE]
  | succ j ih =>
    rw [show j + 1 + k = (j + k) + 1 by omega, readLE_succ', ih (a + 1), readLE_succ',
      show a + 1 + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (j + 1) by
        apply BitVec.eq_of_toNat_eq; simp; omega, Nat.pow_succ]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 256 (256 ^ j), Nat.add_assoc]

/-- One byte read is the byte. -/
theorem readLE_one (m : Word → Byte) (a : Word) : readLE m a 1 = (m a).toNat := by
  simp [readLE]

private theorem toNat_ofNat_readLE (m : Word → Byte) (a : Word) {n : Nat} (hn : n ≤ 8) :
    (BitVec.ofNat 64 (readLE m a n)).toNat = readLE m a n := by
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_lt_of_le (readLE_lt m a n)
    (by have := Nat.pow_le_pow_right (by decide : 0 < 256) hn; simpa using this)

/-- The value of a load is the bytes read. -/
theorem toNat_read64 (m : Word → Byte) (a : Word) : (read64 m a).toNat = readLE m a 8 :=
  toNat_ofNat_readLE m a (by decide)
theorem toNat_read32 (m : Word → Byte) (a : Word) : (read32 m a).toNat = readLE m a 4 :=
  toNat_ofNat_readLE m a (by decide)
theorem toNat_read16 (m : Word → Byte) (a : Word) : (read16 m a).toNat = readLE m a 2 :=
  toNat_ofNat_readLE m a (by decide)
theorem toNat_read8 (m : Word → Byte) (a : Word) : (read8 m a).toNat = (m a).toNat := by
  rw [show (read8 m a).toNat = readLE m a 1 from toNat_ofNat_readLE m a (by decide), readLE_one]

/-- A 64-bit load is its low 32-bit half plus `2^32` times its high half. -/
theorem toNat_read64_halves (m : Word → Byte) (a : Word) :
    (read64 m a).toNat = (read32 m a).toNat + 2 ^ 32 * (read32 m (a + BitVec.ofNat 64 4)).toNat := by
  rw [toNat_read64, toNat_read32, toNat_read32, show (8 : Nat) = 4 + 4 from rfl, readLE_add]

/-- The low `j` bytes of a wider read: the read modulo `256^j`. -/
theorem readLE_mod (m : Word → Byte) (a : Word) {j k : Nat} :
    readLE m a (j + k) % 256 ^ j = readLE m a j := by
  rw [readLE_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (readLE_lt m a j)]

/-- The low half of a 64-bit load is the 32-bit load at the same address. -/
theorem read64_mod_2_32 (m : Word → Byte) (a : Word) :
    (read64 m a).toNat % 2 ^ 32 = (read32 m a).toNat := by
  rw [toNat_read64, toNat_read32, show (8 : Nat) = 4 + 4 from rfl,
    show (2 : Nat) ^ 32 = 256 ^ 4 from rfl, readLE_mod]

/-- A word is zero exactly when all the bytes of its load are. -/
theorem readLE_eq_zero_iff (m : Word → Byte) (a : Word) (n : Nat) :
    readLE m a n = 0 ↔ ∀ i, i < n → m (a + BitVec.ofNat 64 i) = 0 := by
  induction n generalizing a with
  | zero => simp [readLE]
  | succ n ih =>
    rw [readLE_succ']
    constructor
    · intro h i hi
      have h0 : (m a).toNat = 0 := by omega
      have hr : readLE m (a + 1) n = 0 := by omega
      cases i with
      | zero => simpa using BitVec.eq_of_toNat_eq (by simpa using h0)
      | succ i =>
        have := (ih (a + 1)).1 hr i (by omega)
        rwa [show a + 1 + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (i + 1) by
          apply BitVec.eq_of_toNat_eq; simp; omega] at this
    · intro h
      have h0 : m a = 0 := by simpa using h 0 (by omega)
      have hr : readLE m (a + 1) n = 0 := (ih (a + 1)).2 fun i hi => by
        rw [show a + 1 + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (i + 1) by
          apply BitVec.eq_of_toNat_eq; simp; omega]
        exact h (i + 1) (by omega)
      rw [h0, hr]; rfl

end NoCompiler.Lib

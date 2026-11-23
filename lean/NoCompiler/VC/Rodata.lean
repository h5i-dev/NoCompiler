import NoCompiler.Image

/-!
# Reading a loaded segment at a constant address

A segment as the chunk export writes it is `Segment.bytesOfNat len bits`: one number literal for all
its bytes. Under `Segment.Loaded` (a precondition: what the loader establishes), `n` bytes read at a
constant address inside it are a number computed from `bits` alone,
`(bits >>> (8 * o)) % 2 ^ (8 * n)` with `o` the address's offset: arithmetic on literals the kernel
does natively (GMP), without evaluating the segment's byte array.
-/
namespace NoCompiler.VC.M
open NoCompiler

theorem toNat_bytesOfNat_get {len bits i : Nat} (h : i < (Segment.bytesOfNat len bits).size) :
    ((Segment.bytesOfNat len bits)[i]).toNat = (bits >>> (8 * i)) % 256 := by
  simp [Segment.bytesOfNat, BitVec.toNat_ofNat]

/-- `n` bytes at offset `o` of a loaded `bytesOfNat` segment. -/
theorem readLE_bytesOfNat {nm : String} {base : Word} {len bits : Nat} {w : Bool} {m : Word → Byte}
    (h : (Segment.mk nm base (Segment.bytesOfNat len bits) w).Loaded m) :
    ∀ (n o : Nat), o + n ≤ len →
      readLE m (base + BitVec.ofNat 64 o) n = (bits >>> (8 * o)) % 2 ^ (8 * n) := by
  intro n
  induction n with
  | zero => intro o _; simp [readLE, Nat.mod_one]
  | succ n ih =>
    intro o hon
    have ho : o < (Segment.bytesOfNat len bits).size := by simp; omega
    have e : base + BitVec.ofNat 64 o + 1 = base + BitVec.ofNat 64 (o + 1) := by
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [Nat.add_mod]
    simp only [readLE]
    rw [h o ho, toNat_bytesOfNat_get ho, e, ih (o + 1) (by omega)]
    have hs : bits >>> (8 * (o + 1)) = (bits >>> (8 * o)) / 256 := by
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]
      congr 1
      rw [show 8 * (o + 1) = 8 * o + 8 by omega, Nat.pow_add]
    rw [hs, show 8 * (n + 1) = 8 + 8 * n by omega, Nat.pow_add,
      show (2 : Nat) ^ 8 = 256 by rfl, Nat.mod_mul]

/-- The same at an address given as a word: its offset from the segment's base (inside it). -/
theorem readLE_seg {nm : String} {base : Word} {len bits : Nat} {w : Bool} {m : Word → Byte}
    (h : (Segment.mk nm base (Segment.bytesOfNat len bits) w).Loaded m) {a : Word} {n : Nat}
    (hr : base.toNat ≤ a.toNat ∧ a.toNat - base.toNat + n ≤ len) :
    readLE m a n = (bits >>> (8 * (a.toNat - base.toNat))) % 2 ^ (8 * n) := by
  have ha : a = base + BitVec.ofNat 64 (a.toNat - base.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have := a.isLt
    rw [Nat.mod_eq_of_lt (by omega : a.toNat - base.toNat < 2 ^ 64)]
    rw [show base.toNat + (a.toNat - base.toNat) = a.toNat by omega, Nat.mod_eq_of_lt a.isLt]
  conv => lhs; rw [ha]
  exact readLE_bytesOfNat h n _ hr.2

end NoCompiler.VC.M

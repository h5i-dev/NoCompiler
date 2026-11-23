import NoCompiler.Lib.Range

/-!
# Library: copy and fill loops

The invariant step of a loop that copies (`memcpy`, `strcpy`) or fills (`memset`) one byte per
iteration: if the first `k` bytes at `d` are the first `k` of the source, storing byte `k` makes
the first `k + 1`; the same with a constant byte for a fill. The write lands past the part
already done, so that part stays. Namespace `NoCompiler.Lib`. Round 7, B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

/-- A one-byte store, read back. -/
theorem writeLE_one_self (m : Word → Byte) (a : Word) (b : Byte) :
    writeLE m a b.toNat 1 a = b := by
  show (if a = a then BitVec.ofNat 8 b.toNat else _) = b
  simp

/-- A store at `d + k` leaves the `k` bytes before it. -/
theorem readBytes_writeLE_past (m : Word → Byte) (d : Word) {k v n : Nat} (hn : 0 < n)
    (hk : k + n ≤ 2 ^ 64) :
    readBytes (writeLE m (d + BitVec.ofNat 64 k) v n) d k = readBytes m d k := by
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0; rfl
  · have hd := disjoint_base_field (b := d) (k := k) (j := k) (n := n) h0 hn hk (Nat.le_refl _)
    exact readBytes_writeLE_disjoint hd.symm

/-- The copy loop's step. -/
theorem copy_step {m m0 : Word → Byte} {d s : Word} {k : Nat} (hk : k + 1 ≤ 2 ^ 64)
    (hdone : readBytes m d k = readBytes m0 s k) (hsrc : m (s + BitVec.ofNat 64 k) = m0 (s + BitVec.ofNat 64 k)) :
    readBytes (writeLE m (d + BitVec.ofNat 64 k) (m (s + BitVec.ofNat 64 k)).toNat 1) d (k + 1) =
      readBytes m0 s (k + 1) := by
  rw [readBytes_snoc, readBytes_snoc, readBytes_writeLE_past m d (by decide) hk, hdone,
    writeLE_one_self, hsrc]

/-- The fill loop's step. -/
theorem fill_step {m : Word → Byte} {d : Word} {k : Nat} {v : Byte} (hk : k + 1 ≤ 2 ^ 64)
    (hdone : readBytes m d k = List.replicate k v) :
    readBytes (writeLE m (d + BitVec.ofNat 64 k) v.toNat 1) d (k + 1) = List.replicate (k + 1) v := by
  rw [readBytes_snoc, readBytes_writeLE_past m d (by decide) hk, hdone, writeLE_one_self,
    List.replicate_succ']

/-- The copy loop's start: nothing copied yet. -/
theorem copy_start (m m0 : Word → Byte) (d s : Word) : readBytes m d 0 = readBytes m0 s 0 := rfl

/-- The fill loop's start. -/
theorem fill_start (m : Word → Byte) (d : Word) (v : Byte) : readBytes m d 0 = List.replicate 0 v := rfl

end NoCompiler.Lib

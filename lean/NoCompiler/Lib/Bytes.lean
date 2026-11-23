import NoCompiler.Lib.Region
import NoCompiler.Trace

/-!
# Library: bytes in memory

Generic facts about `readLE`, `readBytes`, `writeLE`, `writeBytes` (Machine.lean): bounds, reading
back what was written, reading around a write (by `Region.Disjoint`), and the byte list of a value.
In namespace `NoCompiler.Lib` (`open NoCompiler.Lib`), so they never clash with a proof's own helpers.
Already elsewhere: `readBytes_length` (Auto), `readBytes_add` (Trace), `readBytes_congr` (Mem),
`writeLE_other`, `writeBytes_other`, `readLE_congr` (Lemmas). Round 7, B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

@[simp] theorem readBytes_zero (m : Word → Byte) (a : Word) : readBytes m a 0 = [] := rfl

@[simp] theorem readBytes_succ (m : Word → Byte) (a : Word) (n : Nat) :
    readBytes m a (n + 1) = m a :: readBytes m (a + 1) n := rfl

@[simp] theorem readLE_zero (m : Word → Byte) (a : Word) : readLE m a 0 = 0 := rfl

@[simp] theorem writeBytes_nil (m : Word → Byte) (a : Word) : writeBytes m a [] = m := rfl

/-- `n` bytes read are `n` bytes. -/
@[simp] theorem length_readBytes (m : Word → Byte) (a : Word) (n : Nat) :
    (readBytes m a n).length = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [readBytes, ih]

/-- `n` bytes are below `256 ^ n`. -/
theorem readLE_lt (m : Word → Byte) (a : Word) (n : Nat) : readLE m a n < 256 ^ n := by
  induction n generalizing a with
  | zero => simp [readLE]
  | succ n ih => simp only [readLE, Nat.pow_succ]; have := ih (a + 1); have := (m a).isLt; omega

/-- Eight bytes fit a word. -/
theorem readLE_lt_word (m : Word → Byte) (a : Word) : readLE m a 8 < 2 ^ 64 := by
  have := readLE_lt m a 8; simpa using this

/-- The `k`-th byte read is the byte at `a + k`. -/
theorem readBytes_getElem (m : Word → Byte) (a : Word) {n k : Nat} (hk : k < n) :
    (readBytes m a n)[k]'(by rw [length_readBytes]; exact hk) = m (a + BitVec.ofNat 64 k) := by
  induction n generalizing a k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [readBytes_succ, List.getElem_cons_succ]
      rw [ih (a + 1) (by omega)]
      congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

/-- Reading two ranges back to back. -/
theorem readBytes_append (m : Word → Byte) (a : Word) (k r : Nat) :
    readBytes m a k ++ readBytes m (a + BitVec.ofNat 64 k) r = readBytes m a (k + r) :=
  (readBytes_add m a k r).symm

/-- Reading back a byte list just written. -/
theorem readBytes_writeBytes_same (m : Word → Byte) (a : Word) (bs : List Byte)
    (h : bs.length < 2 ^ 64) : readBytes (writeBytes m a bs) a bs.length = bs := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, readBytes_succ, writeBytes, ite_true]
    congr 1
    have hr := ih (a + 1) (by simp at h; omega)
    rw [readBytes_congr (m' := writeBytes m (a + 1) bs) ?_, hr]
    intro j hj
    have hne : a + 1 + BitVec.ofNat 64 j ≠ a := by
      intro e
      have : (BitVec.ofNat 64 (j + 1) : Word) = 0 := by
        apply BitVec.eq_of_toNat_eq
        have e' : a + 1 + BitVec.ofNat 64 j - a = 0 := by rw [e]; simp
        have : a + 1 + BitVec.ofNat 64 j - a = BitVec.ofNat 64 (j + 1) := by
          apply BitVec.eq_of_toNat_eq; simp; omega
        rw [← this, e']
      have := congrArg BitVec.toNat this
      simp at this; simp at h; omega
    show (if a + 1 + BitVec.ofNat 64 j = a then b else _) = _
    split
    · rename_i e; exact absurd e hne
    · rfl

/-- A byte outside the written list keeps its value (by `Region.mem`). -/
theorem writeBytes_apply_not_mem {m : Word → Byte} {a x : Word} {bs : List Byte}
    (h : ¬ (⟨a, bs.length⟩ : Region).mem x) : writeBytes m a bs x = m x :=
  writeBytes_other m a bs x (by simp only [Region.mem] at h; omega)

/-- A byte outside the written range keeps its value (by `Region.mem`). -/
theorem writeLE_apply_not_mem {m : Word → Byte} {a x : Word} {v n : Nat}
    (h : ¬ (⟨a, n⟩ : Region).mem x) : writeLE m a v n x = m x :=
  writeLE_other m a v n x (by simp only [Region.mem] at h; omega)

/-- Reading a range disjoint from a `writeBytes`: unchanged. -/
theorem readBytes_writeBytes_disjoint {m : Word → Byte} {a b : Word} {bs : List Byte} {n : Nat}
    (hd : (⟨a, bs.length⟩ : Region).Disjoint ⟨b, n⟩) :
    readBytes (writeBytes m a bs) b n = readBytes m b n := by
  apply readBytes_congr
  intro j hj
  apply writeBytes_apply_not_mem
  intro hm
  exact hd.not_mem hm (Region.mem_add hj)

/-- Reading a range disjoint from a `writeLE`: unchanged. -/
theorem readBytes_writeLE_disjoint {m : Word → Byte} {a b : Word} {v k n : Nat}
    (hd : (⟨a, k⟩ : Region).Disjoint ⟨b, n⟩) :
    readBytes (writeLE m a v k) b n = readBytes m b n := by
  apply readBytes_congr
  intro j hj
  apply writeLE_apply_not_mem
  intro hm
  exact hd.not_mem hm (Region.mem_add hj)

/-- The number a range disjoint from a `writeLE` reads: unchanged. -/
theorem readLE_writeLE_disjoint {m : Word → Byte} {a b : Word} {v k n : Nat}
    (hd : (⟨a, k⟩ : Region).Disjoint ⟨b, n⟩) :
    readLE (writeLE m a v k) b n = readLE m b n := by
  apply readLE_congr
  intro j hj
  apply writeLE_apply_not_mem
  intro hm
  exact hd.not_mem hm (Region.mem_add hj)

/-- The number a range disjoint from a `writeBytes` reads: unchanged. -/
theorem readLE_writeBytes_disjoint {m : Word → Byte} {a b : Word} {bs : List Byte} {n : Nat}
    (hd : (⟨a, bs.length⟩ : Region).Disjoint ⟨b, n⟩) :
    readLE (writeBytes m a bs) b n = readLE m b n := by
  apply readLE_congr
  intro j hj
  apply writeBytes_apply_not_mem
  intro hm
  exact hd.not_mem hm (Region.mem_add hj)

/-- Memory that agrees on a region reads the same bytes from it. -/
theorem readBytes_eq_of_agree {m m' : Word → Byte} {r : Region}
    (h : ∀ x, r.mem x → m x = m' x) : readBytes m r.base r.size = readBytes m' r.base r.size :=
  readBytes_congr (fun _ hj => h _ (Region.mem_add hj))

theorem readLE_eq_of_agree {m m' : Word → Byte} {r : Region}
    (h : ∀ x, r.mem x → m x = m' x) : readLE m r.base r.size = readLE m' r.base r.size :=
  readLE_congr (fun _ hj => h _ (Region.mem_add hj))

/-- `readLE` is the little-endian value of `readBytes`. -/
theorem readLE_eq_foldr (m : Word → Byte) (a : Word) (n : Nat) :
    readLE m a n = (readBytes m a n).foldr (fun b acc => b.toNat + 256 * acc) 0 := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [readLE, readBytes_succ, List.foldr_cons, ih]

end NoCompiler.Lib

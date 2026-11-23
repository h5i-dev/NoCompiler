import NoCompiler.Lib.Slot

/-!
# Library: C strings in memory

`CStr m a n`: at `a` there are `n` non-zero bytes and then a zero byte (a C string of length
`n`). The facts a loop over a string needs (strlen, strcpy, strchr, ...): the length is unique, the
first byte decides whether the string is empty, the rest of a nonempty string is a string one
shorter, a byte before the end is not zero, the bytes read are the string, and a write outside
the string's `n + 1` bytes keeps it. Namespace `NoCompiler.Lib`. Round 7, B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

/-- At `a`: `n` non-zero bytes, then a zero. -/
def CStr (m : Word → Byte) (a : Word) (n : Nat) : Prop :=
  (∀ i, i < n → m (a + BitVec.ofNat 64 i) ≠ 0) ∧ m (a + BitVec.ofNat 64 n) = 0

theorem CStr.byte_ne {m : Word → Byte} {a : Word} {n i : Nat} (h : CStr m a n) (hi : i < n) :
    m (a + BitVec.ofNat 64 i) ≠ 0 := h.1 i hi

theorem CStr.nul {m : Word → Byte} {a : Word} {n : Nat} (h : CStr m a n) :
    m (a + BitVec.ofNat 64 n) = 0 := h.2

/-- The empty string: a zero byte at `a`. -/
theorem cstr_zero_iff {m : Word → Byte} {a : Word} : CStr m a 0 ↔ m a = 0 := by
  simp [CStr]

/-- The first byte is zero exactly for the empty string. -/
theorem CStr.eq_zero_iff {m : Word → Byte} {a : Word} {n : Nat} (h : CStr m a n) :
    m a = 0 ↔ n = 0 := by
  constructor
  · intro h0
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact hn
    · exact absurd (by simpa using h0) (h.1 0 hn)
  · rintro rfl; simpa using h.2

/-- The length is unique. -/
theorem CStr.unique {m : Word → Byte} {a : Word} {n n' : Nat} (h : CStr m a n) (h' : CStr m a n') :
    n = n' := by
  rcases Nat.lt_trichotomy n n' with hl | he | hl
  · exact absurd h.2 (h'.1 n hl)
  · exact he
  · exact absurd h'.2 (h.1 n' hl)

/-- One byte on: a nonempty string's tail is a string one shorter. -/
theorem CStr.tail {m : Word → Byte} {a : Word} {n : Nat} (h : CStr m a (n + 1)) :
    CStr m (a + 1) n := by
  have e : ∀ i, a + 1 + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (i + 1) := fun i => by
    apply BitVec.eq_of_toNat_eq; simp; omega
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [e]; exact h.1 (i + 1) (by omega)
  · rw [e]; exact h.2

/-- A non-zero first byte in front of a string makes a string one longer. -/
theorem CStr.cons {m : Word → Byte} {a : Word} {n : Nat} (h0 : m a ≠ 0) (h : CStr m (a + 1) n) :
    CStr m a (n + 1) := by
  have e : ∀ i, a + 1 + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (i + 1) := fun i => by
    apply BitVec.eq_of_toNat_eq; simp; omega
  refine ⟨fun i hi => ?_, ?_⟩
  · cases i with
    | zero => simpa using h0
    | succ i => rw [← e]; exact h.1 i (by omega)
  · rw [← e]; exact h.2

/-- From the `k`-th byte on (`k ≤ n`), what is left is a string of length `n - k`: the invariant of
    a loop that walks a pointer along the string. -/
theorem CStr.drop {m : Word → Byte} {a : Word} {n : Nat} (h : CStr m a n) (k : Nat) (hk : k ≤ n) :
    CStr m (a + BitVec.ofNat 64 k) (n - k) := by
  have e : ∀ i, a + BitVec.ofNat 64 k + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (k + i) := fun i => by
    apply BitVec.eq_of_toNat_eq; simp; omega
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [e]; exact h.1 (k + i) (by omega)
  · rw [e, show k + (n - k) = n by omega]; exact h.2

/-- A loop step: at offset `k` the byte is zero exactly when `k` is the length. -/
theorem CStr.byte_eq_zero_iff {m : Word → Byte} {a : Word} {n k : Nat} (h : CStr m a n)
    (hk : k ≤ n) : m (a + BitVec.ofNat 64 k) = 0 ↔ k = n := by
  have := (h.drop k hk).eq_zero_iff
  rw [this]; omega

/-- The bytes of the string, as read: none is zero. -/
theorem CStr.readBytes_ne_zero {m : Word → Byte} {a : Word} {n : Nat} (h : CStr m a n) :
    ∀ b ∈ readBytes m a n, b ≠ 0 := by
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  have hi' : i < n := by simpa [length_readBytes] using hi
  rw [readBytes_getElem m a hi']
  exact h.1 i hi'

/-- Memory that agrees on the string's `n + 1` bytes holds the same string. -/
theorem CStr.of_agree {m m' : Word → Byte} {a : Word} {n : Nat} (h : CStr m a n)
    (hag : ∀ i, i ≤ n → m' (a + BitVec.ofNat 64 i) = m (a + BitVec.ofNat 64 i)) : CStr m' a n :=
  ⟨fun i hi => by rw [hag i (by omega)]; exact h.1 i hi, by rw [hag n (Nat.le_refl _)]; exact h.2⟩

/-- A write that misses the string's `n + 1` bytes keeps it. -/
theorem CStr.writeLE_disjoint {m : Word → Byte} {a b : Word} {n k v : Nat} (h : CStr m a n)
    (hd : (⟨b, k⟩ : Region).Disjoint ⟨a, n + 1⟩) : CStr (writeLE m b v k) a n :=
  h.of_agree fun i hi => writeLE_apply_not_mem (hd.symm.not_mem
    (Region.mem_add (r := ⟨a, n + 1⟩) (by show i < n + 1; omega)))

theorem CStr.writeBytes_disjoint {m : Word → Byte} {a b : Word} {n : Nat} {bs : List Byte}
    (h : CStr m a n) (hd : (⟨b, bs.length⟩ : Region).Disjoint ⟨a, n + 1⟩) :
    CStr (writeBytes m b bs) a n :=
  h.of_agree fun i hi => writeBytes_apply_not_mem (hd.symm.not_mem
    (Region.mem_add (r := ⟨a, n + 1⟩) (by show i < n + 1; omega)))

end NoCompiler.Lib

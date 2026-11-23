import NoCompiler.Lib.CStr

/-!
# Library: fills and copies

What `memset`, `memcpy` and `strcpy` specifications say about memory, as lemmas about
`writeBytes`: the byte at offset `i` of a written list, a write in two parts, reading back a
prefix, a fill (`List.replicate`) reads back as the fill, a copy reads back as its source, and a
written string with its terminator is a `CStr`. Namespace `NoCompiler.Lib`. Round 7, B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

/-- The byte at offset `i` of a written list. -/
theorem writeBytes_apply_add {m : Word → Byte} {a : Word} {bs : List Byte} {i : Nat}
    (hi : i < bs.length) (h : bs.length < 2 ^ 64) :
    writeBytes m a bs (a + BitVec.ofNat 64 i) = bs[i] := by
  have e := congrArg (fun l => l[i]?) (readBytes_writeBytes_same m a bs h)
  rw [List.getElem?_eq_getElem (by rw [length_readBytes]; exact hi),
    List.getElem?_eq_getElem hi, Option.some.injEq, readBytes_getElem _ _ hi] at e
  exact e

/-- The first byte of a written list. -/
theorem writeBytes_cons_apply_self (m : Word → Byte) (a : Word) (b : Byte) (bs : List Byte) :
    writeBytes m a (b :: bs) a = b := by
  show (if a = a then b else _) = b
  simp

/-- A write in two parts: the second part first, then the first (the first part's bytes win
    nowhere, the two do not overlap). -/
theorem writeBytes_append (m : Word → Byte) (a : Word) (bs cs : List Byte) :
    writeBytes m a (bs ++ cs) = writeBytes (writeBytes m (a + BitVec.ofNat 64 bs.length) cs) a bs := by
  induction bs generalizing a with
  | nil => simp
  | cons b bs ih =>
    show (fun x => if x = a then b else writeBytes m (a + 1) (bs ++ cs) x) =
      (fun x => if x = a then b else
        writeBytes (writeBytes m (a + BitVec.ofNat 64 (bs.length + 1)) cs) (a + 1) bs x)
    rw [ih (a + 1)]
    have e : a + 1 + BitVec.ofNat 64 bs.length = a + BitVec.ofNat 64 (bs.length + 1) := by
      apply BitVec.eq_of_toNat_eq; simp; omega
    rw [e]

/-- Reading back a prefix of a written list. -/
theorem readBytes_writeBytes_prefix (m : Word → Byte) (a : Word) (bs : List Byte) {k : Nat}
    (hk : k ≤ bs.length) (h : bs.length < 2 ^ 64) :
    readBytes (writeBytes m a bs) a k = bs.take k := by
  apply List.ext_getElem
  · simp [length_readBytes]; omega
  · intro i h1 h2
    rw [length_readBytes] at h1
    rw [readBytes_getElem _ _ h1, writeBytes_apply_add (by omega) h, List.getElem_take]

/-- A fill reads back as the fill (`memset`). -/
theorem readBytes_fill (m : Word → Byte) (a : Word) (v : Byte) {n : Nat} (h : n < 2 ^ 64) :
    readBytes (writeBytes m a (List.replicate n v)) a n = List.replicate n v := by
  have := readBytes_writeBytes_same m a (List.replicate n v) (by simpa using h)
  simpa using this

/-- Each byte of a fill. -/
theorem fill_apply (m : Word → Byte) (a : Word) (v : Byte) {n i : Nat} (hi : i < n)
    (h : n < 2 ^ 64) : writeBytes m a (List.replicate n v) (a + BitVec.ofNat 64 i) = v := by
  rw [writeBytes_apply_add (by simpa using hi) (by simpa using h)]; simp

/-- A copy reads back as its source (`memcpy`; the source is read before the write). -/
theorem readBytes_copy (m : Word → Byte) (d s : Word) {n : Nat} (h : n < 2 ^ 64) :
    readBytes (writeBytes m d (readBytes m s n)) d n = readBytes m s n := by
  have := readBytes_writeBytes_same m d (readBytes m s n) (by rw [length_readBytes]; exact h)
  rwa [length_readBytes] at this

/-- A copy leaves its source when the two do not overlap. -/
theorem readBytes_copy_src (m : Word → Byte) (d s : Word) {n : Nat}
    (hd : (⟨d, n⟩ : Region).Disjoint ⟨s, n⟩) :
    readBytes (writeBytes m d (readBytes m s n)) s n = readBytes m s n :=
  readBytes_writeBytes_disjoint (by rw [length_readBytes]; exact hd)

/-- A written list of non-zero bytes followed by a zero is a C string (`strcpy`'s result). -/
theorem cstr_writeBytes (m : Word → Byte) (a : Word) (bs : List Byte) (hnz : ∀ b ∈ bs, b ≠ 0)
    (h : bs.length + 1 < 2 ^ 64) : CStr (writeBytes m a (bs ++ [0])) a bs.length := by
  have hl : (bs ++ [(0 : Byte)]).length < 2 ^ 64 := by simpa using h
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [writeBytes_apply_add (by simp; omega) hl, List.getElem_append_left hi]
    exact hnz _ (List.getElem_mem hi)
  · rw [writeBytes_apply_add (by simp) hl]; simp

/-- A copied C string (with its terminator) is a C string at the destination. -/
theorem cstr_copy {m : Word → Byte} {s : Word} {n : Nat} (hs : CStr m s n) (d : Word)
    (h : n + 1 < 2 ^ 64) : CStr (writeBytes m d (readBytes m s (n + 1))) d n := by
  have e : readBytes m s (n + 1) = readBytes m s n ++ [0] := by
    rw [← readBytes_append m s n 1]; simp [hs.nul]
  rw [e]
  have := cstr_writeBytes m d (readBytes m s n) hs.readBytes_ne_zero (by rw [length_readBytes]; exact h)
  rwa [length_readBytes] at this

end NoCompiler.Lib

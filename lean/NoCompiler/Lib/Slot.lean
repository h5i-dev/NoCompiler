import NoCompiler.Lib.Field

/-!
# Library: stack-frame slots

A function's frame is `⟨sp - F, F⟩` (`F` bytes below the entry `sp`); a slot is `w` bytes at
`sp - o` with `w ≤ o ≤ F`. The facts every frame proof needs, once, for any `F` and `w`: the
slot lies in the frame, a region disjoint from the frame is disjoint from each slot (so a write
there leaves the slots), two slots at non-overlapping offsets are disjoint, and a permission whose
regions all lie in a writable region is below it. Namespace `NoCompiler.Lib`. Round 7, B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

/-- A slot's address as an offset from the frame's base. -/
theorem slot_eq (sp : Word) {F o : Nat} (j : Nat) (h : o ≤ F) (hF : F < 2 ^ 64) :
    sp - BitVec.ofNat 64 o + BitVec.ofNat 64 j = sp - BitVec.ofNat 64 F + BitVec.ofNat 64 (F - o + j) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have : o < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt hF]
  simp only [Nat.reducePow] at *
  omega

/-- The frame covers the slot. -/
theorem frame_covers_slot (sp : Word) {F o w : Nat} (hw : w ≤ o) (h : o ≤ F) (hF : F < 2 ^ 64) :
    (⟨sp - BitVec.ofNat 64 F, F⟩ : Region).covers (sp - BitVec.ofNat 64 o) w := by
  have e := slot_eq sp 0 h hF
  simp only [BitVec.add_zero, Nat.add_zero] at e
  rw [e]
  exact Region.covers_sub (Region.covers_self _ F) (F - o) w (by omega)

/-- Each byte of the slot is in the frame. -/
theorem frame_mem_slot (sp : Word) {F o w j : Nat} (hj : j < w) (hw : w ≤ o) (h : o ≤ F)
    (hF : F < 2 ^ 64) :
    (⟨sp - BitVec.ofNat 64 F, F⟩ : Region).mem (sp - BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
  rw [slot_eq sp j h hF]
  exact Region.mem_add (r := ⟨_, F⟩) (by show F - o + j < F; omega)

/-- A region disjoint from the frame is disjoint from each (nonempty) slot. -/
theorem slot_disjoint {r : Region} (sp : Word) {F o w : Nat}
    (hd : r.Disjoint ⟨sp - BitVec.ofNat 64 F, F⟩) (hw0 : 0 < w) (hr0 : 0 < r.size) (hw : w ≤ o)
    (h : o ≤ F) (hF : F < 2 ^ 64) :
    (⟨sp - BitVec.ofNat 64 o, w⟩ : Region).Disjoint r := by
  have d : r.Disjoint ⟨sp - BitVec.ofNat 64 o, w⟩ :=
    hd.mono (Region.covers_self r.base r.size) (frame_covers_slot sp hw h hF) hr0 hw0
  exact d.symm

/-- A byte of a slot is not in a region disjoint from the frame. -/
theorem slot_not_mem {r : Region} (sp : Word) {F o w j : Nat}
    (hd : r.Disjoint ⟨sp - BitVec.ofNat 64 F, F⟩) (hj : j < w) (hw : w ≤ o) (h : o ≤ F)
    (hF : F < 2 ^ 64) : ¬ r.mem (sp - BitVec.ofNat 64 o + BitVec.ofNat 64 j) :=
  fun hx => hd.symm.not_mem (frame_mem_slot sp hj hw h hF) hx

/-- A write to a region disjoint from the frame leaves a slot's bytes. -/
theorem readLE_slot_writeLE_disjoint {m : Word → Byte} {a : Word} {v k : Nat} (sp : Word)
    {F o w : Nat} (hd : (⟨a, k⟩ : Region).Disjoint ⟨sp - BitVec.ofNat 64 F, F⟩) (hk : 0 < k)
    (hw0 : 0 < w) (hw : w ≤ o) (h : o ≤ F) (hF : F < 2 ^ 64) :
    readLE (writeLE m a v k) (sp - BitVec.ofNat 64 o) w = readLE m (sp - BitVec.ofNat 64 o) w :=
  readLE_writeLE_disjoint (slot_disjoint sp hd hw0 hk hw h hF).symm

/-- The word in a slot after a write to a region disjoint from the frame. -/
theorem read64_slot_writeLE_disjoint {m : Word → Byte} {a : Word} {v k : Nat} (sp : Word)
    {F o : Nat} (hd : (⟨a, k⟩ : Region).Disjoint ⟨sp - BitVec.ofNat 64 F, F⟩) (hk : 0 < k)
    (hw : 8 ≤ o) (h : o ≤ F) (hF : F < 2 ^ 64) :
    read64 (writeLE m a v k) (sp - BitVec.ofNat 64 o) = read64 m (sp - BitVec.ofNat 64 o) := by
  unfold read64; rw [readLE_slot_writeLE_disjoint sp hd hk (by decide) hw h hF]

/-- Two slots at non-overlapping offsets are disjoint. -/
theorem slots_disjoint (sp : Word) {F o w o' w' : Nat} (hw0 : 0 < w) (hw0' : 0 < w')
    (hw : w ≤ o) (h : o ≤ F) (hw' : w' ≤ o') (h' : o' ≤ F) (hF : F < 2 ^ 64)
    (hs : o' + w ≤ o ∨ o + w' ≤ o') :
    (⟨sp - BitVec.ofNat 64 o, w⟩ : Region).Disjoint ⟨sp - BitVec.ofNat 64 o', w'⟩ := by
  have e := slot_eq sp 0 h hF
  have e' := slot_eq sp 0 h' hF
  simp only [BitVec.add_zero, Nat.add_zero] at e e'
  rw [e, e']
  exact disjoint_fields _ hw0 hw0' (by omega) (by omega) (by omega)

/-- The word in one slot after writing another. -/
theorem read64_slot_writeLE_slot {m : Word → Byte} {v : Nat} (sp : Word) {F o w o' : Nat}
    (hw0 : 0 < w) (hw : w ≤ o) (h : o ≤ F) (h8 : 8 ≤ o') (h' : o' ≤ F) (hF : F < 2 ^ 64)
    (hs : o' + w ≤ o ∨ o + 8 ≤ o') :
    read64 (writeLE m (sp - BitVec.ofNat 64 o) v w) (sp - BitVec.ofNat 64 o') =
      read64 m (sp - BitVec.ofNat 64 o') := by
  unfold read64
  rw [readLE_writeLE_disjoint (slots_disjoint sp hw0 (by decide) hw h h8 h' hF hs)]

/-- A permission whose regions all lie within a writable region is below the permission that
    grants it. -/
theorem perm_le_of_within {P Q : Perm} {R : Region} (hw : ∀ p n, R.covers p n → Q.canWrite p n)
    (h : ∀ r ∈ P.rd ++ P.wr, r.within R) : P.le Q := by
  constructor
  · rintro a n (h0 | ⟨r, hr, hc⟩)
    · exact .inl h0
    · exact Perm.canRead_of_canWrite (hw a n (Region.covers_of_within hc (h r hr)))
  · rintro a n (h0 | ⟨r, hr, hc⟩)
    · exact .inl h0
    · exact hw a n (Region.covers_of_within hc (h r (List.mem_append.2 (.inr hr))))

end NoCompiler.Lib

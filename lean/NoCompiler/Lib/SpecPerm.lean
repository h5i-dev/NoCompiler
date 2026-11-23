import NoCompiler.Lib.Signed

/-!
# Library: what a function's specification lets it touch

`Spec.perm sp a s` (Spec.lean) grants the spec's `reads`, its `writes`, and the `sp.stack` bytes
below the entry `sp`. The facts every function proof needs about it: a stack slot (`w` bytes at
`sp - o`, `w ≤ o ≤ stack`) can be written and read, a range inside a listed write region can be
written and read, a range inside a listed read region can be read, and a permission below it
carries each of these over. Namespace `NoCompiler.Lib`. Round 7, B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

variable {α : Type}

theorem stackRegion_mem_perm_wr (sp : Spec α) (a : α) (s : State) :
    Spec.stackRegion s sp.stack ∈ (sp.perm a s).wr := by
  simp [Spec.perm]

/-- A stack slot can be written. -/
theorem perm_canWrite_slot (sp : Spec α) (a : α) (s : State) {o w : Nat} (hw : w ≤ o)
    (ho : o ≤ sp.stack) (hst : sp.stack < 2 ^ 64) :
    (sp.perm a s).canWrite (s.reg Reg.sp - BitVec.ofNat 64 o) w :=
  Perm.canWrite_of_mem (stackRegion_mem_perm_wr sp a s) (frame_covers_slot _ hw ho hst)

/-- A stack slot can be read. -/
theorem perm_canRead_slot (sp : Spec α) (a : α) (s : State) {o w : Nat} (hw : w ≤ o)
    (ho : o ≤ sp.stack) (hst : sp.stack < 2 ^ 64) :
    (sp.perm a s).canRead (s.reg Reg.sp - BitVec.ofNat 64 o) w :=
  Perm.canRead_of_canWrite (perm_canWrite_slot sp a s hw ho hst)

/-- A range inside a region the spec writes can be written. -/
theorem perm_canWrite_of_writes (sp : Spec α) (a : α) (s : State) {r : Region}
    (hr : r ∈ sp.writes a s) {p : Word} {n : Nat} (hc : r.covers p n) :
    (sp.perm a s).canWrite p n :=
  Perm.canWrite_of_mem (by simp [Spec.perm, hr]) hc

/-- A field of a region the spec writes (`base + j`, `n` bytes, `j + n ≤ size`) can be written. -/
theorem perm_canWrite_field (sp : Spec α) (a : α) (s : State) {b : Word} {size : Nat}
    (hr : (⟨b, size⟩ : Region) ∈ sp.writes a s) {j n : Nat} (hj : j + n ≤ size) :
    (sp.perm a s).canWrite (b + BitVec.ofNat 64 j) n :=
  perm_canWrite_of_writes sp a s hr (Region.covers_sub (Region.covers_self b size) j n hj)

/-- A range inside a region the spec writes can be read. -/
theorem perm_canRead_of_writes (sp : Spec α) (a : α) (s : State) {r : Region}
    (hr : r ∈ sp.writes a s) {p : Word} {n : Nat} (hc : r.covers p n) :
    (sp.perm a s).canRead p n :=
  Perm.canRead_of_canWrite (perm_canWrite_of_writes sp a s hr hc)

/-- A range inside a region the spec reads can be read. -/
theorem perm_canRead_of_reads (sp : Spec α) (a : α) (s : State) {r : Region}
    (hr : r ∈ sp.reads a s) {p : Word} {n : Nat} (hc : r.covers p n) :
    (sp.perm a s).canRead p n :=
  Perm.canRead_of_mem (by simp [Spec.perm, hr]) hc

/-- A field of a region the spec reads can be read. -/
theorem perm_canRead_field (sp : Spec α) (a : α) (s : State) {b : Word} {size : Nat}
    (hr : (⟨b, size⟩ : Region) ∈ sp.reads a s) {j n : Nat} (hj : j + n ≤ size) :
    (sp.perm a s).canRead (b + BitVec.ofNat 64 j) n :=
  perm_canRead_of_reads sp a s hr (Region.covers_sub (Region.covers_self b size) j n hj)

/-- A smaller permission's grants hold in the larger one (both directions of `Perm.le`). -/
theorem perm_le_canWrite {P Q : Perm} (h : P.le Q) {p : Word} {n : Nat} (hw : P.canWrite p n) :
    Q.canWrite p n := h.write p n hw

theorem perm_le_canRead {P Q : Perm} (h : P.le Q) {p : Word} {n : Nat} (hr : P.canRead p n) :
    Q.canRead p n := h.read p n hr

end NoCompiler.Lib

import NoCompiler.Lib.Rw
/-! Library rewrite rules (NoCompiler/Lib/Rw.lean): their side conditions close by `decide` on numerals. -/
open NoCompiler NoCompiler.Lib
-- the side conditions close by decide on numerals
example (f : Word) (m : Word → Byte) (v : Nat) :
    read64 (writeLE m (f + BitVec.ofNat 64 40) v 8) (f + BitVec.ofNat 64 56) = read64 m (f + BitVec.ofNat 64 56) :=
  read64_field_after_field f 40 8 56 (by decide) m v
example {f sp : Word} (hFS : (⟨f, 144⟩ : Region).Disjoint ⟨sp - BitVec.ofNat 64 16, 16⟩) (m : Word → Byte) (v : Nat) :
    read64 (writeLE m (sp - BitVec.ofNat 64 8) v 8) (f + BitVec.ofNat 64 40) = read64 m (f + BitVec.ofNat 64 40) := by
  rw [read64_field_after_slot hFS 8 8 40 (by decide)]
example (sp : Word) (m : Word → Byte) (v : Nat) :
    read64 (writeLE m (sp - BitVec.ofNat 64 16) v 8) (sp - BitVec.ofNat 64 8) = read64 m (sp - BitVec.ofNat 64 8) := by
  simp [read64_slot_after_slot sp 64 16 8 8 (by decide)]
-- the same, as a simp set: `lib_rw` closes the side conditions by decide and finds hFS in context
example {f sp : Word} (hFS : (⟨f, 144⟩ : Region).Disjoint ⟨sp - BitVec.ofNat 64 16, 16⟩) (m : Word → Byte) (v w : Nat) :
    read64 (writeLE (writeLE m (sp - BitVec.ofNat 64 8) v 8) (f + BitVec.ofNat 64 0) w 8) (f + BitVec.ofNat 64 40) =
      read64 m (f + BitVec.ofNat 64 40) := by
  lib_rw

import NoCompiler.Lib.Scan
import NoCompiler.Lib.RwAttr

/-!
# Library: rewrite rules for the step tactics, with `decide` side conditions

The forms `nocompiler_wstep [..]` and `simp` take: an equation whose side condition is one
Boolean closed by `decide` once the offsets are numerals. A read of one struct field after a
store to another, a read of a field after a store to a stack slot, and a read of a slot after a
store to a field, for any struct of `S` bytes at `f` and any frame of `F` bytes below `sp` (the
frame and the struct disjoint). Each replaces a family of per-function helpers (`field_after_field`,
`field_after_slot16`, `slot16_after_field`, `sr_slot_after_field`, ... in Examples/Libc).
All are in the simp set `nocompiler_rw` (Lib/RwAttr.lean); the tactic `lib_rw` rewrites
with all of them.
Namespace `NoCompiler.Lib`. Round 7, B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

/-- A field read after a store to another field of the same base. -/
@[nocompiler_rw] theorem readLE_field_after_field (f : Word) (a n b w : Nat)
    (h : (decide (a + n ≤ b) || decide (b + w ≤ a)) && decide (a + n ≤ 2 ^ 64) &&
      decide (b + w ≤ 2 ^ 64) && decide (0 < n) && decide (0 < w) = true)
    (m : Word → Byte) (v : Nat) :
    readLE (writeLE m (f + BitVec.ofNat 64 a) v n) (f + BitVec.ofNat 64 b) w =
      readLE m (f + BitVec.ofNat 64 b) w := by
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hs, h1⟩, h2⟩, hn⟩, hw⟩ := h
  exact readLE_writeLE_field f hn hw h1 h2 hs

@[nocompiler_rw] theorem read64_field_after_field (f : Word) (a n b : Nat)
    (h : (decide (a + n ≤ b) || decide (b + 8 ≤ a)) && decide (a + n ≤ 2 ^ 64) &&
      decide (b + 8 ≤ 2 ^ 64) && decide (0 < n) && decide (0 < 8) = true)
    (m : Word → Byte) (v : Nat) :
    read64 (writeLE m (f + BitVec.ofNat 64 a) v n) (f + BitVec.ofNat 64 b) =
      read64 m (f + BitVec.ofNat 64 b) := by
  unfold read64; rw [readLE_field_after_field f a n b 8 h]

@[nocompiler_rw] theorem read32_field_after_field (f : Word) (a n b : Nat)
    (h : (decide (a + n ≤ b) || decide (b + 4 ≤ a)) && decide (a + n ≤ 2 ^ 64) &&
      decide (b + 4 ≤ 2 ^ 64) && decide (0 < n) && decide (0 < 4) = true)
    (m : Word → Byte) (v : Nat) :
    read32 (writeLE m (f + BitVec.ofNat 64 a) v n) (f + BitVec.ofNat 64 b) =
      read32 m (f + BitVec.ofNat 64 b) := by
  unfold read32; rw [readLE_field_after_field f a n b 4 h]

/-- A field read after a store to a stack slot (the struct and the frame disjoint). -/
@[nocompiler_rw] theorem readLE_field_after_slot {f sp : Word} {S F : Nat}
    (hFS : (⟨f, S⟩ : Region).Disjoint ⟨sp - BitVec.ofNat 64 F, F⟩) (o w b n : Nat)
    (h : decide (w ≤ o) && decide (o ≤ F) && decide (F < 2 ^ 64) && decide (b + n ≤ S) &&
      decide (0 < n) && decide (0 < w) = true)
    (m : Word → Byte) (v : Nat) :
    readLE (writeLE m (sp - BitVec.ofNat 64 o) v w) (f + BitVec.ofNat 64 b) n =
      readLE m (f + BitVec.ofNat 64 b) n := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hw, ho⟩, hF⟩, hb⟩, hn⟩, hw0⟩ := h
  have hd : (⟨f + BitVec.ofNat 64 b, n⟩ : Region).Disjoint ⟨sp - BitVec.ofNat 64 o, w⟩ :=
    hFS.mono (Region.covers_sub (Region.covers_self f S) b n hb) (frame_covers_slot sp hw ho hF) hn hw0
  exact readLE_writeLE_disjoint hd.symm

/-- A slot read after a store to a field (the struct and the frame disjoint). -/
@[nocompiler_rw] theorem readLE_slot_after_field {f sp : Word} {S F : Nat}
    (hFS : (⟨f, S⟩ : Region).Disjoint ⟨sp - BitVec.ofNat 64 F, F⟩) (a n o w : Nat)
    (h : decide (w ≤ o) && decide (o ≤ F) && decide (F < 2 ^ 64) && decide (a + n ≤ S) &&
      decide (0 < n) && decide (0 < w) = true)
    (m : Word → Byte) (v : Nat) :
    readLE (writeLE m (f + BitVec.ofNat 64 a) v n) (sp - BitVec.ofNat 64 o) w =
      readLE m (sp - BitVec.ofNat 64 o) w := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hw, ho⟩, hF⟩, ha⟩, hn⟩, hw0⟩ := h
  have hd : (⟨f + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨sp - BitVec.ofNat 64 o, w⟩ :=
    hFS.mono (Region.covers_sub (Region.covers_self f S) a n ha) (frame_covers_slot sp hw ho hF) hn hw0
  exact readLE_writeLE_disjoint hd

@[nocompiler_rw] theorem read64_slot_after_field {f sp : Word} {S F : Nat}
    (hFS : (⟨f, S⟩ : Region).Disjoint ⟨sp - BitVec.ofNat 64 F, F⟩) (a n o : Nat)
    (h : decide (8 ≤ o) && decide (o ≤ F) && decide (F < 2 ^ 64) && decide (a + n ≤ S) &&
      decide (0 < n) && decide (0 < 8) = true)
    (m : Word → Byte) (v : Nat) :
    read64 (writeLE m (f + BitVec.ofNat 64 a) v n) (sp - BitVec.ofNat 64 o) =
      read64 m (sp - BitVec.ofNat 64 o) := by
  unfold read64; rw [readLE_slot_after_field hFS a n o 8 h]

@[nocompiler_rw] theorem read64_field_after_slot {f sp : Word} {S F : Nat}
    (hFS : (⟨f, S⟩ : Region).Disjoint ⟨sp - BitVec.ofNat 64 F, F⟩) (o w b : Nat)
    (h : decide (w ≤ o) && decide (o ≤ F) && decide (F < 2 ^ 64) && decide (b + 8 ≤ S) &&
      decide (0 < 8) && decide (0 < w) = true)
    (m : Word → Byte) (v : Nat) :
    read64 (writeLE m (sp - BitVec.ofNat 64 o) v w) (f + BitVec.ofNat 64 b) =
      read64 m (f + BitVec.ofNat 64 b) := by
  unfold read64; rw [readLE_field_after_slot hFS o w b 8 h]

@[nocompiler_rw] theorem read32_field_after_slot {f sp : Word} {S F : Nat}
    (hFS : (⟨f, S⟩ : Region).Disjoint ⟨sp - BitVec.ofNat 64 F, F⟩) (o w b : Nat)
    (h : decide (w ≤ o) && decide (o ≤ F) && decide (F < 2 ^ 64) && decide (b + 4 ≤ S) &&
      decide (0 < 4) && decide (0 < w) = true)
    (m : Word → Byte) (v : Nat) :
    read32 (writeLE m (sp - BitVec.ofNat 64 o) v w) (f + BitVec.ofNat 64 b) =
      read32 m (f + BitVec.ofNat 64 b) := by
  unfold read32; rw [readLE_field_after_slot hFS o w b 4 h]

/-- A slot read after a store to another slot of the same frame. -/
@[nocompiler_rw] theorem read64_slot_after_slot (sp : Word) (F o w o' : Nat)
    (h : decide (0 < w) && decide (w ≤ o) && decide (o ≤ F) && decide (8 ≤ o') && decide (o' ≤ F) &&
      decide (F < 2 ^ 64) && (decide (o' + w ≤ o) || decide (o + 8 ≤ o')) = true)
    (m : Word → Byte) (v : Nat) :
    read64 (writeLE m (sp - BitVec.ofNat 64 o) v w) (sp - BitVec.ofNat 64 o') =
      read64 m (sp - BitVec.ofNat 64 o') := by
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hw0, hw⟩, ho⟩, h8⟩, ho'⟩, hF⟩, hs⟩ := h
  exact read64_slot_writeLE_slot sp hw0 hw ho h8 ho' hF hs

/-- Rewrite with every rule of `nocompiler_rw`, closing each side condition by `decide` and each
    disjointness hypothesis (`hFS`) from the context. The default `simp` discharger does not close
    the `decide` conditions, so plain `simp [nocompiler_rw]` makes no progress. -/
macro "lib_rw" : tactic =>
  `(tactic| simp (disch := first | decide | assumption) only [nocompiler_rw])

/-- Offset 0 written as the base itself, for rules stated at `f + 0`. -/
theorem add_ofNat_zero (f : Word) : f + BitVec.ofNat 64 0 = f := by simp

end NoCompiler.Lib

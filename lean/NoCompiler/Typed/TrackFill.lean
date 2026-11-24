import NoCompiler.Typed.Track

/-!
# Fills: the pattern of `memset`-like functions

A fill writes the low `w` bytes of a value `v` again and again: byte `j` of `d[0, n)` is byte
`j mod w` of `v`. As a pattern for `Written` (`Track.lean`) it repeats with period `w`, so a
register holding `v` keeps its cells across the loop (`Cells.ok_periodic`).
-/
namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed.Bytes

/-- The pattern of a fill with the low `w` bytes of `v`. -/
def fillPat (v : Word) (w : Nat) : Nat → Byte := fun j => byte v (j % w)

theorem fillPat_periodic (v : Word) (w : Nat) (j : Nat) : fillPat v w (j + w) = fillPat v w j := by
  simp [fillPat, Nat.add_mod_right]

/-- The cells of the fill register at entry: its byte `i` is the pattern's byte `i`. -/
def fillCells (w : Nat) : Cells := (List.range w).map .src

theorem fillCells_ok (v : Word) {w : Nat} (hw : w ≤ 8) : Cells.ok (fillPat v w) 0 v (fillCells w) := by
  intro i hi
  by_cases hiw : i < w
  · have : (fillCells w).getD i .unk = .src i := by
      simp [fillCells, List.getD_eq_getElem?_getD, hiw]
    rw [this]
    simp only [Cell.ok, fillPat, Nat.zero_add, Nat.mod_eq_of_lt hiw]
  · have : (fillCells w).getD i .unk = .unk := by
      simp [fillCells, List.getD_eq_getElem?_getD, hiw]
    rw [this]; trivial

/-- Memory after a fill of `c` bytes of `d` with the low `w` bytes of `v`: every byte of the
    prefix is the pattern's, every other byte the entry's. -/
abbrev Filled (m0 m : Word → Byte) (d v : Word) (w c : Nat) : Prop := Written m0 m d (fillPat v w) c

theorem Filled.bytes {m0 m : Word → Byte} {d v : Word} {w c : Nat} (h : Filled m0 m d v w c)
    (hc : c < 2 ^ 64) : ∀ j < c, m (d + BitVec.ofNat 64 j) = byte v (j % w) := by
  intro j hj
  rw [h]
  have e : (d + BitVec.ofNat 64 j - d) = BitVec.ofNat 64 j := by bv_omega
  rw [e, if_pos (by simp [BitVec.toNat_ofNat]; omega)]
  simp [fillPat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega)]

end NoCompiler.Typed.Track

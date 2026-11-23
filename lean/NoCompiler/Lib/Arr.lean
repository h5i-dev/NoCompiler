import NoCompiler.Lib.Entry

/-!
# Library: arrays

An array of `n` elements of `w` bytes at `a`: element `i` is `w` bytes at `a + w * i`. It lies in
the array, two different elements are disjoint, the next element is `w` further, a write to one
element leaves the others, an element reads back what was written, and a write outside the array
leaves every element. Namespace `NoCompiler.Lib`. Round 7, B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

/-- Element `i` of an array of `n` elements of `w` bytes at `a`: `a + w * i`. -/
theorem arr_covers (a : Word) {w n i : Nat} (hi : i < n) :
    (⟨a, w * n⟩ : Region).covers (a + BitVec.ofNat 64 (w * i)) w :=
  Region.covers_sub (Region.covers_self a (w * n)) (w * i) w (by
    have : w * (i + 1) ≤ w * n := Nat.mul_le_mul_left w hi; rw [Nat.mul_succ] at this; exact this)

/-- Two different elements of an array are disjoint. -/
theorem arr_disjoint (a : Word) {w n i j : Nat} (hw : 0 < w) (hi : i < n) (hj : j < n)
    (hn : w * n ≤ 2 ^ 64) (hij : i ≠ j) :
    (⟨a + BitVec.ofNat 64 (w * i), w⟩ : Region).Disjoint ⟨a + BitVec.ofNat 64 (w * j), w⟩ := by
  have h1 : w * i + w ≤ w * n := by
    have : w * (i + 1) ≤ w * n := Nat.mul_le_mul_left w hi; rwa [Nat.mul_succ] at this
  have h2 : w * j + w ≤ w * n := by
    have : w * (j + 1) ≤ w * n := Nat.mul_le_mul_left w hj; rwa [Nat.mul_succ] at this
  apply disjoint_fields a hw hw (by omega) (by omega)
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · left; have : w * (i + 1) ≤ w * j := Nat.mul_le_mul_left w h; rwa [Nat.mul_succ] at this
  · right; have : w * (j + 1) ≤ w * i := Nat.mul_le_mul_left w h; rwa [Nat.mul_succ] at this

/-- The next element's address: `a + w * (i + 1) = (a + w * i) + w`. -/
theorem arr_next (a : Word) (w i : Nat) :
    a + BitVec.ofNat 64 (w * (i + 1)) = a + BitVec.ofNat 64 (w * i) + BitVec.ofNat 64 w := by
  rw [add_ofNat_add_ofNat, Nat.mul_succ]

/-- Reading element `j` after writing element `i ≠ j`. -/
theorem arr_readLE_writeLE_other {m : Word → Byte} (a : Word) {w n i j v : Nat} (hw : 0 < w)
    (hi : i < n) (hj : j < n) (hn : w * n ≤ 2 ^ 64) (hij : i ≠ j) :
    readLE (writeLE m (a + BitVec.ofNat 64 (w * i)) v w) (a + BitVec.ofNat 64 (w * j)) w =
      readLE m (a + BitVec.ofNat 64 (w * j)) w :=
  readLE_writeLE_disjoint (arr_disjoint a hw hi hj hn hij)

/-- Reading element `i` just written (`w ≤ 8`). -/
theorem arr_readLE_writeLE_same (m : Word → Byte) (a : Word) (v : Nat) {w i : Nat} (hw : w ≤ 8) :
    readLE (writeLE m (a + BitVec.ofNat 64 (w * i)) v w) (a + BitVec.ofNat 64 (w * i)) w = v % 256 ^ w :=
  readLE_writeLE_same m _ v hw

/-- A write outside the array leaves every element. -/
theorem arr_readLE_writeLE_outside {m : Word → Byte} {p : Word} {k v : Nat} (a : Word) {w n i : Nat}
    (hd : (⟨p, k⟩ : Region).Disjoint ⟨a, w * n⟩) (hk : 0 < k) (hw : 0 < w) (hi : i < n) :
    readLE (writeLE m p v k) (a + BitVec.ofNat 64 (w * i)) w = readLE m (a + BitVec.ofNat 64 (w * i)) w := by
  have d : (⟨p, k⟩ : Region).Disjoint ⟨a + BitVec.ofNat 64 (w * i), w⟩ :=
    hd.mono (Region.covers_self p k) (arr_covers a hi) hk hw
  exact readLE_writeLE_disjoint d

end NoCompiler.Lib

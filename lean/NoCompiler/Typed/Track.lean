import NoCompiler.Typed.Bytes

/-
The copy relation for value invariants (docs/typed/value-tracker.md): memory is the entry memory
with a prefix of one range copied to another, and a store of the next bytes extends it.
-/
namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed.Bytes

/-- Memory `m` is the entry memory `m0` with `d[0, c)` holding the pattern `G` (byte `j` of the
    prefix is `G j`): a copy (`G = srcPat m0 src`) or a fill (`G` periodic). -/
def Written (m0 m : Word → Byte) (d : Word) (G : Nat → Byte) (c : Nat) : Prop :=
  ∀ p, m p = if (p - d).toNat < c then G (p - d).toNat else m0 p

/-- The pattern of a copy from `src`: byte `j` is the entry memory's at `src + j`. -/
def srcPat (m0 : Word → Byte) (src : Word) : Nat → Byte := fun j => m0 (src + BitVec.ofNat 64 j)

/-- Memory `m` is the entry memory `m0` with the first `c` bytes of `src` copied to `d`. -/
def Copied (m0 m : Word → Byte) (d src : Word) (c : Nat) : Prop :=
  ∀ p, m p = if (p - d).toNat < c then m0 (src + (p - d)) else m0 p

theorem copied_iff_written {m0 m : Word → Byte} {d src : Word} {c : Nat} :
    Copied m0 m d src c ↔ Written m0 m d (srcPat m0 src) c := by
  unfold Copied Written srcPat
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem Written.zero (m0 : Word → Byte) (d : Word) (G : Nat → Byte) : Written m0 m0 d G 0 := by
  intro p; simp

/-- A store of `k ≤ 8` bytes of `w` at `d + c`, whose bytes are the pattern's next `k`, extends
    the written prefix to `c + k`. -/
theorem Written.store {m0 m : Word → Byte} {d : Word} {G : Nat → Byte} {c : Nat}
    (h : Written m0 m d G c) (w : Word) {k : Nat} (hk : k ≤ 8) (hck : c + k < 2 ^ 64)
    (hw : ∀ i < k, byte w i = G (c + i)) :
    Written m0 (writeLE m (d + BitVec.ofNat 64 c) w.toNat k) d G (c + k) := by
  intro p
  rw [writeLE_apply _ _ _ (by omega), h p]
  have hc : c < 2 ^ 64 := by omega
  by_cases h1 : (p - (d + BitVec.ofNat 64 c)).toNat < k
  · rw [if_pos h1]
    have e : (p - d).toNat = c + (p - (d + BitVec.ofNat 64 c)).toNat := by bv_omega
    rw [if_pos (by omega)]
    have hb := hw _ h1
    rw [byte_eq] at hb
    have e2 : (2 : Nat) ^ (8 * (p - (d + BitVec.ofNat 64 c)).toNat) = 256 ^ (p - (d + BitVec.ofNat 64 c)).toNat := by
      rw [Nat.pow_mul]
    rw [e2] at hb
    rw [hb, e]
  · rw [if_neg h1]
    by_cases h2 : (p - d).toNat < c
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by bv_omega)]

theorem Copied.zero (m0 : Word → Byte) (d src : Word) : Copied m0 m0 d src 0 := by
  intro p; simp

/-- A store of `k ≤ 8` bytes of `w` at `d + c`, whose bytes are the next `k` source bytes,
    extends the copied prefix to `c + k`. -/
theorem Copied.store {m0 m : Word → Byte} {d src : Word} {c : Nat} (h : Copied m0 m d src c)
    (w : Word) {k : Nat} (hk : k ≤ 8) (hck : c + k < 2 ^ 64)
    (hw : ∀ i < k, byte w i = m0 (src + BitVec.ofNat 64 (c + i))) :
    Copied m0 (writeLE m (d + BitVec.ofNat 64 c) w.toNat k) d src (c + k) := by
  intro p
  rw [writeLE_apply _ _ _ (by omega), h p]
  have hc : c < 2 ^ 64 := by omega
  by_cases h1 : (p - (d + BitVec.ofNat 64 c)).toNat < k
  · rw [if_pos h1]
    have e : (p - d).toNat = c + (p - (d + BitVec.ofNat 64 c)).toNat := by bv_omega
    rw [if_pos (by omega)]
    have hb := hw _ h1
    rw [byte_eq] at hb
    have e2 : (2 : Nat) ^ (8 * (p - (d + BitVec.ofNat 64 c)).toNat) = 256 ^ (p - (d + BitVec.ofNat 64 c)).toNat := by
      rw [Nat.pow_mul]
    rw [e2] at hb
    rw [hb]
    congr 1
    bv_omega
  · rw [if_neg h1]
    by_cases h2 : (p - d).toNat < c
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by bv_omega)]

/-- Everything copied gives the copy's bytes. -/
theorem Copied.bytes {m0 m : Word → Byte} {d src : Word} {n : Nat} (h : Copied m0 m d src n)
    (hn : n < 2 ^ 64) : ∀ j < n, m (d + BitVec.ofNat 64 j) = m0 (src + BitVec.ofNat 64 j) := by
  intro j hj
  rw [h]
  have e : (d + BitVec.ofNat 64 j - d) = BitVec.ofNat 64 j := by bv_omega
  rw [e, if_pos (by simp [BitVec.toNat_ofNat]; omega)]

end NoCompiler.Typed.Track

namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed.Bytes

/-- What a register's byte is known to hold: anything, zero, or source byte `c + o` (relative
    to the copied prefix `c`). -/
inductive Cell where
  | unk
  | zero
  | src (o : Nat)
  deriving DecidableEq, Repr

/-- A byte of word `w` satisfies its cell (`src o`: the pattern's byte `c + o`). -/
def Cell.ok (G : Nat → Byte) (c : Nat) (w : Word) (i : Nat) : Cell → Prop
  | .unk => True
  | .zero => byte w i = 0#8
  | .src o => byte w i = G (c + o)

/-- Eight cells, one per byte (missing ones are `unk`). -/
abbrev Cells := List Cell

def Cells.ok (G : Nat → Byte) (c : Nat) (w : Word) (cs : Cells) : Prop :=
  ∀ i < 8, (cs.getD i .unk).ok G c w i

def Cells.shl (b : Nat) (cs : Cells) : Cells :=
  (List.range 8).map fun i => if i < b then .zero else cs.getD (i - b) .unk

def Cells.shr (b : Nat) (cs : Cells) : Cells :=
  (List.range 8).map fun i => if i + b < 8 then cs.getD (i + b) .unk else .zero

/-- `srliw` by `8b` with `1 ≤ b ≤ 3`. -/
def Cells.srliw (b : Nat) (cs : Cells) : Cells :=
  (List.range 8).map fun i => if i + b < 4 then cs.getD (i + b) .unk else .zero

def Cell.or : Cell → Cell → Cell
  | .zero, y => y
  | x, .zero => x
  | x, y => if x = y then x else .unk

def Cells.or (xs ys : Cells) : Cells :=
  (List.range 8).map fun i => (xs.getD i .unk).or (ys.getD i .unk)

theorem getD_range_map (f : Nat → Cell) {i : Nat} (hi : i < 8) :
    ((List.range 8).map f).getD i .unk = f i := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem Cells.shl_ok {G c w cs} (b : Nat) (h : Cells.ok G c w cs) :
    Cells.ok G c (w <<< (8 * b)) (cs.shl b) := by
  intro i hi
  rw [Cells.shl, getD_range_map _ hi]
  split
  · show byte _ i = 0#8
    rw [byte_shiftLeft w hi, if_pos (by assumption)]
  · have := h (i - b) (by omega)
    revert this
    cases cs.getD (i - b) .unk <;> simp only [Cell.ok] <;> intro hc <;>
      first | trivial | (rw [byte_shiftLeft w hi, if_neg (by assumption)]; exact hc)

theorem Cells.shr_ok {G c w cs} (b : Nat) (h : Cells.ok G c w cs) :
    Cells.ok G c (w >>> (8 * b)) (cs.shr b) := by
  intro i hi
  rw [Cells.shr, getD_range_map _ hi]
  split
  · have := h (i + b) (by assumption)
    revert this
    cases cs.getD (i + b) .unk <;> simp only [Cell.ok] <;> intro hc <;>
      first | trivial | (rw [byte_ushiftRight w hi, if_pos (by assumption)]; exact hc)
  · show byte _ i = 0#8
    rw [byte_ushiftRight w hi, if_neg (by assumption)]

theorem Cells.srliw_ok {G c w cs} {b : Nat} (hb : 1 ≤ b) (hb4 : b ≤ 3)
    (h : Cells.ok G c w cs) :
    Cells.ok G c (((w.setWidth 32) >>> (8 * b)).signExtend 64) (cs.srliw b) := by
  intro i hi
  rw [Cells.srliw, getD_range_map _ hi]
  split
  · have := h (i + b) (by omega)
    revert this
    cases cs.getD (i + b) .unk <;> simp only [Cell.ok] <;> intro hc <;>
      first | trivial | (rw [byte_srliw w hi hb hb4, if_pos (by assumption)]; exact hc)
  · show byte _ i = 0#8
    rw [byte_srliw w hi hb hb4, if_neg (by assumption)]

theorem Cell.or_ok {G c x y i} {a b : Cell} (ha : a.ok G c x i) (hb : b.ok G c y i) :
    (a.or b).ok G c (x ||| y) i := by
  cases a with
  | unk => cases b <;> simp [Cell.or, Cell.ok]
  | zero =>
    simp only [Cell.ok] at ha
    cases b with
    | unk => simp [Cell.or, Cell.ok]
    | zero => simp only [Cell.or, Cell.ok] at hb ⊢; rw [byte_or_zero_left ha]; exact hb
    | src o => simp only [Cell.or, Cell.ok] at hb ⊢; rw [byte_or_zero_left ha]; exact hb
  | src o =>
    simp only [Cell.ok] at ha
    cases b with
    | unk => simp [Cell.or, Cell.ok]
    | zero => simp only [Cell.or, Cell.ok] at hb ⊢; rw [byte_or_zero_right hb]; exact ha
    | src o' =>
      simp only [Cell.ok] at hb
      simp only [Cell.or]
      split
      · rename_i he
        cases he
        simp only [Cell.ok]
        rw [byte_or, ha, hb]
        simp
      · simp [Cell.ok]

theorem Cells.or_ok {G c x y xs ys} (hx : Cells.ok G c x xs) (hy : Cells.ok G c y ys) :
    Cells.ok G c (x ||| y) (xs.or ys) := by
  intro i hi
  rw [Cells.or, getD_range_map _ hi]
  exact Cell.or_ok (hx i hi) (hy i hi)

end NoCompiler.Typed.Track

namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed.Bytes

/-- The cells relative to a prefix `k` bytes longer (bytes before it are already copied: unknown). -/
def Cells.rebase (k : Nat) (cs : Cells) : Cells :=
  cs.map fun | .src o => (if o < k then .unk else .src (o - k)) | x => x

theorem Cells.rebase_ok {G c w cs} (k : Nat) (h : Cells.ok G c w cs) :
    Cells.ok G (c + k) w (cs.rebase k) := by
  intro i hi
  have := h i hi
  simp only [Cells.rebase, List.getD_eq_getElem?_getD, List.getElem?_map] at this ⊢
  cases hc : cs[i]? with
  | none => simp [Cell.ok]
  | some x =>
    rw [hc] at this
    cases x with
    | unk => simp [Cell.ok]
    | zero => simpa [Cell.ok] using this
    | src o =>
      simp only [Option.map_some, Option.getD_some]
      split
      · simp [Cell.ok]
      · simp only [Cell.ok] at this ⊢
        rw [show c + k + (o - k) = c + o by omega]; exact this

/-- Source and destination ranges apart: every source byte is outside `d[0, n)`. -/
def Disj (d src : Word) (n : Nat) : Prop := ∀ j < n, n ≤ (src + BitVec.ofNat 64 j - d).toNat

/-- Inside the source range, the current memory still holds the entry bytes. -/
theorem Copied.src {m0 m : Word → Byte} {d src : Word} {c n : Nat} (h : Copied m0 m d src c)
    (hd : Disj d src n) (hc : c ≤ n) {j : Nat} (hj : j < n) :
    m (src + BitVec.ofNat 64 j) = m0 (src + BitVec.ofNat 64 j) := by
  rw [h, if_neg (by have := hd j hj; omega)]

/-- The cells of a load of `w` bytes from source byte `c + o` (sign bits unknown, or zero). -/
def Cells.load (o : Nat) (w : Nat) : Cells :=
  (List.range 8).map fun i => if i < w then .src (o + i) else .unk

end NoCompiler.Typed.Track

namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed.Bytes

/-- The bytes of a loaded value are the memory's, for the loads that do not sign-extend past
    the loaded width's bytes (all of them, below the width). -/
theorem byte_loadVal (op : LdOp) (m : Word → Byte) (a : Word) {i : Nat} (hi : i < op.width)
    (hop : op ≠ .lh ∧ op ≠ .lhu) :
    byte (loadVal op m a) i = m (a + BitVec.ofNat 64 i) := by
  cases op with
  | lb =>
    simp only [LdOp.width] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    simp only [loadVal]
    rw [byte_signExtend8]
    have := (m a).isLt
    apply BitVec.eq_of_toNat_eq
    simp [readLE, Nat.mod_eq_of_lt this]
  | lbu => simp only [LdOp.width] at hi; exact byte_ofNat_readLE m a (by decide) hi
  | lw =>
    simp only [LdOp.width] at hi
    simp only [loadVal]
    rw [byte_signExtend32 _ hi, setWidth_ofNat32 (by have := readLE_lt m a 4; omega)]
    exact byte_ofNat_readLE m a (by decide) hi
  | lwu => simp only [LdOp.width] at hi; exact byte_ofNat_readLE m a (by decide) hi
  | ld => simp only [LdOp.width] at hi; exact byte_ofNat_readLE m a (by decide) hi
  | lh => exact absurd rfl hop.1
  | lhu => exact absurd rfl hop.2

end NoCompiler.Typed.Track

namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed.Bytes

/-- A load of `op` from source byte `c + o` (inside `src[0, n)`, which `d[0, n)` misses) gives
    the cells `load o width`. -/
theorem Cells.load_ok {m0 m : Word → Byte} {d srcB : Word} {c n : Nat}
    (hC : Written m0 m d (srcPat m0 srcB) c)
    (hd : Disj d srcB n) (hcn : c ≤ n) (op : LdOp) (hop : op ≠ .lh ∧ op ≠ .lhu) (o : Nat)
    (hin : c + o + op.width ≤ n) :
    Cells.ok (srcPat m0 srcB) c (loadVal op m (srcB + BitVec.ofNat 64 (c + o))) (Cells.load o op.width) := by
  intro i hi
  rw [Cells.load, getD_range_map _ hi]
  split
  · rename_i hw
    show byte _ i = _
    rw [byte_loadVal op m _ hw hop]
    have e : srcB + BitVec.ofNat 64 (c + o) + BitVec.ofNat 64 i = srcB + BitVec.ofNat 64 (c + (o + i)) := by
      rw [BitVec.add_assoc]; congr 1; rw [← Nat.add_assoc]; exact (BitVec.ofNat_add _ _).symm
    rw [e, (copied_iff_written.2 hC).src hd hcn (by omega)]
    rfl
  · trivial

end NoCompiler.Typed.Track

namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed.Bytes

/-- A store of `k` bytes of a register whose first `k` cells are the next source bytes, at
    `d + c`, extends the copied prefix to `c + k`. -/
theorem Cells.store_ok {m0 m : Word → Byte} {d : Word} {G : Nat → Byte} {c : Nat}
    (hC : Written m0 m d G c)
    {w : Word} {cs : Cells} (hcs : Cells.ok G c w cs) {k : Nat} (hk : k ≤ 8)
    (hck : c + k < 2 ^ 64) (hpre : ∀ i < k, cs.getD i .unk = .src i) :
    Written m0 (writeLE m (d + BitVec.ofNat 64 c) w.toNat k) d G (c + k) :=
  hC.store w hk hck fun i hi => by
    have := hcs i (by omega)
    rw [hpre i hi] at this
    exact this

/-- A fill's pattern repeats with period `P`: the cells of a register stay valid when the
    prefix grows by a multiple of `P` (a fill register keeps its value across iterations). -/
theorem Cells.ok_periodic {G : Nat → Byte} {P : Nat} (hG : ∀ j, G (j + P) = G j) {c : Nat}
    {w : Word} {cs : Cells} (h : Cells.ok G c w cs) (m : Nat) : Cells.ok G (c + P * m) w cs := by
  have hper : ∀ m j, G (j + P * m) = G j := by
    intro m; induction m with
    | zero => intro j; simp
    | succ m ih => intro j; rw [Nat.mul_succ, ← Nat.add_assoc, hG, ih]
  intro i hi
  have := h i hi
  revert this
  cases cs.getD i .unk <;> simp only [Cell.ok] <;> intro hc <;> first | trivial | skip
  rename_i o
  rw [show c + P * m + o = (c + o) + P * m by omega, hper]; exact hc

/-- A pattern with period `P` takes equal values at positions equal mod `P`. -/
theorem periodic_eq {G : Nat → Byte} {P : Nat} (hG : ∀ j, G (j + P) = G j) {x y : Nat}
    (h : x % P = y % P) : G x = G y := by
  have hper : ∀ m j, G (j + P * m) = G j := by
    intro m; induction m with
    | zero => intro j; simp
    | succ m ih => intro j; rw [Nat.mul_succ, ← Nat.add_assoc, hG, ih]
  have ex : ∀ z, G z = G (z % P) := fun z => by
    conv => lhs; rw [← Nat.mod_add_div z P]
    exact hper _ _
  rw [ex x, ex y, h]

end NoCompiler.Typed.Track

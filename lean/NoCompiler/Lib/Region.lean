import NoCompiler.Auto
import NoCompiler.Lemmas
import NoCompiler.Vocab.Memory

/-!
# Library: regions

Generic facts about `Region` (`base`, `size`, wrapping at 2^64; Step.lean), its `mem`/`covers`
(Step.lean) and `Region.Disjoint` (Auto.lean): membership at an offset, covering a sub-range,
disjointness and what it gives about members, and the bridge to `Fast.Disjoint`. Nothing about
any binary's addresses. Round 7, B's row.
-/

namespace NoCompiler

namespace Region

theorem mem_iff (r : Region) (x : Word) : r.mem x ↔ (x - r.base).toNat < r.size := Iff.rfl

theorem covers_iff (r : Region) (a : Word) (n : Nat) :
    r.covers a n ↔ (a - r.base).toNat + n ≤ r.size := Iff.rfl

/-- The first byte of a nonempty region is in it. -/
theorem mem_base {r : Region} (h : 0 < r.size) : r.mem r.base := by
  simp [mem]; exact h

/-- The byte at offset `k` of a region is in it. -/
theorem mem_add {r : Region} {k : Nat} (h : k < r.size) : r.mem (r.base + BitVec.ofNat 64 k) := by
  unfold mem
  have e : r.base + BitVec.ofNat 64 k - r.base = BitVec.ofNat 64 k := by bv_omega
  rw [e, BitVec.toNat_ofNat]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) h

/-- A region covers its own bytes. -/
theorem covers_self (a : Word) (n : Nat) : (⟨a, n⟩ : Region).covers a n := by
  simp [covers]

/-- Covering `n` bytes covers fewer. -/
theorem covers_le {r : Region} {a : Word} {n m : Nat} (h : r.covers a n) (hm : m ≤ n) :
    r.covers a m := by
  unfold covers at *; omega

/-- Covering `n` bytes from `a` covers any sub-range `[a + j, a + j + len)`. -/
theorem covers_sub {r : Region} {a : Word} {n : Nat} (h : r.covers a n) (j len : Nat)
    (hj : j + len ≤ n) : r.covers (a + BitVec.ofNat 64 j) len := by
  unfold covers at *
  have e : a + BitVec.ofNat 64 j - r.base = (a - r.base) + BitVec.ofNat 64 j := by bv_omega
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1 : ((a - r.base).toNat + j % 2 ^ 64) % 2 ^ 64 ≤ (a - r.base).toNat + j :=
    Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
  omega

/-- A covered byte is a member. -/
theorem mem_of_covers {r : Region} {a : Word} {n : Nat} (h : r.covers a n) {j : Nat} (hj : j < n) :
    r.mem (a + BitVec.ofNat 64 j) :=
  covers_mem h (by
    have e : a + BitVec.ofNat 64 j - a = BitVec.ofNat 64 j := by bv_omega
    rw [e, BitVec.toNat_ofNat]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hj)

/-- Covering is transitive: a range inside `r'`, itself inside `r`, is inside `r`. -/
theorem covers_trans {r r' : Region} {a : Word} {n : Nat} (h : r'.covers a n)
    (h' : r.covers r'.base r'.size) : r.covers a n := by
  unfold covers at *
  have e : a - r.base = (a - r'.base) + (r'.base - r.base) := by bv_omega
  rw [e, BitVec.toNat_add]
  exact Nat.le_trans (Nat.add_le_add_right (Nat.mod_le _ _) _) (by omega)

/-! ## Disjointness -/

theorem disjoint_iff (r r' : Region) :
    r.Disjoint r' ↔ r.size ≤ (r'.base - r.base).toNat ∧ r'.size ≤ (r.base - r'.base).toNat :=
  Iff.rfl

/-- An empty region is disjoint from every region that does not wrap all the way round. -/
theorem disjoint_empty_left (a : Word) (r : Region) (h : r.size ≤ (a - r.base).toNat) :
    (⟨a, 0⟩ : Region).Disjoint r := ⟨Nat.zero_le _, h⟩

-- `Region.Disjoint.not_mem` (no byte is in two disjoint regions) is NoCompiler.Vocab.Memory's.

/-- Two members of disjoint regions are different addresses. -/
theorem Disjoint.ne {r r' : Region} (h : r.Disjoint r') {x y : Word} (hx : r.mem x)
    (hy : r'.mem y) : x ≠ y := by
  rintro rfl; exact h.not_mem hx hy

/-- The byte `b` is `a` plus `(b - a).toNat`. -/
theorem add_sub_toNat (a b : Word) : a + BitVec.ofNat 64 (b - a).toNat = b := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega

/-- Disjointness passes to nonempty sub-regions on both sides. (An empty region is not
    disjoint from a region around its base, by `Region.Disjoint`'s definition.) -/
theorem Disjoint.mono {r r' s s' : Region} (h : r.Disjoint s) (hr : r.covers r'.base r'.size)
    (hs : s.covers s'.base s'.size) (hr0 : 0 < r'.size) (hs0 : 0 < s'.size) :
    r'.Disjoint s' := by
  constructor
  · apply Nat.le_of_not_lt; intro hlt
    have hx : r.mem s'.base := by
      have := mem_of_covers hr hlt; rwa [add_sub_toNat] at this
    have hy : s.mem s'.base := by
      have := mem_of_covers hs hs0; simpa using this
    exact h.not_mem hx hy
  · apply Nat.le_of_not_lt; intro hlt
    have hx : s.mem r'.base := by
      have := mem_of_covers hs hlt; rwa [add_sub_toNat] at this
    have hy : r.mem r'.base := by
      have := mem_of_covers hr hr0; simpa using this
    exact h.not_mem hy hx

/-- `Region.Disjoint` of two ranges is `Fast.Disjoint` of them. -/
theorem disjoint_iff_fast (a b : Word) (k n : Nat) :
    (⟨a, k⟩ : Region).Disjoint ⟨b, n⟩ ↔ Fast.Disjoint a k b n := by
  unfold Region.Disjoint Fast.Disjoint; exact And.comm

/-- A region split in two at `n` (a nonempty first half that does not wrap): the halves are
    disjoint. -/
theorem disjoint_split (a : Word) {n m : Nat} (h0 : 0 < n) (hn : n < 2 ^ 64) (h : n + m ≤ 2 ^ 64) :
    (⟨a, n⟩ : Region).Disjoint ⟨a + BitVec.ofNat 64 n, m⟩ := by
  constructor
  · have e : a + BitVec.ofNat 64 n - a = BitVec.ofNat 64 n := by bv_omega
    rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; exact Nat.le_refl _
  · have e : a - (a + BitVec.ofNat 64 n) = -(BitVec.ofNat 64 n) := by bv_omega
    rw [e, BitVec.toNat_neg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    simp only [Nat.reducePow] at *
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- Disjoint from a range, disjoint from any nonempty sub-range of it. -/
theorem Disjoint.sub {r : Region} {a : Word} {n : Nat} (h : r.Disjoint ⟨a, n⟩) (j len : Nat)
    (hj : j + len ≤ n) (hl : 0 < len) (hr : 0 < r.size) :
    r.Disjoint ⟨a + BitVec.ofNat 64 j, len⟩ :=
  h.mono (covers_self _ _) (covers_sub (covers_self a n) j len hj) hr hl

end Region

namespace Perm

/-- A region listed as writable lets every range it covers be written. -/
theorem canWrite_of_mem {P : Perm} {r : Region} (hr : r ∈ P.wr) {a : Word} {n : Nat}
    (hc : r.covers a n) : P.canWrite a n := .inr ⟨r, hr, hc⟩

/-- A region listed as readable (or writable) lets every range it covers be read. -/
theorem canRead_of_mem {P : Perm} {r : Region} (hr : r ∈ P.rd ++ P.wr) {a : Word} {n : Nat}
    (hc : r.covers a n) : P.canRead a n := .inr ⟨r, hr, hc⟩

/-- Read permission for `n` bytes gives it for any sub-range. -/
theorem canRead_sub {P : Perm} {a : Word} {n : Nat} (h : P.canRead a n) (j len : Nat)
    (hj : j + len ≤ n) : P.canRead (a + BitVec.ofNat 64 j) len := by
  rcases h with h | ⟨r, hr, hc⟩
  · exact .inl (by omega)
  · exact .inr ⟨r, hr, Region.covers_sub hc j len hj⟩

/-- Write permission for `n` bytes gives it for any sub-range. -/
theorem canWrite_sub {P : Perm} {a : Word} {n : Nat} (h : P.canWrite a n) (j len : Nat)
    (hj : j + len ≤ n) : P.canWrite (a + BitVec.ofNat 64 j) len := by
  rcases h with h | ⟨r, hr, hc⟩
  · exact .inl (by omega)
  · exact .inr ⟨r, hr, Region.covers_sub hc j len hj⟩

/-- Fewer bytes from the same address. -/
theorem canRead_le {P : Perm} {a : Word} {n m : Nat} (h : P.canRead a n) (hm : m ≤ n) :
    P.canRead a m := by
  have := canRead_sub h 0 m (by omega); simpa using this

theorem canWrite_le {P : Perm} {a : Word} {n m : Nat} (h : P.canWrite a n) (hm : m ≤ n) :
    P.canWrite a m := by
  have := canWrite_sub h 0 m (by omega); simpa using this

/-- Nothing to read or write. -/
theorem canRead_zero (P : Perm) (a : Word) : P.canRead a 0 := .inl rfl
theorem canWrite_zero (P : Perm) (a : Word) : P.canWrite a 0 := .inl rfl

/-- `top` allows every range of at most 2^64 bytes. -/
theorem top_canWrite (a : Word) {n : Nat} (hn : n ≤ 2 ^ 64 - (a - 0).toNat) : top.canWrite a n :=
  .inr ⟨⟨0, 2 ^ 64⟩, by simp [top], by unfold Region.covers; simp only at *; omega⟩

/-- A permission that allows `Q`'s reads and writes allows its reads of written ranges. -/
theorem le.canRead {P Q : Perm} (h : P.le Q) {a : Word} {n : Nat} (hp : P.canWrite a n) :
    Q.canRead a n := h.read a n (canRead_of_canWrite hp)

end Perm

end NoCompiler

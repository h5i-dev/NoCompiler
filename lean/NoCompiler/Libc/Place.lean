import NoCompiler.Libc.Relocate

/-!
# Placing a library function's theorem in another image

A library function is proved once over its own image `img` (scripts/libc/fn_image.py: its words at the address
of the build they came from). The theorem then holds in any image `c` that has the same words at `base + δ`, when
every word of `img` decodes to a pcFree instruction (`Code.allPcFree`, decided once per function) and the
specification does not look at the pc or `ra` (`SpecP.ShiftInv`): `VerifiedProc.place`.
-/
namespace NoCompiler.Linux
open NoCompiler

/-- Every word of `c` decodes to a pcFree instruction (or to none). -/
def _root_.NoCompiler.Code.allPcFree (c : Code) : Bool := c.words.all fun w => match decode w with
  | some i => i.pcFree
  | none => true

theorem _root_.NoCompiler.Code.pcFree_of_all {c : Code} (h : c.allPcFree = true) (x : Word) (i : Instr) (hi : c.instr x = some i) :
    i.pcFree = true := by
  unfold Code.instr Code.fetch at hi
  dsimp only at hi
  split at hi
  · cases hw : c.words[(x - c.base).toNat / 4]? with
    | none => rw [hw] at hi; cases hi
    | some w =>
      rw [hw] at hi
      simp only [Option.bind_some] at hi
      have hm : w ∈ c.words := Array.mem_of_getElem? hw
      have := (Array.all_eq_true.1 h)
      obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hm
      have hj' := this j hj
      simp only [hi] at hj'
      exact hj'
  · cases hi

/-- `img`'s theorem at `base + δ` in `c`, from `c`'s words there. -/
theorem VerifiedProc.place {α : Type} {img c : Code} {D : Dom} {e δ : Word} {sp : SpecP α}
    (hv : VerifiedProc img D e sp) (hs : sp.ShiftInv) (hf : img.allPcFree = true) (hδ : aligned δ 4)
    (hc : ∀ x, D.mem x → c.instr (x + δ) = img.instr x) : VerifiedProc c (D.shift δ) (e + δ) sp :=
  VerifiedProc.shift ⟨hc, fun x i _ hi => Code.pcFree_of_all hf x i hi, hδ⟩ hs hv

/-- `c` holds `img`'s words at `img.base + δ` (word-aligned in `c`, not wrapping): a check by `decide`. -/
def _root_.NoCompiler.Code.holdsAt (c img : Code) (δ : Word) : Bool :=
  let A := (img.base + δ - c.base).toNat
  A % 4 == 0 && decide (A + 4 * img.words.size < 2 ^ 64) &&
    (List.range img.words.size).all fun i => c.words[A / 4 + i]? == img.words[i]?

theorem _root_.NoCompiler.Code.instr_of_holdsAt {c img : Code} {δ : Word} (h : c.holdsAt img δ = true) :
    ∀ x, Dom.mem [(img.base, 4 * img.words.size)] x → c.instr (x + δ) = img.instr x := by
  intro x hx
  simp only [Code.holdsAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hA4, hAn⟩, hw⟩ := h
  simp only [Dom.mem, List.any_cons, List.any_nil, Bool.or_false, decide_eq_true_eq] at hx
  have hoff : (x + δ - c.base).toNat = (img.base + δ - c.base).toNat + (x - img.base).toNat := by
    have : x + δ - c.base = (img.base + δ - c.base) + (x - img.base) := by bv_omega
    rw [this, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  unfold Code.instr Code.fetch
  dsimp only
  rw [hoff]
  by_cases h4 : (x - img.base).toNat % 4 = 0
  · rw [if_pos (by omega), if_pos h4]
    have e : ((img.base + δ - c.base).toNat + (x - img.base).toNat) / 4 =
        (img.base + δ - c.base).toNat / 4 + (x - img.base).toNat / 4 := by omega
    rw [e, hw _ (by omega)]
  · rw [if_neg (by omega), if_neg h4]

/-- `img`'s theorem in `c` at `img.base + δ`, from the check `c.holdsAt img δ`. -/
theorem VerifiedProc.placeAt {α : Type} {img c : Code} {e δ : Word} {sp : SpecP α}
    (hv : VerifiedProc img [(img.base, 4 * img.words.size)] e sp) (hs : sp.ShiftInv) (hf : img.allPcFree = true)
    (hδ : aligned δ 4) (hc : c.holdsAt img δ = true) :
    VerifiedProc c (Dom.shift δ [(img.base, 4 * img.words.size)]) (e + δ) sp :=
  VerifiedProc.place hv hs hf hδ (Code.instr_of_holdsAt hc)

/-- The same for a state-level theorem (`VerifiedImg`, `Spec`): `img`'s theorem in `c` at `img.base + δ`. -/
theorem _root_.NoCompiler.VerifiedImg.placeAt {α : Type} {img c : Code} {e δ : Word} {sp : Spec α}
    (hv : VerifiedImg img [(img.base, 4 * img.words.size)] e sp) (hs : sp.ShiftInv) (hf : img.allPcFree = true)
    (hδ : aligned δ 4) (hc : c.holdsAt img δ = true) :
    VerifiedImg c (Dom.shift δ [(img.base, 4 * img.words.size)]) (e + δ) sp :=
  VerifiedImg.shift ⟨Code.instr_of_holdsAt hc, fun x i _ hi => Code.pcFree_of_all hf x i hi, hδ⟩ hs hv

/-- An exported image's chunk `ck` (at `B`) and a library image of one chunk `c0` with the same words, at the
    chunk's address: the same instructions there. Compares the chunks' lengths and bits only. -/
theorem _root_.NoCompiler.Code.chunk_instr_eq {B b : Word} {ck c0 : Chunk} (hl : c0.len = ck.len)
    (hbits : c0.bits = ck.bits) (h0 : c0.off = 0) (hb : b = B + BitVec.ofNat 64 (4 * ck.off))
    (hcont : Chunk.contig 0 [c0] = true) (hbd : 4 * Chunk.total [c0] < 2 ^ 64) :
    ∀ x, Dom.mem [ck.range B] x → (ck.code B).instr x = (Code.ofChunks b [c0]).instr x := by
  intro x hx
  have hr : c0.range b = ck.range B := by simp only [Chunk.range, h0, hl, hb, Nat.mul_zero, BitVec.add_zero]
  rw [Code.ofChunks_instr (k := 0) hcont rfl hbd x (by rw [hr]; exact hx)]
  have hw : c0.words = ck.words := by unfold Chunk.words; rw [hl, hbits]
  have : c0.code b = ck.code B := by
    unfold Chunk.code; rw [h0, hb, hw]; simp only [Nat.mul_zero, BitVec.add_zero]
  rw [this]

/-- Two chunks with the same words at the same address are the same code. -/
theorem _root_.NoCompiler.Chunk.code_eq_of {B b : Word} {ck c : Chunk} (hl : c.len = ck.len) (hbits : c.bits = ck.bits)
    (ha : b + BitVec.ofNat 64 (4 * c.off) = B + BitVec.ofNat 64 (4 * ck.off)) : c.code b = ck.code B := by
  have hw : c.words = ck.words := by unfold Chunk.words; rw [hl, hbits]
  unfold Chunk.code; rw [ha, hw]

/-- Two chunks with the same words at the same address cover the same range. -/
theorem _root_.NoCompiler.Chunk.range_eq_of {B b : Word} {ck c : Chunk} (hl : c.len = ck.len)
    (ha : b + BitVec.ofNat 64 (4 * c.off) = B + BitVec.ofNat 64 (4 * ck.off)) : c.range b = ck.range B := by
  unfold Chunk.range; rw [ha, hl]

/-- An image `c` that agrees with its chunk `ck` (at `B`) on the chunk's range (the exporter's `*_chunk` lemma) agrees
    there with a library image `Code.ofChunks b cs` whose chunk `k` has the same words at the same address. -/
theorem _root_.NoCompiler.Code.instr_eq_of_chunk {c : Code} {B b : Word} {cs : List Chunk} {ck c0 : Chunk} {k : Nat}
    (hcont : Chunk.contig 0 cs = true) (hk : cs[k]? = some c0) (hbd : 4 * Chunk.total cs < 2 ^ 64)
    (hc : ∀ x, Dom.mem [ck.range B] x → c.instr x = (ck.code B).instr x)
    (hl : c0.len = ck.len) (hbits : c0.bits = ck.bits)
    (ha : b + BitVec.ofNat 64 (4 * c0.off) = B + BitVec.ofNat 64 (4 * ck.off)) :
    ∀ x, Dom.mem [ck.range B] x → c.instr x = (Code.ofChunks b cs).instr x := by
  intro x hx
  rw [hc x hx, Code.ofChunks_instr hcont hk hbd x (by rw [Chunk.range_eq_of hl ha]; exact hx),
    Chunk.code_eq_of hl hbits ha]

theorem _root_.NoCompiler.Dom.mem_cons_iff {r : Word × Nat} {rs : Dom} {x : Word} :
    Dom.mem (r :: rs) x ↔ (x - r.1).toNat < r.2 ∨ Dom.mem rs x := by
  simp only [Dom.mem, List.any_cons, Bool.or_eq_true, decide_eq_true_eq]

theorem _root_.NoCompiler.Dom.mem_single_iff {r : Word × Nat} {x : Word} :
    Dom.mem [r] x ↔ (x - r.1).toNat < r.2 := by
  simp only [Dom.mem, List.any_cons, List.any_nil, Bool.or_false, decide_eq_true_eq]

/-- Two chunk images with chunks `c1` (in `cs1`, at `b1`) and `c2` (in `cs2`, at `b2`) holding the same words at the
    same address agree on that chunk's range: a library theorem over one image (`VerifiedProc.of_code_eq`) holds in
    the other, e.g. a callee's own image and its caller's. -/
theorem _root_.NoCompiler.Code.instr_eq_of_chunks {b1 b2 : Word} {cs1 cs2 : List Chunk} {c1 c2 : Chunk} {k1 k2 : Nat}
    (h1 : Chunk.contig 0 cs1 = true) (hk1 : cs1[k1]? = some c1) (hb1 : 4 * Chunk.total cs1 < 2 ^ 64)
    (h2 : Chunk.contig 0 cs2 = true) (hk2 : cs2[k2]? = some c2) (hb2 : 4 * Chunk.total cs2 < 2 ^ 64)
    (hl : c1.len = c2.len) (hbits : c1.bits = c2.bits)
    (ha : b1 + BitVec.ofNat 64 (4 * c1.off) = b2 + BitVec.ofNat 64 (4 * c2.off)) :
    ∀ x, Dom.mem [c2.range b2] x → (Code.ofChunks b1 cs1).instr x = (Code.ofChunks b2 cs2).instr x := by
  intro x hx
  rw [Code.ofChunks_instr h1 hk1 hb1 x (by rw [Chunk.range_eq_of hl ha]; exact hx),
    Code.ofChunks_instr h2 hk2 hb2 x hx, Chunk.code_eq_of hl hbits ha]


end NoCompiler.Linux

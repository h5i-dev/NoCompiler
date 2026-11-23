import LPS.Bridge.HexImage
import NoCompiler.Image

/-!
# The per-image facts for an exported image, chunk by chunk

`nocompiler export` writes `.text` as chunks (`Code.ofChunks base cs`). `codeFacts_ofChunks`: if each chunk's
own code passes the per-image check (`codeAgree segs (c.code base)`, small, one kernel evaluation per chunk,
on an image of `SegH`s by `codeAgree_hex`), then every word the whole image fetches has the facts the step
theorems take (`codeAgree_sound`'s conclusion).
-/

namespace LPS.Bridge
open NoCompiler LPS.RiscvSemantics

theorem chunk_of_index : ∀ (o : Nat) (cs : List Chunk) (i : Nat), Chunk.contig o cs = true → o ≤ i →
    i < o + Chunk.total cs → ∃ (k : Nat) (c : Chunk), cs[k]? = some c ∧ c.off ≤ i ∧ i < c.off + c.len
  | _, [], _, _, _, h2 => by simp [Chunk.total] at h2; omega
  | o, d :: ds, i, h, h1, h2 => by
    simp only [Chunk.contig, Bool.and_eq_true, beq_iff_eq] at h
    by_cases hi : i < o + d.len
    · exact ⟨0, d, rfl, by omega, by omega⟩
    · have ht : Chunk.total (d :: ds) = d.len + Chunk.total ds := by simp [Chunk.total]
      obtain ⟨k, c, hk, hc1, hc2⟩ := chunk_of_index (o + d.len) ds i h.2 (by omega) (by omega)
      exact ⟨k + 1, c, by rw [List.getElem?_cons_succ]; exact hk, hc1, hc2⟩

/-- Every word an exported image fetches has the per-image facts, from one check per chunk. -/
theorem codeFacts_ofChunks {segs : List Segment} {base : Word} {cs : List Chunk}
    (hc : Chunk.contig 0 cs = true) (hb : 4 * Chunk.total cs < 2 ^ 64)
    (ha : ∀ c ∈ cs, codeAgree segs (c.code base) = true) {pc : Word} {w : BitVec 32}
    (h : (Code.ofChunks base cs).fetch pc = some w) :
    fetch_word segs pc = some w ∧
      ∀ i j, NoCompiler.decode w = some i → toLPS i = some j →
        LPS.decode w = some j ∧ bv_unsigned (bits 0 2 w) = 3 := by
  have h' := h
  simp only [Code.fetch, Code.ofChunks] at h'
  by_cases hm : (pc - base).toNat % 4 = 0
  · simp only [hm, ite_true] at h'
    have hlt : (pc - base).toNat / 4 < Chunk.total cs := by
      rcases Nat.lt_or_ge ((pc - base).toNat / 4) (Chunk.total cs) with h1 | h1
      · exact h1
      · rw [List.getElem?_toArray, List.getElem?_eq_none (by rw [Chunk.length_flatten]; exact h1)] at h'
        cases h'
    obtain ⟨k, c, hk, hc1, hc2⟩ := chunk_of_index 0 cs ((pc - base).toNat / 4) hc (Nat.zero_le _) (by omega)
    have hx : (pc - (c.code base).base).toNat < 4 * c.len := by
      simp only [Chunk.code]
      have hoff : 4 * c.off < 2 ^ 64 := by omega
      have e : pc - (base + BitVec.ofNat 64 (4 * c.off)) = (pc - base) - BitVec.ofNat 64 (4 * c.off) := by
        bv_omega
      rw [e, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff]; omega),
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff]
      omega
    rw [Code.ofChunks_fetch hc hk hb hx] at h
    exact codeAgree_sound (ha c (List.mem_of_getElem? hk)) h
  · simp only [hm, ite_false] at h'; cases h'

end LPS.Bridge

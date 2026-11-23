import LPS.Bridge.StepStore

/-!
# Bridge: the per-image facts, as one Boolean check

The step theorems (Bridge/Step, StepStore) take, at the pc, LPS's fetch of a word `w`, NoCompiler's decode of
`w`, LPS's decode of `w` to `toLPS i`, and `w`'s low bits 11. `codeAgree segs c` checks all of them for every
word of a NoCompiler code image `c` against an LPS image `segs`, so that one evaluation per image (`decide`,
or `decide +kernel`) discharges them; `codeAgree_sound` turns it into exactly the hypotheses the step theorems
take.
-/

namespace LPS.Bridge
open NoCompiler LPS.RiscvSemantics

/-- The decoders agree on `w` wherever NoCompiler decodes it to an instruction LPS models. -/
def decodeAgree (w : BitVec 32) : Bool :=
  match NoCompiler.decode w with
  | none => true
  | some i => (bv_unsigned (bits 0 2 w) == 3) &&
    match toLPS i with
    | none => true
    | some j => LPS.decode w == some j

def wordOK (segs : List Segment) (pc : Word) (w : BitVec 32) : Bool :=
  fetch_word segs pc == some w && decodeAgree w

def codeAgree (segs : List Segment) (c : Code) : Bool :=
  (List.range c.words.size).all fun k => wordOK segs (c.base + BitVec.ofNat 64 (4 * k)) (c.words[k]?.getD 0)

theorem fetch_some {c : Code} {pc : Word} {w : BitVec 32} (h : c.fetch pc = some w) :
    ∃ k, k < c.words.size ∧ pc = c.base + BitVec.ofNat 64 (4 * k) ∧ c.words[k]?.getD 0 = w := by
  unfold Code.fetch at h
  dsimp only at h
  split at h
  · rename_i hm
    have hlt : (pc - c.base).toNat / 4 < c.words.size := by
      rcases Nat.lt_or_ge ((pc - c.base).toNat / 4) c.words.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at h; cases h
    refine ⟨_, hlt, ?_, ?_⟩
    · have e : 4 * ((pc - c.base).toNat / 4) = (pc - c.base).toNat := by omega
      rw [e, BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
    · rw [h]; rfl
  · cases h

/-- From the per-image check: at any pc where NoCompiler's code has `w`, LPS fetches `w`, and wherever
    NoCompiler decodes `w` to `i` with an LPS counterpart `j`, LPS decodes `w` to `j` and `w` is a 32-bit
    encoding. -/
theorem codeAgree_sound {segs : List Segment} {c : Code} (hc : codeAgree segs c = true) {pc : Word}
    {w : BitVec 32} (h : c.fetch pc = some w) :
    fetch_word segs pc = some w ∧
      ∀ i j, NoCompiler.decode w = some i → toLPS i = some j →
        LPS.decode w = some j ∧ bv_unsigned (bits 0 2 w) = 3 := by
  obtain ⟨k, hk, rfl, rfl⟩ := fetch_some h
  have hw := List.all_eq_true.1 hc k (List.mem_range.2 hk)
  simp only [wordOK, Bool.and_eq_true, beq_iff_eq] at hw
  refine ⟨hw.1, fun i j hi hj => ?_⟩
  have hd := hw.2
  simp only [decodeAgree, hi, hj, Bool.and_eq_true, beq_iff_eq] at hd
  exact ⟨hd.2, hd.1⟩

end LPS.Bridge

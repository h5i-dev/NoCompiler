import LPS.Bridge.RefineSimple

/-!
# Refinement for `brk`, the converse direction

`brk_covers`: every outcome LPS's `syscall_spec` admits for `brk(req)` (the current break, or `req`) is one
NoCompiler's model (`brkSpec`) allows, and the breaks stay related (`KernBrk`: NoCompiler's `startBrk`,
`brk` are LPS's `vm_start_brk`, `vm_brk`). The bytes the two zero on growth are compared separately
(`brk_zeros_agree`: on growth NoCompiler's zero range and LPS's `brk_zeros` cover the same bytes); the memory maps relation (NoCompiler's `maps` against LPS's `vm_maps`) is not
part of this file.
-/

namespace LPS.Bridge
open LPS.RiscvSemantics NoCompiler.Linux

/-- `brk` in NoCompiler's model, unfolded. -/
theorem procSpec7_brk {k k' : Kern} {i : NoCompiler.Linux.SyscallInput} {o : Outcome} (h : i.sysno = NoCompiler.Linux.sysBrk) :
    procSpec7 k i o k' ↔ brkSpec k (i.arg 0) o k' := by
  simp only [procSpec7, procSpec6, procSpec5, procSpec4, procSpec3, procSpec2, procSpec, h]
  simp (config := { decide := true })

structure KernBrk (k : Kern) (m : Model) : Prop where
  start : k.startBrk = (m_vmmaps m).vm_start_brk
  brk : k.brk = (m_vmmaps m).vm_brk

theorem m_vmmaps_forget (l : List (word × word)) (m : Model) : m_vmmaps (forget_vm_ranges l m) = m_vmmaps m := by
  induction l generalizing m with
  | nil => rfl
  | cons p r ih => obtain ⟨a, n⟩ := p; simp only [forget_vm_ranges]; rw [ih]; rfl

theorem brk_next_brk (m : Model) (req r : word) : (m_vmmaps (with_brk_next m req r)).vm_brk = r := by
  simp only [with_brk_next, m_vmmaps_forget]; rfl

theorem brk_next_start (m : Model) (req r : word) :
    (m_vmmaps (with_brk_next m req r)).vm_start_brk = (m_vmmaps m).vm_start_brk := by
  simp only [with_brk_next, m_vmmaps_forget]; rfl

/-- Every `brk` outcome LPS admits: its return is the current break or the request, as one of NoCompiler's
    outcomes, and the breaks stay related. (The zero ranges: see the module doc.) -/
theorem brk_covers {k : Kern} {i : NoCompiler.Linux.SyscallInput} {j : SyscallInput} {m m' : Model}
    {eff : SyscallEffect} {evs : List event} (hr : InRel i j) (h214 : i.sysno = NoCompiler.Linux.sysBrk)
    (hk : KernBrk k m) (hs : syscall_spec j m (Ok eff m' evs)) :
    ∃ zs k', procSpec7 k i (.ret { ret := eff.eff_ret, zeros := zs } none) k' ∧ KernBrk k' m' ∧ evs = [] ∧
      eff.eff_writes = [] := by
  have hn : bv_unsigned j.in_sysno = 214 := by rw [hr.sysno, h214]; rfl
  rw [lookup_arm_of (a := mkSpecArm 214 (fun i => brk_spec (in_arg i 0) i))
    (by simp [spec_table, lookup_arm, mkSpecArm]) j hn] at hs
  change brk_spec (in_arg j 0) j m (Ok eff m' evs) at hs
  unfold brk_spec at hs
  rw [bind_get_model] at hs
  obtain ⟨r, m1, e1, e2, ⟨r', hok, hr1⟩, hk2, rfl⟩ := hs
  cases hr1
  obtain ⟨x, m2, e3, e4, hmod, hret, rfl⟩ := hk2
  cases hmod
  have hret' : Ok eff m' e4 = Ok (mkEffectU r [] (brk_zeros (in_arg j 0) r (m_vmmaps m).vm_brk)
      (brk_unmaps r (m_vmmaps m).vm_brk) [] []) (with_brk_next m (in_arg j 0) r) [] := hret
  cases hret'
  rw [hr.args 0] at hok ⊢
  simp only [mkEffectU]
  generalize hreq : i.arg 0 = req at hok ⊢
  have hb : (m_vmmaps m).vm_brk = k.brk := hk.brk.symm
  have hst : (m_vmmaps m).vm_start_brk = k.startBrk := hk.start.symm
  have hw0 : w_is0 req = true ↔ req = 0 := by unfold w_is0; rw [bv_eqb_iff]; rfl
  have hlt : ∀ x y : word, bv_unsigned x < bv_unsigned y ↔ x.toNat < y.toNat := by
    intro x y; unfold bv_unsigned; omega
  simp only [brk_r_ok, min_brk] at hok
  simp only [hb, hst] at hok
  have hkb : ∀ r', r' = k.brk → KernBrk k (with_brk_next m req r') := fun r' h =>
    ⟨by rw [brk_next_start]; exact hk.start, by rw [brk_next_brk, h]⟩
  by_cases c1 : req = 0 ∨ req.toNat < k.startBrk.toNat
  · have c1' : (w_is0 req || decide (bv_unsigned req < bv_unsigned k.startBrk)) = true := by
      rcases c1 with h | h
      · simp [(hw0).2 h]
      · simp [(hlt _ _).2 h]
    rw [if_pos c1'] at hok
    have hrb : r = k.brk := bv_eqb_iff.1 hok
    refine ⟨[], k, ?_, hkb r hrb, rfl, trivial⟩
    rw [procSpec7_brk h214]; unfold brkSpec; rw [hreq, if_pos c1, hrb]; exact ⟨rfl, rfl⟩
  · have c1' : (w_is0 req || decide (bv_unsigned req < bv_unsigned k.startBrk)) = false := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
      exact ⟨by cases h : w_is0 req; rfl; exact absurd (.inl (hw0.1 h)) c1, fun h => c1 (.inr ((hlt _ _).1 h))⟩
    rw [if_neg (by simp [c1'])] at hok
    by_cases c2 : req.toNat < k.brk.toNat
    · rw [if_pos ((hlt _ _).2 c2)] at hok
      simp only [Bool.or_eq_true, bv_eqb_iff] at hok
      rcases hok with rfl | rfl
      · refine ⟨[], { k.unmap (BitVec.ofNat 64 (pageUp r)) (pageUp k.brk - pageUp r) with brk := r }, ?_,
          ⟨by rw [brk_next_start]; exact hk.start, by rw [brk_next_brk]⟩, rfl, trivial⟩
        rw [procSpec7_brk h214]; unfold brkSpec; rw [hreq, if_neg c1, if_pos c2]; exact .inl ⟨rfl, rfl⟩
      · refine ⟨[], k, ?_, hkb _ rfl, rfl, trivial⟩
        rw [procSpec7_brk h214]; unfold brkSpec; rw [hreq, if_neg c1, if_pos c2]; exact .inr ⟨rfl, rfl⟩
    · rw [if_neg (by rw [hlt]; exact c2)] at hok
      simp only [Bool.and_eq_true, Bool.or_eq_true, bv_eqb_iff] at hok
      rcases hok.1 with rfl | rfl
      · refine ⟨[(BitVec.ofNat 64 (pageUp k.brk), pageUp r - pageUp k.brk)],
          { k with brk := r, maps := (BitVec.ofNat 64 (pageUp k.brk), pageUp r - pageUp k.brk) :: k.maps }, ?_,
          ⟨by rw [brk_next_start]; exact hk.start, by rw [brk_next_brk]⟩, rfl, trivial⟩
        rw [procSpec7_brk h214]; unfold brkSpec; rw [hreq, if_neg c1, if_neg c2]; exact .inl ⟨rfl, rfl⟩
      · refine ⟨[], k, ?_, hkb _ rfl, rfl, trivial⟩
        rw [procSpec7_brk h214]; unfold brkSpec; rw [hreq, if_neg c1, if_neg c2]; exact .inr ⟨rfl, rfl⟩

end LPS.Bridge

namespace LPS.Bridge
open LPS.RiscvSemantics NoCompiler.Linux

/-- NoCompiler's `pageUp` is LPS's `page_round_up_Z`. -/
theorem pageUp_eq (x : word) : (pageUp x : Int) = page_round_up_Z (bv_unsigned x) := by
  unfold pageUp page_round_up_Z page_size Z.div bv_unsigned
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]
  omega

/-- The bytes a list of zero ranges covers. -/
def ZeroSet (zs : List (word × Nat)) (a : word) : Prop :=
  ∃ z ∈ zs, (a - z.1).toNat < z.2

def ZeroSetL (zs : List (word × word)) (a : word) : Prop :=
  ∃ z ∈ zs, (a - z.1).toNat < z.2.toNat

/-- On growth (`0 < old < r`, `r < 2^63`), NoCompiler's zero range `[pageUp old, pageUp r)` covers the bytes LPS's
    `brk_zeros` does. -/
theorem brk_zeros_agree (req r old : word) (hreq : w_is0 req = false) (h0 : 0 < old.toNat) (hlt : old.toNat < r.toNat)
    (hr : r.toNat < 2 ^ 63) (a : word) :
    ZeroSet [(BitVec.ofNat 64 (pageUp old), pageUp r - pageUp old)] a ↔ ZeroSetL (brk_zeros req r old) a := by
  have hg : brk_is_grow req r old = true := by
    unfold brk_is_grow bv_unsigned; simp [hreq]; omega
  have e1 := pageUp_eq old
  have e2 := pageUp_eq r
  have hpo : pageUp old < 2 ^ 64 := by unfold pageUp; omega
  have hpr : pageUp r < 2 ^ 64 := by unfold pageUp; omega
  have hle : pageUp old ≤ pageUp r := by unfold pageUp; omega
  simp only [brk_zeros, hg, ite_true, brk_page_range, ZeroSet, ZeroSetL]
  by_cases hlt' : pageUp old < pageUp r
  · rw [if_pos (by rw [← e1, ← e2]; omega)]
    simp only [List.mem_singleton, exists_eq_left]
    have h1 : (Z_to_bv 64 (page_round_up_Z (bv_unsigned old))) = BitVec.ofNat 64 (pageUp old) := by
      rw [← e1]; unfold Z_to_bv; apply BitVec.eq_of_toNat_eq; simp
    have h2 : (Z_to_bv 64 (page_round_up_Z (bv_unsigned r) - page_round_up_Z (bv_unsigned old))).toNat =
        pageUp r - pageUp old := by
      rw [← e1, ← e2]; unfold Z_to_bv; simp; omega
    rw [h1, h2]
  · rw [if_neg (by rw [← e1, ← e2]; omega)]
    simp only [List.mem_singleton, exists_eq_left, List.not_mem_nil, false_and, exists_false, iff_false]
    omega

end LPS.Bridge

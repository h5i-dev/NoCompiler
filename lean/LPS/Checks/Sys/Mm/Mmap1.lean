import LPS.Checks.Sys.Prelude
import LPS.LinuxProcessSem.Specs

/-!
# LPS `theories/LinuxProcessSem/Checks/Sys/Mm/Mmap.v` (f1006fe8): PARTIAL port, the brk checker

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Checks/Sys/Mm/Mmap.v` at f1006fe8 (the brk/mmap/munmap checkers and
their proofs against the relational specs of `Sys/Mm/Mmap.v`). PARTIAL: only what `Common/AllocSim.v`
uses: the definition `check_brk` (faithful), `page_round_up_Z_mono`, and the four brk lemmas
`check_brk_sound_ok`, `check_brk_sound_unmodeled`, `check_brk_complete_ok`,
`check_brk_complete_unmodeled`. The mmap/munmap checkers and their lemmas are not ported. The proofs
are Lean's (Rocq's Ltacs `sys_unfold`/`inv_ok` are unfolding the `do` block by hand).

The first section ports, with their Rocq statements, the two items of `Checks/Sys/Prelude.v` that
`check_brk` uses and LPS/Checks/Sys/Prelude.lean does not have: the range-list equality test
`listNN_eqb` and its reflection lemma `listNN_eqb_eq` (kept here, so that the Prelude port stays as it
is).
-/

namespace LPS

/-! ### From Checks/Sys/Prelude.v -/

def listNN_eqb : List (word × word) → List (word × word) → Bool
  | [], [] => true
  | (a1, n1) :: r1, (a2, n2) :: r2 => bv_eqb a1 a2 && bv_eqb n1 n2 && listNN_eqb r1 r2
  | _, _ => false

theorem listNN_eqb_eq : ∀ l1 l2, listNN_eqb l1 l2 = true ↔ l1 = l2 := by
  intro l1
  induction l1 with
  | nil => intro l2; cases l2 <;> simp [listNN_eqb]
  | cons p r1 IH =>
    intro l2
    obtain ⟨a1, n1⟩ := p
    cases l2 with
    | nil => simp [listNN_eqb]
    | cons q r2 =>
      obtain ⟨a2, n2⟩ := q
      simp only [listNN_eqb, Bool.and_eq_true, bv_eqb_eq, IH, List.cons.injEq, Prod.mk.injEq, and_assoc]

/-! ### The brk checker -/

def check_brk (req : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | ⟨r, [], zs, us, [], []⟩ =>
    if brk_r_ok m req r && listNN_eqb zs (brk_zeros req r (m_vmmaps m).vm_brk)
        && listNN_eqb us (brk_unmaps r (m_vmmaps m).vm_brk)
    then CheckOk (with_brk_next m req r) []
    else CheckReject
  | _ => CheckReject

theorem page_round_up_Z_mono : ∀ a b, a ≤ b → page_round_up_Z a ≤ page_round_up_Z b := by
  intro a b h
  unfold page_round_up_Z page_size Z.div
  simp only [Int.fdiv_eq_ediv_of_nonneg _ (by decide : (0 : Int) ≤ 4096)]
  have := Int.ediv_le_ediv (by decide : (0 : Int) < 4096) (show a + 4096 - 1 ≤ b + 4096 - 1 by omega)
  omega

/-- `brk_spec` unfolded: its `Ok` outcomes. -/
private theorem brk_spec_ok_iff (req : word) (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model)
    (evs : List event) :
    brk_spec req i m (Ok eff m' evs) ↔
      brk_r_ok m req eff.eff_ret = true ∧
      eff = mkEffectU eff.eff_ret [] (brk_zeros req eff.eff_ret (m_vmmaps m).vm_brk)
              (brk_unmaps eff.eff_ret (m_vmmaps m).vm_brk) [] [] ∧
      m' = with_brk_next m req eff.eff_ret ∧ evs = [] := by
  constructor
  · rintro ⟨x, m1, e1, e2, h1, h2, rfl⟩
    cases h1
    obtain ⟨r, m2, e3, e4, ⟨r', hr, h3⟩, h4, rfl⟩ := h2
    cases h3
    obtain ⟨u, m3, e5, e6, h5, h6, rfl⟩ := h4
    cases h5
    cases h6
    exact ⟨hr, rfl, rfl, rfl⟩
  · rintro ⟨hr, he, rfl, rfl⟩
    refine ⟨m, m, [], [], rfl, ?_, rfl⟩
    refine ⟨eff.eff_ret, m, [], [], ⟨_, hr, rfl⟩, ?_, rfl⟩
    refine ⟨(), with_brk_next m req eff.eff_ret, [], [], rfl, ?_, rfl⟩
    show Ok eff _ [] = Ok _ _ []
    rw [← he]

private theorem brk_spec_not_unmodeled (req : word) (i : SyscallInput) (m : Model) :
    ¬ brk_spec req i m Unmodeled := by
  rintro (h | ⟨x, m1, e1, h1, h2⟩)
  · cases h
  · cases h1
    rcases h2 with h | ⟨r, m2, e2, ⟨r', _, h3⟩, h4⟩
    · obtain ⟨_, _, h⟩ := h; cases h
    · cases h3
      rcases h4 with h | ⟨u, m3, e3, h5, h6⟩
      · cases h
      · cases h5; cases h6

theorem check_brk_sound_ok : ∀ req eff m m' evs i,
    check_brk req eff m = CheckOk m' evs → brk_spec req i m (Ok eff m' evs) := by
  intro req eff m m' evs i H
  obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
  unfold check_brk at H
  cases ws <;> cases cs <;> cases copyins <;> simp only at H <;> try cases H
  split at H
  · rename_i hc
    simp only [Bool.and_eq_true, listNN_eqb_eq] at hc
    obtain ⟨⟨hr, rfl⟩, rfl⟩ := hc
    cases H
    exact (brk_spec_ok_iff _ _ _ _ _ _).2 ⟨hr, rfl, rfl, rfl⟩
  · cases H

theorem check_brk_sound_unmodeled : ∀ req eff m i,
    check_brk req eff m = CheckUnmodeled → brk_spec req i m Unmodeled := by
  intro req eff m i H
  obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
  unfold check_brk at H
  cases ws <;> cases cs <;> cases copyins <;> simp only at H <;> try cases H
  split at H <;> cases H

theorem check_brk_complete_ok : ∀ req eff m m' evs i,
    brk_spec req i m (Ok eff m' evs) → check_brk req eff m = CheckOk m' evs := by
  intro req eff m m' evs i H
  obtain ⟨hr, he, rfl, rfl⟩ := (brk_spec_ok_iff _ _ _ _ _ _).1 H
  rw [he]
  simp only [check_brk, mkEffectU, hr, (listNN_eqb_eq _ _).2 rfl, Bool.and_self, ↓reduceIte]

theorem check_brk_complete_unmodeled : ∀ req m i eff,
    brk_spec req i m Unmodeled → check_brk req eff m = CheckUnmodeled := by
  intro req m i eff H
  exact absurd H (brk_spec_not_unmodeled req i m)

end LPS

import NoCompiler.Typed.Prog
import NoCompiler.Typed.Sound.Main

/-
Theorem D: every function of a program the checker accepts meets its signature, given that
the external functions meet theirs.
-/
namespace NoCompiler.Typed

theorem Fn.apart_sound {f : Fn} {Dg : Dom} (h : f.apartFrom Dg = true) {j : Nat}
    (hj : j < f.size) : ¬ Dg.mem (f.pcOf j) := by
  unfold Fn.apartFrom at h
  unfold Dom.mem
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  simp only [List.any_eq_true, decide_eq_true_eq, not_exists, not_and, Nat.not_lt]
  intro r hr
  obtain ⟨h1, h2⟩ := h r hr
  have e : f.pcOf j - r.1 = (f.entry - r.1) + BitVec.ofNat 64 (4 * j) := by
    unfold Fn.pcOf; bv_omega
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
  have : 4 * j < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by omega)]
  omega

theorem Dom.mem_cons_of_mem {r : Word × Nat} {D : Dom} {x : Word} (h : D.mem x) :
    Dom.mem (r :: D) x := by
  unfold Dom.mem at *; rw [List.any_cons, h, Bool.or_true]

theorem Dom.mem_head {r : Word × Nat} {D : Dom} {x : Word} (h : Dom.mem [r] x) :
    Dom.mem (r :: D) x := by
  unfold Dom.mem at *
  rw [List.any_cons, List.any_nil, Bool.or_false] at h
  rw [List.any_cons, h, Bool.true_or]

/-- **Theorem D.** -/
theorem Prog.check_sound {c : Code} {T : TokEnv} : ∀ (fs : List Fn) (E : Env),
    (∀ e ∈ E, Meets c e.2.2 e.1 T e.2.1) → Prog.check c E fs = true →
    ∀ e ∈ Prog.env E fs, Meets c e.2.2 e.1 T e.2.1
  | [], _, hE, _ => hE
  | f :: fs, E, hE, h => by
    simp only [Prog.check, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨hc, hnp⟩, hcalls⟩, hrest⟩ := h
    refine Prog.check_sound fs _ ?_ hrest
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · have hso : f.structOk = true := by
        unfold Fn.check at hc; simp only [Bool.and_eq_true] at hc; exact hc.1.1
      have hst := Fn.structOk_spec hso
      refine f.check_sound c T hc hnp (fun k hk => Dom.mem_head (f.pcOf_mem hst hk)) ?_
      intro p hp
      have hq := List.all_eq_true.1 hcalls p hp
      cases hl : E.lookup p.1 with
      | none => rw [hl] at hq; cases hq
      | some q =>
      obtain ⟨σ, Dg⟩ := q
      rw [hl] at hq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
      obtain ⟨⟨rfl, hap⟩, hal⟩ := hq
      refine ⟨hal, Dg, hE _ (lookup_mem hl), ?_, fun j hj => Fn.apart_sound hap hj⟩
      intro x hx
      unfold Dom.mem at hx ⊢
      obtain ⟨r, hr, hrx⟩ := List.any_eq_true.1 hx
      refine List.any_eq_true.2 ⟨r, ?_, hrx⟩
      refine List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨p, hp, ?_⟩)
      rw [hl]; exact hr
    · exact hE e he

/-- Theorem D for a program with no external functions. -/
theorem Prog.check_sound_closed {c : Code} {T : TokEnv} {fs : List Fn}
    (h : Prog.check c [] fs = true) : ∀ e ∈ Prog.env [] fs, Meets c e.2.2 e.1 T e.2.1 :=
  Prog.check_sound fs [] (by simp) h

end NoCompiler.Typed

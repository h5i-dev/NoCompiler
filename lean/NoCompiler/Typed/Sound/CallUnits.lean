import NoCompiler.Typed.Sound.CallTok

/-
The allocator's units across a call (decisions.md I38): the units at the function's entry that
miss its Pool and its stack stay units, whatever the callees do (their Q5).
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

/-- The allocator's units at the entry that miss the Pool and the stack are units under `F`. -/
def Fn.UnitFrame (f : Fn) (T : TokEnv) (a : Val × TokFp) (s0 : State) (F : TokFp) : Prop :=
  ∀ r, (T heapTok).unit (a.2 heapTok) r → (∀ x, r.mem x → ¬ f.sig.pool a.1 a.2 x ∧
    ¬ (Spec.stackRegion s0 f.sig.stack).mem x) → (T heapTok).unit (F heapTok) r

theorem Fn.unitFrame_entry (a : Val × TokFp) (s0 : State) : f.UnitFrame T a s0 a.2 :=
  fun _ hr _ => hr

theorem Fn.unitFrame_call (hst : f.StructSpec) {a : Val × TokFp} {S : STy} {s : State} {ι : Val}
    {Ft : TokFp} (hI : Inv f T ((f.sig.spec T).perm a s0) s0 ι0 S s ι Ft)
    (hι0p : ∀ x ∈ f.sig.params, ι0 x = a.1 x) (hUF : f.UnitFrame T a s0 Ft)
    {g : Sig} (hok : CalleeSpec g) {θ : Subst} {ls : List (BytesCap × HCap)}
    (hls : Fn.lends S g θ = some ls) (htx : (ls.drop g.borrow.length).all (·.2.cap.exclusive) = true)
    (hheld : f.callHeldOk S g ls = true) (hstk : S.depth + g.stack ≤ f.sig.stack)
    {s1 : State} (hregs : ∀ r : Reg, r ≠ 1 → s1.reg r = s.reg r) {Fg : TokFp}
    (hQ5 : ∀ r, (T heapTok).unit (Ft heapTok) r → (∀ x, r.mem x → ¬ g.pool (IExpr.upd ι θ) Ft x ∧
      ¬ (Spec.stackRegion s1 g.stack).mem x) → (T heapTok).unit (Fg heapTok) r) :
    f.UnitFrame T a s0 (callF g Ft Fg) := by
  unfold Fn.callHeldOk at hheld
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at hheld
  obtain ⟨⟨-, horig⟩, hbor⟩ := hheld
  have hh := hI.hyps
  have hspn := hI.sp_toNat hst
  have hK := hI.stackLe
  intro r hr hmiss
  have hU := hUF r hr hmiss
  by_cases hH : heapTok ∈ g.tokNames ∨ heapTok ∈ g.giveToks
  · have e : callF g Ft Fg heapTok = Fg heapTok := by simp [callF, hH]
    rw [e]
    refine hQ5 r hU (fun x hx => ⟨fun hp => ?_, fun hs => ?_⟩)
    · -- the callee's Pool lies in exclusive held capabilities; none of them meets `r`
      obtain ⟨i, hl, hm, hex, hfz, hor⟩ := f.pool_in hI hok hls htx hp
      obtain ⟨rg, hrg, hmx⟩ := (hI.perm _ hm x hfz).2 hex
      simp only [Spec.perm, Sig.spec, Sig.writeRegions, List.mem_append, List.mem_flatMap,
        List.mem_filter, List.mem_singleton] at hrg
      rcases hrg with ⟨e0, ⟨he0, -⟩, hre⟩ | rfl
      · simp only [Sig.entryCaps, List.mem_append, List.mem_map] at he0
        rcases he0 with ⟨b, hb, rfl⟩ | he0
        · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
          cases hkb : f.sig.borrow[j].cap.kind with
          | token t => exact (hmiss x hx).1 (.inr ⟨_, hb, by simp [hkb], rg, hre, hmx⟩)
          | bytes xb =>
            exfalso
            -- the borrow's capability is still held with the whole range, and it is not the lent one
            obtain ⟨c, hc, hcs⟩ := hbor (f.sig.borrow[j], j) (mem_zipIdx_of hj)
            simp only [Bool.and_eq_true, beq_iff_eq] at hcs
            obtain ⟨⟨hco, hcg⟩, hck⟩ := hcs
            cases hkc : c.cap.kind with
            | token t' => simp [hkc, hkb] at hck
            | bytes hb2 =>
              simp only [hkc, hkb] at hck
              have hgb := hst.borrowGuard _ hb
              have hcg' := STy.ent_sound hcg hh
              have heq := STy.ent_sound hck hh
              simp only [Constr.holds, Constr.eval, Bool.and_eq_true, decide_eq_true_eq] at heq
              -- the borrow's range at the entry valuation is its range now
              have hv : ∀ y ∈ xb.base.vars ++ xb.len.vars, ι y = a.1 y := by
                intro y hy
                have hp := ((hst.borrowVars _ hb).2 xb hkb).1 y (List.mem_append_left _ hy)
                rw [hI.prot y (f.param_prot hp), hι0p y hp]
              have hb' : xb.base.eval ι = xb.base.eval a.1 :=
                IExpr.eval_congr _ (fun y hy => hv y (List.mem_append_left _ hy))
              have hl' : xb.len.eval ι = xb.len.eval a.1 :=
                IExpr.eval_congr _ (fun y hy => hv y (List.mem_append_right _ hy))
              have hreg : rg = xb.region a.1 := by
                unfold Cap.regions at hre
                rw [hgb, hkb] at hre
                simpa [Constr.eval] using hre
              have hcx : c.cap.fp ι Ft x := by
                have hcg'' : c.cap.guard.eval ι = true := hcg'
                unfold Cap.fp Cap.regions
                rw [if_pos hcg'', hkc]
                refine ⟨_, List.mem_singleton_self _, ?_⟩
                have : hb2.region ι = xb.region a.1 := by
                  simp only [BytesCap.region]; rw [heq.1, heq.2, hb', hl']
                rw [this, ← hreg]; exact hmx
              refine hI.sep _ hm c hc (fun e => ?_) hex x hfz hcx
              have := eq_of_id_eq hI.ids hm hc e
              rcases hor with hb3 | ⟨t, hkt, -⟩
              · have ho := horig _ (by
                  rw [List.mem_iff_getElem]
                  refine ⟨i - g.borrow.length, by simp; omega, ?_⟩
                  rw [List.getElem_drop]; try simp [Nat.add_sub_cancel' hb3])
                simp only [Nat.add_sub_cancel' hb3] at ho
                revert ho
                rw [this, hco]
                simp <;> omega
              · rw [this, hkc] at hkt; cases hkt
        · exact (hmiss x hx).1 (.inl ⟨e0, he0, rg, hre, hmx⟩)
      · exact (hmiss x hx).2 hmx
    · -- the callee's stack lies in ours
      have hsp1 : (s1.reg Reg.sp).toNat = (s0.reg Reg.sp).toNat - S.depth := by
        rw [hregs _ (by decide)]; exact hspn.1
      rw [stack_mem_iff s1 g.stack (by omega) x, hsp1] at hs
      exact (hmiss x hx).2 ((stack_mem_iff s0 _ hK x).2 ⟨by omega, by omega⟩)
  · have e : callF g Ft Fg heapTok = Ft heapTok := by simp [callF, hH]
    rw [e]; exact hU

end NoCompiler.Typed

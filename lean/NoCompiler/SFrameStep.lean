import NoCompiler.SFrame

/-!
# T2: one structured step keeps `FrameInv`

`FrameInv.exec_step`: an instruction step from a state where the certificate's fact
`F` holds, with `step fr _ F i = some G` (what `checkL2` checked), reaches a state
where `G` holds. Memory: either the step is a slot access (`SStep.slot`), or it
leaves every slot byte alone (a `Step` under a permission without the slots,
`Step.frame`).
-/
namespace NoCompiler
namespace Struct

theorem exec_mem_of_not_store {i : Instr} {s s' : State} (h : exec i s = some s')
    (hn : ∀ op a b k, i ≠ .store op a b k) : s'.mem = s.mem := by
  rcases exec_frame h with e | ⟨op, a, b, k, rfl, _⟩
  · exact e
  · exact absurd rfl (hn op a b k)

theorem load_dst_ne {op : LdOp} {rd rs1 q : Reg} {k : BitVec 12} (hq : q ≠ rd) :
    (Instr.load op rd rs1 k).dst ≠ some q.val := by
  intro h
  simp only [Instr.dst] at h
  split at h
  · cases h
  · simp only [Option.some.injEq] at h
    exact hq (Fin.ext h.symm)

theorem drop_le (F : Fact) (r : Nat) : Fact.le { F with keep := F.keep.filter (· != r) } F = true := by
  simp only [Fact.le, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, List.all_eq_true,
    List.contains_iff_mem]
  exact ⟨fun x hx => (List.mem_filter.1 hx).1, fun x hx => hx⟩

set_option maxHeartbeats 1000000 in
theorem FrameInv.exec_step {fr : Frame} (hwf : fr.wellFormed = true) (hsz : fr.size < 2 ^ 32)
    {s0 s s' : State} {F G : Fact} {i : Instr} {pn : Bool} (hI : FrameInv fr s0 F s)
    (hst : step fr pn F i = some G) (hx : exec i s = some s')
    (hmem : slotAccess fr (s0.reg 2) s i = true ∨ ∀ x, SlotByte fr (s0.reg 2) x → s'.mem x = s.mem x) :
    FrameInv fr s0 G s' := by
  obtain ⟨hb, h3, h4, h2⟩ := step_split hst
  -- Every instruction but a store leaves memory alone.
  have hnm : (∀ op a b k, i ≠ .store op a b k) → ∀ x, SlotByte fr (s0.reg 2) x → s'.mem x = s.mem x :=
    fun hn x _ => by rw [exec_mem_of_not_store hx hn]
  have gen : (∀ op a b k, i ≠ .store op a b k) → i.dst ≠ some 2 →
      stepBase fr F i = some (match i.dst with | some r => { F with keep := F.keep.filter (· != r) } | none => F) →
      FrameInv fr s0 G s' := fun hn hd2 hb' => by
    rw [hb] at hb'; obtain rfl := Option.some.inj hb'
    exact FrameInv.of_drop hwf hsz hI hx hd2 h3 h4 (hnm hn)
  cases i with
  | store op base src k =>
    have hreg : ∀ q : Reg, s'.reg q = s.reg q := fun q => exec_reg_other hx q (by simp [Instr.dst])
    have hd : ∀ G', G'.depth = F.depth → G'.keep = F.keep → (∀ x ∈ G'.held, x ∈ F.held) →
        (∀ x, SlotByte fr (s0.reg 2) x → s'.mem x = s.mem x) → FrameInv fr s0 G' s' :=
      fun G' e1 e2 e3 hm => FrameInv.of_same hwf hsz hI (hreg 2) (hreg 3) (hreg 4) hm e1
        (by rw [e2]; exact fun _ h => h) (fun q _ => hreg q) e3
    by_cases hb2 : base.val = 2
    · have hbs : base = 2 := Fin.ext hb2
      subst hbs
      simp only [stepBase, hb2, ite_true] at hb
      split at hb
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        have h0 : 0 ≤ frameOff fr F.depth k := hc.1
        split at hb
        · rename_i sl hsl
          split at hb
          · cases hb
          · rename_i hsd
            simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hsd
            subst hsd
            obtain ⟨hslm, hso⟩ := slotAt_some hsl
            have hw := wf_slot hwf hslm
            have hmw : s'.mem = writeLE s.mem (fr.base (s0.reg 2) + BitVec.ofNat 64 (frameOff fr F.depth k).toNat)
                (s.reg src).toNat 8 := by
              simp only [exec] at hx; split at hx
              · cases hx; simp [StOp.width, ea_frame hI.sp h0]
              · cases hx
            have hoff : (frameOff fr F.depth k).toNat = sl.off := by omega
            -- the other held slots: 8 bytes apart from this one
            have hother : ∀ k' r', (k', r') ∈ F.held → (k' : Int) ≠ frameOff fr F.depth k →
                read64 s'.mem (fr.base (s0.reg 2) + BitVec.ofNat 64 k') =
                  read64 s.mem (fr.base (s0.reg 2) + BitVec.ofNat 64 k') := by
              intro k' r' hm hne
              have hw' := wf_slot hwf (hI.heldSlot k' r' hm)
              rw [hmw]
              apply read64_writeLE_other <;> simp only at hw' <;> omega
            split at hb
            · rename_i r hkind
              split at hb
              · rename_i hcond
                obtain rfl := Option.some.inj hb
                simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hcond
                obtain ⟨hsr, hkr⟩ := hcond
                have hslr : sl = ⟨(frameOff fr F.depth k).toNat, .save r⟩ := by
                  cases sl; simp only at hkind hoff ⊢; rw [hkind, hoff]
                exact {
                  sp := by rw [hreg 2, hI.sp]
                  gp := by rw [hreg 3, hI.gp]
                  tp := by rw [hreg 4, hI.tp]
                  keep := fun q hq => by rw [hreg q, hI.keep q hq]
                  held := fun k' r' hm q hq => by
                    simp only [List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq] at hm
                    rcases hm with e | ⟨hm, hne⟩
                    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
                      rw [hmw, read64_writeLE_same]
                      have hq' : q = src := Fin.ext (hq.trans hsr.symm)
                      subst hq'
                      exact hI.keep q (hsr ▸ hkr)
                    · rw [hother k' r' hm hne]; exact hI.held k' r' hm q hq
                  keepSaved := hI.keepSaved
                  heldSlot := fun k' r' hm => by
                    simp only [List.mem_cons, List.mem_filter] at hm
                    rcases hm with e | ⟨hm, _⟩
                    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
                      rw [← hslr]; exact hslm
                    · exact hI.heldSlot k' r' hm
                  depth := hI.depth }
              · cases hb
            · obtain rfl := Option.some.inj hb
              exact {
                sp := by rw [hreg 2, hI.sp]
                gp := by rw [hreg 3, hI.gp]
                tp := by rw [hreg 4, hI.tp]
                keep := fun q hq => by rw [hreg q, hI.keep q hq]
                held := fun k' r' hm q hq => by
                  simp only [List.mem_filter, bne_iff_ne, ne_eq] at hm
                  rw [hother k' r' hm.1 hm.2]; exact hI.held k' r' hm.1 q hq
                keepSaved := hI.keepSaved
                heldSlot := fun k' r' hm => hI.heldSlot k' r' (List.mem_filter.1 hm).1
                depth := hI.depth }
        · -- no slot there: a range; the step is not a slot access, so slots are untouched
          rename_i hnone
          split at hb
          · obtain rfl := Option.some.inj hb
            refine hd _ rfl rfl (fun x hx => (List.mem_filter.1 hx).1) ?_
            rcases hmem with hs | hm
            · exfalso
              cases op <;> simp [slotAccess] at hs
              have := isSlot_frameOff hI.sp hI.depth hsz hs
              rw [hnone] at this; cases this
            · exact hm
          · cases hb
      · cases hb
    · simp only [stepBase, hb2, ite_false] at hb
      obtain rfl := Option.some.inj hb
      refine hd _ rfl rfl (fun _ h => h) ?_
      rcases hmem with hs | hm
      · exfalso; cases op <;> simp [slotAccess, hb2] at hs
      · exact hm
  | load op rd rs1 k =>
    have hn : ∀ op' a b k', Instr.load op rd rs1 k ≠ .store op' a b k' := by intro _ _ _ _ h; cases h
    have hd2 : (Instr.load op rd rs1 k).dst ≠ some 2 := fun e => by obtain ⟨_, _, he, _⟩ := h2 e; cases he
    have hdrop := FrameInv.of_drop hwf hsz hI hx hd2 h3 h4 (hnm hn)
    by_cases hs2 : rs1.val = 2
    · have hrs : rs1 = 2 := Fin.ext hs2
      subst hrs
      simp only [stepBase, hs2, ite_true] at hb
      split at hb
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        have h0 : 0 ≤ frameOff fr F.depth k := hc.1.1
        by_cases hr0 : rd.val = 0
        · simp only [hr0, ite_true] at hb
          obtain rfl := Option.some.inj hb
          simpa [Instr.dst, hr0] using hdrop
        · simp only [hr0, ite_false] at hb
          split at hb
          · -- a slot holding rd's entry value: rd is kept
            rename_i hh
            obtain rfl := Option.some.inj hb
            simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hh
            obtain ⟨⟨hld, _⟩, hm⟩ := hh
            subst hld
            have hreg := exec_reg_other hx
            have hv : s'.reg rd = s0.reg rd := by
              simp only [exec] at hx
              split at hx
              · cases hx
                simp only [State.setPc_reg, State.reg_setReg_same _ _ _ (fun e => hr0 (congrArg Fin.val e)),
                  loadVal]
                rw [ea_frame hI.sp h0]
                exact hI.held _ _ hm rd rfl
              · cases hx
            have hdst : ∀ q : Reg, q ≠ rd → (Instr.load .ld rd 2 k).dst ≠ some q.val :=
              fun _ hq => load_dst_ne hq
            have hsv : rd.val ∈ savedRegs := wf_save hwf (hI.heldSlot _ _ hm)
            exact {
              sp := by rw [hreg 2 hd2, hI.sp]
              gp := by rw [hreg 3 h3, hI.gp]
              tp := by rw [hreg 4 h4, hI.tp]
              keep := fun q hq => by
                by_cases e : q = rd
                · subst e; exact hv
                · simp only [List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq] at hq
                  rcases hq with hq | ⟨hq, _⟩
                  · exact absurd (Fin.ext hq) e
                  · rw [hreg q (hdst q e), hI.keep q hq]
              held := fun k' r hm' q hq => by
                rw [show s'.mem = s.mem from exec_mem_of_not_store hx hn]; exact hI.held k' r hm' q hq
              keepSaved := fun r hr => by
                simp only [List.mem_cons, List.mem_filter] at hr
                rcases hr with e | ⟨hr, _⟩
                · rw [e]; exact hsv
                · exact hI.keepSaved r hr
              heldSlot := hI.heldSlot
              depth := hI.depth }
          · obtain rfl := Option.some.inj hb
            simpa [Instr.dst, hr0] using hdrop
      · cases hb
    · refine gen hn hd2 ?_
      simp only [stepBase]; rw [ite_eq_right hs2]; rfl
  | iop op rd rs1 k =>
    have hn : ∀ op' a b k', Instr.iop op rd rs1 k ≠ .store op' a b k' := by intro _ _ _ _ h; cases h
    cases op
    case addi =>
      by_cases hr2 : rd.val = 2
      · -- addi sp, sp, k: the depth moves by k
        simp only [stepBase, hr2, ite_true] at hb
        split at hb
        · rename_i hc
          obtain rfl := Option.some.inj hb
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
          obtain ⟨⟨⟨hs2, _⟩, h0⟩, hle⟩ := hc
          have hrd : rd = 2 := Fin.ext hr2
          have hrs : rs1 = 2 := Fin.ext hs2
          subst hrd hrs
          have hreg := exec_reg_other hx
          have e2 : s'.reg 2 = s.reg 2 + k.signExtend 64 := by
            simp only [exec] at hx; cases hx; simp [evalI]
          exact {
            sp := by rw [e2, hI.sp]; exact sp_addi h0
            gp := by rw [hreg 3 h3, hI.gp]
            tp := by rw [hreg 4 h4, hI.tp]
            keep := fun q hq => by
              have hq2 : q.val ≠ 2 := fun e => by
                have := hI.keepSaved _ hq; rw [e] at this; simp [savedRegs] at this
              rw [hreg q (by simp [Instr.dst]; omega), hI.keep q hq]
            held := fun k' r hm q hq => by
              rw [show s'.mem = s.mem from exec_mem_of_not_store hx hn]; exact hI.held k' r hm q hq
            keepSaved := hI.keepSaved
            heldSlot := hI.heldSlot
            depth := by show ((F.depth : Int) - k.toInt).toNat ≤ fr.size; omega }
        · cases hb
      · by_cases hs2 : rs1.val = 2
        · -- addi rd, sp, k (an address in the frame): rd is written
          simp only [stepBase, hr2, hs2, ite_true, ite_false] at hb
          split at hb
          · obtain rfl := Option.some.inj hb
            have hd2 : (Instr.iop .addi rd rs1 k).dst ≠ some 2 := by
              unfold Instr.dst; split <;> simp_all
            have := FrameInv.of_drop hwf hsz hI hx hd2 h3 h4 (hnm hn)
            by_cases h0 : rd.val = 0
            · simp only [Instr.dst, h0, ite_true] at this
              exact this.weaken (drop_le _ _)
            · simpa [Instr.dst, h0] using this
          · cases hb
        · refine gen hn (by unfold Instr.dst; split <;> simp_all) ?_
          simp only [stepBase]; rw [ite_eq_right hr2, ite_eq_right hs2]; rfl
    all_goals exact gen hn (fun e => by obtain ⟨_, _, he, _⟩ := h2 e; cases he) rfl
  | _ =>
    refine gen (by intro _ _ _ _ h; cases h) (fun e => by obtain ⟨_, _, he, _⟩ := h2 e; cases he) ?_
    rfl

end Struct
end NoCompiler

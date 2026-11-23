import NoCompiler.SFrameStep

/-!
# T2 and T3 on a run: from the certificate, at calls and at returns

* `checkL2_at`, `instrL2_facts`: what `checkL2` says at one instruction of the function.
* `FrameInv.callDone`: a call to a verified callee (`CallDone`) keeps the invariant; the kept
  registers are saved ones other than `ra`, which the callee preserves, and the slots are not
  writable under `P`, so the callee does not change them.
* `FrameInv.ret` (T3): at a return or tail call, every register of `Preserved` and `ra` hold their
  entry values.
-/
namespace NoCompiler
namespace Struct

theorem checkL2_at {c : Code} {f : Func} {fr : Frame} {cert : Cert} (h : checkL2 c f fr cert = true)
    {pc : Word} (hpc : f.contains pc = true) : instrL2 c f fr cert pc = true := by
  unfold checkL2 at h
  unfold Func.contains at hpc
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hpc h
  have hi := List.all_eq_true.1 h.2 ((pc - f.entry).toNat / 4) (List.mem_range.2 (by omega))
  have e : f.entry + BitVec.ofNat 64 (4 * ((pc - f.entry).toNat / 4)) = pc := by
    have : 4 * ((pc - f.entry).toNat / 4) = (pc - f.entry).toNat := by omega
    rw [this]; apply BitVec.eq_of_toNat_eq; simp; bv_omega
  rwa [e] at hi

theorem checkL2_wf {c : Code} {f : Func} {fr : Frame} {cert : Cert} (h : checkL2 c f fr cert = true) :
    fr.wellFormed = true := by
  unfold checkL2 at h; simp only [Bool.and_eq_true] at h; exact h.1.1.1.1.1

/-- At an instruction of an L2 function: its step from the certificate's fact, the successors'
    facts below the result, and at a return or tail call `sp` and the saved registers back. -/
theorem instrL2_facts {c : Code} {f : Func} {fr : Frame} {cert : Cert} {pc : Word} {i : Instr}
    (h : instrL2 c f fr cert pc = true) (hi : c.instr pc = some i) :
    ∃ pn G, step fr pn (factAt f cert pc) i = some G ∧
      (∀ t ∈ succs f pc i, f.contains t = true → (factAt f cert t).le G = true) ∧
      (leaves f pc i = true → (factAt f cert pc).depth = 0 ∧ ∀ r ∈ savedRegs, r ∈ (factAt f cert pc).keep) := by
  unfold instrL2 at h
  rw [hi] at h
  simp only at h
  split at h
  · cases h
  · rename_i G hG
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    refine ⟨_, G, hG, fun t ht hin => ?_, fun hl => ?_⟩
    · rcases h.1 t ht with h1 | h1
      · rw [hin] at h1; cases h1
      · exact h1
    · rcases h.2 with h2 | h2
      · rw [hl] at h2; cases h2
      · simp only [beq_iff_eq, List.contains_iff_mem] at h2
        exact ⟨h2.1, h2.2⟩

/-- A saved register other than `ra` is one a verified callee preserves. -/
theorem preserved_of_saved {q : Reg} (h : q.val ∈ savedRegs) (h1 : q.val ≠ 1) : q ∈ preservedRegs := by
  revert h h1; revert q; decide

/-- A verified callee (`CallDone`) keeps the invariant: it preserves the kept registers (saved,
    not `ra`), `sp`, `gp`, `tp`, and does not write the slots. -/
theorem FrameInv.callDone {fr : Frame} (hwf : fr.wellFormed = true) (hsz : fr.size < 2 ^ 32)
    {P : Perm} {s0 s s' : State} {G : Fact} (hI : FrameInv fr s0 G s) (hk : 1 ∉ G.keep)
    (hoff : SlotsOff fr (s0.reg 2) P) (hd : CallDone P s s') : FrameInv fr s0 G s' := by
  obtain ⟨_, _, hpres, hmem⟩ := hd
  have hp : ∀ q ∈ preservedRegs, s'.reg q = s.reg q := hpres
  refine FrameInv.of_same hwf hsz hI (hp 2 (by decide)) (hp 3 (by decide)) (hp 4 (by decide))
    (fun x hx => hmem x (hoff x hx)) rfl (fun _ h => h) (fun q hq => hp q ?_) (fun _ h => h)
  exact preserved_of_saved (hI.keepSaved _ hq) (fun e => hk (e ▸ hq))

/-- T3: at a fact with `sp` back and every saved register kept (what `checkL2` checks at a return
    or tail call), the state preserves the entry's registers and `ra` is the entry's. -/
theorem FrameInv.ret {fr : Frame} {s0 s : State} {F : Fact} (hI : FrameInv fr s0 F s)
    (hd : F.depth = 0) (hk : ∀ r ∈ savedRegs, r ∈ F.keep) :
    Preserved s0 s ∧ s.reg 1 = s0.reg 1 := by
  have hkeep : ∀ q : Reg, q.val ∈ savedRegs → s.reg q = s0.reg q := fun q hq => hI.keep q (hk _ hq)
  refine ⟨fun q hq => ?_, hkeep 1 (by decide)⟩
  have : q = 2 ∨ q = 3 ∨ q = 4 ∨ q.val ∈ savedRegs := by revert hq; revert q; decide
  rcases this with rfl | rfl | rfl | h
  · rw [hI.sp, hd]; simp
  · exact hI.gp
  · exact hI.tp
  · exact hkeep q h

/-- A syscall step keeps the invariant: it writes `a0` (dropped from the kept registers) and only
    memory `P` lets it write. -/
theorem FrameInv.sys_step {fr : Frame} (hwf : fr.wellFormed = true) (hsz : fr.size < 2 ^ 32)
    {c : Code} {P : Perm} {s0 s s' : State} {F G : Fact} {pn : Bool} (hI : FrameInv fr s0 F s)
    (hst : step fr pn F .ecall = some G) (hs : Step c P s s') (hy : Sys s s')
    (hoff : SlotsOff fr (s0.reg 2) P) : FrameInv fr s0 G s' := by
  obtain ⟨hb, _, _, _⟩ := step_split hst
  simp only [stepBase, Instr.dst] at hb
  obtain rfl := Option.some.inj hb
  have hr := sys_reg_other hy
  refine FrameInv.of_same hwf hsz hI (hr 2 (by decide)) (hr 3 (by decide)) (hr 4 (by decide))
    (fun x hx => hs.frame x (hoff x hx)) rfl (fun r h => (List.mem_filter.1 h).1) (fun q hq => hr q ?_)
    (fun _ h => h)
  exact fun e => by simp [e] at hq

/-- T2 along a run inside the function: a structured step from a state where its instruction's fact
    holds, to a successor inside the function (not a call, return or tail call), reaches a state
    where the successor's fact holds. -/
theorem FrameInv.sstep {c c' : Code} {f : Func} {fr : Frame} {cert : Cert} {P : Perm} {s0 s s' : State}
    (hL2 : checkL2 c' f fr cert = true) (hag : ∀ x, f.contains x = true → c.instr x = c'.instr x) (hsz : fr.size < 2 ^ 32) (hoff : SlotsOff fr (s0.reg 2) P)
    (hin : f.contains s.pc = true) (hI : FrameInv fr s0 (factAt f cert s.pc) s)
    (hs : SStep c fr (s0.reg 2) P s s') (hsucc : ∀ i, c.instr s.pc = some i → s'.pc ∈ succs f s.pc i)
    (hin' : f.contains s'.pc = true) : FrameInv fr s0 (factAt f cert s'.pc) s' := by
  have hwf := checkL2_wf hL2
  have hl2 := checkL2_at hL2 hin
  cases hs with
  | slot hx hi hsl he =>
    obtain ⟨_, G, hG, hsuc, _⟩ := instrL2_facts hl2 ((hag _ hin).symm.trans hi)
    exact (FrameInv.exec_step hwf hsz hI hG he (.inl hsl)).weaken (hsuc _ (hsucc _ hi) hin')
  | step h =>
    cases h with
    | exec hx hi hok he =>
      obtain ⟨_, G, hG, hsuc, _⟩ := instrL2_facts hl2 ((hag _ hin).symm.trans hi)
      have hm : ∀ x, SlotByte fr (s0.reg 2) x → s'.mem x = s.mem x :=
        fun x hx' => (Step.exec hx hi hok he).frame x (hoff x hx')
      exact (FrameInv.exec_step hwf hsz hI hG he (.inr hm)).weaken (hsuc _ (hsucc _ hi) hin')
    | sys hx hi hok hy =>
      obtain ⟨_, G, hG, hsuc, _⟩ := instrL2_facts hl2 ((hag _ hin).symm.trans hi)
      exact (FrameInv.sys_step hwf hsz hI hG (.sys hx hi hok hy) hy hoff).weaken (hsuc _ (hsucc _ hi) hin')

/-- A call (`jal ra` / `jalr ra`) from a state where its fact holds, then a verified callee that
    returns (`CallDone`): the state after it, at `pc + 4`, satisfies the fact there. -/
theorem FrameInv.call {c c' : Code} {f : Func} {fr : Frame} {cert : Cert} {P : Perm} {s0 s s1 s2 : State}
    {i : Instr} (hL2 : checkL2 c' f fr cert = true) (hag : ∀ x, f.contains x = true → c.instr x = c'.instr x) (hsz : fr.size < 2 ^ 32) (hoff : SlotsOff fr (s0.reg 2) P)
    (hin : f.contains s.pc = true) (hI : FrameInv fr s0 (factAt f cert s.pc) s)
    (hi : c.instr s.pc = some i) (hc : calls i = true) (hx : exec i s = some s1) (hd : CallDone P s1 s2)
    (hin' : f.contains (s.pc + 4) = true) :
    s2.pc = s.pc + 4 ∧ FrameInv fr s0 (factAt f cert (s.pc + 4)) s2 := by
  have hwf := checkL2_wf hL2
  obtain ⟨_, G, hG, hsuc, _⟩ := instrL2_facts (checkL2_at hL2 hin) ((hag _ hin).symm.trans hi)
  have hn : ∀ op a b k, i ≠ .store op a b k := by
    intro _ _ _ _ e; subst e; simp [calls] at hc
  have h1 := FrameInv.exec_step hwf hsz hI hG hx
    (.inr fun x _ => by rw [exec_mem_of_not_store hx hn])
  obtain ⟨hb, _, _, _⟩ := step_split hG
  -- the call writes ra, which the fact then no longer keeps
  have key : s1.reg 1 = s.pc + 4 ∧ 1 ∉ G.keep ∧ s.pc + 4 ∈ succs f s.pc i := by
    cases i with
    | jal rd off =>
      have e : rd = 1 := by simp [calls] at hc; exact Fin.ext hc
      subst e
      refine ⟨?_, ?_, by simp [succs]⟩
      · simp only [exec, jumpTo] at hx; split at hx
        · cases hx; simp
        · cases hx
      · simp only [stepBase, Instr.dst] at hb; obtain rfl := Option.some.inj hb; simp
    | jalr rd rs1 off =>
      have e : rd = 1 := by simp [calls] at hc; exact Fin.ext hc
      subst e
      refine ⟨?_, ?_, by simp [succs]⟩
      · simp only [exec, jumpTo] at hx; split at hx
        · cases hx; simp
        · cases hx
      · simp only [stepBase, Instr.dst] at hb; obtain rfl := Option.some.inj hb; simp
    | _ => simp [calls] at hc
  obtain ⟨hs1, hk, hsc⟩ := key
  have h2 := FrameInv.callDone hwf hsz h1 hk hoff hd
  exact ⟨hd.2.1.trans hs1, h2.weaken (hsuc _ hsc hin')⟩

/-- T3 at the step that leaves the function (a return or a tail call, `rd = 0`): the state after it
    preserves the entry's registers and has the entry's `ra`. -/
theorem FrameInv.leave {c c' : Code} {f : Func} {fr : Frame} {cert : Cert} {s0 s s' : State} {i : Instr}
    (hL2 : checkL2 c' f fr cert = true) (hag : ∀ x, f.contains x = true → c.instr x = c'.instr x) (hin : f.contains s.pc = true)
    (hI : FrameInv fr s0 (factAt f cert s.pc) s) (hi : c.instr s.pc = some i)
    (hl : leaves f s.pc i = true) (hx : exec i s = some s') :
    Preserved s0 s' ∧ s'.reg 1 = s0.reg 1 := by
  obtain ⟨_, _, _, _, hret⟩ := instrL2_facts (checkL2_at hL2 hin) ((hag _ hin).symm.trans hi)
  obtain ⟨hd, hk⟩ := hret hl
  obtain ⟨hp, hra⟩ := hI.ret hd hk
  have hnd : ∀ q : Reg, s'.reg q = s.reg q := fun q => exec_reg_other hx q (by
    cases i <;> simp [leaves] at hl
    all_goals (simp only [Instr.dst]; split <;> simp_all))
  exact ⟨fun q hq => (hnd q).trans (hp q hq), (hnd 1).trans hra⟩

end Struct
end NoCompiler

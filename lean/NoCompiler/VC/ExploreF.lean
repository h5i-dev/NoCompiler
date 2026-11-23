import NoCompiler.VC.ExploreFacts

/-!
# Explore with the certificate's facts along each path (round 4, QUEUE-C 2)

`SReach.of_exploreF`: as `SReach.of_explore`, for an L2 function `f` entered at `s0`, exploring only
inside it (`De`, the function's own range; the run's region `D` may be larger) with `strict` on.
Given the certificate's fact at the path's start, each end's condition may assume `EndInv`
(VC/ExploreFacts.lean): the fact at a cut inside `f`, `CallInfo` at a callee's entry, `TailInfo`
after a tail call. The facts are carried by T2 (`FrameInv.sstep`), so no proof obligation about
the frame, the saved registers or the stack is left to the caller.
-/
namespace NoCompiler
namespace VC.M
open Struct

/-- An end's condition, which may assume `I` of the state there. -/
def PEnd.NextI (ρ : Nat → Word) (μ : Word → Byte) (I : State → Prop) (Q : State → Prop) : PEnd → Prop
  | .cut S cs => (∀ x ∈ cs, x.den ρ μ) → ∀ s', Matches ρ μ S s' → s'.exit = none → I s' → Q s'
  | .ret S cs => (∀ x ∈ cs, x.den ρ μ) → ∀ s', Matches ρ μ S s' → s'.exit = none → I s' →
      aligned ((S.reg 1).den ρ μ &&& ~~~1) 4 ∧ Q (s'.setPc ((S.reg 1).den ρ μ &&& ~~~1))

theorem sstep_plain {i : Instr} {S : SState} {x : SState × List Ob} (h : sstep i S = some x) :
    i.plain = true := by
  cases i <;> first | rfl | (simp [sstep] at h)

theorem succs_plain {f : Func} {pc : Word} {i : Instr} (h : i.plain = true) : succs f pc i = [pc + 4] := by
  cases i <;> first | rfl | (cases h)

variable {c c' : Code} {f : Func} {fr : Frame} {cert : Cert} {s0 : State} {P : Perm}

theorem endInv_succ {De : Dom} {cuts : List Word} {s s1 : State} {i : Instr}
    (hL2 : checkL2 c' f fr cert = true) (hag : ∀ x, f.contains x = true → c.instr x = c'.instr x) (hsz : fr.size < 2 ^ 32) (hoff : SlotsOff fr (s0.reg 2) P)
    (hF : InF f fr cert s0 s) (hi : c.instr s.pc = some i) (hx : s.exit = none)
    (hok : InstrOk P i s ∨ slotAccess fr (s0.reg 2) s i = true) (he : exec i s = some s1)
    (hs : s1.pc ∈ succs f s.pc i) (hin : f.contains s1.pc = true) : EndInv f fr cert s0 De cuts s1 :=
  .inl ⟨hin, FrameInv.sstep hL2 hag hsz hoff hF.1 hF.2
    (hok.elim (fun h => .step (.exec hx hi h he)) (fun h => .slot hx hi h he))
    (fun i' hi' => by rw [hi] at hi'; cases hi'; exact hs) hin⟩

theorem endInv_call {De : Dom} {cuts : List Word} {s s1 : State} {i : Instr}
    (hL2 : checkL2 c' f fr cert = true) (hag : ∀ x, f.contains x = true → c.instr x = c'.instr x) (hsz : fr.size < 2 ^ 32)
    (hF : InF f fr cert s0 s) (hi : c.instr s.pc = some i) (hc : calls i = true) (he : exec i s = some s1)
    (hcut : s1.pc ∈ cuts) (hnd : ¬ De.mem s1.pc) : EndInv f fr cert s0 De cuts s1 :=
  .inr (.inl ⟨hcut, hnd, .inl (callInfo_of hL2 hag hsz hF.1 hF.2 hi hc he)⟩)

theorem endInv_leave {De : Dom} {cuts : List Word} {s s1 : State} {i : Instr}
    (_hDe : ∀ x, De.mem x → aligned x 4 → f.contains x = true)
    (hL2 : checkL2 c' f fr cert = true) (hag : ∀ x, f.contains x = true → c.instr x = c'.instr x) (hF : InF f fr cert s0 s) (hi : c.instr s.pc = some i)
    (hl : leaves f s.pc i = true) (he : exec i s = some s1)
    (hcut : ¬ De.mem s1.pc) : EndInv f fr cert s0 De cuts s1 := by
  have ht := FrameInv.leave hL2 hag hF.1 hF.2 hi hl he
  by_cases hc : s1.pc ∈ cuts
  · exact .inr (.inl ⟨hc, hcut, .inr ht⟩)
  · exact .inr (.inr ⟨hc, hcut⟩)

theorem SReach.of_exploreF {entries : List Word} {ρ : Nat → Word} {μ : Word → Byte} {De D : Dom}
    {Q : State → Prop} {cuts : List Word} {τ : List Event} {fetch : Nat → List (BitVec 32)}
    (hb : 4 * c.words.size < 2 ^ 64) (hfe : ∀ k, fetch k = c.words.toList.drop k)
    (hDe : ∀ x, De.mem x → aligned x 4 → f.contains x = true) (hDD : De.sub D) (hchk : check c' f entries = true)
    (hL2 : checkL2 c' f fr cert = true) (hag : ∀ x, f.contains x = true → c.instr x = c'.instr x) (hfs : fr.size < 2 ^ 32) (hoff : SlotsOff fr (s0.reg 2) P) :
    ∀ {fuel : Nat} {first : Bool} {k : Nat} {ws : List (BitVec 32)} {S : SState} {cs : List Cond}
      {ends : List PEnd} {obs : List GOb} {s : State},
      explore c De cuts fetch true fuel first k ws S cs = some (ends, obs) →
      c.words.toList.drop k = ws → S.pc = c.base + BitVec.ofNat 64 (4 * k) → Matches ρ μ S s →
      s.exit = none → s.trace = τ → (∀ x ∈ cs, x.den ρ μ) → (∀ o ∈ obs, o.denS ρ μ P fr (s0.reg 2)) →
      EndInv f fr cert s0 De cuts s → (first = true → InF f fr cert s0 s) →
      (∀ e ∈ ends, e.NextI ρ μ (EndInv f fr cert s0 De cuts) (fun s' => s'.trace = τ → Q s')) →
      Struct.SReach c fr (s0.reg 2) P D Q s
  | 0, _, _, _, _, _, _, _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [explore] at h
  | fuel + 1, first, k, ws, S, cs, ends, obs, s, h, hd, hpc, hm, hx, ht, hcs, hob, hI, hfirst, hN => by
    simp only [explore] at h
    split at h
    · -- a cut point
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact .done (hN _ (List.mem_singleton_self _) hcs s hm hx hI ht)
    rename_i hnc
    split at h
    case isFalse => simp at h
    rename_i hD
    have hpcS : s.pc = S.pc := hm.2.1
    have hDe' : De.mem s.pc := by rw [hpcS]; exact hD
    have hD' : D.mem s.pc := hDD _ hDe'
    -- stepping: not at a cut (or the start), inside the function, so the fact at the pc holds
    have hF : InF f fr cert s0 s := by
      rcases hI with h' | ⟨hc', _⟩ | ⟨_, hnd⟩
      · exact h'
      · cases first
        · exfalso; apply hnc; simp only [Bool.not_false, Bool.true_and]; rw [← hpcS]; exact List.contains_iff_mem.2 hc'
        · exact hfirst rfl
      · exact absurd hDe' hnd
    have hnf : ∀ u, (false = true → InF f fr cert s0 u) := fun _ h => by cases h
    split at h
    · simp at h
    rename_i w ws'
    have hk : k < c.words.toList.length := by
      apply Nat.lt_of_not_le; intro hc
      rw [List.drop_eq_nil_of_le hc] at hd; simp at hd
    have hsz : c.words.toList.length = c.words.size := by simp
    have hk4 : 4 * (k + 1) < 2 ^ 64 := by omega
    have hw : c.words.toList[k]? = some w := by rw [← List.head?_drop, hd]; rfl
    have hfetch : ∀ i, decode w = some i → c.instr s.pc = some i := fun i hi => by
      rw [hpcS, hpc]; unfold Code.instr
      rw [Code.fetch_index c k (by omega), hw]; exact hi
    have hd₁ : c.words.toList.drop (k + 1) = ws' := by rw [← List.drop_drop, hd]; rfl
    have hpc₁ : S.pc + 4 = c.base + BitVec.ofNat 64 (4 * (k + 1)) := by rw [hpc]; exact pc_succ hk4
    split at h
    · -- a conditional branch
      rename_i op rs1 rs2 off hi
      split at h
      case isFalse => simp at h
      rename_i hal
      split at h
      case h_2 => simp at h
      rename_i k' hk'
      unfold both at h
      split at h
      case h_2 => simp at h
      rename_i e₁ o₁ e₂ o₂ h₁ h₂
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      have hra := (hm.2.2.1 rs1).symm
      have hrb := (hm.2.2.1 rs2).symm
      refine Struct.SReach.exec_step hD' hx (hfetch _ hi) (.inl trivial) ?_
      simp only [exec, jumpTo]
      have hbr := check_branch hchk hF.1 ((hag _ hF.1).symm.trans (hfetch _ hi))
      cases hc : evalBr op (s.reg rs1) (s.reg rs2)
      · simp only [Bool.false_eq_true, ite_false, Struct.SReach.opt_some]
        have he : exec (.branch op rs1 rs2 off) s = some (s.setPc (s.pc + 4)) := by
          simp only [exec, hc, Bool.false_eq_true, ite_false]
        have hE := endInv_succ (De := De) (cuts := cuts) hL2 hag hfs hoff hF (hfetch _ hi) hx (.inl trivial) he
          (by simp [succs]) (by simpa using hbr.1)
        rw [hpcS]; rw [hpcS] at hE
        exact SReach.of_exploreF hb hfe hDe hDD hchk hL2 hag hfs hoff h₂ hd₁ hpc₁ (matches_setPc hm _) (by simpa using hx) (by simpa using ht)
          (fun x hx' => by
            simp only [List.mem_cons] at hx'
            rcases hx' with rfl | hx'
            · simp only [Cond.den]; rw [hra, hrb]; exact hc
            · exact hcs x hx')
          (fun o ho => hob o (List.mem_append_right _ ho)) hE (hnf _)
          (fun e he => hN e (List.mem_append_right _ he))
      · have he : exec (.branch op rs1 rs2 off) s = some (s.setPc (S.pc + off.signExtend 64)) := by
          simp only [exec, jumpTo, hc, ite_true, hpcS, hal]
        have hE := endInv_succ (De := De) (cuts := cuts) hL2 hag hfs hoff hF (hfetch _ hi) hx (.inl trivial) he
          (by simp [succs, hpcS]) (by simpa [hpcS] using hbr.2)
        rw [hpcS]
        simp only [ite_true, hal, Struct.SReach.opt_some]
        exact SReach.of_exploreF hb hfe hDe hDD hchk hL2 hag hfs hoff h₁ (hfe _).symm (wordIdx_sound hk') (matches_setPc hm _) (by simpa using hx) (by simpa using ht)
          (fun x hx' => by
            simp only [List.mem_cons] at hx'
            rcases hx' with rfl | hx'
            · simp only [Cond.den]; rw [hra, hrb]; exact hc
            · exact hcs x hx')
          (fun o ho => hob o (List.mem_append_left _ ho)) hE (hnf _)
          (fun e he => hN e (List.mem_append_left _ he))
    · -- jal
      rename_i rd off hi
      split at h
      case isFalse => simp at h
      rename_i hal
      split at h
      case h_2 => simp at h
      rename_i k' hk'
      split at h
      · simp at h
      rename_i hstr
      have he : exec (.jal rd off) s = some ((s.setReg rd (S.pc + 4)).setPc (S.pc + off.signExtend 64)) := by
        simp only [exec, jumpTo, hpcS, hal, ite_true]
      have hE : EndInv f fr cert s0 De cuts ((s.setReg rd (S.pc + 4)).setPc (S.pc + off.signExtend 64)) := by
        by_cases h0 : rd = 0
        · by_cases hin : f.contains (S.pc + off.signExtend 64) = true
          · exact endInv_succ hL2 hag hfs hoff hF (hfetch _ hi) hx (.inl trivial) he
              (by simp [succs, h0, hin, hpcS]) (by simpa using hin)
          · exact endInv_leave hDe hL2 hag hF (hfetch _ hi) (by simp [leaves, h0, hpcS, hin]) he
              (by simp only [State.setPc_pc]; exact fun hd => hin (hDe _ hd hal))
        · have hst2 : cuts.contains (S.pc + off.signExtend 64) = true ∧
              ¬ De.mem (S.pc + off.signExtend 64) := by
            revert hstr; simp only [Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
              Bool.not_eq_true', decide_eq_true_eq]
            intro hstr; by_cases hc : cuts.contains (S.pc + off.signExtend 64) = true
            · exact ⟨hc, fun hd => hstr ⟨h0, .inr hd⟩⟩
            · exact absurd ⟨h0, .inl (by simpa using hc)⟩ hstr
          have hcut : (S.pc + off.signExtend 64) ∈ cuts := List.contains_iff_mem.1 hst2.1
          have h1 := check_jal hchk hF.1 ((hag _ hF.1).symm.trans (hfetch _ hi)) h0
          subst h1
          exact endInv_call hL2 hag hfs hF (hfetch _ hi) (by simp [calls]) he (by simpa using hcut)
            (by simpa using hst2.2)
      refine Struct.SReach.exec_step hD' hx (hfetch _ hi) (.inl trivial) ?_
      simp only [exec, jumpTo]
      rw [hpcS]
      simp only [hal, ite_true, Struct.SReach.opt_some]
      exact SReach.of_exploreF hb hfe hDe hDD hchk hL2 hag hfs hoff h (hfe _).symm (wordIdx_sound hk')
        (matches_setReg_setPc hm rd _ _ (by first | rfl | (rw [hpcS]; rfl)) _) (by simpa using hx) (by simpa using ht) hcs hob hE (hnf _) hN
    · -- jalr: the return, or a jump to a known address
      rename_i rd rs1 off hi
      split at h
      · rename_i hc; obtain ⟨rfl, rfl, rfl⟩ := hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hal, hq⟩ := hN _ (List.mem_singleton_self _) hcs s hm hx hI
        have h1 := (hm.2.2.1 1).symm
        rw [h1] at hal hq
        refine Struct.SReach.exec_step hD' hx (hfetch _ hi) (.inl trivial) ?_
        have hz : s.reg 1 + BitVec.signExtend 64 (0 : BitVec 12) = s.reg 1 := by
          rw [show BitVec.signExtend 64 (0 : BitVec 12) = 0 by decide]; bv_omega
        simp only [exec, jumpTo, setReg_x0', hz, hal, ite_true, Struct.SReach.opt_some]
        exact .done (hq (by simpa using ht))
      · rename_i hnr
        split at h
        case h_2 => simp at h
        rename_i v hv
        split at h
        case isFalse => simp at h
        rename_i hal
        split at h
        case h_2 => simp at h
        rename_i k' hk'
        split at h
        · simp at h
        rename_i hstr
        have hrs : s.reg rs1 = v := by rw [hm.2.2.1 rs1, hv]; rfl
        have he : exec (.jalr rd rs1 off) s = some ((s.setReg rd (s.pc + 4)).setPc ((v + off.signExtend 64) &&& ~~~1)) := by
          simp only [exec, jumpTo, hrs, hal, ite_true]
        have hst2 : cuts.contains ((v + off.signExtend 64) &&& ~~~1) = true ∧
            ¬ De.mem ((v + off.signExtend 64) &&& ~~~1) := by
          revert hstr; simp only [Bool.true_and, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
          intro hstr; by_cases hc : cuts.contains ((v + off.signExtend 64) &&& ~~~1) = true
          · exact ⟨hc, fun hd => hstr (.inr hd)⟩
          · exact absurd (.inl (by simpa using hc)) hstr
        have hcut : ((v + off.signExtend 64) &&& ~~~1) ∈ cuts := List.contains_iff_mem.1 hst2.1
        have hE : EndInv f fr cert s0 De cuts ((s.setReg rd (s.pc + 4)).setPc ((v + off.signExtend 64) &&& ~~~1)) := by
          rcases check_jalr hchk hF.1 ((hag _ hF.1).symm.trans (hfetch _ hi)) hnr with h0 | h1
          · subst h0
            exact endInv_leave hDe hL2 hag hF (hfetch _ hi) (by simp [leaves]) he (by simpa using hst2.2)
          · subst h1
            exact endInv_call hL2 hag hfs hF (hfetch _ hi) (by simp [calls]) he (by simpa using hcut)
              (by simpa using hst2.2)
        refine Struct.SReach.exec_step hD' hx (hfetch _ hi) (.inl trivial) ?_
        simp only [exec, jumpTo, hrs]
        simp only [hal, ite_true, Struct.SReach.opt_some]
        exact SReach.of_exploreF hb hfe hDe hDD hchk hL2 hag hfs hoff h (hfe _).symm (wordIdx_sound hk')
          (matches_setReg_setPc hm rd _ _ (by first | rfl | (rw [hpcS]; rfl)) _) (by simpa using hx) (by simpa using ht) hcs hob hE (hnf _) hN
    · -- a straight-line instruction
      rename_i i _ _ _ hi
      split at h
      case h_2 => simp at h
      rename_i S₁ o₁ hst
      cases hr : explore c De cuts fetch true fuel false (k + 1) ws' S₁ cs with
      | none => rw [hr] at h; simp at h
      | some p =>
        obtain ⟨e₂, o₂⟩ := p
        rw [hr] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨s₁, he, hok, hm₁⟩ := sstep_soundS (P := P) (fr := fr) (sp0 := s0.reg 2) hm hst
          (fun o ho => hob ⟨cs, o⟩ (List.mem_append_left _ (List.mem_map_of_mem ho)) hcs)
        have hS₁ : S₁.pc = c.base + BitVec.ofNat 64 (4 * (k + 1)) := by
          rw [← hpc₁]
          cases i <;> simp only [sstep, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hst <;>
            (try obtain ⟨rfl, rfl⟩ := hst) <;> rfl
        have hp := sstep_plain hst
        have hs4 : s₁.pc = s.pc + 4 := by rw [hm₁.2.1, hS₁, ← hpc₁, hpcS]
        have hE := endInv_succ (De := De) (cuts := cuts) hL2 hag hfs hoff hF (hfetch _ hi) hx hok he
          (by rw [succs_plain hp, hs4]; simp) (by rw [hs4]; exact check_plain hchk hF.1 ((hag _ hF.1).symm.trans (hfetch _ hi)) hp)
        exact Struct.SReach.exec_step hD' hx (hfetch _ hi) hok
          (by rw [he, Struct.SReach.opt_some]
              exact SReach.of_exploreF hb hfe hDe hDD hchk hL2 hag hfs hoff hr hd₁ hS₁ hm₁ ((exec_exit he).trans hx) ((exec_trace he).trans ht) hcs
                (fun o ho => hob o (List.mem_append_right _ ho)) hE (hnf _) hN)
    · simp at h



/-- Every end's condition, assuming `I` there, as one conjunction. -/
def allNextI (ρ : Nat → Word) (μ : Word → Byte) (I Q : State → Prop) : List PEnd → Prop
  | [] => True
  | e :: es => e.NextI ρ μ I Q ∧ allNextI ρ μ I Q es

theorem allNextI_mem {ρ : Nat → Word} {μ : Word → Byte} {I Q : State → Prop} :
    ∀ {es : List PEnd}, allNextI ρ μ I Q es → ∀ e ∈ es, e.NextI ρ μ I Q
  | [], _, _, h => by simp at h
  | _ :: _, ⟨h₁, h₂⟩, _, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact h₁
    · exact allNextI_mem h₂ _ h

/-- One cut point's verification condition for an L2 function: explore (strict) inside `De`;
    the obligations, structured; every end's condition, assuming `I`. -/
def exploreVCF (ρ : Nat → Word) (μ : Word → Byte) (P : Perm) (fr : Frame) (sp0 : Word)
    (I Q : State → Prop) (facts : List Fact) (c : Code) (De : Dom) (cuts : List Word) (fuel k : Nat) (p : Word)
    (fetch : Nat → List (BitVec 32) := fun k => c.words.toList.drop k) : Prop :=
  match exploreR c De cuts fetch fuel k p facts true with
  | some (ends, res) => allObS ρ μ P fr sp0 res ∧ allNextI ρ μ I Q ends
  | none => False

/-- From a cut point of an L2 function where the certificate's fact holds: the structured run, each
    end's condition assuming `EndInv`. -/
theorem SReach.of_exploreAtF {entries : List Word} {De D : Dom} {Q : State → Prop} {facts : List Fact}
    {cuts : List Word} {fuel k : Nat} {p : Word} {s : State} {fetch : Nat → List (BitVec 32)}
    (hb : 4 * c.words.size < 2 ^ 64) (hfe : ∀ k, fetch k = c.words.toList.drop k)
    (hDe : ∀ x, De.mem x → aligned x 4 → f.contains x = true) (hDD : De.sub D) (hchk : check c' f entries = true)
    (hL2 : checkL2 c' f fr cert = true) (hag : ∀ x, f.contains x = true → c.instr x = c'.instr x) (hfs : fr.size < 2 ^ 32) (hoff : SlotsOff fr (s0.reg 2) P)
    (hk : p = c.base + BitVec.ofNat 64 (4 * k)) (hpc : s.pc = p) (hx : s.exit = none)
    (hf : ∀ f ∈ facts, f.den (ρOf s) P) (hF : InF f fr cert s0 s)
    (hvc : exploreVCF (ρOf s) s.mem P fr (s0.reg 2) (EndInv f fr cert s0 De cuts)
      (fun s' => s'.trace = s.trace → Q s') facts c De cuts fuel k p fetch) :
    SReach c fr (s0.reg 2) P D Q s := by
  unfold exploreVCF exploreR at hvc
  cases h : explore c De cuts fetch true fuel true k (fetch k) (SState.init p) [] with
  | none => rw [h] at hvc; exact hvc.elim
  | some r =>
    obtain ⟨ends, obs⟩ := r
    rw [h] at hvc
    simp only [Option.map_some] at hvc
    refine SReach.of_exploreF (τ := s.trace) hb hfe hDe hDD hchk hL2 hag hfs hoff h (hfe k).symm hk
      (matches_init hpc) hx rfl (by simp) (fun o ho => ?_) (.inl hF) (fun _ => hF) (allNextI_mem hvc.2)
    cases hc : o.o.check facts
    · exact allObS_mem hvc.1 o (List.mem_filter.2 ⟨ho, by simp [hc]⟩)
    · exact fun _ => Ob.denS_of_den (Ob.check_sound hf hc)

end VC.M
end NoCompiler

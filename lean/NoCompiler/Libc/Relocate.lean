import NoCompiler.Libc.Transfer
import NoCompiler.Shift

/-!
# Relocating a process-level function theorem

NoCompiler/Shift.lean's `Reach.shift` at the process level: the kernel step (`ProcStep7`) reads only a0..a7
and the memory (`SyscallInput.of`) and writes a0, the pc and the memory, so it commutes with `State.shift`
(pc and `ra` moved by `δ`). Hence a process run of pcFree code (CodeShift) at one address is a run of the same
words `δ` further on (`PReachK.shift`), with the same kernel states.
-/

namespace NoCompiler.Linux

theorem SyscallInput.of_shift (s : State) (δ : Word) : SyscallInput.of (s.shift δ) = SyscallInput.of s := by
  simp only [SyscallInput.of, State.shift_mem, State.shift_reg _ _ (by decide : (10 : Reg) ≠ 1),
    State.shift_reg _ _ (by decide : (11 : Reg) ≠ 1), State.shift_reg _ _ (by decide : (12 : Reg) ≠ 1),
    State.shift_reg _ _ (by decide : (13 : Reg) ≠ 1), State.shift_reg _ _ (by decide : (14 : Reg) ≠ 1),
    State.shift_reg _ _ (by decide : (15 : Reg) ≠ 1), State.shift_reg _ _ (by decide : Reg.a7 ≠ 1)]

theorem Outcome.apply_shift (s : State) (δ : Word) (o : Outcome) : o.apply (s.shift δ) = (o.apply s).shift δ := by
  cases o with
  | ret e ev =>
    cases ev <;> simp only [Outcome.apply, State.shift_sysRet, State.shift_setMem, State.shift_emit, State.shift_mem]
  | exit code => simp only [Outcome.apply, State.shift_halt, State.shift_emit]

theorem ProcStep7.shift {s t : State} {k k' : Kern} (h : ProcStep7 (s, k) (t, k')) (δ : Word) :
    ProcStep7 (s.shift δ, k) (t.shift δ, k') := by
  cases h with
  | step hp =>
    rw [← Outcome.apply_shift]
    exact .step (by rw [SyscallInput.of_shift]; exact hp)

theorem ProcStep7.reg_one {s t : State} {k k' : Kern} (h : ProcStep7 (s, k) (t, k')) : t.reg 1 = s.reg 1 := by
  cases h with
  | step _ =>
    rename_i o _
    cases o with
    | ret e ev =>
      have h0 : ¬ (Reg.a0 = 0) := by decide
      cases ev <;> simp only [Outcome.apply, State.sysRet, State.setMem, State.emit, State.setReg, State.setPc,
        State.reg, h0, ite_false] <;>
        simp only [State.upd, show ¬ ((1 : Reg) = Reg.a0) by decide, ite_false]
    | exit code => simp [Outcome.apply, State.halt, State.emit, State.reg]

variable {c c' : Code} {D : Dom} {δ : Word}

theorem PStep.shift (h : CodeShift c c' D δ) {s s' : State} {k k' : Kern} (hd : D.mem s.pc)
    (hra : aligned (s.reg 1) 4) (st : PStep c (s, k) (s', k')) : PStep c' (s.shift δ, k) (s'.shift δ, k') := by
  cases st with
  | exec he hi hok hx =>
    have hf := h.free _ _ hd hi
    refine .exec he (by rw [State.shift_pc, h.instr _ hd]; exact hi) ((InstrOk_shift hf δ).2 hok) ?_
    rw [exec_shift hf h.aligned hra, hx]; rfl
  | sys he hi hok hy =>
    exact .sys he (by rw [State.shift_pc, h.instr _ hd]; exact hi) ((SysOk_shift δ).2 hok) (hy.shift δ)

theorem PStep.unshift (h : CodeShift c c' D δ) {s : State} {k : Kern} {y : State × Kern} (hd : D.mem s.pc)
    (hra : aligned (s.reg 1) 4) (st : PStep c' (s.shift δ, k) y) :
    ∃ s', y.1 = s'.shift δ ∧ PStep c (s, k) (s', y.2) := by
  cases st with
  | exec he hi hok hx =>
    rw [State.shift_pc, h.instr _ hd] at hi
    have hf := h.free _ _ hd hi
    rw [exec_shift hf h.aligned hra] at hx
    obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.1 hx
    exact ⟨s', rfl, .exec he hi ((InstrOk_shift hf δ).1 hok) hs'⟩
  | sys he hi hok hy =>
    rename_i t k'
    rw [State.shift_pc, h.instr _ hd] at hi
    refine ⟨t.shift (-δ), (State.neg_shift _ _).symm, .sys he hi ((SysOk_shift δ).1 hok) ?_⟩
    have := hy.shift (-δ); rwa [State.shift_neg] at this

theorem PStep.reg_one (h : CodeShift c c' D δ) {s s' : State} {k k' : Kern} (hd : D.mem s.pc)
    (st : PStep c (s, k) (s', k')) : s'.reg 1 = s.reg 1 := by
  cases st with
  | exec _ hi _ hx => exact exec_reg_one (h.free _ _ hd hi) hx
  | sys _ _ _ hy => exact hy.reg_one

/-- A process run of pcFree code is a run of the same code `δ` further on, with the same kernel states. -/
theorem PReachK.shift (h : CodeShift c c' D δ) {Q : State × Kern → Prop} {s : State} {k : Kern}
    (hr : PReachK c D Q (s, k)) (hra : aligned (s.reg 1) 4) :
    PReachK c' (D.shift δ) (fun y => Q (y.1.shift (-δ), y.2)) (s.shift δ, k) := by
  generalize hx : (s, k) = x at hr
  induction hr generalizing s k with
  | done hq => subst hx; exact .done (by simp only [State.shift_neg]; exact hq)
  | @step u ku hd hex _ ih =>
    cases hx
    obtain ⟨⟨u1, k1⟩, st⟩ := hex
    refine .step (by rw [State.shift_pc]; exact Dom.mem_shift.2 hd) ⟨_, PStep.shift h hd hra st⟩ ?_
    rintro ⟨t, kt⟩ st'
    obtain ⟨u', hu', st''⟩ := PStep.unshift h hd hra st'
    simp only at hu' st''
    subst hu'
    exact ih (u', kt) st'' (by rw [PStep.reg_one h hd st'']; exact hra) rfl

/-! ## Specifications that do not look at the pc or `ra` -/

structure SpecP.ShiftInv {α : Type} (sp : SpecP α) : Prop where
  pre : ∀ a s k δ, sp.pre a (s.shift δ) k ↔ sp.pre a s k
  post : ∀ a s k t k' δ, sp.post a (s.shift δ, k) (t.shift δ, k') ↔ sp.post a (s, k) (t, k')
  onExit : ∀ a s k t k' δ, sp.onExit a (s.shift δ, k) (t.shift δ, k') ↔ sp.onExit a (s, k) (t, k')

/-- A process-level proof of pcFree code at one address is a proof `δ` further on: relocation of a library
    function's theorem without re-proof. -/
theorem VerifiedProc.shift {α : Type} {e : Word} {sp : SpecP α} (h : CodeShift c c' D δ)
    (hs : sp.ShiftInv) (hv : VerifiedProc c D e sp) : VerifiedProc c' (D.shift δ) (e + δ) sp := by
  intro a s' k he' hpre'
  have hs' : (s'.shift (-δ)).shift δ = s' := State.neg_shift _ _
  have he : Entry D e (s'.shift (-δ)) :=
    { pc := by rw [State.shift_pc, he'.pc]; bv_omega
      live := by rw [State.shift_exit]; exact he'.live
      ret := by
        rw [State.shift_reg_one]; intro hm; exact he'.ret (Dom.mem_shift'.2 hm)
      retAligned := by
        rw [State.shift_reg_one]; exact (aligned_add_iff (aligned_neg h.aligned)).2 he'.retAligned
      sp := by rw [State.shift_reg _ _ (by decide)]; exact he'.sp }
  have hpre : sp.pre a (s'.shift (-δ)) k := (hs.pre a _ k δ).1 (by rw [hs']; exact hpre')
  have hr := PReachK.shift h (hv a _ k he hpre) he.retAligned
  rw [hs'] at hr
  refine PReachK.mono ?_ hr
  rintro ⟨t, kt⟩ ⟨hf, hd⟩
  refine ⟨?_, ?_⟩
  · rcases hf with hf | hf
    · exact .inl (fun hm => hf (Dom.mem_shift'.1 hm))
    · exact .inr (by simpa using hf)
  · have hpost := hs.post a (s'.shift (-δ)) k (t.shift (-δ)) kt δ
    have hexit := hs.onExit a (s'.shift (-δ)) k (t.shift (-δ)) kt δ
    rw [hs', State.neg_shift] at hpost hexit
    rcases hd with ⟨hx, hpc, hpres, hp⟩ | ⟨hx, ho⟩
    · refine .inl ⟨by simpa using hx, ?_, ?_, hpost.2 hp⟩
      · show t.pc = s'.reg 1
        simp only [State.shift_pc, State.shift_reg_one] at hpc; bv_omega
      · intro r hr'
        have hne : r ≠ 1 := by
          intro e; subst e; simp [preservedRegs] at hr'
        have := hpres r hr'
        rwa [State.shift_reg _ _ hne, State.shift_reg _ _ hne] at this
    · exact .inr ⟨by simpa using hx, hexit.2 ho⟩

end NoCompiler.Linux

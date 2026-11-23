import Examples.Libc.StartMain
import NoCompiler.Linux.RunN
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage

/-- `_start` (crt1, asm) and `_start_c` with what they reach. -/
def startD : Dom := [(0x111d0#64, 76)] ++ lsmD

/-- The tail call of `__libc_start_main(main, argc, argv, _init, _fini, 0)` from the launch state `s`: argc the
    sign-extended word at sp, argv = sp + 8, sp rounded down to 16, gp set, ra as at launch. -/
def StartCall (s z : State) : Prop :=
  z.pc = 0x11584#64 ∧ z.exit = none ∧ z.reg 2 = s.reg 2 &&& 0xfffffffffffffff0#64 ∧
  z.reg 10 = 0x1121c#64 ∧ z.reg 11 = BitVec.signExtend 64 (BitVec.ofNat 32 (readLE s.mem (s.reg 2) 4)) ∧
  z.reg 12 = s.reg 2 + 8#64 ∧ z.reg 13 = 0x112e8#64 ∧ z.reg 14 = 0x11a50#64 ∧ z.reg 15 = 0 ∧
  z.reg 3 = 0x147b0#64 ∧ (∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 3 → z.reg q = s.reg q) ∧ z.reg 1 = s.reg 1 ∧
  z.mem = s.mem ∧ z.trace = s.trace

theorem start_al (sp : Word) : aligned (sp &&& 0xfffffffffffffff0#64) 16 := by
  have h : (sp &&& 0xfffffffffffffff0#64) % 16#64 = 0#64 := NoCompiler.Libc.and_mask16_umod16 sp
  unfold aligned
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_umod] at this
  exact this

/-- The tail call of `__libc_start_main` from `z`. -/
theorem start_tail (L : SpecP Unit) (hL : VerifiedProcNR code lsmD __libc_start_main_entry L)
    (hLp : ∀ x y, ¬ L.post () x y) (s : State) (k : Kern) (z : State) (hSC : StartCall s z) (hpre : L.pre () z k) :
    PReachK code startD (fun y => Final startD y.1 ∧ y.1.exit ≠ none ∧ ∃ z, StartCall s z ∧ L.onExit () (z, k) y) (z, k) := by
  have hSC' := hSC
  obtain ⟨c1, c2, c3, -⟩ := hSC'
  refine PReachK.bind (Dom.sub_of_ranges (by decide)) (fun y hy => ?_)
    (hL () z k ⟨by rw [c1]; rfl, c2, by simp only [Reg.sp, c3]; exact start_al _⟩ hpre)
  obtain ⟨-, hy⟩ := hy
  rcases hy with ⟨-, -, -, hp⟩ | ⟨hex, hon⟩
  · exact (hLp _ _ hp).elim
  · exact .done ⟨.inr hex, hex, z, hSC, hon⟩

theorem start_run (L : SpecP Unit) (hL : VerifiedProcNR code lsmD __libc_start_main_entry L)
    (hLp : ∀ x y, ¬ L.post () x y) (s : State) (k : Kern) (hpc : s.pc = 0x111d0#64) (hx : s.exit = none)
    (hal : aligned (s.reg 2) 16) (hrd : k.perm.canRead (s.reg 2) 4) (hpre : ∀ z, StartCall s z → L.pre () z k) :
    PReachK code startD (fun y => Final startD y.1 ∧ y.1.exit ≠ none ∧ ∃ z, StartCall s z ∧ L.onExit () (z, k) y) (s, k) := by
  have hal4 : aligned (s.reg 2) 4 := by unfold aligned at *; bv_omega
  nocompiler_run_n 19 [hx, hpc, hal4] using [hrd]
  refine start_tail L hL hLp s k _ ⟨by simp only [nocompiler_state], by simp only [nocompiler_state]; exact hx,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq a2 a3 => ?_, ?_, by simp only [nocompiler_state],
    by simp only [nocompiler_state]⟩ (hpre _ ⟨by simp only [nocompiler_state], by simp only [nocompiler_state]; exact hx,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq a2 a3 => ?_, ?_, by simp only [nocompiler_state],
    by simp only [nocompiler_state]⟩)
  all_goals (try simp (disch := nocompiler_decide_closed) only [nocompiler_state])
  all_goals (try rfl)
  all_goals
    have hne : q ≠ 1 ∧ q ≠ 6 ∧ q ≠ 10 ∧ q ≠ 11 ∧ q ≠ 12 ∧ q ≠ 13 ∧ q ≠ 14 ∧ q ≠ 15 := by revert hq; revert q; decide
    simp only [State.setPc_reg, State.reg_setReg_other _ _ _ _ hne.1, State.reg_setReg_other _ _ _ _ hne.2.1,
      State.reg_setReg_other _ _ _ _ hne.2.2.1, State.reg_setReg_other _ _ _ _ hne.2.2.2.1,
      State.reg_setReg_other _ _ _ _ hne.2.2.2.2.1, State.reg_setReg_other _ _ _ _ hne.2.2.2.2.2.1,
      State.reg_setReg_other _ _ _ _ hne.2.2.2.2.2.2.1, State.reg_setReg_other _ _ _ _ hne.2.2.2.2.2.2.2,
      State.reg_setReg_other _ _ _ _ a2, State.reg_setReg_other _ _ _ _ a3]

end Examples.Libc.Slen

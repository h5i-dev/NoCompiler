import NoCompiler.Lib.SpecPerm

/-!
# Library: callee-saved registers

`Preserved s s'` (Spec.lean): sp, gp, tp and s0 to s11 hold in `s'` what they held in `s`. Its
rules: reflexive and transitive (a chain of calls), kept by writes to other registers and by
changes of pc, memory and trace, and read off per register (`sp`, `gp`, `tp`, `s0`, `s1`; the others by `Preserved.reg _ (by decide)`). Namespace
`NoCompiler.Lib`. Round 7, B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

theorem preserved_refl (s : State) : Preserved s s := fun _ _ => rfl

/-- Two calls in a row keep the callee-saved registers. -/
theorem preserved_trans {s s' s'' : State} (h : Preserved s s') (h' : Preserved s' s'') :
    Preserved s s'' := fun r hr => (h' r hr).trans (h r hr)

theorem preserved_symm {s s' : State} (h : Preserved s s') : Preserved s' s :=
  fun r hr => (h r hr).symm

/-- Writing a register that is not callee-saved (a temporary, an argument, ra). -/
theorem preserved_setReg {s s' : State} (h : Preserved s s') {q : Reg} (v : Word)
    (hq : q ∉ preservedRegs) : Preserved s (s'.setReg q v) := by
  intro r hr
  have hne : r ≠ q := fun e => hq (e ▸ hr)
  rw [State.reg_setReg_other _ _ _ _ hne]; exact h r hr

theorem preserved_setPc {s s' : State} (h : Preserved s s') (p : Word) : Preserved s (s'.setPc p) := h
theorem preserved_setMem {s s' : State} (h : Preserved s s') (m : Word → Byte) :
    Preserved s (s'.setMem m) := h
theorem preserved_emit {s s' : State} (h : Preserved s s') (e : Event) : Preserved s (s'.emit e) := h

/-- Writing a callee-saved register with the value it had at entry (a restore from the frame). -/
theorem preserved_restore {s s' : State} (h : Preserved s s') {q : Reg} :
    Preserved s (s'.setReg q (s.reg q)) := by
  intro r hr
  by_cases e : r = q
  · subst e
    have h0 : r ≠ 0 := fun e0 => by subst e0; exact absurd hr (by decide)
    exact State.reg_setReg_same _ _ _ h0
  · rw [State.reg_setReg_other _ _ _ _ e]; exact h r hr

/-- One register of `Preserved`, by its number. -/
theorem Preserved.reg {s s' : State} (h : Preserved s s') {r : Reg} (hr : r ∈ preservedRegs) :
    s'.reg r = s.reg r := h r hr

theorem Preserved.sp {s s' : State} (h : Preserved s s') : s'.reg 2 = s.reg 2 := h 2 (by decide)
theorem Preserved.gp {s s' : State} (h : Preserved s s') : s'.reg 3 = s.reg 3 := h 3 (by decide)
theorem Preserved.tp {s s' : State} (h : Preserved s s') : s'.reg 4 = s.reg 4 := h 4 (by decide)
theorem Preserved.s0 {s s' : State} (h : Preserved s s') : s'.reg 8 = s.reg 8 := h 8 (by decide)
theorem Preserved.s1 {s s' : State} (h : Preserved s s') : s'.reg 9 = s.reg 9 := h 9 (by decide)

end NoCompiler.Lib

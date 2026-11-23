import LPS.Bridge.SimReg2
import LPS.Bridge.Load

/-!
# Bridge, step 2 (composition): a NoCompiler step is an LPS `RiscvSemantics.step`

`Rel segs P s ms`: the LPS machine state `ms` holds `s`'s registers and pc (`RelC` on its core), `s`'s
memory on what `P` covers (`RelM`), and no pending syscall. `sim_step_reg`/`sim_step_load`: if LPS fetches
the 32-bit word `w` at the pc, NoCompiler decodes it to `i`, and LPS decodes it to `toLPS i`, then NoCompiler's
step `s → s'` is LPS's `step` `ms → ms'` with `Rel segs P s' ms'`. The fetch and decode facts are what an
image discharges (Bridge/Decode's `agree`, and the image's code bytes).
-/

namespace LPS.Bridge
open NoCompiler LPS.RiscvSemantics

/-- The LPS core inside a machine state (as `decode_exec_accesses` builds it). -/
def coreOf (ms : machine_state) : core :=
  { c_regs := ms.ms_regs, c_fregs := ms.ms_fregs, c_pc := ms.ms_pc_val, c_fcsr := ms.ms_fcsr, c_resv := ms.ms_resv }

def Rel (segs : List Segment) (P : Perm) (s : State) (ms : machine_state) : Prop :=
  RelC s (coreOf ms) ∧ RelM segs P s ms.ms_mem ∧ ms.ms_svc_pending = none

/-- What `decode_exec_accesses` makes of a 32-bit non-ecall word LPS decodes to `j`, whose execution from the
    machine's core ends in `MachineOk ⟨(c', m'), acc⟩`. -/
theorem decode_exec_of (segs : List Segment) (ms : machine_state) (w : bv 32) (j : LPS.instr)
    (hec : is_ecall w = false) (hlow : bv_unsigned (bits 0 2 w) = 3) (hdec : LPS.decode w = some j)
    {c' : core} {m' : word → Option byte} {acc : List memory_access}
    (hi : interp_eff_accesses segs (LPS.exec 4 j (coreOf ms)) ms.ms_mem = .MachineOk (mkAccessReport (c', m') acc)) :
    decode_exec segs ms w = .MachineOk
      { ms_regs := c'.c_regs, ms_fregs := c'.c_fregs, ms_pc_val := c'.c_pc, ms_svc_pending := none,
        ms_resv := c'.c_resv, ms_fcsr := c'.c_fcsr, ms_mem := m', ms_rom := ms.ms_rom } := by
  have hany : decode_any w = some (j, 4) := by simp [decode_any, hlow, hdec]
  have h4 : (Z_to_bv 64 4 : word) = 4 := rfl
  simp only [decode_exec, decode_exec_accesses, hec, hany, h4, Bool.false_eq_true, ite_false]
  unfold coreOf at hi
  rw [hi]; rfl

/-- A register-only NoCompiler step leaves memory as it was. -/
theorem exec_regOnly_mem {i : Instr} {s s' : State} (hm : Instr.regOnly i = true) (hs : NoCompiler.exec i s = some s') :
    s'.mem = s.mem := by
  have key : ∀ (t : State) (p : Word) (rd : Reg) (v : Word), ((t.setReg rd v).setPc p).mem = t.mem ∧
      (t.setPc p).mem = t.mem := by
    intro t p rd v; refine ⟨?_, rfl⟩; unfold State.setReg State.setPc; split <;> rfl
  cases i <;> simp only [Instr.regOnly, Bool.false_eq_true] at hm <;> revert hs <;>
    simp only [NoCompiler.exec, jumpTo] <;> (repeat' split) <;> intro hs <;>
    simp only [Option.some.injEq, reduceCtorEq] at hs <;> subst hs <;>
    first | exact (key _ _ _ _).1 | exact (key _ _ 0 0).2

theorem RelM.of_mem_eq {segs P s s' m} (h : RelM segs P s m) (e : s'.mem = s.mem) : RelM segs P s' m := by
  refine ⟨fun a ha => ?_, h.2⟩; rw [e]; exact h.1 a ha

theorem not_ecall_word {w : bv 32} {i : Instr} (hdecN : NoCompiler.decode w = some i) (hi : i ≠ .ecall) :
    is_ecall w = false := by
  cases h : is_ecall w
  · rfl
  · exfalso; apply hi
    have hw : w = Z_to_bv 32 0x73 := by
      simp only [is_ecall, bv_eqb_eq, beq_iff_eq] at h; exact h
    subst hw
    have : NoCompiler.decode (Z_to_bv 32 0x73) = some .ecall := by decide
    rw [this] at hdecN; exact (Option.some.inj hdecN).symm

theorem step_of_fetch {segs : List Segment} {ms : machine_state} {w : bv 32}
    (hfetch : fetch_word segs (ms_pc ms) = some w) : RiscvSemantics.step segs ms = decode_exec segs ms w := by
  simp only [RiscvSemantics.step, step_accesses, hfetch]; rfl

/-- A register-only NoCompiler step from a related state is an LPS `step` to a related state. -/
theorem sim_step_reg {segs : List Segment} {P : Perm} {s s' : State} {ms : machine_state} {w : bv 32}
    {i : Instr} {j : LPS.instr} (hr : Rel segs P s ms) (hfetch : fetch_word segs (ms_pc ms) = some w)
    (hdecN : NoCompiler.decode w = some i) (hj : toLPS i = some j) (hdec : LPS.decode w = some j)
    (hlow : bv_unsigned (bits 0 2 w) = 3) (hm : Instr.regOnly i = true) (hs : NoCompiler.exec i s = some s') :
    ∃ ms', RiscvSemantics.step segs ms = .MachineOk ms' ∧ Rel segs P s' ms' := by
  obtain ⟨c', hx, hc'⟩ := sim_reg hr.1 hm hj hs
  have hec := not_ecall_word hdecN (by intro e; subst e; simp [Instr.regOnly] at hm)
  have hi : interp_eff_accesses segs (LPS.exec 4 j (coreOf ms)) ms.ms_mem =
      .MachineOk (mkAccessReport (c', ms.ms_mem) []) := by rw [hx]; rfl
  refine ⟨_, by rw [step_of_fetch hfetch, decode_exec_of segs ms w j hec hlow hdec hi], by exact hc', ?_, rfl⟩
  exact hr.2.1.of_mem_eq (exec_regOnly_mem hm hs)

/-- A NoCompiler load from a related state is an LPS `step` to a related state. -/
theorem sim_step_load {segs : List Segment} {P : Perm} {s s' : State} {ms : machine_state} {w : bv 32}
    {op : LdOp} {rd rs1 : Reg} {off : BitVec 12} (hr : Rel segs P s ms)
    (hfetch : fetch_word segs (ms_pc ms) = some w) (hdecN : NoCompiler.decode w = some (.load op rd rs1 off))
    (hdec : LPS.decode w = some (.Load (ldOp op).1 (ldOp op).2 (r rd) (r rs1) off))
    (hlow : bv_unsigned (bits 0 2 w) = 3) (hok : P.canRead (ea s rs1 off) op.width)
    (hs : NoCompiler.exec (.load op rd rs1 off) s = some s') :
    ∃ ms', RiscvSemantics.step segs ms = .MachineOk ms' ∧ Rel segs P s' ms' := by
  obtain ⟨c', acc, hi, hc'⟩ := sim_load hr.1 hr.2.1 op rd rs1 off hok hs
  have hec := not_ecall_word hdecN (by intro e; cases e)
  have hmem : s'.mem = s.mem := by
    simp only [NoCompiler.exec] at hs; split at hs
    · simp only [Option.some.injEq] at hs; subst hs; unfold State.setReg State.setPc; split <;> rfl
    · cases hs
  refine ⟨_, by rw [step_of_fetch hfetch, decode_exec_of segs ms w _ hec hlow hdec hi], by exact hc', ?_, rfl⟩
  exact hr.2.1.of_mem_eq hmem

end LPS.Bridge

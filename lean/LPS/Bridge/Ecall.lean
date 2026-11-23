import LPS.Bridge.Proc

/-!
# Bridge: ECALL. LPS's machine step at an `ecall` marks the syscall pending

From related states at a fetched `ecall` word, LPS's `RiscvSemantics.step` leaves registers, memory and pc as
they are and sets `ms_svc_pending` to NoCompiler's a7; the six syscall arguments LPS's specs read
(`syscall_args`) are NoCompiler's a0..a5. The syscall itself is then LPS's (its process step `sstep_cfg_syscall`
with `syscall_spec`), not bridged to NoCompiler's own kernel model (design note, STATUS-D 13:24).
-/

namespace LPS.Bridge
open NoCompiler LPS.RiscvSemantics

theorem ms_reg_rget (ms : machine_state) (x : reg) : ms_reg ms x = rget (coreOf ms) x := by
  unfold ms_reg rget is_x0 bv_eqb coreOf; rfl

theorem sim_ecall {segs : List Segment} {P : Perm} {s : State} {ms : machine_state}
    (hr : Rel segs P s ms) (hfetch : fetch_word segs (ms_pc ms) = some (Z_to_bv 32 0x73)) :
    ∃ ms', RiscvSemantics.step segs ms = .MachineOk ms' ∧ ms'.ms_svc_pending = some (s.reg 17) ∧
      ms'.ms_regs = ms.ms_regs ∧ ms'.ms_mem = ms.ms_mem ∧ ms'.ms_pc_val = ms.ms_pc_val := by
  have hec : is_ecall (Z_to_bv 32 0x73) = true := by decide
  refine ⟨{ ms with ms_svc_pending := some (ms_reg ms 17) }, ?_, ?_, rfl, rfl, rfl⟩
  · rw [step_of_fetch hfetch]; simp only [decode_exec, decode_exec_accesses, hec, ite_true]; rfl
  · show some (ms_reg ms 17) = some (s.reg 17)
    rw [ms_reg_rget, show (17 : reg) = r 17 from rfl, hr.1.1 17]

/-- The six argument registers LPS's syscall specs read are NoCompiler's a0..a5. -/
theorem syscall_args_rel {s : State} {ms : machine_state} (h : RelC s (coreOf ms)) :
    syscall_args ms = [s.reg 10, s.reg 11, s.reg 12, s.reg 13, s.reg 14, s.reg 15] := by
  have g : ∀ n : Fin 32, rget (coreOf ms) (r n) = s.reg n := h.1
  simp only [syscall_args]
  rw [show ms_gpr ms 0 = rget (coreOf ms) (r 10) from rfl, show ms_gpr ms 1 = rget (coreOf ms) (r 11) from rfl,
    show ms_gpr ms 2 = rget (coreOf ms) (r 12) from rfl, show ms_gpr ms 3 = rget (coreOf ms) (r 13) from rfl,
    show ms_gpr ms 4 = rget (coreOf ms) (r 14) from rfl, show ms_gpr ms 5 = rget (coreOf ms) (r 15) from rfl,
    g, g, g, g, g, g]

end LPS.Bridge

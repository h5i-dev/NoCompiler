import LPS.Bridge.Step
import LPS.Bridge.Store

/-!
# Bridge, step 2 (composition, stores): a NoCompiler store is an LPS `RiscvSemantics.step`
-/

namespace LPS.Bridge
open NoCompiler LPS.RiscvSemantics

theorem sim_step_store {segs : List Segment} {P : Perm} {s s' : State} {ms : machine_state} {w : bv 32}
    {op : StOp} {rs1 rs2 : Reg} {off : BitVec 12} (hr : Rel segs P s ms)
    (hfetch : fetch_word segs (ms_pc ms) = some w) (hdecN : NoCompiler.decode w = some (.store op rs1 rs2 off))
    (hdec : LPS.decode w = some (.Store (stOp op) (r rs1) (r rs2) off))
    (hlow : bv_unsigned (bits 0 2 w) = 3) (hok : P.canWrite (ea s rs1 off) op.width)
    (hs : NoCompiler.exec (.store op rs1 rs2 off) s = some s') :
    ∃ ms', RiscvSemantics.step segs ms = .MachineOk ms' ∧ Rel segs P s' ms' := by
  obtain ⟨c', m', acc, hi, hc', hm'⟩ := sim_store hr.1 hr.2.1 op rs1 rs2 off hok hs
  have hec := not_ecall_word hdecN (by intro e; cases e)
  exact ⟨_, by rw [step_of_fetch hfetch, decode_exec_of segs ms w _ hec hlow hdec hi], by exact hc', hm', rfl⟩

end LPS.Bridge

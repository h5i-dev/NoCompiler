import LPS.Bridge.Image
import LPS.LinuxProcessSem.Run2

/-!
# Bridge: one NoCompiler instruction step is one LPS process step (`sstep_cfg`)

LPS's process step for an instruction (`sstep_cfg_instr`) runs `RiscvSemantics.step_accesses` and then
materializes the lazily-backed pages the instruction touched (`mi_account_step`). With no lazy ranges (lazy
backing comes only from MAP_NORESERVE mappings), materializing changes nothing. `sim_sstep`: a machine step
the bridge gives (`step segs ms = MachineOk ms'`, from Bridge/Step, StepStore) is an `sstep_cfg` step with the
model unchanged, under any spurious-failure configuration.
-/

namespace LPS.Bridge
open NoCompiler LPS.RiscvSemantics

theorem materialize_no_lazy (m : Model) (acc : List (word × Nat)) (h : m_vm_lazy m = []) :
    materialize_model_accesses m acc = some m := by
  have hnew : newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) acc = [] := by
    simp [newly_materialized_pages, h, page_in_ranges]
  simp only [materialize_model_accesses, materialize_accesses, hnew]
  simp only [with_vm_backing, ← h]
  rfl

theorem step_accesses_of_step {segs : List Segment} {ms ms' : machine_state}
    (h : RiscvSemantics.step segs ms = .MachineOk ms') :
    ∃ r, step_accesses segs ms = .MachineOk r ∧ r.access_value = ms' := by
  unfold RiscvSemantics.step drop_access_report at h
  split at h
  · rename_i r hr; exact ⟨r, hr, by cases h; rfl⟩
  · cases h
  · cases h

/-- A bridged machine step is a process step of LPS (`sstep_cfg_instr`), the model unchanged. -/
theorem sim_sstep {segs : List Segment} {cfg : SpuriousCfg} {ms ms' : machine_state} {model : Model}
    (hhalt : m_halted model = none) (hsvc : ms.ms_svc_pending = none) (hlazy : m_vm_lazy model = [])
    (h : RiscvSemantics.step segs ms = .MachineOk ms') :
    sstep_cfg segs cfg (mkCfg ms model) [] (.SNext (mkCfg ms' model)) := by
  obtain ⟨r, hr, hv⟩ := step_accesses_of_step h
  refine .sstep_cfg_instr ms model ms' model hhalt hsvc ?_
  simp only [mi_account_step, hr, materialize_no_lazy model _ hlazy, hv]

end LPS.Bridge

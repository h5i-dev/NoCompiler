import LPS.LinuxProcessSem.State4

/-!
# LPS `theories/LinuxProcessSem/State.v` (f1006fe8), part 5: the lemmas the Sim files use

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/State.v` at f1006fe8: the lemmas of State.v that `Run.v`'s
`mi_account_step_no_lazy` (Run3) and `Common/ExitSim.v` use (State1..State4 port its definitions only).
Same names and statements as State.v; the proofs are Lean's. Rocq's `Hint Rewrite … : model` database is
not reproduced: a proof that wants these rewrites names them.
-/

namespace LPS

theorem m_fs_with_halted : ∀ (v : word) (m : Model), m_fs (with_halted v m) = m_fs m := fun _ _ => rfl

theorem m_halted_with_halted : ∀ (v : word) (m : Model), m_halted (with_halted v m) = some v := fun _ _ => rfl

theorem m_killed_with_halted : ∀ (v : word) (m : Model), m_killed (with_halted v m) = none := fun _ _ => rfl

theorem materialize_model_accesses_no_lazy :
    ∀ m accesses, m_vm_lazy m = [] → materialize_model_accesses m accesses = some m := by
  intro m accesses h
  obtain ⟨fd, ⟨maps, lazy, mat⟩, io, fs, proc, lim, time⟩ := m
  simp only [m_vm_lazy] at h
  subst h
  have hf : ∀ l : List word, List.filter (fun _ => false) l = [] := by
    intro l; induction l <;> simp_all [List.filter]
  simp [materialize_model_accesses, materialize_accesses, newly_materialized_pages, page_in_ranges,
    with_vm_backing, m_vm_lazy, m_vm_materialized, m_vmmaps, hf]

end LPS

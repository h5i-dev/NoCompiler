import LPS.LinuxProcessSem.Run2
import LPS.LinuxProcessSem.State5

/-!
# LPS `theories/LinuxProcessSem/Run.v` (f1006fe8), part 3: the lemmas the Omni and Sim files use

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Run.v` at f1006fe8: the lemmas of Run.v that `OmniRun.v`,
`OmniEquivalence.v`, `SimInv.v` and `ExitSim.v` use (Run1/Run2 port its definitions only). Same names
and statements as Run.v (`nth_error` is `l[i]?`); the proofs are Lean's. Not a complete port of Run.v's
lemmas: only these. `mi_account_step_no_lazy` uses State.v's `materialize_model_accesses_no_lazy` (State5).
-/

namespace LPS
open RiscvSemantics

theorem is_prefix_refl {A : Type} : ∀ (l : List A), is_prefix l l
  | [] => trivial
  | _ :: xs => ⟨rfl, is_prefix_refl xs⟩

theorem is_prefix_nil {A : Type} : ∀ (l : List A), is_prefix [] l
  | [] => trivial
  | _ :: _ => trivial

theorem is_prefix_trans {A : Type} : ∀ (l1 l2 l3 : List A), is_prefix l1 l2 → is_prefix l2 l3 → is_prefix l1 l3
  | [], _, _, _, _ => trivial
  | _ :: _, [], _, h, _ => h.elim
  | _ :: _, _ :: _, [], _, h => h.elim
  | _ :: l1, _ :: l2, _ :: l3, ⟨e1, h1⟩, ⟨e2, h2⟩ => ⟨e1.trans e2, is_prefix_trans l1 l2 l3 h1 h2⟩

theorem is_prefix_app {A : Type} : ∀ (l1 l2 : List A), is_prefix l1 (l1 ++ l2)
  | [], _ => trivial
  | _ :: l1, l2 => ⟨rfl, is_prefix_app l1 l2⟩

theorem star_one (segs : List Segment) : ∀ c evs c', sstep segs c evs (.SNext c') → star segs c evs c' := by
  intro c evs c' h
  have := star.star_step c evs c' [] c' h (star.star_refl c')
  simpa using this

theorem star_trans (segs : List Segment) :
    ∀ c1 t1 c2 t2 c3, star segs c1 t1 c2 → star segs c2 t2 c3 → star segs c1 (t1 ++ t2) c3 := by
  intro c1 t1 c2 t2 c3 h1 h2
  induction h1 with
  | star_refl c => simpa using h2
  | star_step c1 evs c2 tr c3' hss _ ih =>
    rw [List.append_assoc]; exact star.star_step _ _ _ _ _ hss (ih h2)

theorem obs_trace_nil (segs : List Segment) : ∀ c0, obs_trace segs c0 [] :=
  fun c0 => ⟨[], c0, star.star_refl c0, is_prefix_nil _⟩

theorem obs_trace_prefix_closed (segs : List Segment) :
    ∀ c0 tr tr', obs_trace segs c0 tr → is_prefix tr' tr → obs_trace segs c0 tr' := by
  rintro c0 tr tr' ⟨tr'', c, hstar, hp⟩ hp'
  exact ⟨tr'', c, hstar, is_prefix_trans _ _ _ hp' hp⟩

/-- Being uncovered is a special case of erroring (Run.v's `unmodeled_at_sstep_error`). -/
theorem unmodeled_at_sstep_error (segs : List Segment) :
    ∀ c, unmodeled_at segs c → ∃ evs, sstep segs c evs .SError
  | ⟨ms, model⟩, ⟨hh, .inl ⟨hsvc, hstep⟩⟩ => ⟨[], .sstep_instr_unmodeled ms model hh hsvc hstep⟩
  | ⟨ms, model⟩, ⟨hh, .inr ⟨x8, hsvc, hspec⟩⟩ => ⟨[], .sstep_syscall_unmodeled ms model x8 hh hsvc hspec⟩

/-- With no lazy mappings there is nothing to charge: accounting erases completely. -/
theorem mi_account_step_no_lazy (segs : List Segment) :
    ∀ ms model, m_vm_lazy model = [] →
      mi_account_step segs ms model =
        match RiscvSemantics.step segs ms with
        | .MachineOk ms' => .MachineOk (ms', model)
        | .MachineFault => .MachineFault
        | .MachineUnmodeled => .MachineUnmodeled := by
  intro ms model h
  unfold mi_account_step RiscvSemantics.step drop_access_report
  cases step_accesses segs ms <;> simp [materialize_model_accesses_no_lazy _ _ h]

/-- No address in the layout moves: the slack is a suffix. -/
theorem entry_stack_image_block_prefix :
    ∀ ph sp argv envp uid hwcap draw (i : Nat),
      i < (build_stack_bytes ph sp argv envp uid hwcap draw).length →
        (entry_stack_image ph sp argv envp uid hwcap draw)[i]? = (build_stack_bytes ph sp argv envp uid hwcap draw)[i]? := by
  intro ph sp argv envp uid hwcap draw i hi
  simp only [entry_stack_image]
  exact List.getElem?_append_left hi

/-- Inside the block, the image answers exactly as the block does. -/
theorem stack_to_mem_image_in_block :
    ∀ ph (sp : word) argv envp uid hwcap draw (addr : word),
      bv_unsigned addr < entry_block_top sp (build_stack_bytes ph sp argv envp uid hwcap draw) →
        stack_to_mem sp (entry_stack_image ph sp argv envp uid hwcap draw) addr =
          stack_to_mem sp (build_stack_bytes ph sp argv envp uid hwcap draw) addr := by
  intro ph sp argv envp uid hwcap draw addr hlt
  unfold entry_block_top at hlt
  unfold stack_to_mem
  by_cases hle : bv_unsigned sp ≤ bv_unsigned addr
  · have hlen : (build_stack_bytes ph sp argv envp uid hwcap draw).length ≤
        (entry_stack_image ph sp argv envp uid hwcap draw).length := by
      simp [entry_stack_image]
    have h1 : bv_unsigned addr - bv_unsigned sp < ((entry_stack_image ph sp argv envp uid hwcap draw).length : Int) := by
      omega
    have h2 : bv_unsigned addr - bv_unsigned sp < ((build_stack_bytes ph sp argv envp uid hwcap draw).length : Int) := by
      omega
    simp only [hle, ite_true, h1, h2]
    exact entry_stack_image_block_prefix ph sp argv envp uid hwcap draw _ (by omega)
  · simp [hle]

end LPS

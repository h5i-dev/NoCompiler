import LPS.Common.DrainSim1

/-!
# LPS `theories/Common/DrainSim.v` (f1006fe8), part 2: admissibility and exhaustiveness

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/DrainSim.v` at f1006fe8 (image-INDEPENDENT proof library, not the trusted
specification there), DrainSim.v:661-859 of Section `Drain`: one loop iteration `drain_read_step`,
admissibility `drain_star_admits_ok`/`drain_star_admits_err` (every drain trace is realized), and
exhaustiveness `star_drain_only` (every run trace is a drain trace). Conventions as DrainSim1 (namespace
`LPS.DrainSim`; section variables `segs cnt Hcnt f out ec Hec LH H_LH` as leading explicit arguments of
the items that use them, in that order).
-/

namespace LPS
open RiscvSemantics OmniRun InputStream

namespace DrainSim

/-- One loop iteration: deliver block `bs` off the front of the model's input. -/
theorem drain_read_step (segs : List Segment) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max) :
    ∀ bs ms model buf x8 w, M_loop model → ms.ms_svc_pending = some x8 → bv_unsigned x8 = 63 →
      ms_gpr ms 0 = Z_to_bv 64 0 → ms_gpr ms 1 = buf → ms_gpr ms 2 = cnt →
      read_bytes_map (ms_writable_byte segs ms) buf cnt = some w →
      access_okb buf (bv_unsigned cnt) = true →
      1 ≤ (bs.length : Int) → (bs.length : Int) ≤ bv_unsigned cnt →
      (stream_take (m_stdin model) bs.length).1 = bs →
      sstep segs (mkCfg ms model) (bs.map (event.ReadEv (Z_to_bv 64 0)))
        (.SNext (mkCfg (advance_past_svc (apply_effect ms (mkEffect (len_word bs) [(buf, bs)] [])))
          (with_stdin (stream_take (m_stdin model) bs.length).2 model))) := by
  intro bs ms model buf x8 w HM hsvc hno hg0 hg1 hg2 hw haok hlo hhi hpre
  obtain ⟨hfd0, _, hh, hlazy⟩ := HM
  subst hg1
  exact .sstep_syscall ms model x8 _ (with_stdin (stream_take (m_stdin model) bs.length).2 model)
    (with_stdin (stream_take (m_stdin model) bs.length).2 model) _ hh hsvc
    (read0_ok_bytes_cnt segs cnt Hcnt ms x8 model w bs hno hfd0 hg0 hg2 hw haok hlo hhi hpre) (by exact hh)
    (materialize_model_accesses_no_lazy (with_stdin (stream_take (m_stdin model) bs.length).2 model) _
      (by exact hlazy))

section
variable {A : Type} (segs : List Segment) (cnt : word) (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
  (f : A → byte → Option A) (out : A → List byte) (ec : word) (Hec : bv_unsigned ec < 256)
  (LH : A → machine_state → Prop) (H_LH : ∀ a ms, LH a ms → to_rd segs cnt f out ec LH a ms)

include Hcnt H_LH in
theorem drain_star_admits_ok : ∀ s blocks s', chunks cnt s blocks s' →
    ∀ a a' ms model, M_loop model → m_stdin model = s → to_rd segs cnt f out ec LH a ms →
      procs f a blocks.flatten = some a' →
        ∃ c, star segs (mkCfg ms model) (reads blocks ++ out_tail out s' a' (m_fs model)) c := by
  intro s blocks s' HC
  induction HC with
  | chunks_nil s =>
    intro a a' ms model HM Hst Hrd Hp
    cases Hp
    have HM0 := HM
    obtain ⟨hfd0, hfd1, hh, hlazy⟩ := HM0
    cases hs : s.out with
    | none =>
      obtain ⟨msR, ⟨buf, x8, hsvc, hno, hg0, hg1, hg2, ⟨w, hw⟩, haok, hout, hobm, _⟩, hstar0⟩ :=
        to_rd_star segs cnt f out ec LH a ms model hh hlazy Hrd
      subst hg1
      have hsE : sstep segs (mkCfg msR model) []
          (.SNext (mkCfg (advance_past_svc (set_gpr0 msR (Z_to_bv 64 0))) model)) := by
        rw [← apply_effect_no_write msR (Z_to_bv 64 0)]
        refine .sstep_syscall msR model x8 _ model model [] hh hsvc ?_ hh (materialize_model_accesses_no_lazy _ _ hlazy)
        refine read0_ok_eof_cnt segs cnt Hcnt msR x8 model w hno hfd0 ?_ hg0 hg2 hw haok
        rw [Hst]; exact InputStream.eq_IEof_of_out_none _ hs
      obtain ⟨c, hstar2⟩ := to_out_star_admits segs (out a) _ model hfd1 hh hlazy hout hobm
      refine ⟨c, ?_⟩
      have := star_trans segs _ _ _ _ _ hstar0 (star.star_step _ _ _ _ _ hsE hstar2)
      simpa [reads, reads_ch, out_tail, hs] using this
    | some p =>
      refine ⟨mkCfg ms model, ?_⟩
      simpa [reads, reads_ch, out_tail, hs] using star.star_refl (segs := segs) (mkCfg ms model)
  | chunks_cons s bs blocks s'' hlo hhi hpre HC ih =>
    intro a a' ms model HM Hst Hrd Hp
    rw [List.flatten_cons, procs_app] at Hp
    cases hp1 : procs f a bs with
    | none => rw [hp1] at Hp; cases Hp
    | some a1 =>
      rw [hp1] at Hp
      have HM0 := HM
      obtain ⟨_, _, hh, hlazy⟩ := HM0
      obtain ⟨msR, ⟨buf, x8, hsvc, hno, hg0, hg1, hg2, ⟨w, hw⟩, haok, _, _, hbytes⟩, hstar0⟩ :=
        to_rd_star segs cnt f out ec LH a ms model hh hlazy Hrd
      have hcont := hbytes bs hlo hhi
      simp only [hp1] at hcont
      have HM' : M_loop (with_stdin (stream_take s bs.length).2 model) := by
        rw [← Hst]; exact M_loop_take _ _ HM
      have hsR := drain_read_step segs cnt Hcnt bs msR model buf x8 w HM hsvc hno hg0 hg1 hg2 hw haok hlo hhi
        (by rw [Hst]; exact hpre)
      rw [Hst] at hsR
      obtain ⟨msL, hms, hla1⟩ := hcont
      have hrd1 := msteps_to_rd segs cnt f out ec LH a1 _ msL hms (H_LH a1 msL hla1)
      obtain ⟨c, hstar3⟩ := ih a1 a' _ _ HM' rfl hrd1 Hp
      refine ⟨c, ?_⟩
      have := star_trans segs _ _ _ _ _ hstar0 (star.star_step _ _ _ _ _ hsR hstar3)
      simpa [reads_cons, List.append_assoc, m_fs_with_stdin] using this

include Hcnt Hec H_LH in
theorem drain_star_admits_err : ∀ s blocks s1, chunks cnt s blocks s1 →
    ∀ a a' bsE ms model, M_loop model → m_stdin model = s → to_rd segs cnt f out ec LH a ms →
      procs f a blocks.flatten = some a' →
      1 ≤ (bsE.length : Int) → (bsE.length : Int) ≤ bv_unsigned cnt →
      (stream_take s1 bsE.length).1 = bsE → procs f a' bsE = none →
        ∃ c, star segs (mkCfg ms model) (reads (blocks ++ [bsE]) ++ [.ExitEv ec (m_fs model)]) c := by
  intro s blocks s1 HC
  induction HC with
  | chunks_nil s =>
    intro a a' bsE ms model HM Hst Hrd Hp hloE hhiE hpreE hn
    cases Hp
    have HM0 := HM
    obtain ⟨_, _, hh, hlazy⟩ := HM0
    obtain ⟨msR, ⟨buf, x8, hsvc, hno, hg0, hg1, hg2, ⟨w, hw⟩, haok, _, _, hbytes⟩, hstar0⟩ :=
      to_rd_star segs cnt f out ec LH a ms model hh hlazy Hrd
    have hcont := hbytes bsE hloE hhiE
    simp only [hn] at hcont
    have hsR := drain_read_step segs cnt Hcnt bsE msR model buf x8 w HM hsvc hno hg0 hg1 hg2 hw haok hloE hhiE
      (by rw [Hst]; exact hpreE)
    obtain ⟨c, hstar2⟩ := to_exit_star_admits segs ec _ (with_stdin (stream_take (m_stdin model) bsE.length).2 model)
      (by exact hh) (by exact hlazy) hcont
    rw [land_255_small ec Hec] at hstar2
    refine ⟨c, ?_⟩
    have := star_trans segs _ _ _ _ _ hstar0 (star.star_step _ _ _ _ _ hsR hstar2)
    simpa [reads, reads_ch, m_fs_with_stdin] using this
  | chunks_cons s bs blocks s'' hlo hhi hpre HC ih =>
    intro a a' bsE ms model HM Hst Hrd Hp hloE hhiE hpreE hn
    rw [List.flatten_cons, procs_app] at Hp
    cases hp1 : procs f a bs with
    | none => rw [hp1] at Hp; cases Hp
    | some a1 =>
      rw [hp1] at Hp
      have HM0 := HM
      obtain ⟨_, _, hh, hlazy⟩ := HM0
      obtain ⟨msR, ⟨buf, x8, hsvc, hno, hg0, hg1, hg2, ⟨w, hw⟩, haok, _, _, hbytes⟩, hstar0⟩ :=
        to_rd_star segs cnt f out ec LH a ms model hh hlazy Hrd
      have hcont := hbytes bs hlo hhi
      simp only [hp1] at hcont
      have HM' : M_loop (with_stdin (stream_take s bs.length).2 model) := by
        rw [← Hst]; exact M_loop_take _ _ HM
      have hsR := drain_read_step segs cnt Hcnt bs msR model buf x8 w HM hsvc hno hg0 hg1 hg2 hw haok hlo hhi
        (by rw [Hst]; exact hpre)
      rw [Hst] at hsR
      obtain ⟨msL, hms, hla1⟩ := hcont
      have hrd1 := msteps_to_rd segs cnt f out ec LH a1 _ msL hms (H_LH a1 msL hla1)
      obtain ⟨c, hstar3⟩ := ih a1 a' bsE _ _ HM' rfl hrd1 Hp hloE hhiE hpreE hn
      refine ⟨c, ?_⟩
      have := star_trans segs _ _ _ _ _ hstar0 (star.star_step _ _ _ _ _ hsR hstar3)
      simpa [reads_cons, List.append_assoc, m_fs_with_stdin] using this

include Hcnt Hec H_LH in
/-- Exhaustiveness: every run trace is a drain trace. -/
theorem star_drain_only : ∀ c0 tr c', star segs c0 tr c' →
    ∀ a ms model, c0 = mkCfg ms model → M_loop model → to_rd segs cnt f out ec LH a ms →
      drain_from cnt f out ec a (m_fs model) (m_stdin model) tr := by
  intro c0 tr c' hstar
  induction hstar with
  | star_refl c =>
    intro a ms model _ _ _
    exact drain_from_nil cnt f out ec _ _ _
  | star_step c1 evs c2 tr2 c3 hss hstar ih =>
    intro a ms model heq HM hrd
    subst heq
    have HM0 := HM
    obtain ⟨hfd0, hfd1, hh, hlazy⟩ := HM0
    cases hrd with
    | trd_here _ HRP =>
      obtain ⟨buf, x8, hsvc, hno, hg0, hg1, hg2, ⟨w, hw⟩, haok, hout, hobm, hbytes⟩ := HRP
      rcases sstep_read_inv_cnt segs cnt Hcnt ms model buf x8 w evs _ hh hlazy hfd0 hsvc hno hg0 hg1 hg2 hw haok hss
        with ⟨hs, hevs, hc2⟩ | ⟨bs, hlo, hhi, hpre, hevs, hc2⟩
      · cases hc2
        subst hevs
        have hpref := to_out_star_only segs (out a) _ model hfd1 hh hlazy hout hobm tr2 c3 hstar
        rw [hs]
        exact drain_from_out cnt f out ec a _ _ hpref
      · cases hc2
        subst hevs
        have hcont := hbytes bs hlo hhi
        cases hp1 : procs f a bs with
        | some a1 =>
          simp only [hp1] at hcont
          obtain ⟨msL, hms, hla1⟩ := hcont
          have hrd1 := msteps_to_rd segs cnt f out ec LH a1 _ msL hms (H_LH a1 msL hla1)
          exact drain_from_block cnt f out ec a a1 _ _ bs tr2 hlo hhi hpre hp1
            (ih a1 _ _ rfl (M_loop_take bs.length model HM) hrd1)
        | none =>
          simp only [hp1] at hcont
          refine drain_from_err cnt f out ec a _ _ bs tr2 hlo hhi hpre hp1 ?_
          rcases to_exit_star_only segs ec _ (with_stdin (stream_take (m_stdin model) bs.length).2 model)
              (by exact hh) (by exact hlazy) hcont tr2 c3 hstar with h | h
          · subst h; exact is_prefix_nil _
          · subst h; rw [land_255_small ec Hec]; exact is_prefix_refl _
    | trd_step _ ms' hsvc hstep hrd' =>
      obtain ⟨hevs, hc2⟩ := sstep_instr_inv segs ms model ms' evs _ hlazy hsvc hstep hss
      cases hc2
      subst hevs
      exact ih a ms' model rfl HM hrd'

end

end DrainSim
end LPS

import LPS.Common.DrainSim2

/-!
# LPS `theories/Common/DrainSim.v` (f1006fe8), part 3: no error, the packaging, the pair equivalences

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/DrainSim.v` at f1006fe8 (image-INDEPENDENT proof library, not the trusted
specification there), DrainSim.v:860-1117: the rest of Section `Drain` (the phase invariant `dinv` with
`wall_out_dinv_step`, `dinv_step`, `dinv_no_error`, `star_dinv`, `to_rd_no_error`; the packaging
`drain_obs_iff`, `drain_no_error`; the omni reading `to_rd_coexec`, `drain_omni_corun`,
`drain_omni_cosafe`), in namespace `LPS.DrainSim` as in DrainSim1, and the pair equivalences
`drain_omni_strong_equiv`, `drain_strong_equiv` (outside the section, bare names). Section variables
as DrainSim1/2.

Proof difference (not a statement change): DrainSim.v proves `drain_omni_cosafe`'s prefix-closedness
side condition through `drain_obs_iff` and `obs_trace_prefix_closed`; here it is `drain_from_prefix`.
-/

namespace LPS
open RiscvSemantics OmniRun InputStream

namespace DrainSim

/-! ### No error: the phase invariant -/

def dinv {A : Type} (segs : List Segment) (cnt : word) (f : A → byte → Option A) (out : A → List byte)
    (ec : word) (LH : A → machine_state → Prop) (c : config) : Prop :=
  (M_loop c.cfg_model ∧ ∃ a, to_rd segs cnt f out ec LH a c.cfg_ms) ∨
  (fd1chan c.cfg_model ∧ m_halted c.cfg_model = none ∧ m_vm_lazy c.cfg_model = [] ∧
    ∃ rest, buf_modeled rest ∧ to_wall_tail segs (Z_to_bv 64 1) c.cfg_ms rest (to_exit segs (Z_to_bv 64 0))) ∨
  on_path segs (Z_to_bv 64 0) c ∨
  on_path segs ec c

section
variable {A : Type} (segs : List Segment) (cnt : word) (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
  (f : A → byte → Option A) (out : A → List byte) (ec : word) (Hec : bv_unsigned ec < 256)
  (LH : A → machine_state → Prop) (H_LH : ∀ a ms, LH a ms → to_rd segs cnt f out ec LH a ms)

theorem wall_out_dinv_step : ∀ rest ms model evs ms' model', fd1chan model → m_halted model = none →
    m_vm_lazy model = [] → buf_modeled rest →
    to_wall_tail segs (Z_to_bv 64 1) ms rest (to_exit segs (Z_to_bv 64 0)) →
    sstep segs (mkCfg ms model) evs (.SNext (mkCfg ms' model')) →
    dinv segs cnt f out ec LH (mkCfg ms' model') := by
  intro rest ms model evs ms' model' hfd1 hh hlazy hbm ht hss
  have hfdc := fd1chan_fdchan _ hfd1
  cases ht with
  | twt_done _ _ hk => exact .inr (.inr (.inl (on_path_step segs _ (mkCfg ms model) evs _ (.inl ⟨hh, hlazy, hk⟩) hss)))
  | twt_more _ _ _ _ hwl =>
    obtain ⟨n, _, _, _, hc2, ht2⟩ :=
      sstep_to_wall_inv segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 ms rest _ model evs _ hh hlazy hfdc hbm hwl hss
    cases hc2
    exact .inr (.inl ⟨hfd1, hh, hlazy, rest.drop n, buf_modeled_skipn n rest hbm, ht2⟩)
  | twt_step _ msS' _ _ hsvcS hstepS ht' =>
    obtain ⟨_, hc2⟩ := sstep_instr_inv segs ms model msS' evs _ hlazy hsvcS hstepS hss
    cases hc2
    exact .inr (.inl ⟨hfd1, hh, hlazy, rest, hbm, ht'⟩)

include Hcnt H_LH in
theorem dinv_step : ∀ c evs c', dinv segs cnt f out ec LH c → sstep segs c evs (.SNext c') →
    dinv segs cnt f out ec LH c' := by
  rintro ⟨ms, model⟩ evs ⟨ms', model'⟩ hinv hss
  rcases hinv with ⟨HM, a, hrd⟩ | ⟨hfd1, hh, hlazy, rest, hbm, ht⟩ | hop | hop
  · have HM0 := HM
    obtain ⟨hfd0, hfd1, hh, hlazy⟩ := HM0
    cases hrd with
    | trd_here _ HRP =>
      obtain ⟨buf, x8, hsvc, hno, hg0, hg1, hg2, ⟨w, hw⟩, haok, hout, hobm, hbytes⟩ := HRP
      rcases sstep_read_inv_cnt segs cnt Hcnt ms model buf x8 w evs _ hh hlazy hfd0 hsvc hno hg0 hg1 hg2 hw haok hss
        with ⟨_, _, hc2⟩ | ⟨bs, hlo, hhi, _, _, hc2⟩
      · cases hc2
        exact .inr (.inl ⟨hfd1, hh, hlazy, out a, hobm, to_out_wall_tail segs _ _ hout⟩)
      · cases hc2
        have hcont := hbytes bs hlo hhi
        cases hp1 : procs f a bs with
        | some a1 =>
          simp only [hp1] at hcont
          obtain ⟨msL, hms, hla1⟩ := hcont
          exact .inl ⟨M_loop_take _ _ HM, a1, msteps_to_rd segs cnt f out ec LH a1 _ msL hms (H_LH a1 msL hla1)⟩
        | none =>
          simp only [hp1] at hcont
          exact .inr (.inr (.inr (.inl ⟨by exact hh, by exact hlazy, hcont⟩)))
    | trd_step _ ms1 hsvc hstep hrd' =>
      obtain ⟨_, hc2⟩ := sstep_instr_inv segs ms model ms1 evs _ hlazy hsvc hstep hss
      cases hc2
      exact .inl ⟨HM, a, hrd'⟩
  · exact wall_out_dinv_step segs cnt f out ec LH rest ms model evs ms' model' hfd1 hh hlazy hbm ht hss
  · exact .inr (.inr (.inl (on_path_step segs _ _ _ _ hop hss)))
  · exact .inr (.inr (.inr (on_path_step segs _ _ _ _ hop hss)))

include Hcnt in
theorem dinv_no_error : ∀ c evs, dinv segs cnt f out ec LH c → ¬ sstep segs c evs .SError := by
  rintro ⟨ms, model⟩ evs hinv hss
  rcases hinv with ⟨HM, a, hrd⟩ | ⟨hfd1, hh, hlazy, rest, hbm, ht⟩ | hop | hop
  · obtain ⟨hfd0, _, hh, hlazy⟩ := HM
    cases hrd with
    | trd_here _ HRP =>
      obtain ⟨buf, x8, hsvc, hno, hg0, hg1, hg2, ⟨w, hw⟩, haok, _, _, _⟩ := HRP
      rcases sstep_read_inv_cnt segs cnt Hcnt ms model buf x8 w evs _ hh hlazy hfd0 hsvc hno hg0 hg1 hg2 hw haok hss
        with ⟨_, _, hc2⟩ | ⟨_, _, _, _, _, hc2⟩ <;> cases hc2
    | trd_step _ ms1 hsvc hstep _ =>
      exact nomatch (sstep_instr_inv segs ms model ms1 evs _ hlazy hsvc hstep hss).2
  · have hfdc := fd1chan_fdchan _ hfd1
    cases ht with
    | twt_done _ _ hk => exact on_path_no_error segs _ (mkCfg ms model) evs (.inl ⟨hh, hlazy, hk⟩) hss
    | twt_more _ _ _ _ hwl =>
      exact to_wall_no_error_sstep segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 ms rest _ model evs hh hlazy hfdc hbm hwl hss
    | twt_step _ msS' _ _ hsvcS hstepS _ =>
      exact nomatch (sstep_instr_inv segs ms model msS' evs _ hlazy hsvcS hstepS hss).2
  · exact on_path_no_error segs _ _ _ hop hss
  · exact on_path_no_error segs _ _ _ hop hss

include Hcnt H_LH in
theorem star_dinv : ∀ c tr c', dinv segs cnt f out ec LH c → star segs c tr c' → dinv segs cnt f out ec LH c' :=
  star_inv segs (dinv segs cnt f out ec LH) (dinv_step segs cnt Hcnt f out ec LH H_LH)

include Hcnt H_LH in
theorem to_rd_no_error : ∀ a ms model, M_loop model → to_rd segs cnt f out ec LH a ms →
    ¬ reaches_error segs (mkCfg ms model) := by
  intro a ms model HM hrd
  exact inv_no_reaches_error segs (dinv segs cnt f out ec LH) (dinv_step segs cnt Hcnt f out ec LH H_LH)
    (dinv_no_error segs cnt Hcnt f out ec LH) _ (.inl ⟨HM, a, hrd⟩)

/-! ### Whole-run packaging from the initial state -/

include Hcnt Hec H_LH in
theorem drain_obs_iff : ∀ pc ph sp brk0 mb rnd lim inp a0,
    to_rd segs cnt f out ec LH a0 (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) →
    ∀ tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr ↔
      drain_from cnt f out ec a0 (in_fs inp) inp.in_stdin tr := by
  intro pc ph sp brk0 mb rnd lim inp a0 hrd tr
  have HM0 := init_M_loop (segments_reserved segs) brk0 mb sp lim inp
  constructor
  · rintro ⟨tr', c, hstar, hp⟩
    exact drain_from_prefix cnt f out ec a0 _ _ tr' tr
      (star_drain_only segs cnt Hcnt f out ec Hec LH H_LH _ _ _ hstar a0 _ _ rfl HM0 hrd) hp
  · rintro (⟨blocks, s', a', HC, Hp, Hpref⟩ | ⟨blocks, bsE, s', a', HC, Hp, Hn, Hpref⟩)
    · obtain ⟨c, hstar⟩ := drain_star_admits_ok segs cnt Hcnt f out ec LH H_LH _ blocks s' HC a0 a' _ _ HM0 rfl hrd Hp
      exact ⟨_, c, hstar, Hpref⟩
    · obtain ⟨s1, HC1, HC2⟩ := chunks_split cnt blocks [bsE] _ _ HC
      obtain ⟨hloE, hhiE, hpreE, _⟩ := chunks_single_inv cnt _ _ _ HC2
      obtain ⟨c, hstar⟩ := drain_star_admits_err segs cnt Hcnt f out ec Hec LH H_LH _ blocks s1 HC1 a0 a' bsE _ _
        HM0 rfl hrd Hp hloE hhiE hpreE Hn
      exact ⟨_, c, hstar, Hpref⟩

include Hcnt H_LH in
theorem drain_no_error : ∀ pc ph sp brk0 mb rnd lim inp a0,
    to_rd segs cnt f out ec LH a0 (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) →
    ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) := by
  intro pc ph sp brk0 mb rnd lim inp a0 hrd
  exact to_rd_no_error segs cnt Hcnt f out ec LH H_LH a0 _ _ (init_M_loop _ _ _ _ _ _) hrd

/-! ### The omni reading -/

include Hcnt H_LH in
theorem to_rd_coexec : ∀ a ms model, M_loop model → to_rd segs cnt f out ec LH a ms →
    OmniRun.coexec segs (mkCfg ms model) never_errors := by
  intro a ms model HM hrd
  exact inv_coexec segs (dinv segs cnt f out ec LH) (dinv_step segs cnt Hcnt f out ec LH H_LH)
    (dinv_no_error segs cnt Hcnt f out ec LH) _ (.inl ⟨HM, a, hrd⟩)

include Hcnt H_LH in
theorem drain_omni_corun : ∀ pc ph sp brk0 mb rnd lim inp a0,
    to_rd segs cnt f out ec LH a0 (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) →
    omni_corun (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp never_errors := by
  intro pc ph sp brk0 mb rnd lim inp a0 hrd
  exact to_rd_coexec segs cnt Hcnt f out ec LH H_LH a0 _ _ (init_M_loop _ _ _ _ _ _) hrd

include Hcnt Hec H_LH in
theorem drain_omni_cosafe : ∀ pc ph sp brk0 mb rnd lim inp a0,
    to_rd segs cnt f out ec LH a0 (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) →
    omni_cosafe (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
      (drain_from cnt f out ec a0 (in_fs inp) inp.in_stdin) := by
  intro pc ph sp brk0 mb rnd lim inp a0 hrd
  apply (cosafe_obs_iff segs _ _ (fun t t' ht hp => drain_from_prefix cnt f out ec a0 _ _ t t' ht hp)).2
  intro tr hobs
  exact (drain_obs_iff segs cnt Hcnt f out ec Hec LH H_LH pc ph sp brk0 mb rnd lim inp a0 hrd tr).1 hobs

end

end DrainSim

/-! ### Pair equivalence: two drain loops on the same input stream, at the same chunk count -/

/-- The omni equivalence of two drain loops on the same input stream, at the two role budgets. -/
theorem drain_omni_strong_equiv :
    ∀ (A : Type) (cnt : word) (f : A → byte → Option A) (out : A → List byte) (ec : word) (a0 : A)
      source_segs rLH rpc rph rsp rbrk rmb rrnd target_segs aLH apc aph asp abrk amb arnd inp,
      bv_unsigned ec < 256 →
      0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max →
      (∀ a ms, rLH a ms → DrainSim.to_rd source_segs cnt f out ec rLH a ms) →
      (∀ a ms, aLH a ms → DrainSim.to_rd target_segs cnt f out ec aLH a ms) →
      DrainSim.to_rd source_segs cnt f out ec rLH a0
        (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) →
      DrainSim.to_rd target_segs cnt f out ec aLH a0
        (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) →
      omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
        (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp := by
  intro A cnt f out ec a0 source_segs rLH rpc rph rsp rbrk rmb rrnd target_segs aLH apc aph asp abrk amb arnd inp
    Hec Hcnt HrLH HaLH Hr Ha
  refine ⟨?_, .inr ⟨?_, ?_⟩⟩
  · exact coexec_conseq source_segs _ _ _
      (DrainSim.drain_omni_corun source_segs cnt Hcnt f out ec rLH HrLH rpc rph rsp rbrk rmb rrnd source_alloc_limit
        inp a0 Hr)
      (never_errors_covered source_segs)
  · apply (trace_equiv_iff_omni _ _ _ _ _ _ _).1
    intro tr
    exact (DrainSim.drain_obs_iff source_segs cnt Hcnt f out ec Hec rLH HrLH rpc rph rsp rbrk rmb rrnd
        source_alloc_limit inp a0 Hr tr).trans
      (DrainSim.drain_obs_iff target_segs cnt Hcnt f out ec Hec aLH HaLH apc aph asp abrk amb arnd
        target_alloc_limit inp a0 Ha tr).symm
  · exact DrainSim.drain_omni_corun target_segs cnt Hcnt f out ec aLH HaLH apc aph asp abrk amb arnd
      target_alloc_limit inp a0 Ha

theorem drain_strong_equiv :
    ∀ (A : Type) (cnt : word) (f : A → byte → Option A) (out : A → List byte) (ec : word) (a0 : A)
      source_segs rLH rpc rph rsp rbrk rmb rrnd rlim target_segs aLH apc aph asp abrk amb arnd alim inp,
      bv_unsigned ec < 256 →
      0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max →
      (∀ a ms, rLH a ms → DrainSim.to_rd source_segs cnt f out ec rLH a ms) →
      (∀ a ms, aLH a ms → DrainSim.to_rd target_segs cnt f out ec aLH a ms) →
      DrainSim.to_rd source_segs cnt f out ec rLH a0
        (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) →
      DrainSim.to_rd target_segs cnt f out ec aLH a0
        (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) →
      modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp) ∧
        equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
          (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp) := by
  intro A cnt f out ec a0 source_segs rLH rpc rph rsp rbrk rmb rrnd rlim target_segs aLH apc aph asp abrk amb arnd
    alim inp Hec Hcnt HrLH HaLH Hr Ha
  refine ⟨no_error_run_modeled _ _ _ _ _ _ _ _ _
    (DrainSim.drain_no_error source_segs cnt Hcnt f out ec rLH HrLH rpc rph rsp rbrk rmb rrnd rlim inp a0 Hr),
    .inr ⟨?_, ?_⟩⟩
  · intro tr
    exact (DrainSim.drain_obs_iff source_segs cnt Hcnt f out ec Hec rLH HrLH rpc rph rsp rbrk rmb rrnd rlim inp a0
        Hr tr).trans
      (DrainSim.drain_obs_iff target_segs cnt Hcnt f out ec Hec aLH HaLH apc aph asp abrk amb arnd alim inp a0
        Ha tr).symm
  · exact DrainSim.drain_no_error target_segs cnt Hcnt f out ec aLH HaLH apc aph asp abrk amb arnd alim inp a0 Ha

end LPS

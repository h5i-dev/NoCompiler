import LPS.Common.StreamSim2

/-!
# LPS `theories/Common/StreamSim.v` (f1006fe8), part 3: no error, the packaging, the pair equivalences

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/StreamSim.v` at f1006fe8 (image-INDEPENDENT proof library, not the trusted
specification there), StreamSim.v:1041-1283: the rest of `Section Loop` (the phase invariant `sinv`
with `sinv_step`, `sinv_no_error`, `star_sinv`, `to_rd_no_error`; the whole-run packaging
`stream_obs_iff`, `stream_no_error`; the omni reading `to_rd_coexec`, `stream_omni_corun`,
`stream_omni_cosafe`), and the pair equivalences `stream_omni_strong_equiv`, `stream_strong_equiv`.
Section conventions as StreamSim2: `segs LH cnt Hcnt H_LH` are leading explicit arguments of the items
that use them.
-/

namespace LPS
open RiscvSemantics OmniRun InputStream

/-! ### No error: the phase invariant -/

def sinv (segs : List Segment) (LH : machine_state → Prop) (cnt : word) (c : config) : Prop :=
  (M_loop c.cfg_model ∧
    (to_rd segs LH cnt c.cfg_ms ∨
      ∃ bs, 1 ≤ bs.length ∧ buf_modeled bs ∧ to_wall_tail segs (Z_to_bv 64 1) c.cfg_ms bs (lh_next segs LH))) ∨
  on_path segs (Z_to_bv 64 0) c

theorem sinv_step (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms) :
    ∀ c evs c', sinv segs LH cnt c → sstep segs c evs (.SNext c') → sinv segs LH cnt c' := by
  rintro ⟨ms, model⟩ evs c' hinv hss
  rcases hinv with ⟨HM, hphase⟩ | hop
  · have HM0 := HM
    obtain ⟨hfd0, hfd1, hh, hlazy⟩ := HM0
    have hfdc := fd1chan_fdchan _ hfd1
    rcases hphase with hrd | ⟨bs, hnb, hbm, hwt⟩
    · cases hrd with
      | trd_here _ HRP =>
        obtain ⟨buf, x8, hsvc, hno, hg0, hg1, hg2, ⟨w, hw⟩, haok, hex, hbytes⟩ := HRP
        rcases sstep_read_inv cnt Hcnt segs ms model buf x8 w evs _ hh hlazy hfd0 hsvc hno hg0 hg1 hg2 hw haok hss
          with ⟨_, _, hc2⟩ | ⟨bs, hlo, hhi, _, _, hc2⟩
        · cases hc2
          exact .inr (.inl ⟨hh, hlazy, hex⟩)
        · cases hc2
          exact .inl ⟨M_loop_take _ _ HM, .inr ⟨bs, by omega, by unfold buf_modeled; omega,
            to_wr_wall_tail segs LH bs _ (hbytes bs hlo hhi)⟩⟩
      | trd_step _ ms1 hsvc hstep hrd' =>
        obtain ⟨_, hc2⟩ := sstep_instr_inv segs ms model ms1 evs _ hlazy hsvc hstep hss
        cases hc2
        exact .inl ⟨HM, .inl hrd'⟩
    · cases hwt with
      | twt_done => simp at hnb
      | twt_more _ _ _ _ hwl =>
        obtain ⟨n, hn1, hn2, _, hc2, hwt2⟩ :=
          sstep_to_wall_inv segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 ms bs (lh_next segs LH) model evs _
            hh hlazy hfdc hbm hwl hss
        cases hc2
        by_cases hn : n = bs.length
        · subst hn
          rw [List.drop_length] at hwt2
          obtain ⟨msL, hmL, hlhL⟩ := to_wall_tail_nil_msteps segs (Z_to_bv 64 1) _ _ hwt2
          exact .inl ⟨HM, .inl (msteps_to_rd segs LH cnt _ msL hmL (lh_next_to_rd segs LH cnt H_LH msL hlhL))⟩
        · exact .inl ⟨HM, .inr ⟨bs.drop n, by rw [List.length_drop]; omega, buf_modeled_skipn n bs hbm, hwt2⟩⟩
      | twt_step _ msS' _ _ hsvcS hstepS hwt' =>
        obtain ⟨_, hc2⟩ := sstep_instr_inv segs ms model msS' evs _ hlazy hsvcS hstepS hss
        cases hc2
        exact .inl ⟨HM, .inr ⟨bs, hnb, hbm, hwt'⟩⟩
  · exact .inr (on_path_step segs _ _ _ _ hop hss)

theorem sinv_no_error (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max) :
    ∀ c evs, sinv segs LH cnt c → ¬ sstep segs c evs .SError := by
  rintro ⟨ms, model⟩ evs hinv hss
  rcases hinv with ⟨HM, hphase⟩ | hop
  · obtain ⟨hfd0, hfd1, hh, hlazy⟩ := HM
    have hfdc := fd1chan_fdchan _ hfd1
    rcases hphase with hrd | ⟨bs, hnb, hbm, hwt⟩
    · cases hrd with
      | trd_here _ HRP =>
        obtain ⟨buf, x8, hsvc, hno, hg0, hg1, hg2, ⟨w, hw⟩, haok, _, _⟩ := HRP
        rcases sstep_read_inv cnt Hcnt segs ms model buf x8 w evs _ hh hlazy hfd0 hsvc hno hg0 hg1 hg2 hw haok hss
          with ⟨_, _, hc2⟩ | ⟨_, _, _, _, _, hc2⟩ <;> cases hc2
      | trd_step _ ms1 hsvc hstep _ =>
        exact nomatch (sstep_instr_inv segs ms model ms1 evs _ hlazy hsvc hstep hss).2
    · cases hwt with
      | twt_done => simp at hnb
      | twt_more _ _ _ _ hwl =>
        exact to_wall_no_error_sstep segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 ms bs (lh_next segs LH) model evs
          hh hlazy hfdc hbm hwl hss
      | twt_step _ msS' _ _ hsvcS hstepS _ =>
        exact nomatch (sstep_instr_inv segs ms model msS' evs _ hlazy hsvcS hstepS hss).2
  · exact on_path_no_error segs _ _ _ hop hss

theorem star_sinv (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms) :
    ∀ c tr c', sinv segs LH cnt c → star segs c tr c' → sinv segs LH cnt c' :=
  star_inv segs (sinv segs LH cnt) (sinv_step segs LH cnt Hcnt H_LH)

theorem to_rd_no_error (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms) :
    ∀ ms model, M_loop model → to_rd segs LH cnt ms → ¬ reaches_error segs (mkCfg ms model) := by
  intro ms model HM Hrd
  exact inv_no_reaches_error segs (sinv segs LH cnt) (sinv_step segs LH cnt Hcnt H_LH)
    (sinv_no_error segs LH cnt Hcnt) _ (.inl ⟨HM, .inl Hrd⟩)

/-! ### Whole-run packaging from the initial state -/

theorem stream_obs_iff (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms) :
    ∀ pc ph sp brk0 mb rnd lim inp,
      to_rd segs LH cnt (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) →
      ∀ tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr ↔
        stream_traces cnt (in_fs inp) inp.in_stdin tr := by
  intro pc ph sp brk0 mb rnd lim inp Hrd tr
  have HM0 := init_M_loop (segments_reserved segs) brk0 mb sp lim inp
  constructor
  · rintro ⟨tr', c, hstar, hp⟩
    obtain ⟨blocks, s', HC, Hp'⟩ :=
      (star_loop_only segs LH cnt Hcnt H_LH _ _ _ hstar _ _ rfl HM0).1 Hrd
    exact stream_traces_prefix_closed cnt _ _ tr' tr ⟨blocks, s', HC, Hp'⟩ hp
  · rintro ⟨blocks, s', HC, hp⟩
    obtain ⟨c, hstar⟩ := stream_star_admits segs LH cnt Hcnt H_LH _ blocks s' HC _ _ HM0 rfl Hrd
    exact ⟨_, c, hstar, hp⟩

theorem stream_no_error (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms) :
    ∀ pc ph sp brk0 mb rnd lim inp,
      to_rd segs LH cnt (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) →
      ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) := by
  intro pc ph sp brk0 mb rnd lim inp Hrd
  exact to_rd_no_error segs LH cnt Hcnt H_LH _ _ (init_M_loop _ _ _ _ _ _) Hrd

/-! ### The omni reading -/

theorem to_rd_coexec (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms) :
    ∀ ms model, M_loop model → to_rd segs LH cnt ms → OmniRun.coexec segs (mkCfg ms model) never_errors := by
  intro ms model HM Hrd
  exact inv_coexec segs (sinv segs LH cnt) (sinv_step segs LH cnt Hcnt H_LH) (sinv_no_error segs LH cnt Hcnt) _
    (.inl ⟨HM, .inl Hrd⟩)

theorem stream_omni_corun (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms) :
    ∀ pc ph sp brk0 mb rnd lim inp,
      to_rd segs LH cnt (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) →
      omni_corun (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp never_errors := by
  intro pc ph sp brk0 mb rnd lim inp Hrd
  exact to_rd_coexec segs LH cnt Hcnt H_LH _ _ (init_M_loop _ _ _ _ _ _) Hrd

theorem stream_omni_cosafe (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms) :
    ∀ pc ph sp brk0 mb rnd lim inp,
      to_rd segs LH cnt (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) →
      omni_cosafe (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
        (stream_traces cnt (in_fs inp) inp.in_stdin) := by
  intro pc ph sp brk0 mb rnd lim inp Hrd
  apply (cosafe_obs_iff segs _ _ (fun t t' ht hp => stream_traces_prefix_closed cnt _ _ t t' ht hp)).2
  intro tr hobs
  exact (stream_obs_iff segs LH cnt Hcnt H_LH pc ph sp brk0 mb rnd lim inp Hrd tr).1 hobs

/-! ### Pair equivalence: two binaries with the same characterization, on the same input stream -/

/-- The omni equivalence of two stream loops on the same input stream, at the two role budgets. -/
theorem stream_omni_strong_equiv :
    ∀ cnt : word, 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max →
    ∀ source_segs rLH rpc rph rsp rbrk rmb rrnd target_segs aLH apc aph asp abrk amb arnd inp,
      (∀ ms, rLH ms → to_rd source_segs rLH cnt ms) →
      (∀ ms, aLH ms → to_rd target_segs aLH cnt ms) →
      to_rd source_segs rLH cnt
        (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) →
      to_rd target_segs aLH cnt
        (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) →
      omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
        (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp := by
  intro cnt Hcnt source_segs rLH rpc rph rsp rbrk rmb rrnd target_segs aLH apc aph asp abrk amb arnd inp
    HrLH HaLH Hr Ha
  refine ⟨?_, .inr ⟨?_, ?_⟩⟩
  · exact coexec_conseq source_segs _ _ _
      (stream_omni_corun source_segs rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd source_alloc_limit inp Hr)
      (never_errors_covered source_segs)
  · apply (trace_equiv_iff_omni _ _ _ _ _ _ _).1
    intro tr
    exact (stream_obs_iff source_segs rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd source_alloc_limit inp Hr tr).trans
      (stream_obs_iff target_segs aLH cnt Hcnt HaLH apc aph asp abrk amb arnd target_alloc_limit inp Ha tr).symm
  · exact stream_omni_corun target_segs aLH cnt Hcnt HaLH apc aph asp abrk amb arnd target_alloc_limit inp Ha

theorem stream_strong_equiv :
    ∀ cnt : word, 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max →
    ∀ source_segs rLH rpc rph rsp rbrk rmb rrnd rlim target_segs aLH apc aph asp abrk amb arnd alim inp,
      (∀ ms, rLH ms → to_rd source_segs rLH cnt ms) →
      (∀ ms, aLH ms → to_rd target_segs aLH cnt ms) →
      to_rd source_segs rLH cnt
        (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) →
      to_rd target_segs aLH cnt
        (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) →
      modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp) ∧
        equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
          (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp) := by
  intro cnt Hcnt source_segs rLH rpc rph rsp rbrk rmb rrnd rlim target_segs aLH apc aph asp abrk amb arnd alim
    inp HrLH HaLH Hr Ha
  refine ⟨no_error_run_modeled _ _ _ _ _ _ _ _ _
    (stream_no_error source_segs rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd rlim inp Hr), .inr ⟨?_, ?_⟩⟩
  · intro tr
    exact (stream_obs_iff source_segs rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd rlim inp Hr tr).trans
      (stream_obs_iff target_segs aLH cnt Hcnt HaLH apc aph asp abrk amb arnd alim inp Ha tr).symm
  · exact stream_no_error target_segs aLH cnt Hcnt HaLH apc aph asp abrk amb arnd alim inp Ha

end LPS

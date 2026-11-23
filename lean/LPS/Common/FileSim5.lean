import LPS.Common.FileSim4

/-!
# LPS `theories/Common/FileSim.v` (f1006fe8), part 5: the raw-ecall wrappers and the packaging

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/FileSim.v` at f1006fe8 (shared proof library, not the trusted specification
there), FileSim.v:1880-2456: the raw-ecall-record wrappers of `Section OpenNodes` (`record_gpr`,
`tfo_exit_rec`, `tfo_read_rec`, `tfo_write_rec`, `tfo_close_rec`, `tfo_open_enoent_rec`,
`tfo_open_rd_rec`, `tfo_open_wr_rec`, `tfo_open_wr_isdir_rec`, `tfo_open_toolong_rec`), and the run-level
packaging (`fout_omni_run`, `fout_obs_iff`, `fout_no_error_run`, `fout_omni_strong_equiv`,
`fout_strong_equiv`, `spec_err_escape_equiv`). Statements are FileSim.v's; the open wrappers are proved
through FileSim4's `tfo_open_core_spec`/`tfo_sys_char` and FileSim3's characterizations (FileSim.v:
through `tfo_open_core` and the checker reductions, see FileSim4). Rocq's `vm_compute` on a concrete
flag word is `decide`.
-/

namespace LPS
open RiscvSemantics OmniRun InputStream

theorem record_gpr : ∀ regs fr pc sv rv fc mem rom k,
    ms_gpr { ms_regs := regs, ms_fregs := fr, ms_pc_val := pc, ms_svc_pending := sv, ms_resv := rv,
             ms_fcsr := fc, ms_mem := mem, ms_rom := rom } k = reg_get regs (Z_to_bv 5 (10 + (k : Int))) :=
  fun _ _ _ _ _ _ _ _ _ => rfl

section
variable [FPState] (segs : List Segment)

/-- Exit leaf. -/
theorem tfo_exit_rec : ∀ regs pc mem rom model code fsv, bv_unsigned (getr regs 17) = 93 →
    reg_get regs 10 = code → bv_unsigned code < 256 → m_fs model = fsv →
    to_fout segs { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
                   ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom }
      model (fun o => o = (code, fsv)) := by
  intro regs pc mem rom model code fsv H17 H10 hc hfs
  subst hfs
  refine .tfo_exit _ model (getr regs 17) _ rfl (.inl H17) ?_
  intro o
  rw [record_gpr, arg_reg_0, H10, land_255_small code hc]

/-- File read of `cnt` bytes. -/
theorem tfo_read_rec : ∀ regs pc mem rom model fdv p off data buf cnt U, bv_unsigned (getr regs 17) = 63 →
    reg_get regs 10 = fdv → reg_get regs 11 = buf → reg_get regs 12 = cnt →
    fd_lookup (m_fds model) fdv = some (.FdFile p off) → fd32 fdv = fdv → fs_lookup (m_fs model) p = some data →
    wseg_ok segs buf (word_to_nat cnt) = true → bv_unsigned cnt ≤ rw_bytes_max → 0 < bv_unsigned cnt →
    access_okb buf (bv_unsigned cnt) = true → m_halted model = none → m_vm_lazy model = [] →
    to_fout segs
      (mkst (regupd regs 10 (len_word (file_read data off cnt))) (v_addi pc 4)
        (write_to_mem mem buf (file_read data off cnt)) rom)
      (with_fds (fd_insert (m_fds model) fdv (.FdFile p (off + len_word (file_read data off cnt)))) model) U →
    to_fout segs { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
                   ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom } model U := by
  intro regs pc mem rom model fdv p off data buf cnt U H17 H10 H11 H12 hfd hfd32 hfs hwseg hcnt hpos haok hh hlazy hcont
  obtain ⟨w, hw⟩ := wseg_ok_wdef segs buf cnt
    ({ ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
       ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom } : machine_state) hwseg
  refine tfo_read_file segs _ model (getr regs 17) p off data w U rfl H17 ?_ ?_ hfs ?_ ?_ ?_ ?_ hh hlazy ?_ <;>
    simp only [record_gpr, arg_reg_0, arg_reg_1, arg_reg_2, H10, H11, H12]
  · exact hfd
  · exact hfd32
  · exact hw
  · exact hcnt
  · exact hpos
  · exact haok
  · rw [adv_apply_delivered]; exact hcont

/-- File write: deterministic full write of the readable buffer bytes. -/
theorem tfo_write_rec : ∀ regs pc mem model fdv p off data bs buf cnt U, bv_unsigned (getr regs 17) = 64 →
    reg_get regs 10 = fdv → reg_get regs 11 = buf → reg_get regs 12 = cnt →
    fd_lookup (m_fds model) fdv = some (.FdFileW p off) → fd32 fdv = fdv →
    rdn segs mem buf (word_to_nat cnt) = some bs → bv_unsigned cnt ≤ rw_bytes_max →
    fs_lookup (m_fs model) p = some data → (!(modeled_file_gap data off bs)) = false →
    (access_okb buf (bv_unsigned cnt) = true ∨ 0 < bv_unsigned cnt) →
    m_halted model = none → m_vm_lazy model = [] →
    to_fout segs (mkst (regupd regs 10 cnt) (v_addi pc 4) mem (seg_rom segs))
      (with_fds (fd_insert (m_fds model) fdv (.FdFileW p (off + cnt)))
        (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) U →
    to_fout segs { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
                   ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := seg_rom segs } model U := by
  intro regs pc mem model fdv p off data bs buf cnt U H17 H10 H11 H12 hfd hfd32 hrd hcnt hfs hgap hok hh hlazy hcont
  have hrb : read_bytes_map (ms_read_byte
      ({ ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
         ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := seg_rom segs } : machine_state)) buf cnt =
      some bs := by
    rw [read_bytes_map_read_byte, ms_read_bytes_rdn segs _ _ _ rfl]; exact hrd
  cases hz : w_is0 cnt with
  | true =>
    have hokb : access_okb buf (bv_unsigned cnt) = true := by
      rcases hok with h | h
      · exact h
      · rw [w_is0_pos cnt h] at hz; cases hz
    refine tfo_write_file_zero segs _ model (getr regs 17) p off data bs U rfl H17 ?_ ?_ ?_ ?_ hfs hgap ?_ ?_ hh hlazy ?_ <;>
      simp only [record_gpr, arg_reg_0, arg_reg_1, arg_reg_2, H10, H11, H12]
    · exact hfd
    · exact hfd32
    · exact hrb
    · exact hcnt
    · exact hz
    · exact hokb
    · rw [adv_eff_ret]; exact hcont
  | false =>
    refine tfo_write_file segs _ model (getr regs 17) p off data bs U rfl H17 ?_ ?_ ?_ ?_ hfs hgap ?_ hh hlazy ?_ <;>
      simp only [record_gpr, arg_reg_0, arg_reg_1, arg_reg_2, H10, H11, H12]
    · exact hfd
    · exact hfd32
    · exact hrb
    · exact hcnt
    · exact hz
    · rw [adv_eff_ret_copyins]; exact hcont

/-- close: deterministic, removes the fd. -/
theorem tfo_close_rec : ∀ regs pc mem rom model fdv e U, bv_unsigned (getr regs 17) = 57 → reg_get regs 10 = fdv →
    fd_lookup (m_fds model) fdv = some e → fd32 fdv = fdv → m_halted model = none → m_vm_lazy model = [] →
    to_fout segs (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom)
      (with_fds (fd_remove (m_fds model) fdv) model) U →
    to_fout segs { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
                   ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom } model U := by
  intro regs pc mem rom model fdv e U H17 H10 hfd hfd32 hh hlazy hcont
  refine tfo_close segs _ model (getr regs 17) e U rfl H17 ?_ ?_ hh hlazy ?_ <;>
    simp only [record_gpr, arg_reg_0, H10]
  · exact hfd
  · exact hfd32
  · rw [adv_eff_ret]; exact hcont

/-- O_RDONLY openat of an absent file: deterministic -ENOENT. -/
theorem tfo_open_enoent_rec : ∀ regs pc mem model p U, bv_unsigned (getr regs 17) = 56 →
    reg_get regs 10 = AT_FDCWD → reg_get regs 12 = Z_to_bv 64 0 →
    read_cstr (mrb segs mem) (reg_get regs 11) = .CstrOk p → openat_plain_name p = true →
    fs_lookup (m_fs model) p = none → m_halted model = none → m_vm_lazy model = [] →
    to_fout segs (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4) mem (seg_rom segs)) model U →
    to_fout segs { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
                   ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := seg_rom segs } model U := by
  intro regs pc mem model p U H17 H10 H12 hpath hdot hfs hh hlazy hcont
  refine tfo_openat_enoent segs _ model (getr regs 17) p U rfl H17 ?_ ?_ ?_ hdot hfs hh hlazy ?_
  · rw [record_gpr, arg_reg_0]; exact H10
  · rw [record_gpr, arg_reg_1, ms_read_byte_rec_mrb]; exact hpath
  · rw [record_gpr, arg_reg_2, H12]; decide
  · rw [adv_eff_ret_copyins]; exact hcont

/-- O_RDONLY openat of a present file: errno branch or the lowest free fd. -/
theorem tfo_open_rd_rec : ∀ regs pc mem model p d (Te : Int → (word × Fs) → Prop) (Ts : word → (word × Fs) → Prop) U,
    bv_unsigned (getr regs 17) = 56 → reg_get regs 10 = AT_FDCWD → reg_get regs 12 = Z_to_bv 64 0 →
    read_cstr (mrb segs mem) (reg_get regs 11) = .CstrOk p → path_eqb p [] = false → openat_plain_name p = true →
    fs_lookup (m_fs model) p = some d → m_halted model = none → m_vm_lazy model = [] →
    (∀ e, e ∈ openat_errnos →
      to_fout segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs)) model (Te e)) →
    (∀ fd, fd_lookup (m_fds model) fd = none → fd = alloc_fd (m_fds model) →
      to_fout segs (mkst (regupd regs 10 fd) (v_addi pc 4) mem (seg_rom segs))
        (with_fds (fd_insert (m_fds model) fd (.FdFile p (Z_to_bv 64 0))) model) (Ts fd)) →
    (∀ o, U o ↔ ((∃ e, e ∈ openat_errnos ∧ Te e o) ∨
      (∃ fd, fd_lookup (m_fds model) fd = none ∧ fd = alloc_fd (m_fds model) ∧ Ts fd o))) →
    to_fout segs { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
                   ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := seg_rom segs } model U := by
  intro regs pc mem model p d Te Ts U H17 H10 H12 hpath hpe hdot hfs hh hlazy herr hok hU
  refine tfo_open_core_spec segs _ model (fun fd => with_fds (fd_insert (m_fds model) fd (.FdFile p (Z_to_bv 64 0))) model)
    (getr regs 17) _ Te Ts U rfl hh hlazy
    (openat_rd_char segs _ (getr regs 17) model p d H17 (by rw [record_gpr, arg_reg_0]; exact H10)
      (by rw [record_gpr, arg_reg_1, ms_read_byte_rec_mrb]; exact hpath) hpe
      (by rw [record_gpr, arg_reg_2, H12]; decide) hdot hfs)
    (fun _ => ⟨hh, hlazy⟩) ?_ ?_ hU
  · intro e he; rw [adv_eff_ret_copyins]; exact herr e he
  · intro fd hlk hfd; rw [adv_eff_ret_copyins]; exact hok fd hlk hfd

/-- O_WRONLY|O_CREAT|O_TRUNC openat of a plain name nothing lives under: errno branch or create-empty at
    the lowest free fd. -/
theorem tfo_open_wr_rec : ∀ regs pc mem model p (Te : Int → (word × Fs) → Prop) (Ts : word → (word × Fs) → Prop) U,
    bv_unsigned (getr regs 17) = 56 → reg_get regs 10 = AT_FDCWD → reg_get regs 12 = Z_to_bv 64 577 →
    read_cstr (mrb segs mem) (reg_get regs 11) = .CstrOk p → path_eqb p [] = false → openat_plain_name p = true →
    fs_under (m_fs model) p = false → m_halted model = none → m_vm_lazy model = [] →
    (∀ e, e ∈ openat_errnos →
      to_fout segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs)) model (Te e)) →
    (∀ fd, fd_lookup (m_fds model) fd = none → fd = alloc_fd (m_fds model) →
      to_fout segs (mkst (regupd regs 10 fd) (v_addi pc 4) mem (seg_rom segs))
        (with_fds (fd_insert (m_fds model) fd (.FdFileW p (Z_to_bv 64 0))) (with_fs (fs_set (m_fs model) p []) model))
        (Ts fd)) →
    (∀ o, U o ↔ ((∃ e, e ∈ openat_errnos ∧ Te e o) ∨
      (∃ fd, fd_lookup (m_fds model) fd = none ∧ fd = alloc_fd (m_fds model) ∧ Ts fd o))) →
    to_fout segs { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
                   ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := seg_rom segs } model U := by
  intro regs pc mem model p Te Ts U H17 H10 H12 hpath hpe hdot hun hh hlazy herr hok hU
  refine tfo_open_core_spec segs _ model
    (fun fd => with_fds (fd_insert (m_fds model) fd (.FdFileW p (Z_to_bv 64 0))) (with_fs (fs_set (m_fs model) p []) model))
    (getr regs 17) _ Te Ts U rfl hh hlazy
    (openat_wr_char segs _ (getr regs 17) model p H17 (by rw [record_gpr, arg_reg_0]; exact H10)
      (by rw [record_gpr, arg_reg_1, ms_read_byte_rec_mrb]; exact hpath) hpe
      (by rw [record_gpr, arg_reg_2, H12]; decide) hdot hun)
    (fun _ => ⟨hh, hlazy⟩) ?_ ?_ hU
  · intro e he; rw [adv_eff_ret_copyins]; exact herr e he
  · intro fd hlk hfd; rw [adv_eff_ret_copyins]; exact hok fd hlk hfd

/-- O_WRONLY|O_CREAT|O_TRUNC openat of a plain name some key lives under: deterministic -EISDIR. -/
theorem tfo_open_wr_isdir_rec : ∀ regs pc mem model p U, bv_unsigned (getr regs 17) = 56 →
    reg_get regs 10 = AT_FDCWD → reg_get regs 12 = Z_to_bv 64 577 →
    read_cstr (mrb segs mem) (reg_get regs 11) = .CstrOk p → path_eqb p [] = false → openat_plain_name p = true →
    fs_under (m_fs model) p = true → m_halted model = none → m_vm_lazy model = [] →
    to_fout segs (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model U →
    to_fout segs { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
                   ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := seg_rom segs } model U := by
  intro regs pc mem model p U H17 H10 H12 hpath hpe hdot hun hh hlazy hcont
  refine tfo_sys_char segs _ model (getr regs 17) _ model U rfl
    (openat_wr_isdir_char segs _ (getr regs 17) model p H17 (by rw [record_gpr, arg_reg_0]; exact H10)
      (by rw [record_gpr, arg_reg_1, ms_read_byte_rec_mrb]; exact hpath) hpe
      (by rw [record_gpr, arg_reg_2, H12]; decide) hdot hun) hh hlazy ?_
  rw [adv_eff_ret_copyins]; exact hcont

/-- openat on a path with no NUL within PATH_MAX: -ENAMETOOLONG, independent of the dirfd. -/
theorem tfo_open_toolong_rec : ∀ regs pc mem model U, bv_unsigned (getr regs 17) = 56 →
    modeled_open_flags (reg_get regs 12) = true → read_cstr (mrb segs mem) (reg_get regs 11) = .CstrTooLong →
    m_halted model = none → m_vm_lazy model = [] →
    to_fout segs (mkst (regupd regs 10 (errno_ret ENAMETOOLONG)) (v_addi pc 4) mem (seg_rom segs)) model U →
    to_fout segs { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
                   ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := seg_rom segs } model U := by
  intro regs pc mem model U H17 hfl hpath hh hlazy hcont
  refine tfo_openat_toolong segs _ model (getr regs 17) U rfl H17 ?_ ?_ hh hlazy ?_
  · rw [record_gpr, arg_reg_2]; exact hfl
  · rw [record_gpr, arg_reg_1, ms_read_byte_rec_mrb]; exact hpath
  · rw [adv_eff_ret_copyins]; exact hcont

end

/-! ### Run-level packaging and the equivalence glue -/

/-- The run-level omni judgment of a file-copying run. -/
theorem fout_omni_run : ∀ segs pc ph sp brk0 mb rnd lim inp U,
    to_fout segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) U →
    omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (fout_post U) := by
  intro segs pc ph sp brk0 mb rnd lim inp U hto
  exact to_fout_exec segs _ _ U hto rfl rfl

theorem fout_obs_iff : ∀ segs pc ph sp brk0 mb rnd lim inp U,
    to_fout segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) U →
    ∀ tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr ↔ ∃ o, U o ∧ is_prefix tr (fout_trace o) := by
  intro segs pc ph sp brk0 mb rnd lim inp U hto tr
  constructor
  · rintro ⟨tr', c, hstar, hp⟩
    obtain ⟨o, ho, hp'⟩ := to_fout_star_only segs _ _ U hto rfl rfl tr' c hstar
    exact ⟨o, ho, is_prefix_trans _ _ _ hp hp'⟩
  · rintro ⟨o, ho, hp⟩
    obtain ⟨c, hstar⟩ := to_fout_star_admits segs _ _ U hto rfl rfl o ho
    exact ⟨fout_trace o, c, hstar, hp⟩

theorem fout_no_error_run : ∀ segs pc ph sp brk0 mb rnd lim inp U,
    to_fout segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) U →
    ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) := by
  intro segs pc ph sp brk0 mb rnd lim inp U hto
  exact exec_no_error segs _ (exec_conseq segs _ _ _ (fout_omni_run segs pc ph sp brk0 mb rnd lim inp U hto)
    (fun _ _ ⟨_, _, _, hx⟩ => exits_with_never_errors _ _ _ hx))

/-- The omni equivalence for two file-copying binaries with the SAME outcome set `U`, at the two role
    budgets. -/
theorem fout_omni_strong_equiv :
    ∀ source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd U inp,
      to_fout source_segs
        (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp) U →
      to_fout target_segs
        (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp) U →
      omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
        (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp := by
  intro source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd U inp hsource htarget
  refine ⟨?_, .inr ⟨?_, ?_⟩⟩
  · exact coexec_conseq source_segs _ _ _
      (exec_coexec source_segs _ _ (fout_omni_run source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U hsource))
      (fun _ _ ⟨_, _, _, hx⟩ => never_errors_covered source_segs _ _ (exits_with_never_errors _ _ _ hx))
  · apply (trace_equiv_iff_omni _ _ _ _ _ _ _).1
    intro tr
    exact (fout_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U hsource tr).trans
      (fout_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit inp U htarget tr).symm
  · apply (bh_errors_iff _ _ _ _).1
    exact fout_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit inp U htarget

/-- The `Equivalence`-level equivalence for two file-copying binaries with the SAME outcome set `U`. -/
theorem fout_strong_equiv :
    ∀ source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim U inp,
      to_fout source_segs
        (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp) U →
      to_fout target_segs
        (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (init_model (segments_reserved target_segs) abrk amb asp alim inp) U →
      modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp) ∧
        equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
          (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp) := by
  intro source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim U inp hsource htarget
  refine ⟨no_error_run_modeled _ _ _ _ _ _ _ _ _
    (fout_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim inp U hsource), .inr ⟨?_, ?_⟩⟩
  · intro tr
    exact (fout_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp U hsource tr).trans
      (fout_obs_iff target_segs apc aph asp abrk amb arnd alim inp U htarget tr).symm
  · exact fout_no_error_run target_segs apc aph asp abrk amb arnd alim inp U htarget

/-- SOURCE-ERROR ESCAPE at the Equivalence level. -/
theorem spec_err_escape_equiv : ∀ segs pc ph sp brk0 mb rnd lim inp (target : behavior),
    all_traces_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) →
    equiv (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) target := by
  intro segs pc ph sp brk0 mb rnd lim inp target hall
  exact .inl hall

end LPS

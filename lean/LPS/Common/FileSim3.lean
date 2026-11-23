import LPS.Common.FileSim2

/-!
# LPS `theories/Common/FileSim.v` (f1006fe8), part 3: syscall decoding for the file-system surface

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/FileSim.v` at f1006fe8 (shared proof library, not the trusted specification
there), the spec-level part of FileSim.v:1030-1385 ("Syscall decoding through the verified checker"):
`fd_not_error`, `errno_ret_recover`, `ENOMEM_in_openat_errnos`, `openat_errno_range`, `open_copyins`,
`effect_from_copyins_and_clear`; and, in their place for the checker reductions, the Lean-only
characterizations of the openat/close/read/write outcomes this file's nodes need, proved against the
relational spec (`Sys/Fs/Open.v`'s `openat_spec`, `close_spec`; `Sys/Fs/ReadWrite.v`'s `read_spec`,
`write_spec`). Part 4 (FileSim4) has the nodes, part 5 (FileSim5) the wrappers and the packaging.

Not ported (they are statements ABOUT the verified checker `Checks.ExecutableSpecs.check_syscall` and
`Checks.Sys.Fs.Open`'s `check_openat`/`check_open_result`, which are not ported to Lean; see
LPS/Checks/Sys/Fs/ReadWrite1.lean): `check_syscall_56`, `check_syscall_57`, `check_syscall_63`,
`check_syscall_64`, `check_open_result_never_unmodeled`, `check_open_result_ok_iff`, the definition
`check_open_result_copyins` with `check_open_result_copyins_never_unmodeled`,
`check_open_result_copyins_ok_iff`, `check_copyins_after_ret_only`, `openat_rd_check`,
`openat_wr_check`, `openat_wr_isdir_check`, `openat_toolong_check`. Their role (reduce a syscall's
admissible outcomes to a small explicit set) is played here by `syscall_spec_openat`,
`syscall_spec_close`, `open_result_spec_iff`, `create_wronly_iff`, `openat_rd_char`, `openat_wr_char`,
`openat_wr_isdir_char`, `openat_toolong_char`, `openat_enoent_char`, `close_char`, `read_file_char`,
`write_file_char`, `write_file_zero_char` (Lean-only), each an `↔` over all outcomes `o`.

Lean-only helpers besides: the `Sys` combinator lemmas `record_copyins_iff`, `bind_choose_ok_iff`;
`alloc_fd_aux_le`, `alloc_fd_le`, `alloc_fd_not_error_b`, `errno_ret_unsigned`, `errno_ret_error_b`
(these five are lemmas of `Checks/Sys/Prelude.v` and `Checks/Sys/Fs/Open.v`, with their Rocq names and
statements, proved here).
-/

namespace LPS
open RiscvSemantics OmniRun InputStream

/-! ### Errno and fd arithmetic -/

theorem errno_ret_unsigned : ∀ e, 1 ≤ e → e ≤ 4095 → bv_unsigned (errno_ret e) = two_pow_64 - e := by
  intro e h1 h2
  unfold errno_ret Z_to_bv bv_unsigned two_pow_64
  rw [BitVec.toNat_ofInt]
  have h64 : ((2 ^ 64 : Nat) : Int) = 18446744073709551616 := rfl
  have h3 : (-e) % (18446744073709551616 : Int) = 18446744073709551616 - e := by omega
  rw [h64, h3, Int.toNat_of_nonneg (by omega), show (2 : Int) ^ 64 = 18446744073709551616 from rfl]

theorem errno_ret_error_b : ∀ e, 1 ≤ e → e ≤ 4095 → addr_is_error_b (errno_ret e) = true := by
  intro e h1 h2
  unfold addr_is_error_b
  rw [errno_ret_unsigned e h1 h2]
  unfold two_pow_64
  simp only [decide_eq_true_eq]
  omega

/-- An in-range fd is never an error-encoded return. -/
theorem fd_not_error : ∀ fd : word, bv_unsigned fd < 2 ^ 31 → addr_is_error_b fd = false := by
  intro fd h
  unfold addr_is_error_b two_pow_64
  simp only [decide_eq_false_iff_not]
  omega

/-- Recover the errno from an errno-encoded return value. -/
theorem errno_ret_recover : ∀ e, 1 ≤ e → e ≤ 4095 → two_pow_64 - bv_unsigned (errno_ret e) = e := by
  intro e h1 h2
  rw [errno_ret_unsigned e h1 h2]
  omega

theorem ENOMEM_in_openat_errnos : ENOMEM ∈ openat_errnos := by simp [openat_errnos]

theorem openat_errno_range : ∀ e, e ∈ openat_errnos → 1 ≤ e ∧ e ≤ 4095 := by
  intro e h
  simp only [openat_errnos, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem alloc_fd_aux_le : ∀ (fuel : Nat) fds (cand : word), bv_unsigned cand + (fuel : Int) < two_pow_64 →
    bv_unsigned (alloc_fd_aux fds cand fuel) ≤ bv_unsigned cand + (fuel : Int) := by
  intro fuel
  induction fuel with
  | zero => intro fds cand _; simp [alloc_fd_aux]
  | succ fuel ih =>
    intro fds cand hk
    unfold two_pow_64 at hk ih
    simp only [alloc_fd_aux]
    cases fd_lookup fds cand with
    | none => simp only []; omega
    | some _ =>
      simp only []
      have hu : bv_unsigned (cand + 1) = bv_unsigned cand + 1 := by
        unfold bv_unsigned at hk ⊢
        rw [BitVec.toNat_add, show BitVec.toNat (1 : word) = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
        push_cast; rfl
      have := ih fds (cand + 1) (by omega)
      omega

theorem alloc_fd_le : ∀ fds, bv_unsigned (alloc_fd fds) ≤ 4096 := by
  intro fds
  have := alloc_fd_aux_le 4096 fds (Z_to_bv 64 0) (by unfold two_pow_64; decide)
  have h0 : bv_unsigned (Z_to_bv 64 0) = 0 := by decide
  unfold alloc_fd
  omega

theorem alloc_fd_not_error_b : ∀ fds, addr_is_error_b (alloc_fd fds) = false := by
  intro fds
  have := alloc_fd_le fds
  unfold addr_is_error_b two_pow_64
  simp only [decide_eq_false_iff_not]
  omega

/-! ### The pathname copy-in and effect algebra -/

def open_copyins (ms : machine_state) : List (word × Nat) :=
  [(ms_gpr ms 1, cstr_access_len_aux (ms_read_byte ms) (ms_gpr ms 1) path_max)]

theorem effect_from_copyins_and_clear : ∀ eff reads core,
    eff.eff_copyins = reads → clear_copyins eff = core → eff = with_copyins reads core := by
  intro eff reads core h1 h2
  subst h1 h2
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  rfl

/-! ### Lean-only: the `Sys` combinators, unfolded -/

theorem record_copyins_iff (reads : List (word × Nat)) (c : Sys SyscallEffect) (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    record_copyins reads c i m o ↔
      (∃ eff m' evs, c i m (Ok eff m' evs) ∧ o = Ok (with_copyins (reads ++ eff.eff_copyins) eff) m' evs) ∨
      (o = Unmodeled ∧ c i m Unmodeled) := by
  show Sys.bind c _ i m o ↔ _
  cases o with
  | Ok y m2 evs =>
    constructor
    · rintro ⟨x, m1, e1, e2, h1, h2, rfl⟩
      simp only [Sys.pure, outcome.Ok.injEq] at h2
      obtain ⟨rfl, rfl, rfl⟩ := h2
      exact .inl ⟨x, _, _, h1, by simp⟩
    · rintro (⟨eff, m', evs', h, he⟩ | ⟨h, _⟩)
      · simp only [outcome.Ok.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        exact ⟨eff, _, _, [], h, rfl, by simp⟩
      · cases h
  | Unmodeled =>
    constructor
    · rintro (h | ⟨x, m1, e1, _, h2⟩)
      · exact .inr ⟨rfl, h⟩
      · cases h2
    · rintro (⟨_, _, _, _, h⟩ | ⟨_, h⟩)
      · cases h
      · exact .inl h

theorem bind_choose_ok_iff {A : Type} (P : A → Prop) (k : A → Sys SyscallEffect) (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : (choose P >>= k) i m o ↔ ∃ x, P x ∧ k x i m o := bind_choose_iff P k i m o

theorem open_result_spec_iff (m : Model) (mk : word → Model → Model) (i : SyscallInput) (o : outcome SyscallEffect) :
    open_result_spec m mk i m o ↔
      (∃ e, e ∈ openat_errnos ∧ o = Ok (mkEffect (errno_ret e) [] []) m []) ∨
      (∃ fd, (fd_lookup (m_fds m) fd = none ∧ fd = alloc_fd (m_fds m)) ∧ o = Ok (mkEffect fd [] []) (mk fd m) []) := by
  unfold open_result_spec alt errno_from lowest_fd
  rw [bind_choose_iff, bind_choose_iff]
  apply or_congr Iff.rfl
  apply exists_congr; intro fd; apply and_congr_right; intro _
  rw [bind_modify_iff]
  exact Iff.rfl

theorem create_wronly_iff (p : path) (m : Model) (i : SyscallInput) (o : outcome SyscallEffect) :
    create_wronly p m i m o ↔
      (∃ e, e ∈ openat_errnos ∧ o = Ok (mkEffect (errno_ret e) [] []) m []) ∨
      (∃ fd, (fd_lookup (m_fds m) fd = none ∧ fd = alloc_fd (m_fds m)) ∧
        o = Ok (mkEffect fd [] []) (with_fds (fd_insert (m_fds m) fd (.FdFileW p (Z_to_bv 64 0)))
          (with_fs (fs_set (m_fs m) p []) m)) []) := by
  unfold create_wronly alt errno_from lowest_fd
  rw [bind_choose_iff, bind_choose_iff]
  apply or_congr Iff.rfl
  apply exists_congr; intro fd; apply and_congr_right; intro _
  rw [show set_fs (fs_set (m_fs m) p []) = modify (with_fs (fs_set (m_fs m) p [])) from rfl, bind_modify_iff,
    show set_fds (fd_insert (m_fds m) fd (.FdFileW p (Z_to_bv 64 0))) =
      modify (with_fds (fd_insert (m_fds m) fd (.FdFileW p (Z_to_bv 64 0)))) from rfl, bind_modify_iff]
  exact Iff.rfl

/-! ### Lean-only: the arm lookups -/

theorem syscall_spec_openat : ∀ segs ms x8 model o, bv_unsigned x8 = 56 →
    (syscall_spec (sys_input segs ms x8) model o ↔
      openat_spec (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2) (sys_input segs ms x8) model o) := by
  intro segs ms x8 model o hno
  have hl : lookup_arm spec_table (bv_unsigned (sys_input segs ms x8).in_sysno) =
      some (mkSpecArm 56 (fun i => openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)) := by
    rw [in_sysno_sys_input64, hno]; simp [spec_table, lookup_arm, mkSpecArm]
  simp only [syscall_spec, dispatch, hl]
  exact Iff.rfl

theorem syscall_spec_close : ∀ segs ms x8 model o, bv_unsigned x8 = 57 →
    (syscall_spec (sys_input segs ms x8) model o ↔ close_spec (fd32 (ms_gpr ms 0)) (sys_input segs ms x8) model o) := by
  intro segs ms x8 model o hno
  have hl : lookup_arm spec_table (bv_unsigned (sys_input segs ms x8).in_sysno) =
      some (mkSpecArm 57 (fun i => close_spec (fd32 (in_arg i 0)) i)) := by
    rw [in_sysno_sys_input64, hno]; simp [spec_table, lookup_arm, mkSpecArm]
  simp only [syscall_spec, dispatch, hl]
  exact Iff.rfl

/-! ### Lean-only: the outcome characterizations -/

/-- The common prefix of every openat characterization: past the copy-in ledger, the input, the
    model and the flag gate. -/
theorem openat_unfold : ∀ segs ms x8 model o, bv_unsigned x8 = 56 → modeled_open_flags (ms_gpr ms 2) = true →
    (syscall_spec (sys_input segs ms x8) model o ↔
      ((∃ eff m' evs, openat_body_spec (sys_input segs ms x8) model (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
          (sys_input segs ms x8) model (Ok eff m' evs) ∧
          o = Ok (with_copyins (open_copyins ms ++ eff.eff_copyins) eff) m' evs) ∨
        (o = Unmodeled ∧ openat_body_spec (sys_input segs ms x8) model (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
          (sys_input segs ms x8) model Unmodeled))) := by
  intro segs ms x8 model o hno hfl
  rw [syscall_spec_openat _ _ _ _ _ hno]
  unfold openat_spec
  rw [bind_input_iff, record_copyins_iff]
  unfold openat_core_spec open_copyins
  simp only [bind_input_iff, bind_get_model_iff, hfl, Bool.not_true, Bool.false_eq_true, ite_false, in_mem_si]

/-- A ret-only inner effect under the ledger. -/
theorem ledger_ret_iff (reads : List (word × Nat)) (P : outcome SyscallEffect → Prop) (r : word) (m' : Model)
    (hc : ∀ o, P o ↔ o = Ok (mkEffect r [] []) m' []) (o : outcome SyscallEffect) :
    ((∃ eff m'' evs, P (Ok eff m'' evs) ∧ o = Ok (with_copyins (reads ++ eff.eff_copyins) eff) m'' evs) ∨
      (o = Unmodeled ∧ P Unmodeled)) ↔ o = Ok (with_copyins reads (mkEffect r [] [])) m' [] := by
  constructor
  · rintro (⟨eff, m'', evs, h, rfl⟩ | ⟨_, h⟩)
    · have := (hc _).1 h
      simp only [outcome.Ok.injEq] at this
      obtain ⟨rfl, rfl, rfl⟩ := this
      simp [mkEffect, mkEffectU]
    · cases (hc _).1 h
  · intro h
    subst h
    exact .inl ⟨_, _, _, (hc _).2 rfl, by simp [mkEffect, mkEffectU]⟩

theorem openat_toolong_char : ∀ segs ms x8 model, bv_unsigned x8 = 56 → modeled_open_flags (ms_gpr ms 2) = true →
    read_cstr (ms_read_byte ms) (ms_gpr ms 1) = .CstrTooLong →
    ∀ o, syscall_spec (sys_input segs ms x8) model o ↔
      o = Ok (with_copyins (open_copyins ms) (mkEffect (errno_ret ENAMETOOLONG) [] [])) model [] := by
  intro segs ms x8 model hno hfl hpath o
  rw [openat_unfold _ _ _ _ _ hno hfl]
  apply ledger_ret_iff _ _ _ model
  intro o'
  simp only [openat_body_spec, in_mem_si, hpath]
  exact Iff.rfl

theorem openat_enoent_char : ∀ segs ms x8 model p, bv_unsigned x8 = 56 → ms_gpr ms 0 = AT_FDCWD →
    read_cstr (ms_read_byte ms) (ms_gpr ms 1) = .CstrOk p →
    Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0 → openat_plain_name p = true →
    fs_lookup (m_fs model) p = none →
    ∀ o, syscall_spec (sys_input segs ms x8) model o ↔
      o = Ok (with_copyins (open_copyins ms) (mkEffect (errno_ret ENOENT) [] [])) model [] := by
  intro segs ms x8 model p hno hdirfd hpath hfl hdot hfs o
  have hunw := openat_plain_name_noslash _ hdot
  have hndr := openat_plain_name_nodirref _ hdot
  rw [openat_unfold _ _ _ _ _ hno (modeled_open_flags_rd _ hfl)]
  apply ledger_ret_iff _ _ _ model
  intro o'
  simp only [openat_body_spec, in_mem_si, hpath]
  cases hpe : path_eqb p []
  · simp only [Bool.false_eq_true, ite_false, hdirfd, show bv_eqb (fd32 AT_FDCWD) AT_FDCWD32 = true from
      (bv_eqb_eq _ _).2 rfl, Bool.not_true]
    simp only [openat_resolved_spec, hunw, hfl, openat_read_spec, hndr, hfs, Bool.false_eq_true, ite_false,
      beq_self_eq_true, ite_true]
    exact Iff.rfl
  · exact Iff.rfl

/-- An open-result inner shape under the ledger. -/
theorem ledger_open_iff (reads : List (word × Nat)) (P : outcome SyscallEffect → Prop) (m : Model)
    (mk : word → Model)
    (hc : ∀ o, P o ↔ (∃ e, e ∈ openat_errnos ∧ o = Ok (mkEffect (errno_ret e) [] []) m []) ∨
      (∃ fd, (fd_lookup (m_fds m) fd = none ∧ fd = alloc_fd (m_fds m)) ∧ o = Ok (mkEffect fd [] []) (mk fd) []))
    (o : outcome SyscallEffect) :
    ((∃ eff m'' evs, P (Ok eff m'' evs) ∧ o = Ok (with_copyins (reads ++ eff.eff_copyins) eff) m'' evs) ∨
      (o = Unmodeled ∧ P Unmodeled)) ↔
    ((∃ e, e ∈ openat_errnos ∧ o = Ok (with_copyins reads (mkEffect (errno_ret e) [] [])) m []) ∨
      (∃ fd, (fd_lookup (m_fds m) fd = none ∧ fd = alloc_fd (m_fds m)) ∧
        o = Ok (with_copyins reads (mkEffect fd [] [])) (mk fd) [])) := by
  constructor
  · rintro (⟨eff, m'', evs, h, rfl⟩ | ⟨_, h⟩)
    · rcases (hc _).1 h with ⟨e, he, hq⟩ | ⟨fd, hfd, hq⟩
      · simp only [outcome.Ok.injEq] at hq
        obtain ⟨rfl, rfl, rfl⟩ := hq
        exact .inl ⟨e, he, by simp [mkEffect, mkEffectU]⟩
      · simp only [outcome.Ok.injEq] at hq
        obtain ⟨rfl, rfl, rfl⟩ := hq
        exact .inr ⟨fd, hfd, by simp [mkEffect, mkEffectU]⟩
    · rcases (hc _).1 h with ⟨_, _, hq⟩ | ⟨_, _, hq⟩ <;> cases hq
  · rintro (⟨e, he, rfl⟩ | ⟨fd, hfd, rfl⟩)
    · exact .inl ⟨_, _, _, (hc _).2 (.inl ⟨e, he, rfl⟩), by simp [mkEffect, mkEffectU]⟩
    · exact .inl ⟨_, _, _, (hc _).2 (.inr ⟨fd, hfd, rfl⟩), by simp [mkEffect, mkEffectU]⟩

theorem fd32_AT_FDCWD_eqb : bv_eqb (fd32 AT_FDCWD) AT_FDCWD32 = true := (bv_eqb_eq _ _).2 rfl

theorem wr_create_flags_ne0 : (wr_create_flags == 0) = false := by decide

/-- The O_RDONLY open of a present plain name: an errno, or the lowest free fd on the file. -/
theorem openat_rd_char : ∀ segs ms x8 model p d, bv_unsigned x8 = 56 → ms_gpr ms 0 = AT_FDCWD →
    read_cstr (ms_read_byte ms) (ms_gpr ms 1) = .CstrOk p → path_eqb p [] = false →
    Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0 → openat_plain_name p = true →
    fs_lookup (m_fs model) p = some d →
    ∀ o, syscall_spec (sys_input segs ms x8) model o ↔
      ((∃ e, e ∈ openat_errnos ∧ o = Ok (with_copyins (open_copyins ms) (mkEffect (errno_ret e) [] [])) model []) ∨
        (∃ fd, (fd_lookup (m_fds model) fd = none ∧ fd = alloc_fd (m_fds model)) ∧
          o = Ok (with_copyins (open_copyins ms) (mkEffect fd [] []))
            (with_fds (fd_insert (m_fds model) fd (.FdFile p (Z_to_bv 64 0))) model) [])) := by
  intro segs ms x8 model p d hno hdirfd hpath hpe hfl hdot hfs o
  have hunw := openat_plain_name_noslash _ hdot
  have hndr := openat_plain_name_nodirref _ hdot
  rw [openat_unfold _ _ _ _ _ hno (modeled_open_flags_rd _ hfl)]
  apply ledger_open_iff _ _ model (fun fd => with_fds (fd_insert (m_fds model) fd (.FdFile p (Z_to_bv 64 0))) model)
  intro o'
  simp only [openat_body_spec, in_mem_si, hpath, hpe, hdirfd, fd32_AT_FDCWD_eqb, Bool.not_true,
    Bool.false_eq_true, ite_false]
  simp only [openat_resolved_spec, hunw, hfl, openat_read_spec, hndr, hfs, Bool.false_eq_true, ite_false,
    beq_self_eq_true, ite_true]
  exact open_result_spec_iff model _ _ o'

/-- The write-create open of a plain name nothing lives under: an errno, or create-empty at the lowest
    free fd. -/
theorem openat_wr_char : ∀ segs ms x8 model p, bv_unsigned x8 = 56 → ms_gpr ms 0 = AT_FDCWD →
    read_cstr (ms_read_byte ms) (ms_gpr ms 1) = .CstrOk p → path_eqb p [] = false →
    Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = wr_create_flags → openat_plain_name p = true →
    fs_under (m_fs model) p = false →
    ∀ o, syscall_spec (sys_input segs ms x8) model o ↔
      ((∃ e, e ∈ openat_errnos ∧ o = Ok (with_copyins (open_copyins ms) (mkEffect (errno_ret e) [] [])) model []) ∨
        (∃ fd, (fd_lookup (m_fds model) fd = none ∧ fd = alloc_fd (m_fds model)) ∧
          o = Ok (with_copyins (open_copyins ms) (mkEffect fd [] []))
            (with_fds (fd_insert (m_fds model) fd (.FdFileW p (Z_to_bv 64 0))) (with_fs (fs_set (m_fs model) p []) model))
            [])) := by
  intro segs ms x8 model p hno hdirfd hpath hpe hfl hdot hun o
  have hunw := openat_plain_name_noslash _ hdot
  have hndr := openat_plain_name_nodirref _ hdot
  rw [openat_unfold _ _ _ _ _ hno (modeled_open_flags_wr _ hfl)]
  apply ledger_open_iff _ _ model
  intro o'
  simp only [openat_body_spec, in_mem_si, hpath, hpe, hdirfd, fd32_AT_FDCWD_eqb, Bool.not_true,
    Bool.false_eq_true, ite_false]
  simp only [openat_resolved_spec, hunw, hfl, wr_create_flags_ne0, beq_self_eq_true, openat_create_spec, hndr, hun,
    Bool.or_false, Bool.false_eq_true, ite_false, ite_true]
  exact create_wronly_iff p model _ o'

/-- The write-create open of a plain name some key lives under: deterministic -EISDIR. -/
theorem openat_wr_isdir_char : ∀ segs ms x8 model p, bv_unsigned x8 = 56 → ms_gpr ms 0 = AT_FDCWD →
    read_cstr (ms_read_byte ms) (ms_gpr ms 1) = .CstrOk p → path_eqb p [] = false →
    Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = wr_create_flags → openat_plain_name p = true →
    fs_under (m_fs model) p = true →
    ∀ o, syscall_spec (sys_input segs ms x8) model o ↔
      o = Ok (with_copyins (open_copyins ms) (mkEffect (errno_ret EISDIR) [] [])) model [] := by
  intro segs ms x8 model p hno hdirfd hpath hpe hfl hdot hun o
  have hunw := openat_plain_name_noslash _ hdot
  have hndr := openat_plain_name_nodirref _ hdot
  rw [openat_unfold _ _ _ _ _ hno (modeled_open_flags_wr _ hfl)]
  apply ledger_ret_iff _ _ _ model
  intro o'
  simp only [openat_body_spec, in_mem_si, hpath, hpe, hdirfd, fd32_AT_FDCWD_eqb, Bool.not_true,
    Bool.false_eq_true, ite_false]
  simp only [openat_resolved_spec, hunw, hfl, wr_create_flags_ne0, beq_self_eq_true, openat_create_spec, hndr, hun,
    Bool.or_true, Bool.false_eq_true, ite_false, ite_true]
  exact Iff.rfl

/-- close of an open fd: deterministic, removes the fd. -/
theorem close_char : ∀ segs ms x8 model e, bv_unsigned x8 = 57 → fd_lookup (m_fds model) (ms_gpr ms 0) = some e →
    fd32 (ms_gpr ms 0) = ms_gpr ms 0 →
    ∀ o, syscall_spec (sys_input segs ms x8) model o ↔
      o = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_fds (fd_remove (m_fds model) (ms_gpr ms 0)) model) [] := by
  intro segs ms x8 model e hno hfd hfd32 o
  rw [syscall_spec_close _ _ _ _ _ hno, hfd32]
  unfold close_spec
  rw [bind_get_model_iff]
  simp only [hfd]
  rw [show set_fds (fd_remove (m_fds model) (ms_gpr ms 0)) = modify (with_fds (fd_remove (m_fds model) (ms_gpr ms 0)))
    from rfl, bind_modify_iff]
  exact Iff.rfl

/-- File read of `count` bytes on an `FdFile`: deterministic. -/
theorem read_file_char : ∀ segs ms x8 model p off data w, bv_unsigned x8 = 63 →
    fd_lookup (m_fds model) (ms_gpr ms 0) = some (.FdFile p off) → fd32 (ms_gpr ms 0) = ms_gpr ms 0 →
    fs_lookup (m_fs model) p = some data →
    read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) (ms_gpr ms 2) = some w →
    bv_unsigned (ms_gpr ms 2) ≤ rw_bytes_max →
    access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true →
    ∀ o, syscall_spec (sys_input segs ms x8) model o ↔
      o = Ok (mkEffect (len_word (file_read data off (ms_gpr ms 2)))
                (delivered_writes (ms_gpr ms 1) (file_read data off (ms_gpr ms 2))) [])
            (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
              (.FdFile p (off + len_word (file_read data off (ms_gpr ms 2))))) model) [] := by
  intro segs ms x8 model p off data w hno hfd hfd32 hfs hw hcnt haok o
  have hl : bv_unsigned (len_word (file_read data off (ms_gpr ms 2))) ≤ bv_unsigned (ms_gpr ms 2) := by
    have hlen := length_file_read data off (ms_gpr ms 2)
    have hr := u64_range (ms_gpr ms 2)
    have h1 : (file_read data off (ms_gpr ms 2)).length ≤ word_to_nat (ms_gpr ms 2) := by
      rw [hlen]; exact Nat.min_le_left _ _
    have h2 : (word_to_nat (ms_gpr ms 2) : Int) = bv_unsigned (ms_gpr ms 2) := by unfold word_to_nat; omega
    rw [len_word_unsigned _ (by unfold two_pow_64; omega)]
    omega
  have hwb := read_bytes_map_prefix _ _ _ _ _ hl hw
  have hcl : Z_to_bv 64 (rw_count_clamp (ms_gpr ms 2)) = ms_gpr ms 2 := by
    rw [rw_count_clamp_of_rw _ hcnt, Z_to_bv_bv_unsigned]
  rw [syscall_spec_read _ _ _ _ _ hno, hfd32]
  unfold read_spec
  rw [bind_input_iff, bind_get_model_iff]
  simp only [hfd, haok, hfs, hcl, Bool.not_true, Bool.false_eq_true, ite_false, in_wmem_si, hwb]
  rw [show set_fds (fd_insert (m_fds model) (ms_gpr ms 0) (.FdFile p (off + len_word (file_read data off (ms_gpr ms 2))))) =
      modify (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
        (.FdFile p (off + len_word (file_read data off (ms_gpr ms 2)))))) from rfl, bind_modify_iff]
  exact Iff.rfl

/-- The facts the two file-write characterizations share (Lean-only helper). -/
private theorem write_file_setup (segs : List Segment) (ms : machine_state) (x8 : word) (bs : List byte)
    (hrd : read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = some bs)
    (hcnt : bv_unsigned (ms_gpr ms 2) ≤ rw_bytes_max) :
    write_source (sys_input segs ms x8).in_mem (ms_gpr ms 1) (ms_gpr ms 2) = bs ∧ len_word bs = ms_gpr ms 2 := by
  have hrb : read_bytes_map (sys_input segs ms x8).in_mem (ms_gpr ms 1) (ms_gpr ms 2) = some bs := hrd
  refine ⟨by rw [write_source_of_rw _ _ _ hcnt, readable_bytes_full _ _ _ _ hrb], ?_⟩
  have hlen := read_bytes_map_length _ _ _ _ hrb
  unfold len_word
  rw [hlen, Z_to_bv_bv_unsigned]

/-- File write of a positive count on an `FdFileW`: deterministic full write. -/
theorem write_file_char : ∀ segs ms x8 model p off data bs, bv_unsigned x8 = 64 →
    fd_lookup (m_fds model) (ms_gpr ms 0) = some (.FdFileW p off) → fd32 (ms_gpr ms 0) = ms_gpr ms 0 →
    read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = some bs →
    bv_unsigned (ms_gpr ms 2) ≤ rw_bytes_max → fs_lookup (m_fs model) p = some data →
    (!(modeled_file_gap data off bs)) = false → w_is0 (ms_gpr ms 2) = false →
    ∀ o, syscall_spec (sys_input segs ms x8) model o ↔
      o = Ok (with_copyins [(ms_gpr ms 1, bs.length)] (mkEffect (ms_gpr ms 2) [] []))
            (with_fds (fd_insert (m_fds model) (ms_gpr ms 0) (.FdFileW p (off + ms_gpr ms 2)))
              (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) [] := by
  intro segs ms x8 model p off data bs hno hfd hfd32 hrd hcnt hfs hgap hnz o
  obtain ⟨hws, hret⟩ := write_file_setup segs ms x8 bs hrd hcnt
  have hgate : (bs.length == 0) = false := by
    have hlen := read_bytes_map_length _ _ _ _ hrd
    have := w_is0_false_pos _ hnz
    cases h : bs.length with
    | zero => rw [h] at hlen; simp at hlen; omega
    | succ n => simp
  rw [syscall_spec_write _ _ _ _ _ hno, hfd32]
  unfold write_spec
  rw [bind_input_iff, bind_get_model_iff]
  simp only [hfd, write_range_gate, rw_range_in_range _ _ hcnt, Bool.false_eq_true, ite_false, write_file_tail,
    hws, hgate, hfs, hgap, hnz, write_ledger, Bool.not_false, Bool.true_and]
  rw [show set_fs (fs_set (m_fs model) p (file_write data off bs)) =
      modify (with_fs (fs_set (m_fs model) p (file_write data off bs))) from rfl, bind_modify_iff,
    show set_fds (fd_insert (m_fds model) (ms_gpr ms 0) (.FdFileW p (off + len_word bs))) =
      modify (with_fds (fd_insert (m_fds model) (ms_gpr ms 0) (.FdFileW p (off + len_word bs)))) from rfl,
    bind_modify_iff, record_copyins_ret_only, hret]

/-- The `count = 0` half: no user byte is read, no copy-in range, `access_ok`'s verdict is all. -/
theorem write_file_zero_char : ∀ segs ms x8 model p off data bs, bv_unsigned x8 = 64 →
    fd_lookup (m_fds model) (ms_gpr ms 0) = some (.FdFileW p off) → fd32 (ms_gpr ms 0) = ms_gpr ms 0 →
    read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = some bs →
    bv_unsigned (ms_gpr ms 2) ≤ rw_bytes_max → fs_lookup (m_fs model) p = some data →
    (!(modeled_file_gap data off bs)) = false → w_is0 (ms_gpr ms 2) = true →
    access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true →
    ∀ o, syscall_spec (sys_input segs ms x8) model o ↔
      o = Ok (mkEffect (ms_gpr ms 2) [] [])
            (with_fds (fd_insert (m_fds model) (ms_gpr ms 0) (.FdFileW p (off + ms_gpr ms 2)))
              (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) [] := by
  intro segs ms x8 model p off data bs hno hfd hfd32 hrd hcnt hfs hgap hz hok o
  obtain ⟨hws, hret⟩ := write_file_setup segs ms x8 bs hrd hcnt
  rw [syscall_spec_write _ _ _ _ _ hno, hfd32]
  unfold write_spec
  rw [bind_input_iff, bind_get_model_iff]
  simp only [hfd, write_range_gate, rw_range_in_range _ _ hcnt, Bool.false_eq_true, ite_false, write_file_tail,
    hws, hz, Bool.not_true, Bool.false_and, hfs, hgap, write_ledger, ite_true, access_ok_zero, hok]
  rw [show set_fs (fs_set (m_fs model) p (file_write data off bs)) =
      modify (with_fs (fs_set (m_fs model) p (file_write data off bs))) from rfl, bind_modify_iff,
    show set_fds (fd_insert (m_fds model) (ms_gpr ms 0) (.FdFileW p (off + len_word bs))) =
      modify (with_fds (fd_insert (m_fds model) (ms_gpr ms 0) (.FdFileW p (off + len_word bs)))) from rfl,
    bind_modify_iff, hret]
  exact Iff.rfl

end LPS

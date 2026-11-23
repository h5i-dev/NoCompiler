import LPS.Common.FileSim3

/-!
# LPS `theories/Common/FileSim.v` (f1006fe8), part 4: the syscall nodes

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/FileSim.v` at f1006fe8 (shared proof library, not the trusted specification
there), FileSim.v:1386-1880, the first half of `Section OpenNodes`: the `to_fout` nodes
`tfo_openat_toolong`, `tfo_openat_enoent`, `tfo_read_file`, `tfo_write_file`, `tfo_write_file_zero`,
`tfo_close`. Part 5 (FileSim5) has the raw-ecall wrappers and the run-level packaging.

Section `OpenNodes`' variable `segs` is the leading explicit argument; `Context {fx : FPState}` an
instance argument of the items naming `fp_regs`/`fp_csr`.

What changed and why: FileSim.v proves the nodes through the verified checker
(`check_syscall_ok_iff`, `check_syscall_complete_unmodeled` and the `openat_*_check`/`check_syscall_6x`
reductions), which is not ported; here every node is proved from the Lean-only outcome
characterizations of FileSim3 (`openat_toolong_char` .. `write_file_zero_char`), through the Lean-only
`tfo_sys_char` (a syscall whose admissible outcomes are exactly one) and `tfo_open_core_spec`. The
latter replaces FileSim.v's `tfo_open_core`, whose checker hypothesis
`∀ eff, check_syscall .. eff model = check_open_result_copyins reads eff model mk` is stated here as
the equivalent outcome set of the relational spec; `tfo_open_core` and `open_ok_fd` (whose statements
mention `check_syscall`) are therefore not ported. All other statements are FileSim.v's.
-/

namespace LPS
open RiscvSemantics OmniRun InputStream

section
variable (segs : List Segment)

/-- A syscall whose admissible outcomes are exactly one, silent, non-halting (Lean-only helper). -/
theorem tfo_sys_char : ∀ ms model x8 eff model' U, ms.ms_svc_pending = some x8 →
    (∀ o, syscall_spec (sys_input segs ms x8) model o ↔ o = Ok eff model' []) →
    m_halted model' = none → m_vm_lazy model' = [] →
    to_fout segs (advance_past_svc (apply_effect ms eff)) model' U → to_fout segs ms model U := by
  intro ms model x8 eff model' U hsvc hchar hh' hlazy' hcont
  refine tfo_sys_det segs ms model x8 eff model' U hsvc ((hchar _).2 rfl) ?_ ?_ hh' hlazy' hcont
  · intro eff2 m2 evs2 hs
    have := (hchar _).1 hs
    simp only [outcome.Ok.injEq] at this
    exact this
  · intro hs
    cases (hchar _).1 hs

/-- The continuation outcome sets of an open, by the returned value (Lean-only helper). -/
def open_T (Te : Int → (word × Fs) → Prop) (Ts : word → (word × Fs) → Prop) (eff : SyscallEffect) (_ : Model) :
    (word × Fs) → Prop :=
  if addr_is_error_b eff.eff_ret then Te (two_pow_64 - bv_unsigned eff.eff_ret) else Ts eff.eff_ret

theorem open_T_err (Te : Int → (word × Fs) → Prop) (Ts : word → (word × Fs) → Prop) (reads : List (word × Nat))
    (m : Model) (e : Int) (he : e ∈ openat_errnos) :
    open_T Te Ts (with_copyins reads (mkEffect (errno_ret e) [] [])) m = Te e := by
  obtain ⟨h1, h2⟩ := openat_errno_range e he
  have : (with_copyins reads (mkEffect (errno_ret e) [] [])).eff_ret = errno_ret e := rfl
  unfold open_T
  rw [this, errno_ret_error_b e h1 h2, if_pos rfl, errno_ret_recover e h1 h2]

theorem open_T_ok (Te : Int → (word × Fs) → Prop) (Ts : word → (word × Fs) → Prop) (reads : List (word × Nat))
    (m : Model) (fds : List (word × FdEntry)) (fd : word) (hfd : fd = alloc_fd fds) :
    open_T Te Ts (with_copyins reads (mkEffect fd [] [])) m = Ts fd := by
  have : (with_copyins reads (mkEffect fd [] [])).eff_ret = fd := rfl
  unfold open_T
  rw [this, hfd, alloc_fd_not_error_b, if_neg (by simp)]

/-- The core open node over a success-model builder `mk`, its admissible outcomes given as a set
    (Lean-only; FileSim.v's `tfo_open_core` with its checker hypothesis read through the spec). -/
theorem tfo_open_core_spec : ∀ ms model (mk : word → Model) x8 reads
    (Te : Int → (word × Fs) → Prop) (Ts : word → (word × Fs) → Prop) U,
    ms.ms_svc_pending = some x8 → m_halted model = none → m_vm_lazy model = [] →
    (∀ o, syscall_spec (sys_input segs ms x8) model o ↔
      ((∃ e, e ∈ openat_errnos ∧ o = Ok (with_copyins reads (mkEffect (errno_ret e) [] [])) model []) ∨
        (∃ fd, (fd_lookup (m_fds model) fd = none ∧ fd = alloc_fd (m_fds model)) ∧
          o = Ok (with_copyins reads (mkEffect fd [] [])) (mk fd) []))) →
    (∀ fd, m_halted (mk fd) = none ∧ m_vm_lazy (mk fd) = []) →
    (∀ e, e ∈ openat_errnos →
      to_fout segs (advance_past_svc (apply_effect ms (with_copyins reads (mkEffect (errno_ret e) [] [])))) model (Te e)) →
    (∀ fd, fd_lookup (m_fds model) fd = none → fd = alloc_fd (m_fds model) →
      to_fout segs (advance_past_svc (apply_effect ms (with_copyins reads (mkEffect fd [] [])))) (mk fd) (Ts fd)) →
    (∀ o, U o ↔ ((∃ e, e ∈ openat_errnos ∧ Te e o) ∨
      (∃ fd, fd_lookup (m_fds model) fd = none ∧ fd = alloc_fd (m_fds model) ∧ Ts fd o))) →
    to_fout segs ms model U := by
  intro ms model mk x8 reads Te Ts U hsvc hh hlazy hchar hmk herr hok hU
  refine .tfo_sys ms model x8 (open_T Te Ts) U hsvc ?_ ?_ ?_ ?_ ?_
  · intro hs
    rcases (hchar _).1 hs with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h
  · exact ⟨_, _, _, (hchar _).2 (.inl ⟨ENOMEM, ENOMEM_in_openat_errnos, rfl⟩)⟩
  · intro eff model' evs hs
    rcases (hchar _).1 hs with ⟨e, _, h⟩ | ⟨fd, _, h⟩ <;> simp only [outcome.Ok.injEq] at h <;>
      obtain ⟨rfl, rfl, rfl⟩ := h
    · exact ⟨rfl, hh, hlazy⟩
    · exact ⟨rfl, (hmk fd).1, (hmk fd).2⟩
  · intro eff model' evs hs
    rcases (hchar _).1 hs with ⟨e, he, h⟩ | ⟨fd, ⟨hlk, hfd⟩, h⟩ <;> simp only [outcome.Ok.injEq] at h <;>
      obtain ⟨rfl, rfl, rfl⟩ := h
    · rw [open_T_err Te Ts reads _ e he]; exact herr e he
    · rw [open_T_ok Te Ts reads _ _ fd hfd]; exact hok fd hlk hfd
  · intro o
    rw [hU o]
    constructor
    · rintro (⟨e, he, ht⟩ | ⟨fd, hlk, hfd, ht⟩)
      · exact ⟨_, _, _, (hchar _).2 (.inl ⟨e, he, rfl⟩), by rw [open_T_err Te Ts reads _ e he]; exact ht⟩
      · exact ⟨_, _, _, (hchar _).2 (.inr ⟨fd, ⟨hlk, hfd⟩, rfl⟩), by rw [open_T_ok Te Ts reads _ _ fd hfd]; exact ht⟩
    · rintro ⟨eff, model', evs, hs, ht⟩
      rcases (hchar _).1 hs with ⟨e, he, h⟩ | ⟨fd, ⟨hlk, hfd⟩, h⟩ <;> simp only [outcome.Ok.injEq] at h <;>
        obtain ⟨rfl, rfl, rfl⟩ := h
      · rw [open_T_err Te Ts reads _ e he] at ht
        exact .inl ⟨e, he, ht⟩
      · rw [open_T_ok Te Ts reads _ _ fd hfd] at ht
        exact .inr ⟨fd, hlk, hfd, ht⟩

/-! ### Section `OpenNodes`: the nodes -/

/-- An over-PATH_MAX pathname: deterministic -ENAMETOOLONG, whatever the dirfd is. -/
theorem tfo_openat_toolong : ∀ ms model x8 U, ms.ms_svc_pending = some x8 → bv_unsigned x8 = 56 →
    modeled_open_flags (ms_gpr ms 2) = true → read_cstr (ms_read_byte ms) (ms_gpr ms 1) = .CstrTooLong →
    m_halted model = none → m_vm_lazy model = [] →
    to_fout segs (advance_past_svc (apply_effect ms
      (with_copyins (open_copyins ms) (mkEffect (errno_ret ENAMETOOLONG) [] [])))) model U →
    to_fout segs ms model U := by
  intro ms model x8 U hsvc hno hfl hpath hh hlazy hcont
  exact tfo_sys_char segs ms model x8 _ model U hsvc (openat_toolong_char segs ms x8 model hno hfl hpath) hh hlazy hcont

/-- O_RDONLY open of an absent file: deterministic -ENOENT. -/
theorem tfo_openat_enoent : ∀ ms model x8 p U, ms.ms_svc_pending = some x8 → bv_unsigned x8 = 56 →
    ms_gpr ms 0 = AT_FDCWD → read_cstr (ms_read_byte ms) (ms_gpr ms 1) = .CstrOk p →
    Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0 → openat_plain_name p = true →
    fs_lookup (m_fs model) p = none → m_halted model = none → m_vm_lazy model = [] →
    to_fout segs (advance_past_svc (apply_effect ms
      (with_copyins (open_copyins ms) (mkEffect (errno_ret ENOENT) [] [])))) model U →
    to_fout segs ms model U := by
  intro ms model x8 p U hsvc hno hdirfd hpath hfl hdot hfs hh hlazy hcont
  exact tfo_sys_char segs ms model x8 _ model U hsvc
    (openat_enoent_char segs ms x8 model p hno hdirfd hpath hfl hdot hfs) hh hlazy hcont

theorem tfo_read_file : ∀ ms model x8 p off data w U, ms.ms_svc_pending = some x8 → bv_unsigned x8 = 63 →
    fd_lookup (m_fds model) (ms_gpr ms 0) = some (.FdFile p off) → fd32 (ms_gpr ms 0) = ms_gpr ms 0 →
    fs_lookup (m_fs model) p = some data →
    read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) (ms_gpr ms 2) = some w →
    bv_unsigned (ms_gpr ms 2) ≤ rw_bytes_max → 0 < bv_unsigned (ms_gpr ms 2) →
    access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true →
    m_halted model = none → m_vm_lazy model = [] →
    to_fout segs
      (advance_past_svc (apply_effect ms
        (mkEffect (len_word (file_read data off (ms_gpr ms 2)))
          (delivered_writes (ms_gpr ms 1) (file_read data off (ms_gpr ms 2))) [])))
      (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
        (.FdFile p (off + len_word (file_read data off (ms_gpr ms 2))))) model) U →
    to_fout segs ms model U := by
  intro ms model x8 p off data w U hsvc hno hfd hfd32 hfs hw hcnt _ haok hh hlazy hcont
  exact tfo_sys_char segs ms model x8 _ _ U hsvc
    (read_file_char segs ms x8 model p off data w hno hfd hfd32 hfs hw hcnt haok) hh hlazy hcont

theorem tfo_write_file : ∀ ms model x8 p off data bs U, ms.ms_svc_pending = some x8 → bv_unsigned x8 = 64 →
    fd_lookup (m_fds model) (ms_gpr ms 0) = some (.FdFileW p off) → fd32 (ms_gpr ms 0) = ms_gpr ms 0 →
    read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = some bs →
    bv_unsigned (ms_gpr ms 2) ≤ rw_bytes_max → fs_lookup (m_fs model) p = some data →
    (!(modeled_file_gap data off bs)) = false → w_is0 (ms_gpr ms 2) = false →
    m_halted model = none → m_vm_lazy model = [] →
    to_fout segs
      (advance_past_svc (apply_effect ms (with_copyins [(ms_gpr ms 1, bs.length)] (mkEffect (ms_gpr ms 2) [] []))))
      (with_fds (fd_insert (m_fds model) (ms_gpr ms 0) (.FdFileW p (off + ms_gpr ms 2)))
        (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) U →
    to_fout segs ms model U := by
  intro ms model x8 p off data bs U hsvc hno hfd hfd32 hrd hcnt hfs hgap hnz hh hlazy hcont
  exact tfo_sys_char segs ms model x8 _ _ U hsvc
    (write_file_char segs ms x8 model p off data bs hno hfd hfd32 hrd hcnt hfs hgap hnz) hh hlazy hcont

/-- The `count = 0` half of `tfo_write_file`. -/
theorem tfo_write_file_zero : ∀ ms model x8 p off data bs U, ms.ms_svc_pending = some x8 → bv_unsigned x8 = 64 →
    fd_lookup (m_fds model) (ms_gpr ms 0) = some (.FdFileW p off) → fd32 (ms_gpr ms 0) = ms_gpr ms 0 →
    read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = some bs →
    bv_unsigned (ms_gpr ms 2) ≤ rw_bytes_max → fs_lookup (m_fs model) p = some data →
    (!(modeled_file_gap data off bs)) = false → w_is0 (ms_gpr ms 2) = true →
    access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true →
    m_halted model = none → m_vm_lazy model = [] →
    to_fout segs (advance_past_svc (apply_effect ms (mkEffect (ms_gpr ms 2) [] [])))
      (with_fds (fd_insert (m_fds model) (ms_gpr ms 0) (.FdFileW p (off + ms_gpr ms 2)))
        (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) U →
    to_fout segs ms model U := by
  intro ms model x8 p off data bs U hsvc hno hfd hfd32 hrd hcnt hfs hgap hz hok hh hlazy hcont
  exact tfo_sys_char segs ms model x8 _ _ U hsvc
    (write_file_zero_char segs ms x8 model p off data bs hno hfd hfd32 hrd hcnt hfs hgap hz hok) hh hlazy hcont

theorem tfo_close : ∀ ms model x8 e U, ms.ms_svc_pending = some x8 → bv_unsigned x8 = 57 →
    fd_lookup (m_fds model) (ms_gpr ms 0) = some e → fd32 (ms_gpr ms 0) = ms_gpr ms 0 →
    m_halted model = none → m_vm_lazy model = [] →
    to_fout segs (advance_past_svc (apply_effect ms (mkEffect (Z_to_bv 64 0) [] [])))
      (with_fds (fd_remove (m_fds model) (ms_gpr ms 0)) model) U →
    to_fout segs ms model U := by
  intro ms model x8 e U hsvc hno hfd hfd32 hh hlazy hcont
  exact tfo_sys_char segs ms model x8 _ _ U hsvc (close_char segs ms x8 model e hno hfd hfd32) hh hlazy hcont

end

end LPS

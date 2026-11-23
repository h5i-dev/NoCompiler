import LPS.Bridge.RefineFd
import LPS.LinuxProcessSem.Sys.Fs.Ioctl

/-!
# Refinement, the converse direction, for the syscalls that do not touch the fd table

`*_covers`: every outcome LPS's `syscall_spec` admits is one NoCompiler's model (`procSpec7`) allows: the
direction a NoCompiler theorem about EVERY run needs to hold of LPS's runs (STATUS-D, design note). Here
`exit_group` (LPS halts with the low 8 bits; NoCompiler's `.exit` carries all of a0, so the status LPS
records is NoCompiler's `c &&& 255`) and `set_tid_address` (LPS: a fresh tid in (0, 2^22), or the one it
recorded; NoCompiler: any tid in [1, 2^22]), the latter under the invariant that a recorded tid is in range.
-/

namespace LPS.Bridge
open LPS.RiscvSemantics NoCompiler.Linux

theorem exit_group_covers {k : Kern} {i : NoCompiler.Linux.SyscallInput} {j : SyscallInput} {m m' : Model}
    {eff : SyscallEffect} {evs : List event} (hr : InRel i j) (h94 : i.sysno = NoCompiler.sysExitGroup)
    (hs : syscall_spec j m (Ok eff m' evs)) :
    procSpec7 k i (.exit (i.arg 0)) k ∧ m' = with_halted (bv_and (i.arg 0) (Z_to_bv 64 255)) m ∧
      eff = mkEffect 0#64 [] [] ∧ evs = [] := by
  have hn : bv_unsigned j.in_sysno = 94 := by rw [hr.sysno, h94]; rfl
  refine ⟨(procSpec7_exitGroup h94).2 ⟨rfl, rfl⟩, ?_⟩
  rw [lookup_arm_of (a := mkSpecArm 94 (fun i => exit_spec (in_arg i 0) i))
    (by simp [spec_table, lookup_arm, mkSpecArm]) j hn] at hs
  change exit_spec (in_arg j 0) j m (Ok eff m' evs) at hs
  unfold exit_spec at hs
  obtain ⟨x, m1, e1, e2, h1, h2, rfl⟩ := hs
  cases h1
  have h2' : Ok eff m' e2 = Ok (mkEffect (Z_to_bv 64 0) [] []) _ [] := h2
  cases h2'
  rw [hr.args 0]
  exact ⟨rfl, rfl, rfl⟩

/-- A recorded tid is one `set_tid_address` could have chosen (an invariant of LPS's runs from the start,
    where none is recorded). -/
def TidOk (m : Model) : Prop := ∀ t, m_tid m = some t → 0 < bv_unsigned t ∧ bv_unsigned t < PID_MAX_ENVELOPE

theorem set_tid_address_covers {k : Kern} {i : NoCompiler.Linux.SyscallInput} {j : SyscallInput} {m m' : Model}
    {eff : SyscallEffect} {evs : List event} (hr : InRel i j) (h96 : i.sysno = sysSetTidAddress) (ht : TidOk m)
    (hs : syscall_spec j m (Ok eff m' evs)) :
    procSpec7 k i (.ret { ret := eff.eff_ret } none) k ∧ eff = mkEffect eff.eff_ret [] [] ∧ evs = [] ∧ TidOk m' := by
  have hn : bv_unsigned j.in_sysno = 96 := by rw [hr.sysno, h96]; rfl
  rw [lookup_arm_of (a := mkSpecArm 96 (fun i => set_tid_address_spec i))
    (by simp [spec_table, lookup_arm, mkSpecArm]) j hn] at hs
  change set_tid_address_spec j m (Ok eff m' evs) at hs
  unfold set_tid_address_spec at hs
  rw [bind_get_model] at hs
  -- the tid returned, in range
  have key : ∀ t : word, 0 < bv_unsigned t → bv_unsigned t < PID_MAX_ENVELOPE →
      setTidSpec (.ret { ret := t } none) := by
    intro t h1 h2
    have hb : bv_unsigned t = (t.toNat : Int) := rfl
    have hP : PID_MAX_ENVELOPE = 4194304 := by unfold PID_MAX_ENVELOPE; decide
    rw [hb] at h1 h2; rw [hP] at h2
    exact ⟨t.toNat, by omega, by omega, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
  cases htid : m_tid m with
  | some t =>
    rw [htid] at hs
    have hs' : Ok eff m' evs = Ok (mkEffect t [] []) m [] := hs
    cases hs'
    obtain ⟨h1, h2⟩ := ht t htid
    exact ⟨(procSpec7_setTid h96).2 ⟨key t h1 h2, rfl⟩, rfl, rfl, ht⟩
  | none =>
    rw [htid] at hs
    obtain ⟨t, m1, e1, e2, ⟨t', ⟨h1, h2⟩, ht1⟩, hk, rfl⟩ := hs
    cases ht1
    obtain ⟨x, m2, e3, e4, hset, hret, rfl⟩ := hk
    cases hset
    have hret' : Ok eff m' e4 = Ok (mkEffect t [] []) (with_tid t m) [] := hret
    cases hret'
    refine ⟨(procSpec7_setTid h96).2 ⟨key t h1 h2, rfl⟩, rfl, rfl, fun t' h => ?_⟩
    simp only [m_tid, with_tid, Option.some.injEq] at h
    subst h; exact ⟨h1, h2⟩

theorem cmd32_tiocgwinsz : cmd32 tiocgwinsz = tiocgwinsz := by decide
theorem tty_only_tiocgwinsz : tty_only_request tiocgwinsz = true := by decide
theorem enotty_eq : enotty = errno_ret ENOTTY := by decide

/-- `ioctl(fd, TIOCGWINSZ, ws)`, the request musl's stdio makes: every outcome LPS admits (EBADF on a closed
    fd, ENOTTY on an open one) is one NoCompiler's model allows, the kernels unchanged. NoCompiler's model has
    an outcome for this request only, hence the hypothesis. -/
theorem ioctl_covers {k : Kern} {i : NoCompiler.Linux.SyscallInput} {j : SyscallInput} {m m' : Model}
    {eff : SyscallEffect} {evs : List event} (hr : InRel i j) (h29 : i.sysno = sysIoctl)
    (hreq : i.arg 1 = tiocgwinsz) (hk : KernFd k m) (hs : syscall_spec j m (Ok eff m' evs)) :
    procSpec7 k i (.ret { ret := eff.eff_ret } none) k ∧ eff = mkEffect eff.eff_ret [] [] ∧ evs = [] ∧ m' = m := by
  have hn : bv_unsigned j.in_sysno = 29 := by rw [hr.sysno, h29]; rfl
  have hfd : fd32 (in_arg j 0) = i.fd 0 := by rw [hr.args 0, fd32_eq_fd]
  have hcmd : cmd32 (in_arg j 1) = tiocgwinsz := by rw [hr.args 1, hreq, cmd32_tiocgwinsz]
  have hlt := fd_lt i 0
  rw [lookup_arm_of (a := mkSpecArm 29 (fun i => ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i))
    (by simp [spec_table, lookup_arm, mkSpecArm]) j hn] at hs
  change ioctl_spec (fd32 (in_arg j 0)) (cmd32 (in_arg j 1)) j m (Ok eff m' evs) at hs
  unfold ioctl_spec at hs
  rw [bind_get_model, hfd, hcmd] at hs
  cases hl : fd_lookup (m_fds m) (i.fd 0) with
  | none =>
    rw [hl] at hs
    have hs' : Ok eff m' evs = Ok (mkEffect (errno_ret EBADF) [] []) m [] := hs
    cases hs'
    have hm : i.fd 0 ∉ k.fds := fun h => by have := (hk.fds _ hlt).1 h; simp [hl] at this
    refine ⟨(procSpec7_ioctl h29).2 ⟨?_, rfl⟩, rfl, rfl, rfl⟩
    simp only [ioctlSpec, hreq, ite_true, hm, ite_false]; rw [ebadf_eq]; rfl
  | some e =>
    have hm : i.fd 0 ∈ k.fds := (hk.fds _ hlt).2 (by simp [hl])
    rw [hl] at hs
    cases e <;> simp only [tty_only_tiocgwinsz, ite_true] at hs <;>
      first
      | (have hs' : Ok eff m' evs = Ok (mkEffect (errno_ret ENOTTY) [] []) m [] := hs
         cases hs'
         refine ⟨(procSpec7_ioctl h29).2 ⟨?_, rfl⟩, rfl, rfl, rfl⟩
         simp only [ioctlSpec, hreq, ite_true, hm]; exact .inl (by rw [enotty_eq]; rfl))
      | exact absurd hs (by simp [unmodeled])

end LPS.Bridge

import NoCompiler.Linux.Prot
import NoCompiler.Linux.Process

namespace NoCompiler.Linux

/-! What the process step allows at `set_tid_address`, `ioctl`, `writev`, `read` and `readv` (beyond the trusted four):
`procSpec7` (the Linux layer's top) reduced to the one call's specification. -/

theorem procSpec7_setTid {k k' : Kern} {i : SyscallInput} {o : Outcome} (h : i.sysno = sysSetTidAddress) :
    procSpec7 k i o k' ↔ setTidSpec o ∧ k' = k := by
  simp only [procSpec7, procSpec6, procSpec5, procSpec4, h]
  simp (config := { decide := true })

theorem procSpec7_ioctl {k k' : Kern} {i : SyscallInput} {o : Outcome} (h : i.sysno = sysIoctl) :
    procSpec7 k i o k' ↔ ioctlSpec k i o ∧ k' = k := by
  simp only [procSpec7, procSpec6, procSpec5, procSpec4, h]
  simp (config := { decide := true })

theorem procSpec7_readv {k k' : Kern} {i : SyscallInput} {o : Outcome} (h : i.sysno = sysReadv) :
    procSpec7 k i o k' ↔ readvSpec k i o k' := by
  simp only [procSpec7, procSpec6, h]
  simp (config := { decide := true })

theorem procSpec7_writev {k k' : Kern} {i : SyscallInput} {o : Outcome} (h : i.sysno = sysWritev) :
    procSpec7 k i o k' ↔ writevSpec k i o k' := by
  simp only [procSpec7, procSpec6, procSpec5, procSpec4, procSpec3, h]
  simp (config := { decide := true })

/-- An `ioctl(fd, TIOCGWINSZ, p)` always has an outcome at the process level. -/
theorem ioctl_progress (s : State) (k : Kern) (h7 : s.reg Reg.a7 = sysIoctl) (h1 : s.reg Reg.a1 = tiocgwinsz) :
    ∃ y, ProcStep7 (s, k) y := by
  have hno : (SyscallInput.of s).sysno = sysIoctl := h7
  have ha1 : (SyscallInput.of s).arg 1 = tiocgwinsz := h1
  by_cases hfd : (SyscallInput.of s).fd 0 ∈ k.fds
  · exact ⟨_, .step (o := .ret { ret := enotty } none) (k' := k)
      ((procSpec7_ioctl hno).2 ⟨by simp [ioctlSpec, ha1, hfd], rfl⟩)⟩
  · exact ⟨_, .step (o := .ret { ret := ebadf } none) (k' := k)
      ((procSpec7_ioctl hno).2 ⟨by simp [ioctlSpec, ha1, hfd], rfl⟩)⟩

/-- What an `ioctl(fd, TIOCGWINSZ, p)` does: the kernel unchanged; ENOTTY or EBADF, or 0 with 8 bytes
    written at `p` (a2). -/
theorem ioctl_cases {s : State} {k : Kern} {y : State × Kern} (h7 : s.reg Reg.a7 = sysIoctl)
    (h1 : s.reg Reg.a1 = tiocgwinsz) (hs : ProcStep7 (s, k) y) :
    y.2 = k ∧ (y.1 = s.sysRet enotty ∨ y.1 = s.sysRet ebadf ∨
      ∃ ws : List Byte, ws.length = 8 ∧ y.1 = (s.sysRet 0).setMem (writeBytes s.mem (s.reg Reg.a2) ws)) := by
  cases hs with
  | step h =>
    have hno : (SyscallInput.of s).sysno = sysIoctl := h7
    obtain ⟨hi, rfl⟩ := (procSpec7_ioctl hno).1 h
    have ha1 : (SyscallInput.of s).arg 1 = tiocgwinsz := h1
    simp only [ioctlSpec, ha1, ↓reduceIte] at hi
    refine ⟨rfl, ?_⟩
    split at hi
    · rcases hi with rfl | ⟨ws, hws, rfl⟩
      · exact .inl rfl
      · exact .inr (.inr ⟨ws, hws, rfl⟩)
    · subst hi; exact .inr (.inl rfl)

/-- `exit_group(c)` at the process level: the process ends with status a0; the kernel unchanged. -/
theorem procSpec7_exitGroup {k k' : Kern} {i : SyscallInput} {o : Outcome} (h : i.sysno = sysExitGroup) :
    procSpec7 k i o k' ↔ o = .exit (i.arg 0) ∧ k' = k := by
  have e : exitSpec i o ↔ o = .exit (i.arg 0) := by cases o <;> simp [exitSpec]
  simp only [procSpec7, procSpec6, procSpec5, procSpec4, procSpec3, procSpec2, procSpec, fdSpec, spec, h]
  simp (config := { decide := true }) [e]

theorem exitGroup_progress (s : State) (k : Kern) (h7 : s.reg Reg.a7 = sysExitGroup) : ∃ y, ProcStep7 (s, k) y :=
  ⟨_, .step (k' := k) (o := .exit (s.reg Reg.a0)) ((procSpec7_exitGroup h7).2 ⟨rfl, rfl⟩)⟩

theorem exitGroup_cases {s : State} {k : Kern} {y : State × Kern} (h7 : s.reg Reg.a7 = sysExitGroup)
    (hs : ProcStep7 (s, k) y) : y = ((s.halt (s.reg Reg.a0)).emit (.exit (s.reg Reg.a0)), k) := by
  cases hs with
  | step h =>
    obtain ⟨rfl, rfl⟩ := (procSpec7_exitGroup h7).1 h
    rfl

/-- A `writev` always has an outcome at the process level. -/
theorem writev_progress (s : State) (k : Kern) (h7 : s.reg Reg.a7 = sysWritev) : ∃ y, ProcStep7 (s, k) y := by
  have hno : (SyscallInput.of s).sysno = sysWritev := h7
  by_cases hfd : (SyscallInput.of s).fd 0 ∈ k.fds
  · by_cases hn : 1024 < ((SyscallInput.of s).arg 2).toNat
    · exact ⟨_, .step (o := .ret { ret := einval } none) (k' := k)
        ((procSpec7_writev hno).2 ⟨rfl, by simp [hfd, hn]⟩)⟩
    · exact ⟨_, .step (o := .ret { ret := -(BitVec.ofNat 64 5) } none) (k' := k)
        ((procSpec7_writev hno).2 ⟨rfl, by
          simp only [hfd, hn, ↓reduceIte, writeBytesSpec, true_and]
          exact .inr ⟨5, by omega, by omega, by simp, by simp⟩⟩)⟩
  · exact ⟨_, .step (o := .ret { ret := ebadf } none) (k' := k)
      ((procSpec7_writev hno).2 ⟨rfl, by simp [hfd]⟩)⟩

/-- What a `writev(fd, iov, n)` does: the kernel unchanged; `r` bytes of the gathered buffers accepted (at
    least one if there are any), the event `write fd` of them, `r` in a0; or an error code in a0
    (EINVAL, EBADF, or `-n` for `1 ≤ n ≤ 4095`), no event. Memory unchanged either way. -/
theorem writev_cases {s : State} {k : Kern} {y : State × Kern} (h7 : s.reg Reg.a7 = sysWritev)
    (hs : ProcStep7 (s, k) y) :
    y.2 = k ∧
    ((∃ r : Nat, r ≤ (gather s.mem (s.reg 11) (s.reg 12).toNat).length ∧
        (0 < (gather s.mem (s.reg 11) (s.reg 12).toNat).length → 0 < r) ∧ r ≤ maxRW ∧
        y.1 = (s.sysRet (BitVec.ofNat 64 r)).emit
          (.write ((SyscallInput.of s).fd 0) ((gather s.mem (s.reg 11) (s.reg 12).toNat).take r))) ∨
     (∃ e : Word, (e = einval ∨ e = ebadf ∨ ∃ n : Nat, 1 ≤ n ∧ n ≤ 4095 ∧ e = -(BitVec.ofNat 64 n)) ∧
        y.1 = s.sysRet e)) := by
  cases hs with
  | @step _ _ _ o h =>
    have hno : (SyscallInput.of s).sysno = sysWritev := h7
    obtain ⟨rfl, h⟩ := (procSpec7_writev hno).1 h
    refine ⟨rfl, ?_⟩
    split at h
    · split at h
      · subst h; exact .inr ⟨_, .inl rfl, rfl⟩
      · rcases o with ⟨⟨ret, ws, zs⟩, ev⟩ | c
        · obtain ⟨hw, hz, h⟩ := h
          simp only at hw hz
          subst hw hz
          rcases h with ⟨r, hr, hm, hpos, rfl, rfl⟩ | ⟨n, h1, h2, rfl, rfl⟩
          · exact .inl ⟨r, hr, hpos, hm, rfl⟩
          · exact .inr ⟨_, .inr (.inr ⟨n, h1, h2, rfl⟩), rfl⟩
        · exact h.elim
    · subst h; exact .inr ⟨_, .inr (.inl rfl), rfl⟩

theorem procSpec7_read {k k' : Kern} {i : SyscallInput} {o : Outcome} (h : i.sysno = sysRead)
    (hl : k.files.lookup (i.fd 0) = none) :
    procSpec7 k i o k' ↔ (if i.fd 0 ∈ k.fds then readSpec i o ∧ k' = k else o = .ret { ret := ebadf } none ∧ k' = k) := by
  simp only [procSpec7, procSpec6, procSpec5, procSpec4, procSpec3, procSpec2, procSpec, fdSpec, spec, h, hl]
  simp (config := { decide := true })

theorem read_progress (s : State) (k : Kern) (h7 : s.reg Reg.a7 = sysRead)
    (hl : k.files.lookup ((SyscallInput.of s).fd 0) = none) : ∃ y, ProcStep7 (s, k) y := by
  have hno : (SyscallInput.of s).sysno = sysRead := h7
  by_cases hfd : (SyscallInput.of s).fd 0 ∈ k.fds
  · exact ⟨_, .step (o := .ret { ret := -(BitVec.ofNat 64 5) } none) (k' := k)
      ((procSpec7_read hno hl).2 (by rw [if_pos hfd]; exact ⟨⟨rfl, .inr ⟨5, by omega, by omega, rfl, rfl, rfl⟩⟩, rfl⟩))⟩
  · exact ⟨_, .step (o := .ret { ret := ebadf } none) (k' := k)
      ((procSpec7_read hno hl).2 (by rw [if_neg hfd]; exact ⟨rfl, rfl⟩))⟩

/-- What a `read(fd, buf, n)` on an fd with no file behind it (a terminal, a pipe) does: the kernel
    unchanged; at most `n` bytes `ds` stored at `buf`, the event `read fd ds`, `|ds|` in a0; or an error code
    (EBADF or `-n`, `1 ≤ n ≤ 4095`), no event, memory unchanged. -/
theorem read_cases {s : State} {k : Kern} {y : State × Kern} (h7 : s.reg Reg.a7 = sysRead)
    (hl : k.files.lookup ((SyscallInput.of s).fd 0) = none) (hs : ProcStep7 (s, k) y) :
    y.2 = k ∧
    ((∃ ds : List Byte, ds.length ≤ (s.reg 12).toNat ∧ ds.length ≤ maxRW ∧
        y.1 = ((s.sysRet (BitVec.ofNat 64 ds.length)).setMem (writeBytes s.mem (s.reg 11) ds)).emit (.read ((SyscallInput.of s).fd 0) ds)) ∨
     (∃ e : Word, (e = ebadf ∨ ∃ n : Nat, 1 ≤ n ∧ n ≤ 4095 ∧ e = -(BitVec.ofNat 64 n)) ∧ y.1 = s.sysRet e)) := by
  cases hs with
  | @step _ _ k' o h =>
    have hno : (SyscallInput.of s).sysno = sysRead := h7
    have hh := (procSpec7_read hno hl).1 h
    clear h
    split at hh
    · obtain ⟨hr, rfl⟩ := hh
      refine ⟨rfl, ?_⟩
      rcases o with ⟨⟨ret, ws, zs⟩, ev⟩ | c
      · obtain ⟨hz, ⟨ds, h1, h2, hw, hr, he⟩ | ⟨n, h1, h2, hw, hr, he⟩⟩ := hr
        · simp only at hz hw hr; subst hz hw hr he
          exact .inl ⟨ds, h1, h2, rfl⟩
        · simp only at hz hw hr; subst hz hw hr he
          exact .inr ⟨_, .inr ⟨n, h1, h2, rfl⟩, rfl⟩
      · exact hr.elim
    · obtain ⟨rfl, rfl⟩ := hh
      exact ⟨rfl, .inr ⟨_, .inl rfl, rfl⟩⟩

theorem readv_progress (s : State) (k : Kern) (h7 : s.reg Reg.a7 = sysReadv)
    (hl : k.files.lookup ((SyscallInput.of s).fd 0) = none) : ∃ y, ProcStep7 (s, k) y := by
  have hno : (SyscallInput.of s).sysno = sysReadv := h7
  have hl' : k.files.lookup ((SyscallInput.of s).fd 0) = none := hl
  by_cases hfd : (SyscallInput.of s).fd 0 ∈ k.fds
  · by_cases hn : 1024 < ((SyscallInput.of s).arg 2).toNat
    · exact ⟨_, .step (o := .ret { ret := einval } none) (k' := k)
        ((procSpec7_readv hno).2 (by simp [readvSpec, hfd, hn]))⟩
    · exact ⟨_, .step (o := .ret { ret := -(BitVec.ofNat 64 5) } none) (k' := k)
        ((procSpec7_readv hno).2 (by
          simp only [readvSpec, hfd, hn, hl', ↓reduceIte, true_and]
          exact .inr ⟨5, by omega, by omega, rfl⟩))⟩
  · exact ⟨_, .step (o := .ret { ret := ebadf } none) (k' := k)
      ((procSpec7_readv hno).2 (by simp [readvSpec, hfd]))⟩

/-- What a `readv(fd, iov, n)` on an fd with no file behind it does: the kernel unchanged; bytes `ds`, at most
    the iovecs' total, scattered over them, the event `read fd ds`, `|ds|` in a0; or an error code (EINVAL,
    EBADF, or `-n`), no event, memory unchanged. -/
theorem readv_cases {s : State} {k : Kern} {y : State × Kern} (h7 : s.reg Reg.a7 = sysReadv)
    (hl : k.files.lookup ((SyscallInput.of s).fd 0) = none) (hs : ProcStep7 (s, k) y) :
    y.2 = k ∧
    ((∃ ds : List Byte, ds.length ≤ iovTotal (iovs s.mem (s.reg 11) (s.reg 12).toNat) ∧ ds.length ≤ maxRW ∧
        y.1 = ((s.sysRet (BitVec.ofNat 64 ds.length)).setMem
          (applyWrites s.mem (scatter (iovs s.mem (s.reg 11) (s.reg 12).toNat) ds))).emit (.read ((SyscallInput.of s).fd 0) ds)) ∨
     (∃ e : Word, (e = einval ∨ e = ebadf ∨ ∃ n : Nat, 1 ≤ n ∧ n ≤ 4095 ∧ e = -(BitVec.ofNat 64 n)) ∧
        y.1 = s.sysRet e)) := by
  cases hs with
  | @step _ _ k' o h =>
    have hno : (SyscallInput.of s).sysno = sysReadv := h7
    have hl' : k.files.lookup ((SyscallInput.of s).fd 0) = none := hl
    have hh := (procSpec7_readv hno).1 h
    clear h
    simp only [readvSpec, hl'] at hh
    split at hh
    · split at hh
      · obtain ⟨rfl, rfl⟩ := hh; exact ⟨rfl, .inr ⟨_, .inl rfl, rfl⟩⟩
      · obtain ⟨rfl, hh⟩ := hh
        refine ⟨rfl, ?_⟩
        rcases hh with ⟨ds, h1, h2, rfl⟩ | ⟨n, h1, h2, rfl⟩
        · exact .inl ⟨ds, h1, h2, rfl⟩
        · exact .inr ⟨_, .inr (.inr ⟨n, h1, h2, rfl⟩), rfl⟩
    · obtain ⟨rfl, rfl⟩ := hh; exact ⟨rfl, .inr ⟨_, .inr (.inl rfl), rfl⟩⟩

/-- The kernel after a read of `m` bytes from the file open on `fd`: its offset moved on. -/
def Kern.advance (k : Kern) (fd : Word) (m : Nat) : Kern :=
  { k with files := k.files.map fun p => if p.1 = fd then (p.1, { p.2 with off := p.2.off + m }) else p }

@[simp] theorem Kern.advance_perm (k : Kern) (fd : Word) (m : Nat) : (k.advance fd m).perm = k.perm := rfl
@[simp] theorem Kern.advance_fds (k : Kern) (fd : Word) (m : Nat) : (k.advance fd m).fds = k.fds := rfl

theorem procSpec7_read_file {k k' : Kern} {i : SyscallInput} {o : Outcome} {f : OpenFile} (h : i.sysno = sysRead)
    (hl : k.files.lookup (i.fd 0) = some f) :
    procSpec7 k i o k' ↔ (o = fileReadOutcome i f ∧ k' = k.advance (i.fd 0) (f.chunk (i.arg 2).toNat).length) := by
  simp only [procSpec7, procSpec6, procSpec5, h, hl, Kern.advance]
  simp (config := { decide := true })

theorem read_progress_file (s : State) (k : Kern) (f : OpenFile) (h7 : s.reg Reg.a7 = sysRead)
    (hl : k.files.lookup ((SyscallInput.of s).fd 0) = some f) : ∃ y, ProcStep7 (s, k) y :=
  ⟨_, .step ((procSpec7_read_file (i := SyscallInput.of s) h7 hl).2 ⟨rfl, rfl⟩)⟩

/-- A `read(fd, buf, n)` on a file: its next bytes (at most `n`), stored at `buf`, the event `read fd ds`,
    `|ds|` in a0, the offset moved on. -/
theorem read_cases_file {s : State} {k : Kern} {f : OpenFile} {y : State × Kern} (h7 : s.reg Reg.a7 = sysRead)
    (hl : k.files.lookup ((SyscallInput.of s).fd 0) = some f) (hs : ProcStep7 (s, k) y) :
    y.2 = k.advance ((SyscallInput.of s).fd 0) (f.chunk (s.reg 12).toNat).length ∧
    y.1 = ((s.sysRet (BitVec.ofNat 64 (f.chunk (s.reg 12).toNat).length)).setMem
      (writeBytes s.mem (s.reg 11) (f.chunk (s.reg 12).toNat))).emit (.read ((SyscallInput.of s).fd 0) (f.chunk (s.reg 12).toNat)) := by
  cases hs with
  | @step _ _ k' o h =>
    obtain ⟨rfl, rfl⟩ := (procSpec7_read_file (i := SyscallInput.of s) h7 hl).1 h
    exact ⟨rfl, rfl⟩

theorem readv_progress_file (s : State) (k : Kern) (f : OpenFile) (h7 : s.reg Reg.a7 = sysReadv)
    (hl : k.files.lookup ((SyscallInput.of s).fd 0) = some f) : ∃ y, ProcStep7 (s, k) y := by
  have hno : (SyscallInput.of s).sysno = sysReadv := h7
  have hl' : k.files.lookup ((SyscallInput.of s).fd 0) = some f := hl
  by_cases hfd : (SyscallInput.of s).fd 0 ∈ k.fds
  · by_cases hn : 1024 < ((SyscallInput.of s).arg 2).toNat
    · exact ⟨_, .step (o := .ret { ret := einval } none) (k' := k)
        ((procSpec7_readv hno).2 (by simp [readvSpec, hfd, hn]))⟩
    · exact ⟨_, .step ((procSpec7_readv hno).2 (by simp only [readvSpec, hfd, hn, hl', ↓reduceIte]; exact ⟨rfl, rfl⟩))⟩
  · exact ⟨_, .step (o := .ret { ret := ebadf } none) (k' := k)
      ((procSpec7_readv hno).2 (by simp [readvSpec, hfd]))⟩

/-- A `readv(fd, iov, n)` on a file: (open) its next bytes, at most the iovecs' total, scattered, the event, the
    offset moved on; or an error, the kernel unchanged: EINVAL (more than 1024 iovecs) or EBADF (`fd` not open). -/
theorem readv_cases_file {s : State} {k : Kern} {f : OpenFile} {y : State × Kern} (h7 : s.reg Reg.a7 = sysReadv)
    (hl : k.files.lookup ((SyscallInput.of s).fd 0) = some f) (hs : ProcStep7 (s, k) y) :
    (y.2 = k.advance ((SyscallInput.of s).fd 0) (f.chunk (iovTotal (iovs s.mem (s.reg 11) (s.reg 12).toNat))).length ∧
      y.1 = ((s.sysRet (BitVec.ofNat 64 (f.chunk (iovTotal (iovs s.mem (s.reg 11) (s.reg 12).toNat))).length)).setMem
        (applyWrites s.mem (scatter (iovs s.mem (s.reg 11) (s.reg 12).toNat)
          (f.chunk (iovTotal (iovs s.mem (s.reg 11) (s.reg 12).toNat)))))).emit
        (.read ((SyscallInput.of s).fd 0) (f.chunk (iovTotal (iovs s.mem (s.reg 11) (s.reg 12).toNat))))) ∨
    (y.2 = k ∧ ∃ e : Word, ((e = einval ∧ 1024 < (s.reg 12).toNat) ∨ (e = ebadf ∧ (SyscallInput.of s).fd 0 ∉ k.fds)) ∧
      y.1 = s.sysRet e) := by
  cases hs with
  | @step _ _ k' o h =>
    have hno : (SyscallInput.of s).sysno = sysReadv := h7
    have hl' : k.files.lookup ((SyscallInput.of s).fd 0) = some f := hl
    have hh := (procSpec7_readv hno).1 h
    clear h
    simp only [readvSpec, hl'] at hh
    split at hh
    · split at hh
      · obtain ⟨rfl, rfl⟩ := hh; exact .inr ⟨rfl, _, .inl ⟨rfl, by assumption⟩, rfl⟩
      · obtain ⟨rfl, rfl⟩ := hh; exact .inl ⟨rfl, rfl⟩
    · obtain ⟨rfl, rfl⟩ := hh; exact .inr ⟨rfl, _, .inr ⟨rfl, by assumption⟩, rfl⟩

end NoCompiler.Linux

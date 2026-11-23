import LPS.Bridge.Refine

/-!
# Refinement: the fd table and `close`

`KernFd k m`: NoCompiler's descriptors and open files (`Kern.fds`, `Kern.files`) are LPS's (`m_fds`, files in
`m_fs`). Both read an fd argument as its low 32 bits (NoCompiler's `SyscallInput.fd`, LPS's `fd32`; user decision
2026-11-22 (4)), so no hypothesis on the argument is needed.
-/

namespace LPS.Bridge
open LPS.RiscvSemantics NoCompiler.Linux

structure KernFd (k : Kern) (m : Model) : Prop where
  nodup : k.fds.Nodup
  small : ∀ fd ∈ k.fds, fd.toNat < 2 ^ 32
  fds : ∀ fd : NoCompiler.Word, fd.toNat < 2 ^ 32 → (fd ∈ k.fds ↔ (fd_lookup (m_fds m) fd).isSome)
  files : ∀ fd f, k.files.lookup fd = some f →
    ∃ p, fd_lookup (m_fds m) fd = some (.FdFile p (BitVec.ofNat 64 f.off)) ∧ fs_lookup (m_fs m) p = some f.data

theorem bv_eqb_iff {a b : word} : bv_eqb a b = true ↔ a = b := by
  unfold bv_eqb bv_unsigned; simp only [decide_eq_true_eq]
  constructor
  · intro h; exact BitVec.eq_of_toNat_eq (by omega)
  · intro h; subst h; rfl

/-- LPS's `fd32` of an argument is NoCompiler's `SyscallInput.fd` of it. -/
theorem fd32_eq_fd (i : NoCompiler.Linux.SyscallInput) (k : Nat) : fd32 (i.arg k) = i.fd k := by
  unfold fd32 abi_low32 Z.modulo bv_unsigned Z_to_bv NoCompiler.Linux.SyscallInput.fd
  rw [Int.fmod_eq_emod_of_nonneg _ (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and]
  have : (0xffffffff#64).toNat = 2 ^ 32 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  simp; omega

theorem fd_lt (i : NoCompiler.Linux.SyscallInput) (k : Nat) : (i.fd k).toNat < 2 ^ 32 := by
  unfold NoCompiler.Linux.SyscallInput.fd
  rw [BitVec.toNat_and]
  have : (0xffffffff#64).toNat = 2 ^ 32 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]; omega

theorem fd_lookup_remove (l : List (word × FdEntry)) (fd x : word) :
    fd_lookup (fd_remove l fd) x = if x = fd then none else fd_lookup l x := by
  induction l with
  | nil => simp [fd_remove, fd_lookup]
  | cons p r ih =>
    obtain ⟨a, e⟩ := p
    unfold fd_remove at ih ⊢
    by_cases ha : a = fd
    · subst ha
      have : bv_eqb a a = true := bv_eqb_iff.2 rfl
      simp only [List.filter_cons, this, Bool.not_true, Bool.false_eq_true, ite_false, ih]
      by_cases hx : x = a
      · simp [hx]
      · simp only [hx, ite_false, fd_lookup]
        have : bv_eqb a x = false := by
          cases h : bv_eqb a x
          · rfl
          · exact absurd (bv_eqb_iff.1 h).symm hx
        simp [this]
    · have hn : bv_eqb a fd = false := by
        cases h : bv_eqb a fd
        · rfl
        · exact absurd (bv_eqb_iff.1 h) ha
      simp only [List.filter_cons, hn, Bool.not_false, ite_true, fd_lookup, ih]
      by_cases hx : x = fd
      · subst hx; simp [hn]
      · simp [hx]

/-- `close` in NoCompiler's model: an open fd is closed (`ret 0`), else EBADF; its file is forgotten. -/
theorem procSpec7_close {k k' : Kern} {i : NoCompiler.Linux.SyscallInput} {o : Outcome}
    (h : i.sysno = sysClose) :
    procSpec7 k i o k' ↔
      if i.fd 0 ∈ k.fds then o = .ret { ret := 0 } none ∧
        k' = { k with fds := k.fds.erase (i.fd 0), files := k.files.filter (·.1 ≠ i.fd 0) }
      else o = .ret { ret := ebadf } none ∧ k' = { k with files := k.files.filter (·.1 ≠ i.fd 0) } := by
  simp only [procSpec7, procSpec6, procSpec5, procSpec4, procSpec3, procSpec2, procSpec, fdSpec, h]
  simp (config := { decide := true }) only [ite_false, ite_true, or_false, false_or, or_true]
  by_cases hm : i.fd 0 ∈ k.fds
  · simp only [hm, ite_true]
    constructor
    · rintro ⟨k₁, ⟨rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨_, ⟨rfl, rfl⟩, rfl⟩
  · simp only [hm, ite_false]
    constructor
    · rintro ⟨k₁, ⟨rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨_, ⟨rfl, rfl⟩, rfl⟩

/-- close(fd) on a closed fd: LPS's spec admits EBADF, the model unchanged. -/
theorem close_ebadf_admits (i : SyscallInput) (m : Model) (h : bv_unsigned i.in_sysno = 57)
    (hfd : fd_lookup (m_fds m) (fd32 (in_arg i 0)) = none) :
    syscall_spec i m (Ok (mkEffect (errno_ret EBADF) [] []) m []) := by
  rw [lookup_arm_of (a := mkSpecArm 57 (fun i => close_spec (fd32 (in_arg i 0)) i))
    (by simp [spec_table, lookup_arm, mkSpecArm]) i h]
  show (close_spec (fd32 (in_arg i 0))) i m _
  unfold close_spec
  rw [bind_get_model]; simp only [hfd]; rfl

theorem ebadf_eq : ebadf = errno_ret EBADF := by decide

theorem lookup_filter_ne {l : List (NoCompiler.Word × OpenFile)} {a x : NoCompiler.Word} {f : OpenFile}
    (h : (l.filter (·.1 ≠ a)).lookup x = some f) : x ≠ a ∧ l.lookup x = some f := by
  induction l with
  | nil => simp at h
  | cons p r ih =>
    obtain ⟨q, g⟩ := p
    by_cases hq : q = a
    · subst hq
      have h' : (r.filter (·.1 ≠ q)).lookup x = some f := by simpa using h
      obtain ⟨hx, hl⟩ := ih h'
      refine ⟨hx, ?_⟩
      simp only [List.lookup, show (x == q) = false from by simpa using hx]; exact hl
    · simp only [List.filter_cons, ne_eq, hq, not_false_eq_true, decide_true, ite_true, List.lookup] at h
      by_cases hx : x = q
      · subst hx; simp at h; subst h; exact ⟨hq, by simp⟩
      · simp only [show (x == q) = false from by simpa using hx] at h
        obtain ⟨hxa, hl⟩ := ih h
        exact ⟨hxa, by simp only [List.lookup, show (x == q) = false from by simpa using hx]; exact hl⟩

/-- `close`: every outcome NoCompiler's model allows is one LPS's `syscall_spec` admits, and the fd tables
    stay related. -/
theorem close_refines {k k' : Kern} {i : NoCompiler.Linux.SyscallInput} {o : Outcome} {j : SyscallInput}
    {m : Model} (hr : InRel i j) (h57 : i.sysno = sysClose) (hs : procSpec7 k i o k') (hk : KernFd k m) :
    ∃ r m', o = .ret { ret := r } none ∧ syscall_spec j m (Ok (mkEffect r [] []) m' []) ∧ KernFd k' m' := by
  have hn : bv_unsigned j.in_sysno = 57 := by rw [hr.sysno, h57]; rfl
  have hfd : fd32 (in_arg j 0) = i.fd 0 := by rw [hr.args 0, fd32_eq_fd]
  have hlt := fd_lt i 0
  rw [procSpec7_close h57] at hs
  split at hs
  · rename_i hm
    obtain ⟨rfl, rfl⟩ := hs
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 ((hk.fds _ hlt).1 hm)
    refine ⟨0, with_fds (fd_remove (m_fds m) (i.fd 0)) m, rfl, ?_, ?_⟩
    · have := close_admits j m hn e (by rw [hfd]; exact he); rw [hfd] at this; exact this
    · refine ⟨hk.nodup.erase _, fun fd h => hk.small fd (List.mem_of_mem_erase h), fun fd hf => ?_, fun fd f h => ?_⟩
      · simp only [m_fds, with_fds]
        rw [hk.nodup.mem_erase_iff]
        show _ ↔ (fd_lookup (fd_remove (m_fds m) (i.fd 0)) fd).isSome
        rw [fd_lookup_remove]
        by_cases hx : fd = i.fd 0
        · simp [hx]
        · simp only [hx, ne_eq, not_false_eq_true, true_and, ite_false]; exact hk.fds fd hf
      · obtain ⟨hx, hl⟩ := lookup_filter_ne h
        obtain ⟨p, hp, hfs⟩ := hk.files fd f hl
        refine ⟨p, ?_, hfs⟩
        show fd_lookup (fd_remove (m_fds m) (i.fd 0)) fd = _
        rw [fd_lookup_remove, if_neg hx]; exact hp
  · rename_i hm
    obtain ⟨rfl, rfl⟩ := hs
    have hnone : fd_lookup (m_fds m) (i.fd 0) = none := by
      cases h : fd_lookup (m_fds m) (i.fd 0) with
      | none => rfl
      | some e => exact absurd ((hk.fds _ hlt).2 (by simp [h])) hm
    refine ⟨ebadf, m, rfl, ?_, ?_⟩
    · rw [ebadf_eq]; exact close_ebadf_admits j m hn (by rw [hfd]; exact hnone)
    · exact ⟨hk.nodup, hk.small, hk.fds, fun fd f h => hk.files fd f (lookup_filter_ne h).2⟩

/-- The converse of `close_refines`, the direction a theorem about every run needs: every outcome LPS's
    `syscall_spec` admits for `close` is one NoCompiler's model allows (with the same return and no
    writes or events), and the fd tables stay related. -/
theorem close_covers {k : Kern} {i : NoCompiler.Linux.SyscallInput} {j : SyscallInput} {m m' : Model}
    {eff : SyscallEffect} {evs : List event} (hr : InRel i j) (h57 : i.sysno = sysClose) (hk : KernFd k m)
    (hs : syscall_spec j m (Ok eff m' evs)) :
    ∃ k', procSpec7 k i (.ret { ret := eff.eff_ret } none) k' ∧ eff = mkEffect eff.eff_ret [] [] ∧ evs = [] ∧
      KernFd k' m' := by
  have hn : bv_unsigned j.in_sysno = 57 := by rw [hr.sysno, h57]; rfl
  have hfd : fd32 (in_arg j 0) = i.fd 0 := by rw [hr.args 0, fd32_eq_fd]
  have hlt := fd_lt i 0
  rw [lookup_arm_of (a := mkSpecArm 57 (fun i => close_spec (fd32 (in_arg i 0)) i))
    (by simp [spec_table, lookup_arm, mkSpecArm]) j hn] at hs
  change close_spec (fd32 (in_arg j 0)) j m (Ok eff m' evs) at hs
  unfold close_spec at hs
  rw [bind_get_model, hfd] at hs
  cases hl : fd_lookup (m_fds m) (i.fd 0) with
  | none =>
    rw [hl] at hs
    have hs' : Ok eff m' evs = Ok (mkEffect (errno_ret EBADF) [] []) m [] := hs
    cases hs'
    have hm : i.fd 0 ∉ k.fds := fun h => by have := (hk.fds _ hlt).1 h; simp [hl] at this
    refine ⟨{ k with files := k.files.filter (·.1 ≠ i.fd 0) }, ?_, rfl, rfl, ?_⟩
    · rw [procSpec7_close h57, if_neg hm]; exact ⟨by rw [← ebadf_eq]; rfl, rfl⟩
    · exact ⟨hk.nodup, hk.small, hk.fds, fun fd f h => hk.files fd f (lookup_filter_ne h).2⟩
  | some e =>
    rw [hl] at hs
    obtain ⟨x, m1, e1, e2, h1, h2, rfl⟩ := hs
    cases h1
    have h2' : Ok eff m' e2 = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_fds (fd_remove (m_fds m) (i.fd 0)) m) [] := h2
    cases h2'
    have hm : i.fd 0 ∈ k.fds := (hk.fds _ hlt).2 (by simp [hl])
    refine ⟨{ k with fds := k.fds.erase (i.fd 0), files := k.files.filter (·.1 ≠ i.fd 0) }, ?_, rfl, rfl, ?_⟩
    · rw [procSpec7_close h57, if_pos hm]; exact ⟨rfl, rfl⟩
    · refine ⟨hk.nodup.erase _, fun fd h => hk.small fd (List.mem_of_mem_erase h), fun fd hf => ?_, fun fd f h => ?_⟩
      · rw [hk.nodup.mem_erase_iff]
        show _ ↔ (fd_lookup (fd_remove (m_fds m) (i.fd 0)) fd).isSome
        rw [fd_lookup_remove]
        by_cases hx : fd = i.fd 0
        · simp [hx]
        · simp only [hx, ne_eq, not_false_eq_true, true_and, ite_false]; exact hk.fds fd hf
      · obtain ⟨hx, hl'⟩ := lookup_filter_ne h
        obtain ⟨p, hp, hfs⟩ := hk.files fd f hl'
        exact ⟨p, by show fd_lookup (fd_remove (m_fds m) (i.fd 0)) fd = _; rw [fd_lookup_remove, if_neg hx]; exact hp, hfs⟩

end LPS.Bridge

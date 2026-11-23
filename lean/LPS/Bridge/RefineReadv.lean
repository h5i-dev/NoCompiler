import LPS.Bridge.RefineRead

/-!
# Refinement, the converse direction: `readv`

`readv_covers`: every outcome LPS's `syscall_spec` admits for `readv(fd, iov, n)` on a closed fd, a channel, or
a file NoCompiler has open in `k.files` (`ReadvKind`) is one NoCompiler's model (`procSpec7`, `readvSpec`)
allows (`ReadvCovered`: same return, LPS's writes the non-empty pieces of NoCompiler's `scatter`, events as in
`ReadEvAgree`, `KernFd` kept, the file offset advanced on both sides), except on a file LPS's EFAULT and EINVAL
(`ReadvFileErr`), which the two models genuinely disagree on: NoCompiler's file readv always delivers the next
bytes (its memory is total, it checks no iovec), LPS returns EFAULT for an unreadable iovec array or an
unwritable buffer and EINVAL for an iovec length of 2^63 or more or `off + total > 2^63 - 1`, as Linux does.

What the two models share (`MemAgree`, as for `writev`): the iovecs LPS imports are NoCompiler's
(`import_ok`, `iovs_iovList`); LPS's total over the capped iovecs is `min (iovTotal vs) MAX_RW_COUNT`
(`total_cap`), so on a file LPS's `file_read` is NoCompiler's `chunk` (`file_read_chunk_nat`); LPS's scatter over
the capped iovecs is NoCompiler's `scatter` without its empty pieces (`scatter_cap`).

Hypotheses of `readv_covers`, and why:
- `hr`, `hk`, `hmem`, `hcid`: as for `writev_covers` (inputs, fd tables, readable memory, channel labels).
- `hkind`: LPS's other arms (FdFileRW, FdFileW/FdFileA, directories, pipes, sockets, /dev/null, urandom) are
  not covered, nor an LPS `FdFile` NoCompiler does not have in `k.files`.
- `hcnt`, `n < 2^32`: LPS reads the count's low 32 bits (`iovcnt32`), NoCompiler all 64.
- `hch`: a channel other than 0 (LPS: EBADF, not readable) only with at most 1024 iovecs; above, NoCompiler's
  only outcome on an open fd is EINVAL.
- `hoff`: a file's offset below 2^64 (`KernFd` relates offsets modulo 2^64).
LPS's `readv_heap_iovecb` arm (9..1024 iovecs) is `Unmodeled`, not an `Ok` outcome, so it is not constrained.
LPS's `eff_copyins` (the iovec array it read) is its ledger, not a memory effect; `ReadvCovered` leaves it free.
-/

namespace LPS.Bridge
open LPS.RiscvSemantics NoCompiler.Linux

/-- LPS's iovecs, with NoCompiler's `Nat` lengths. -/
def iovNat (iovs : List (word × word)) : List (NoCompiler.Word × Nat) := iovs.map fun p => (p.1, p.2.toNat)

section V
variable {M : NoCompiler.Word → NoCompiler.Byte} {mp : word → Option byte}

theorem iovAt_succ (a : NoCompiler.Word) (j : Nat) : iovAt M a (j + 1) = iovAt M (a + 16) j := by
  unfold iovAt
  have h16 : (16 : BitVec 64).toNat = 16 := rfl
  have e1 : a + BitVec.ofNat 64 (16 * (j + 1)) = a + 16 + BitVec.ofNat 64 (16 * j) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h16]; omega
  have e2 : a + BitVec.ofNat 64 (16 * (j + 1) + 8) = a + 16 + BitVec.ofNat 64 (16 * j + 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h16]; omega
  rw [e1, e2]

theorem iovs_iovList (a : NoCompiler.Word) : ∀ n, iovs M a n = iovNat (iovList M a n) := by
  intro n
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [iovs, List.range_succ_eq_map, List.map_cons, List.map_map] at ih ⊢
    have : (iovAt M a ∘ Nat.succ) = iovAt M (a + 16) := funext fun j => iovAt_succ a j
    rw [this, ih]
    simp [iovList, iovNat, iovAt]

theorem iovs_total_eq : ∀ iovs : List (word × word), iovs_total iovs = (iovTotal (iovNat iovs) : Int) := by
  intro iovs
  induction iovs with
  | nil => rfl
  | cons p r ih =>
    simp only [iovs_total, ih, iovNat, iovTotal, List.map_cons, List.sum_cons] at *
    unfold bv_unsigned; push_cast; rfl

theorem total_cap : ∀ iovs (left : Int), 0 ≤ left →
    iovs_total (cap_iovecs_aux iovs left) = min (iovs_total iovs) left := by
  intro iovs
  induction iovs with
  | nil => intro left hl; simp [cap_iovecs_aux, iovs_total]; omega
  | cons p r ih =>
    intro left hl
    obtain ⟨base, len⟩ := p
    have hl0 := bv_unsigned_nonneg len
    have hl1 := bv_unsigned_lt len
    have := iovs_total_nonneg r
    simp only [cap_iovecs_aux, iovs_total]
    rw [bv_unsigned_Z_to_bv _ (by omega) (by omega), ih _ (by omega)]
    omega

theorem scatter_nil_filter : ∀ vs : List (NoCompiler.Word × Nat),
    (scatter vs []).filter (fun p => !p.2.isEmpty) = [] := by
  intro vs
  induction vs with
  | nil => rfl
  | cons p r ih => obtain ⟨b, n⟩ := p; simp [scatter, ih]

/-- LPS's scatter over the capped iovecs writes the non-empty pieces of NoCompiler's scatter. -/
theorem scatter_cap : ∀ iovs (left : Int) (ds : List byte) ws, 0 ≤ left → (ds.length : Int) ≤ left →
    scatter_iovecs mp (cap_iovecs_aux iovs left) ds = some ws →
    ws = (scatter (iovNat iovs) ds).filter (fun p => !p.2.isEmpty) := by
  intro iovs
  induction iovs with
  | nil =>
    intro left ds ws _ _ h
    cases ds with
    | nil => simp [cap_iovecs_aux, scatter_iovecs] at h; subst h; rfl
    | cons d ds => simp [cap_iovecs_aux, scatter_iovecs] at h
  | cons p r ih =>
    intro left ds ws hl hd h
    obtain ⟨base, len⟩ := p
    have hl0 := bv_unsigned_nonneg len
    have hl1 := bv_unsigned_lt len
    cases ds with
    | nil =>
      simp only [cap_iovecs_aux, scatter_iovecs, Option.some.injEq] at h
      subst h; exact (scatter_nil_filter _).symm
    | cons d ds' =>
      have hmn : bv_unsigned (Z_to_bv 64 (min left (bv_unsigned len))) = min left (bv_unsigned len) :=
        bv_unsigned_Z_to_bv _ (by omega) (by omega)
      have hn : word_to_nat_bounded (Z_to_bv 64 (min left (bv_unsigned len))) (d :: ds').length =
          min len.toNat (d :: ds').length := by
        rw [word_to_nat_bounded_eq_min]; unfold word_to_nat; rw [hmn]
        show Nat.min _ _ = _
        simp only [Nat.min_def, Int.min_def]
        unfold bv_unsigned at *; simp only [List.length_cons] at *
        split <;> split <;> (try split) <;> omega
      simp only [cap_iovecs_aux] at h
      rw [scatter_iovecs] at h
      simp only [hn] at h
      have ht : (d :: ds').take len.toNat = (d :: ds').take (min len.toNat (d :: ds').length) := by
        rw [List.take_eq_take_iff]; omega
      have hdr : (d :: ds').drop len.toNat = (d :: ds').drop (min len.toNat (d :: ds').length) := by
        apply List.ext_getElem
        · simp only [List.length_drop]; omega
        · intro n h1 h2; simp only [List.getElem_drop]; congr 1; simp only [List.length_drop] at h1; omega
      have hrest : (((d :: ds').drop (min len.toNat (d :: ds').length)).length : Int) ≤
          left - min left (bv_unsigned len) := by
        simp only [List.length_drop]; unfold bv_unsigned at *; simp only [List.length_cons] at *; omega
      have hscat : scatter (iovNat ((base, len) :: r)) (d :: ds') =
          (base, (d :: ds').take (min len.toNat (d :: ds').length)) ::
            scatter (iovNat r) ((d :: ds').drop (min len.toNat (d :: ds').length)) := by
        rw [← ht, ← hdr]; rfl
      rw [hscat]
      generalize (d :: ds').take (min len.toNat (d :: ds').length) = here at h
      generalize hlt : (d :: ds').drop (min len.toNat (d :: ds').length) = later at h hrest
      cases here with
      | nil =>
        simp only at h
        simpa using ih _ later ws (by omega) hrest h
      | cons b bs =>
        simp only at h
        split at h
        · rename_i w1 ws' _ h2
          cases h
          simp only [List.filter_cons, List.isEmpty_cons, Bool.not_false, ite_true, List.cons.injEq, true_and]
          exact ih _ later ws' (by omega) hrest h2
        · cases h
end V


theorem file_read_chunk_nat (f : OpenFile) (n : Nat) (h : f.off < 2 ^ 64) :
    file_read f.data (BitVec.ofNat 64 f.off) (Z_to_bv 64 (min (n : Int) MAX_RW_COUNT)) = f.chunk n := by
  unfold file_read OpenFile.chunk
  have ho : bv_unsigned (BitVec.ofNat 64 f.off) = (f.off : Int) := by
    unfold bv_unsigned; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  simp only [ho, file_from_eq, word_to_nat_bounded_eq_min]
  have hc : word_to_nat (Z_to_bv 64 (min (n : Int) MAX_RW_COUNT)) = min n NoCompiler.maxRW := by
    unfold word_to_nat MAX_RW_COUNT
    rw [bv_unsigned_Z_to_bv _ (by omega) (by omega)]
    unfold NoCompiler.maxRW; omega
  rw [hc]
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, Nat.min_def]; split <;> (try split) <;> (try split) <;> omega
  · intro n h1 h2; simp

/-- What `readv_covers` concludes, NoCompiler's side: as `ReadCovered`, but LPS's `eff_copyins` (its ledger of
    the iovec array it read) is not constrained. -/
def ReadvCovered (k : Kern) (i : NoCompiler.Linux.SyscallInput) (eff : SyscallEffect) (m' : Model)
    (evs : List event) : Prop :=
  eff.eff_zeros = [] ∧ eff.eff_unmaps = [] ∧ eff.eff_copies = [] ∧
  ∃ ws ev k', procSpec7 k i (.ret { ret := eff.eff_ret, writes := ws } ev) k' ∧
    eff.eff_writes = ws.filter (fun p => !p.2.isEmpty) ∧
    ReadEvAgree (k.files.lookup (i.fd 0)).isSome (i.fd 0) (i.fd 0) ev evs ∧ KernFd k' m'

/-- The outcomes LPS admits on a file and NoCompiler does not: EFAULT (a buffer LPS cannot write) and
    EINVAL (an iovec LPS refuses, or offset plus length past 2^63 - 1), nothing stored, no event. -/
def ReadvFileErr (k : Kern) (i : NoCompiler.Linux.SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) : Prop :=
  (k.files.lookup (i.fd 0)).isSome ∧ m' = m ∧ evs = [] ∧ eff.eff_writes = [] ∧ eff.eff_zeros = [] ∧
    (eff.eff_ret = errno_ret EFAULT ∨ eff.eff_ret = errno_ret EINVAL)

/-- The fds `readv_covers` covers: closed, a channel, a file NoCompiler has open. -/
def ReadvKind (k : Kern) (m : Model) (fd : word) : Prop :=
  match fd_lookup (m_fds m) fd with
  | none => True
  | some (.FdChannel _) => True
  | some (.FdFile _ _) => (k.files.lookup fd).isSome
  | some _ => False

theorem readv_err_covered {k : Kern} {i : NoCompiler.Linux.SyscallInput} {m : Model} (hk : KernFd k m)
    (h65 : i.sysno = sysReadv) (hl : k.files.lookup (i.fd 0) = none) (hm : i.fd 0 ∈ k.fds)
    (hc : ¬ 1024 < (i.arg 2).toNat) (n : Nat) (h1 : 1 ≤ n) (h2 : n ≤ 4095) :
    ReadvCovered k i (mkEffect (-(BitVec.ofNat 64 n)) [] []) m [] := by
  refine ⟨rfl, rfl, rfl, [], none, k, ?_, rfl, by simp [ReadEvAgree, hl], hk⟩
  rw [procSpec7_readv h65]
  simp only [readvSpec, hm, hc, hl, ite_true, ite_false]
  exact ⟨trivial, .inr ⟨n, h1, h2, rfl⟩⟩

theorem readv_ok_covered {k : Kern} {i : NoCompiler.Linux.SyscallInput} {m' : Model} (hk : KernFd k m')
    (h65 : i.sysno = sysReadv) (hl : k.files.lookup (i.fd 0) = none) (hm : i.fd 0 ∈ k.fds)
    (hc : ¬ 1024 < (i.arg 2).toNat) (ds : List NoCompiler.Byte)
    (h1 : ds.length ≤ iovTotal (iovs i.mem (i.arg 1) (i.arg 2).toNat)) (h2 : ds.length ≤ NoCompiler.maxRW)
    (ws : List (word × List byte))
    (hws : ws = (scatter (iovs i.mem (i.arg 1) (i.arg 2).toNat) ds).filter (fun p => !p.2.isEmpty)) :
    ReadvCovered k i (mkEffect (BitVec.ofNat 64 ds.length) ws []) m' (ds.map (event.ReadEv (i.fd 0))) := by
  refine ⟨rfl, rfl, rfl, scatter (iovs i.mem (i.arg 1) (i.arg 2).toNat) ds, some (.read (i.fd 0) ds), k,
    ?_, hws, by simp [ReadEvAgree, hl], hk⟩
  rw [procSpec7_readv h65]
  simp only [readvSpec, hm, hc, hl, ite_true, ite_false]
  exact ⟨trivial, .inl ⟨ds, h1, h2, rfl⟩⟩

theorem word_to_nat_eq (w : word) : word_to_nat w = w.toNat := by
  unfold word_to_nat bv_unsigned; simp

theorem kernfd_advance_zero {k : Kern} {m : Model} (hk : KernFd k m) (fd : NoCompiler.Word) :
    KernFd (k.advance fd 0) m := by
  refine ⟨hk.nodup, hk.small, hk.fds, fun x g hg => ?_⟩
  obtain ⟨g0, hg0, rfl⟩ := lookup_advance hg
  have : (if x = fd then { g0 with off := g0.off + 0 } else g0) = g0 := by split <;> rfl
  rw [this]; exact hk.files x g0 hg0

theorem kernfd_advance {k : Kern} {m : Model} (hk : KernFd k m) {fd : NoCompiler.Word} {f : OpenFile} {p : path}
    (hf : k.files.lookup fd = some f) (hfs : fs_lookup (m_fs m) p = some f.data) (hm : fd ∈ k.fds) (n : Nat) :
    KernFd (k.advance fd n) (with_fds (fd_insert (m_fds m) fd (.FdFile p (BitVec.ofNat 64 f.off + BitVec.ofNat 64 n))) m) := by
  refine ⟨hk.nodup, hk.small, fun x hx => ?_, fun x g hg => ?_⟩
  · show x ∈ k.fds ↔ (fd_lookup (fd_insert (m_fds m) fd _) x).isSome
    rw [fd_lookup_insert]
    by_cases h : x = fd
    · subst h; simp [hm]
    · rw [if_neg h]; exact hk.fds x hx
  · obtain ⟨g0, hg0, rfl⟩ := lookup_advance hg
    show ∃ p, fd_lookup (fd_insert (m_fds m) fd _) x = _ ∧ fs_lookup (m_fs m) p = _
    rw [fd_lookup_insert]
    by_cases h : x = fd
    · subst h
      rw [hf] at hg0; cases hg0
      refine ⟨p, ?_, by simpa using hfs⟩
      simp only [ite_true, Option.some.injEq, FdEntry.FdFile.injEq, true_and]
      apply BitVec.eq_of_toNat_eq; simp
    · simp only [h, ite_false]; exact hk.files x g0 hg0

/-- `readv(fd, iov, n)`: every outcome LPS's `syscall_spec` admits, on the fds `ReadvKind` allows, is one
    NoCompiler's model allows (`ReadvCovered`), except, on a file, LPS's EFAULT and EINVAL
    (`ReadvFileErr`), which NoCompiler's file readv does not have. -/
theorem readv_covers {k : Kern} {i : NoCompiler.Linux.SyscallInput} {j : SyscallInput} {m m' : Model}
    {eff : SyscallEffect} {evs : List event} (hr : InRel i j) (h65 : i.sysno = sysReadv)
    (hk : KernFd k m) (hmem : MemAgree i j) (hcid : ChanId m) (hkind : ReadvKind k m (i.fd 0))
    (hcnt : (i.arg 2).toNat < 2 ^ 32)
    (hch : ∀ ch, fd_lookup (m_fds m) (i.fd 0) = some (.FdChannel ch) → ch ≠ 0 → (i.arg 2).toNat ≤ 1024)
    (hoff : ∀ f, k.files.lookup (i.fd 0) = some f → f.off < 2 ^ 64)
    (hs : syscall_spec j m (Ok eff m' evs)) :
    ReadvCovered k i eff m' evs ∨ ReadvFileErr k i eff m m' evs := by
  have hn : bv_unsigned j.in_sysno = 65 := by rw [hr.sysno, h65]; rfl
  have hfd : fd32 (in_arg j 0) = i.fd 0 := by rw [hr.args 0, fd32_eq_fd]
  have hlt := fd_lt i 0
  rw [lookup_arm_of (a := mkSpecArm 65 (fun i => readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i))
    (by simp [spec_table, lookup_arm, mkSpecArm]) j hn] at hs
  change readv_spec (fd32 (in_arg j 0)) (in_arg j 1) (in_arg j 2) j m (Ok eff m' evs) at hs
  unfold readv_spec at hs
  obtain ⟨x, m1, e1, e2, h1, hs, rfl⟩ := hs
  cases h1
  rw [bind_get_model, hfd, hr.args 1, hr.args 2, iovcnt32_eq _ hcnt] at hs
  simp only [List.nil_append]
  unfold ReadvKind at hkind
  cases hl : fd_lookup (m_fds m) (i.fd 0) with
  | none =>
    rw [hl] at hs
    have hs' : Ok eff m' e2 = Ok (mkEffect (errno_ret EBADF) [] []) m [] := hs
    cases hs'
    have hm : i.fd 0 ∉ k.fds := fun h => by have := (hk.fds _ hlt).1 h; simp [hl] at this
    have hf : k.files.lookup (i.fd 0) = none := by
      cases h : k.files.lookup (i.fd 0) with
      | none => rfl
      | some f => exact absurd (files_mem hk h hlt) hm
    refine .inl ⟨rfl, rfl, rfl, [], none, k, ?_, rfl, by simp [ReadEvAgree, hf], hk⟩
    rw [procSpec7_readv h65]
    simp only [readvSpec, hm, ite_false]
    exact ⟨by rw [← ebadf_eq]; rfl, trivial⟩
  | some e =>
    rw [hl] at hs hkind
    have hm : i.fd 0 ∈ k.fds := (hk.fds _ hlt).2 (by simp [hl])
    have nofile : (∀ p off, e ≠ .FdFile p off) → k.files.lookup (i.fd 0) = none := by
      intro hne
      cases h : k.files.lookup (i.fd 0) with
      | none => rfl
      | some f =>
        obtain ⟨p, hp, _⟩ := hk.files _ f h
        rw [hl] at hp; cases hp; exact absurd rfl (hne _ _)
    simp only at hs
    cases e with
    | FdChannel ch =>
      have hf := nofile (by intros; simp)
      have hch' : ch = i.fd 0 := hcid _ _ hl
      subst hch'
      simp only [readable_fd] at hs
      by_cases hz : w_is0 (i.fd 0) = true
      · rw [if_pos hz] at hs
        simp only at hs
        split at hs
        · cases hs
        replace hs := record_copyins_inv hs
        obtain ⟨e0, hs, rfl⟩ := hs
        left
        by_cases hbig : 1024 < (i.arg 2).toNat
        · rw [import_inval (by unfold bv_unsigned; omega)] at hs
          have hs' : Ok e0 m' e2 = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := hs
          cases hs'
          refine ⟨rfl, rfl, rfl, [], none, k, ?_, rfl, by simp [ReadEvAgree, hf], hk⟩
          rw [procSpec7_readv h65]
          simp only [readvSpec, hm, hbig, ite_true]
          exact ⟨by rw [errno_einval]; rfl, trivial⟩
        cases himp : import_iovecs j.in_mem (i.arg 1) (i.arg 2) with
        | ImpFault =>
          rw [himp] at hs
          have hs' : Ok e0 m' e2 = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := hs
          cases hs'
          rw [errno_efault]; exact readv_err_covered hk h65 hf hm hbig 14 (by omega) (by omega)
        | ImpInval =>
          rw [himp] at hs
          have hs' : Ok e0 m' e2 = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := hs
          cases hs'
          show ReadvCovered k i (mkEffect (errno_ret EINVAL) [] []) m []
          rw [errno_einval]; exact readv_err_covered hk h65 hf hm hbig 22 (by omega) (by omega)
        | ImpOk iovs0 =>
          rw [himp] at hs
          unfold readv_imported at hs
          simp only at hs
          have hv : iovs i.mem (i.arg 1) (i.arg 2).toNat = iovNat iovs0 := by
            rw [import_ok hmem himp, word_to_nat_eq, iovs_iovList]
          have htot : iovs_total (cap_iovecs iovs0) = min (iovTotal (iovNat iovs0) : Int) MAX_RW_COUNT := by
            unfold cap_iovecs; rw [total_cap _ _ (by decide), iovs_total_eq]
          split at hs
          · have hs' : Ok e0 m' e2 = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := hs
            cases hs'
            exact readv_ok_covered hk h65 hf hm hbig [] (Nat.zero_le _) (Nat.zero_le _) []
              (scatter_nil_filter _).symm
          cases hout : (m_stdin m).out with
          | none =>
            rw [hout] at hs
            have hs' : Ok e0 m' e2 = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := hs
            cases hs'
            exact readv_ok_covered hk h65 hf hm hbig [] (Nat.zero_le _) (Nat.zero_le _) []
              (scatter_nil_filter _).symm
          | some q =>
          rw [hout] at hs
          simp only at hs
          cases hsc1 : scatter_iovecs j.in_wmem (cap_iovecs iovs0) [Z_to_bv 8 0] with
          | none =>
            rw [hsc1] at hs
            have hs' : Ok e0 m' e2 = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := hs
            cases hs'
            rw [errno_efault]; exact readv_err_covered hk h65 hf hm hbig 14 (by omega) (by omega)
          | some _ =>
          rw [hsc1] at hs
          simp only at hs
          cases hsc2 : scatter_iovecs j.in_wmem (cap_iovecs iovs0)
              (stream_take_z (m_stdin m) (iovs_total (cap_iovecs iovs0))).1 with
          | none => rw [hsc2] at hs; cases hs
          | some _ =>
          rw [hsc2] at hs
          simp only at hs
          obtain ⟨bs, m2, e3, e4, ⟨bs', ⟨hb1, hb2, _, _⟩, hbeq⟩, hs, rfl⟩ := hs
          cases hbeq
          cases hw : scatter_iovecs j.in_wmem (cap_iovecs iovs0) bs with
          | some writes =>
            rw [hw] at hs
            simp only at hs
            obtain ⟨u, m3, e5, e6, hset, hs, rfl⟩ := hs
            cases hset
            obtain ⟨u, m4, e7, e8, hemit, hs, rfl⟩ := hs
            cases hemit
            have hs' : Ok e0 m' e8 = Ok (mkEffect (len_word bs) writes []) _ [] := hs
            cases hs'
            rw [htot] at hb2
            have hws := scatter_cap iovs0 MAX_RW_COUNT bs writes (by decide) (by omega) hw
            rw [← hv] at hws
            have := readv_ok_covered (m' := with_stdin (stream_take (m_stdin m) bs.length).2 m)
              ⟨hk.nodup, hk.small, hk.fds, hk.files⟩ h65 hf hm hbig bs
              (by rw [hv]; omega) (by unfold MAX_RW_COUNT at hb2; unfold NoCompiler.maxRW; omega) writes hws
            rw [len_word_eq]; simp only [List.nil_append, List.append_nil]; exact this
          | none =>
            rw [hw] at hs
            obtain ⟨_, hfalse, _⟩ := hs; exact hfalse.elim
      · rw [if_neg hz] at hs
        have hs' : Ok eff m' e2 = Ok (mkEffect (errno_ret EBADF) [] []) m [] := hs
        cases hs'
        have hc : ¬ 1024 < (i.arg 2).toNat := by
          have := hch _ hl (fun h => hz (by rw [h]; rfl)); omega
        left; rw [errno_ebadf]; exact readv_err_covered hk h65 hf hm hc 9 (by omega) (by omega)
    | FdFile p off =>
      obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 hkind
      obtain ⟨p', hp', hfs⟩ := hk.files _ f hf
      rw [hl] at hp'
      cases hp'
      have hfile : (k.files.lookup (i.fd 0)).isSome := by simp [hf]
      simp only [readable_fd] at hs
      split at hs
      · cases hs
      replace hs := record_copyins_inv hs
      obtain ⟨e0, hs, rfl⟩ := hs
      by_cases hbig : 1024 < (i.arg 2).toNat
      · rw [import_inval (by unfold bv_unsigned; omega)] at hs
        have hs' : Ok e0 m' e2 = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := hs
        cases hs'
        left
        refine ⟨rfl, rfl, rfl, [], none, k, ?_, rfl, by simp [ReadEvAgree, hf], hk⟩
        rw [procSpec7_readv h65]
        simp only [readvSpec, hm, hbig, ite_true]
        exact ⟨by rw [errno_einval]; rfl, trivial⟩
      cases himp : import_iovecs j.in_mem (i.arg 1) (i.arg 2) with
      | ImpFault =>
        rw [himp] at hs
        have hs' : Ok e0 m' e2 = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := hs
        cases hs'
        exact .inr ⟨hfile, rfl, rfl, rfl, rfl, .inl rfl⟩
      | ImpInval =>
        rw [himp] at hs
        have hs' : Ok e0 m' e2 = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := hs
        cases hs'
        exact .inr ⟨hfile, rfl, rfl, rfl, rfl, .inr rfl⟩
      | ImpOk iovs0 =>
        rw [himp] at hs
        unfold readv_imported at hs
        simp only at hs
        have hv : iovs i.mem (i.arg 1) (i.arg 2).toNat = iovNat iovs0 := by
          rw [import_ok hmem himp, word_to_nat_eq, iovs_iovList]
        have htot : iovs_total (cap_iovecs iovs0) = min (iovTotal (iovNat iovs0) : Int) MAX_RW_COUNT := by
          unfold cap_iovecs; rw [total_cap _ _ (by decide), iovs_total_eq]
        -- NoCompiler's outcome on the file
        have nc : ∀ (eff' : SyscallEffect) (m'' : Model) (ws : List (word × List byte)),
            eff'.eff_ret = BitVec.ofNat 64 (f.chunk (iovTotal (iovNat iovs0))).length →
            eff'.eff_writes = ws → eff'.eff_zeros = [] → eff'.eff_unmaps = [] → eff'.eff_copies = [] →
            ws = (scatter (iovNat iovs0) (f.chunk (iovTotal (iovNat iovs0)))).filter (fun p => !p.2.isEmpty) →
            KernFd (k.advance (i.fd 0) (f.chunk (iovTotal (iovNat iovs0))).length) m'' →
            ReadvCovered k i eff' m'' [] := by
          intro eff' m'' ws h1 h2 h3 h4 h5 h6 h7
          refine ⟨h3, h4, h5, scatter (iovNat iovs0) (f.chunk (iovTotal (iovNat iovs0))),
            some (.read (i.fd 0) (f.chunk (iovTotal (iovNat iovs0)))),
            k.advance (i.fd 0) (f.chunk (iovTotal (iovNat iovs0))).length, ?_, by rw [h2, h6],
            by simp [ReadEvAgree, hf], h7⟩
          rw [procSpec7_readv h65, h1]
          simp only [readvSpec, hm, hbig, hf, hv, ite_true, ite_false]
          exact ⟨trivial, rfl⟩
        split at hs
        · have hs' : Ok e0 m' e2 = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := hs
          cases hs'
          rename_i ht
          have h0 : iovTotal (iovNat iovs0) = 0 := by
            have := beq_iff_eq.1 ht; rw [htot] at this; unfold MAX_RW_COUNT at this; omega
          have hc0 : f.chunk (iovTotal (iovNat iovs0)) = [] := by
            rw [h0]; simp [OpenFile.chunk]
          left
          exact nc _ _ [] (by rw [hc0]; rfl) rfl rfl rfl rfl (by rw [hc0]; exact (scatter_nil_filter _).symm)
            (by rw [hc0]; exact kernfd_advance_zero hk _)
        rw [hfs] at hs
        simp only at hs
        split at hs
        · have hs' : Ok e0 m' e2 = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := hs
          cases hs'
          exact .inr ⟨hfile, rfl, rfl, rfl, rfl, .inr rfl⟩
        rw [htot, file_read_chunk_nat f _ (hoff f hf)] at hs
        have hcl : (f.chunk (iovTotal (iovNat iovs0))).length ≤ NoCompiler.maxRW := by
          simp only [OpenFile.chunk, List.length_take]; omega
        cases hw : scatter_iovecs j.in_wmem (cap_iovecs iovs0) (f.chunk (iovTotal (iovNat iovs0))) with
        | some writes =>
          rw [hw] at hs
          simp only at hs
          split at hs
          · cases hs
          obtain ⟨u, m3, e5, e6, hset, hs, rfl⟩ := hs
          cases hset
          have hs' : Ok e0 m' e6 = Ok (mkEffect (len_word (f.chunk (iovTotal (iovNat iovs0)))) writes []) _ [] := hs
          cases hs'
          left
          have hws := scatter_cap iovs0 MAX_RW_COUNT _ writes (by decide)
            (by unfold MAX_RW_COUNT; unfold NoCompiler.maxRW at hcl; omega) hw
          refine nc _ _ writes (len_word_eq _) rfl rfl rfl rfl hws ?_
          rw [len_word_eq]
          exact kernfd_advance hk hf hfs hm _
        | none =>
          rw [hw] at hs
          simp only at hs
          cases hz : scatter_iovecs j.in_wmem (cap_iovecs iovs0) [Z_to_bv 8 0] with
          | none =>
            rw [hz] at hs
            have hs' : Ok e0 m' e2 = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := hs
            cases hs'
            exact .inr ⟨hfile, rfl, rfl, rfl, rfl, .inl rfl⟩
          | some _ => rw [hz] at hs; cases hs
    | _ => exact hkind.elim

end LPS.Bridge

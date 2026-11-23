import LPS.Bridge.RefineIo

/-!
# Refinement, the converse direction: `read`

`read_covers`: every outcome LPS's `syscall_spec` admits for `read(fd, buf, count)` is one NoCompiler's model
(`procSpec7`: `fileReadOutcome` on a file in `k.files`, else `readSpec` on an open fd, else EBADF) allows, with
the same return, the same bytes stored (`ReadCovered`: NoCompiler's writes, empty ones dropped, are LPS's), the
events related (`ReadEvAgree`), and the kernels related (`KernFd`; on a file both offsets advance by the bytes
read).

The arms covered (`ReadKind`): a closed fd (EBADF on both sides); a channel (LPS's stdin, channel 0: some
nonempty prefix of the stream, or 0 at EOF or for `count = 0`, or EFAULT; another channel: EBADF); a file
NoCompiler has open (`k.files`; LPS's `FdFile` at the same offset: the same deterministic bytes); and the arms
where LPS's read is only an error (`FdFileW`, `FdFileA`: EBADF; `FdDir`: EFAULT or EISDIR), which NoCompiler,
with no file for such an fd, allows as `-n`. LPS's other arms (`FdFileRW`, pipes, sockets, /dev/null, urandom)
are excluded by `ReadKind` (`False` there), as is an LPS `FdFile` NoCompiler does not have in `k.files`: there
NoCompiler's `readSpec` logs a `read` event, LPS none.

Hypotheses of `read_covers`, and why:
- `hr`, `hk`: the inputs and the fd tables are related (`InRel`, `KernFd`).
- `hcid` (`ChanId`, as in `writev_covers`): a channel's id is its fd, so LPS's `ReadEv ch` is labelled by
  `fd32 a0 = i.fd 0`; NoCompiler's event carries all of `a0` (they agree through `fd32`, equal when a0 < 2^32).
- `hkind`: the fd kind, above.
- `hbuf`, on a file only: `access_ok(buf, count)` holds and the `min count MAX_RW_COUNT` bytes at `buf` are
  writable in LPS's `in_wmem`. NoCompiler's file read cannot fail (its memory is total), LPS's returns EFAULT
  for a bad buffer, as Linux does: there the models genuinely disagree.
- `hoff`, on a file only: its offset is below 2^64. `KernFd` relates NoCompiler's `Nat` offset to LPS's word
  offset modulo 2^64; LPS reads at the word.
No hypothesis on `count`: both models read all 64 bits. No memory agreement is needed: a read only stores.

Labels (`ReadEvAgree`): on a channel, NoCompiler's `read a0 ds` is LPS's `ds.map (ReadEv ch)` (for `ds = []`:
no LPS events); on a file, LPS logs no event (the bytes come from its file system state), NoCompiler logs
`read a0 ds` with `ds` the bytes stored (for `read`, always; `readv` with more than 1024 iovecs: EINVAL, no
event).
-/

namespace LPS.Bridge
open LPS.RiscvSemantics NoCompiler.Linux

theorem fd_lookup_insert (l : List (word × FdEntry)) (fd x : word) (e : FdEntry) :
    fd_lookup (fd_insert l fd e) x = if x = fd then some e else fd_lookup l x := by
  show fd_lookup ((fd, e) :: fd_remove l fd) x = _
  simp only [fd_lookup]
  by_cases hx : x = fd
  · subst hx; simp [bv_eqb_iff.2 rfl]
  · rw [bv_eqb_false (Ne.symm hx), fd_lookup_remove, if_neg hx, if_neg hx]; rfl

theorem lookup_map_off {l : List (NoCompiler.Word × OpenFile)} {fd x : NoCompiler.Word} {n : Nat} {f' : OpenFile}
    (h : (l.map fun p => if p.1 = fd then (p.1, { p.2 with off := p.2.off + n }) else p).lookup x = some f') :
    ∃ f, l.lookup x = some f ∧ f' = if x = fd then { f with off := f.off + n } else f := by
  induction l with
  | nil => simp at h
  | cons p r ih =>
    obtain ⟨q, g⟩ := p
    have hne : x ≠ q → (x == q) = false := fun hx => by simpa using hx
    by_cases hx : x = q
    · subst hx
      by_cases hq : x = fd
      · simp only [List.map_cons, hq, ite_true, List.lookup, beq_self_eq_true, Option.some.injEq] at h
        subst h hq; exact ⟨g, by simp, by simp⟩
      · simp only [List.map_cons, hq, ite_false, List.lookup, beq_self_eq_true, Option.some.injEq] at h
        subst h; exact ⟨g, by simp, by simp [hq]⟩
    · have h' : (r.map fun p => if p.1 = fd then (p.1, { p.2 with off := p.2.off + n }) else p).lookup x = some f' := by
        by_cases hq : q = fd
        · subst hq; simpa only [List.map_cons, ite_true, List.lookup, hne hx] using h
        · simpa only [List.map_cons, hq, ite_false, List.lookup, hne hx] using h
      obtain ⟨f, h1, h2⟩ := ih h'
      exact ⟨f, by simp only [List.lookup, hne hx]; exact h1, h2⟩

theorem lookup_advance {k : Kern} {fd x : NoCompiler.Word} {n : Nat} {f' : OpenFile}
    (h : (k.advance fd n).files.lookup x = some f') :
    ∃ f, k.files.lookup x = some f ∧ f' = if x = fd then { f with off := f.off + n } else f :=
  lookup_map_off h

theorem file_from_eq : ∀ (data : List byte) (n : Nat), file_from data n = data.drop n := by
  intro data
  induction data with
  | nil => intro n; simp [file_from]
  | cons b r ih =>
    intro n
    cases n with
    | zero => simp [file_from]
    | succ n =>
      simp only [file_from]
      rw [if_neg (by omega)]
      have : ((n + 1 : Nat) : Int) - 1 = (n : Int) := by omega
      rw [this, ih]; rfl

/-- LPS's file read at the offset NoCompiler's open file has is NoCompiler's chunk. -/
theorem file_read_chunk (f : OpenFile) (count : word) (h : f.off < 2 ^ 64) :
    file_read f.data (BitVec.ofNat 64 f.off) (Z_to_bv 64 (rw_count_clamp count)) = f.chunk count.toNat := by
  unfold file_read OpenFile.chunk
  have ho : bv_unsigned (BitVec.ofNat 64 f.off) = (f.off : Int) := by
    unfold bv_unsigned; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  simp only [ho, file_from_eq, word_to_nat_bounded_eq_min]
  have hc : word_to_nat (Z_to_bv 64 (rw_count_clamp count)) = min count.toNat NoCompiler.maxRW := by
    unfold word_to_nat rw_count_clamp MAX_RW_COUNT
    rw [bv_unsigned_Z_to_bv _ (by have := bv_unsigned_nonneg count; omega)
      (by have := bv_unsigned_lt count; omega)]
    unfold bv_unsigned NoCompiler.maxRW; omega
  rw [hc]
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, Nat.min_def]; split <;> (try split) <;> (try split) <;> omega
  · intro n h1 h2; simp

theorem read_bytes_aux_some (mp : word → Option byte) :
    ∀ n a, (∀ t < n, (mp (a + BitVec.ofNat 64 t)).isSome) → read_bytes_aux mp a n ≠ none := by
  intro n
  induction n with
  | zero => intro a _; simp [read_bytes_aux]
  | succ n ih =>
    intro a h
    simp only [read_bytes_aux]
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (by simpa using h 0 (by omega))
    rw [hb]
    have := ih (a + 1) (fun t ht => by
      have e : a + 1 + BitVec.ofNat 64 t = a + BitVec.ofNat 64 (t + 1) := by
        apply BitVec.eq_of_toNat_eq; simp; omega
      rw [e]; exact h (t + 1) (by omega))
    cases hr : read_bytes_aux mp (a + 1) n with
    | none => exact absurd hr this
    | some r => simp

theorem word_to_nat_len_word {A : Type} (l : List A) (h : l.length < 2 ^ 64) : word_to_nat (len_word l) = l.length := by
  unfold word_to_nat len_word
  rw [bv_unsigned_Z_to_bv _ (by omega) (by omega)]; simp

theorem read_bytes_map_some (mp : word → Option byte) (a : word) {A : Type} (l : List A) (h : l.length < 2 ^ 64)
    (hw : ∀ t < l.length, (mp (a + BitVec.ofNat 64 t)).isSome) : read_bytes_map mp a (len_word l) ≠ none := by
  rw [read_bytes_map_eq, word_to_nat_len_word l h]; exact read_bytes_aux_some mp _ a hw


/-! ### The read outcome relation -/

/-- What LPS's `read_spec` may do on `fd` that this file covers: a closed fd, a channel, a file NoCompiler
    has open in `k.files`, or an fd whose read is only an error (write-only and append files, a directory). -/
def ReadKind (k : Kern) (m : Model) (fd : word) : Prop :=
  match fd_lookup (m_fds m) fd with
  | none => True
  | some (.FdChannel _) => True
  | some (.FdFile _ _) => (k.files.lookup fd).isSome
  | some (.FdFileW _ _) => True
  | some (.FdFileA _ _) => True
  | some .FdDir => True
  | some _ => False

/-- The buffer can take what a read of `count` may deliver: LPS's `access_ok` and writable bytes. -/
def BufOk (j : SyscallInput) (buf count : word) : Prop :=
  access_okb buf (bv_unsigned count) = true ∧
    ∀ t < min count.toNat NoCompiler.maxRW, (j.in_wmem (buf + BitVec.ofNat 64 t)).isSome

/-- The labels: on a channel (or no read), NoCompiler's event `read a0 ds` is LPS's `ReadEv ch b`, `b ∈ ds`;
    on a file LPS logs nothing (the bytes are its file system's), NoCompiler logs `read a0 ds` (or nothing, on
    an error). -/
def ReadEvAgree (file : Bool) (a0 ch : word) (ev : Option NoCompiler.Event) (evs : List event) : Prop :=
  if file then evs = [] ∧ (ev = none ∨ ∃ ds, ev = some (.read a0 ds))
  else (ev = none ∧ evs = []) ∨ ∃ ds, ev = some (.read a0 ds) ∧ evs = ds.map (event.ReadEv ch)

/-- The conclusion of `read_covers`: NoCompiler's model allows the outcome with the same return, its writes
    the non-empty ones of LPS's, the events related, the kernels related. -/
def ReadCovered (k : Kern) (i : NoCompiler.Linux.SyscallInput) (eff : SyscallEffect) (m' : Model)
    (evs : List event) : Prop :=
  eff.eff_zeros = [] ∧ eff.eff_unmaps = [] ∧ eff.eff_copies = [] ∧ eff.eff_copyins = [] ∧
  ∃ ws ev k', procSpec7 k i (.ret { ret := eff.eff_ret, writes := ws } ev) k' ∧
    eff.eff_writes = ws.filter (fun p => !p.2.isEmpty) ∧
    ReadEvAgree (k.files.lookup (i.fd 0)).isSome (i.fd 0) (i.fd 0) ev evs ∧ KernFd k' m'

theorem files_mem {k : Kern} {m : Model} (hk : KernFd k m) {fd : NoCompiler.Word} {f : OpenFile}
    (h : k.files.lookup fd = some f) (hlt : fd.toNat < 2 ^ 32) : fd ∈ k.fds := by
  obtain ⟨p, hp, _⟩ := hk.files fd f h
  exact (hk.fds fd hlt).2 (by simp [hp])

/-- An error on an fd open in NoCompiler's table with no file: NoCompiler allows any `-n`. -/
theorem read_err_covered {k : Kern} {i : NoCompiler.Linux.SyscallInput} {m : Model} (hk : KernFd k m)
    (h63 : i.sysno = NoCompiler.sysRead) (hl : k.files.lookup (i.fd 0) = none) (hm : i.fd 0 ∈ k.fds)
    (n : Nat) (h1 : 1 ≤ n) (h2 : n ≤ 4095) :
    ReadCovered k i (mkEffect (-(BitVec.ofNat 64 n)) [] []) m [] := by
  refine ⟨rfl, rfl, rfl, rfl, [], none, k, ?_, rfl, ?_, hk⟩
  · rw [procSpec7_read h63 hl, if_pos hm]
    exact ⟨⟨rfl, .inr ⟨n, h1, h2, rfl, rfl, rfl⟩⟩, rfl⟩
  · simp [ReadEvAgree, hl]

/-- A read of `ds` on an fd open in NoCompiler's table with no file. -/
theorem read_ok_covered {k : Kern} {i : NoCompiler.Linux.SyscallInput} {m' : Model} (hk : KernFd k m')
    (h63 : i.sysno = NoCompiler.sysRead) (hl : k.files.lookup (i.fd 0) = none) (hm : i.fd 0 ∈ k.fds)
    (ds : List NoCompiler.Byte) (h1 : ds.length ≤ (i.arg 2).toNat) (h2 : ds.length ≤ NoCompiler.maxRW) :
    ReadCovered k i (mkEffect (BitVec.ofNat 64 ds.length) (delivered_writes (i.arg 1) ds) []) m'
      (ds.map (event.ReadEv (i.fd 0))) := by
  refine ⟨rfl, rfl, rfl, rfl, [(i.arg 1, ds)], some (.read (i.fd 0) ds), k, ?_, ?_, ?_, hk⟩
  · rw [procSpec7_read h63 hl, if_pos hm]
    exact ⟨⟨rfl, .inl ⟨ds, h1, h2, rfl, rfl, rfl⟩⟩, rfl⟩
  · cases ds <;> rfl
  · simp [ReadEvAgree, hl]

theorem len_word_eq {A : Type} (l : List A) : len_word l = BitVec.ofNat 64 l.length := by
  unfold len_word Z_to_bv; rw [BitVec.ofInt_natCast]

theorem errno_eisdir : errno_ret EISDIR = -(BitVec.ofNat 64 21) := by decide


/-- `read(fd, buf, count)`: every outcome LPS's `syscall_spec` admits, on the fds `ReadKind` allows, is one
    NoCompiler's model allows (`ReadCovered`); hypotheses in the module doc. -/
theorem read_covers {k : Kern} {i : NoCompiler.Linux.SyscallInput} {j : SyscallInput} {m m' : Model}
    {eff : SyscallEffect} {evs : List event} (hr : InRel i j) (h63 : i.sysno = NoCompiler.sysRead)
    (hk : KernFd k m) (hcid : ChanId m) (hkind : ReadKind k m (i.fd 0))
    (hbuf : (k.files.lookup (i.fd 0)).isSome → BufOk j (i.arg 1) (i.arg 2))
    (hoff : ∀ f, k.files.lookup (i.fd 0) = some f → f.off < 2 ^ 64)
    (hs : syscall_spec j m (Ok eff m' evs)) : ReadCovered k i eff m' evs := by
  have hn : bv_unsigned j.in_sysno = 63 := by rw [hr.sysno, h63]; rfl
  have hfd : fd32 (in_arg j 0) = i.fd 0 := by rw [hr.args 0, fd32_eq_fd]
  have hlt := fd_lt i 0
  rw [lookup_arm_of (a := mkSpecArm 63 (fun i => read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i))
    (by simp [spec_table, lookup_arm, mkSpecArm]) j hn] at hs
  change read_spec (fd32 (in_arg j 0)) (in_arg j 1) (in_arg j 2) j m (Ok eff m' evs) at hs
  unfold read_spec at hs
  obtain ⟨x, m1, e1, e2, h1, hs, rfl⟩ := hs
  cases h1
  rw [bind_get_model, hfd, hr.args 1, hr.args 2] at hs
  simp only [List.nil_append]
  unfold ReadKind at hkind
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
    refine ⟨rfl, rfl, rfl, rfl, [], none, k, ?_, rfl, by simp [ReadEvAgree, hf], hk⟩
    rw [procSpec7_read h63 hf, if_neg hm, ← ebadf_eq]; exact ⟨rfl, rfl⟩
  | some e =>
    rw [hl] at hs hkind
    have hm : i.fd 0 ∈ k.fds := (hk.fds _ hlt).2 (by simp [hl])
    -- an fd that is not a file in NoCompiler's table
    have nofile : (∀ p off, e ≠ .FdFile p off) → k.files.lookup (i.fd 0) = none := by
      intro hne
      cases h : k.files.lookup (i.fd 0) with
      | none => rfl
      | some f =>
        obtain ⟨p, hp, _⟩ := hk.files _ f h
        rw [hl] at hp; cases hp; exact absurd rfl (hne _ _)
    cases e with
    | FdFileW p off =>
      have hf := nofile (by intros; simp)
      have hs' : Ok eff m' e2 = Ok (mkEffect (errno_ret EBADF) [] []) m [] := hs
      cases hs'
      rw [errno_ebadf]; exact read_err_covered hk h63 hf hm 9 (by omega) (by omega)
    | FdFileA p off =>
      have hf := nofile (by intros; simp)
      have hs' : Ok eff m' e2 = Ok (mkEffect (errno_ret EBADF) [] []) m [] := hs
      cases hs'
      rw [errno_ebadf]; exact read_err_covered hk h63 hf hm 9 (by omega) (by omega)
    | FdDir =>
      have hf := nofile (by intros; simp)
      simp only at hs
      split at hs
      · have hs' : Ok eff m' e2 = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := hs
        cases hs'
        rw [errno_efault]; exact read_err_covered hk h63 hf hm 14 (by omega) (by omega)
      · have hs' : Ok eff m' e2 = Ok (mkEffect (errno_ret EISDIR) [] []) m [] := hs
        cases hs'
        rw [errno_eisdir]; exact read_err_covered hk h63 hf hm 21 (by omega) (by omega)
    | FdChannel ch =>
      have hf := nofile (by intros; simp)
      have hch : ch = i.fd 0 := hcid _ _ hl
      subst hch
      simp only at hs
      have zero : ∀ m'', KernFd k m'' → ReadCovered k i (mkEffect (Z_to_bv 64 0) [] []) m'' [] := fun m'' hk'' =>
        read_ok_covered hk'' h63 hf hm [] (Nat.zero_le _) (Nat.zero_le _)
      split at hs
      · have hs' : Ok eff m' e2 = Ok (mkEffect (errno_ret EBADF) [] []) m [] := hs
        cases hs'
        rw [errno_ebadf]; exact read_err_covered hk h63 hf hm 9 (by omega) (by omega)
      split at hs
      · have hs' : Ok eff m' e2 = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := hs
        cases hs'
        rw [errno_efault]; exact read_err_covered hk h63 hf hm 14 (by omega) (by omega)
      split at hs
      · have hs' : Ok eff m' e2 = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := hs
        cases hs'; exact zero m hk
      cases hout : (m_stdin m).out with
      | none =>
        rw [hout] at hs
        have hs' : Ok eff m' e2 = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := hs
        cases hs'; exact zero m hk
      | some q =>
      rw [hout] at hs
      simp only at hs
      cases hb1 : read_bytes_map j.in_wmem (i.arg 1) (Z_to_bv 64 1) with
      | none =>
        rw [hb1] at hs
        have hs' : Ok eff m' e2 = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := hs
        cases hs'
        rw [errno_efault]; exact read_err_covered hk h63 hf hm 14 (by omega) (by omega)
      | some _ =>
      rw [hb1] at hs
      simp only at hs
      cases hb2 : read_bytes_map j.in_wmem (i.arg 1) (len_word (stream_take_z (m_stdin m) (rw_count_clamp (i.arg 2))).1) with
      | none => rw [hb2] at hs; cases hs
      | some _ =>
      rw [hb2] at hs
      simp only at hs
      obtain ⟨bs, m2, e3, e4, ⟨bs', ⟨hb1, hb2, _, _⟩, hbeq⟩, hs, rfl⟩ := hs
      cases hbeq
      obtain ⟨u, m3, e5, e6, hset, hs, rfl⟩ := hs
      cases hset
      obtain ⟨u, m4, e7, e8, hemit, hs, rfl⟩ := hs
      cases hemit
      have hs' : Ok eff m' e8 = Ok (mkEffect (len_word bs) [(i.arg 1, bs)] []) _ [] := hs
      cases hs'
      have hbs : bs ≠ [] := by rintro rfl; simp at hb1
      have hdw : delivered_writes (i.arg 1) bs = [(i.arg 1, bs)] := by
        cases bs with
        | nil => exact absurd rfl hbs
        | cons _ _ => rfl
      have := read_ok_covered (m' := with_stdin (stream_take (m_stdin m) bs.length).2 m) ⟨hk.nodup, hk.small, hk.fds, hk.files⟩ h63 hf hm bs
        (by unfold rw_count_clamp bv_unsigned at hb2; omega)
        (by unfold rw_count_clamp MAX_RW_COUNT at hb2; unfold NoCompiler.maxRW; omega)
      rw [hdw] at this
      simpa [len_word_eq] using this
    | FdFile p off =>
      obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 hkind
      obtain ⟨p', hp', hfs⟩ := hk.files _ f hf
      rw [hl] at hp'
      cases hp'
      obtain ⟨hacc, hw⟩ := hbuf (by simp [hf])
      simp only at hs
      rw [if_neg (by simp [hacc])] at hs
      rw [hfs] at hs
      simp only at hs
      rw [file_read_chunk f (i.arg 2) (hoff f hf)] at hs
      have hcl : (f.chunk (i.arg 2).toNat).length ≤ min (i.arg 2).toNat NoCompiler.maxRW := by
        simp only [OpenFile.chunk, List.length_take]; omega
      have hml : NoCompiler.maxRW < 2 ^ 64 := by decide
      have hrb := read_bytes_map_some j.in_wmem (i.arg 1) (f.chunk (i.arg 2).toNat) (by omega)
        (fun t ht => hw t (by omega))
      cases hb : read_bytes_map j.in_wmem (i.arg 1) (len_word (f.chunk (i.arg 2).toNat)) with
      | none => exact absurd hb hrb
      | some _ =>
      rw [hb] at hs
      simp only at hs
      obtain ⟨u, m3, e5, e6, hset, hs, rfl⟩ := hs
      cases hset
      have hs' : Ok eff m' e6 = Ok (mkEffect (len_word (f.chunk (i.arg 2).toNat))
        (delivered_writes (i.arg 1) (f.chunk (i.arg 2).toNat)) []) _ [] := hs
      cases hs'
      refine ⟨rfl, rfl, rfl, rfl, [(i.arg 1, f.chunk (i.arg 2).toNat)],
        some (.read (i.fd 0) (f.chunk (i.arg 2).toNat)),
        k.advance (i.fd 0) (f.chunk (i.arg 2).toNat).length, ?_, ?_, ?_, ?_⟩
      · rw [procSpec7_read_file h63 hf]
        refine ⟨?_, rfl⟩
        simp only [fileReadOutcome, len_word_eq]; rfl
      · cases f.chunk (i.arg 2).toNat <;> rfl
      · simp [ReadEvAgree, hf]
      · refine ⟨hk.nodup, hk.small, fun fd hfd' => ?_, fun fd g hg => ?_⟩
        · show fd ∈ k.fds ↔ (fd_lookup (fd_insert (m_fds m) (i.fd 0) _) fd).isSome
          rw [fd_lookup_insert]
          by_cases hx : fd = i.fd 0
          · subst hx; simp [hm]
          · rw [if_neg hx]; exact hk.fds fd hfd'
        · obtain ⟨g0, hg0, rfl⟩ := lookup_advance hg
          show ∃ p, fd_lookup (fd_insert (m_fds m) (i.fd 0) _) fd = _ ∧ fs_lookup (m_fs m) p = _
          rw [fd_lookup_insert]
          by_cases hx : fd = i.fd 0
          · subst hx
            rw [hf] at hg0; cases hg0
            refine ⟨p, ?_, by simpa using hfs⟩
            simp only [ite_true, Option.some.injEq, FdEntry.FdFile.injEq, true_and]
            rw [len_word_eq]; apply BitVec.eq_of_toNat_eq; simp
          · simp only [hx, ite_false]; exact hk.files fd g0 hg0
    | _ => exact hkind.elim

end LPS.Bridge

import LPS.Bridge.RefineFd
import LPS.Checks.Sys.Prelude

/-!
# Refinement, the converse direction: `writev`

`writev_covers`: every outcome LPS's `syscall_spec` admits for `writev(fd, iov, n)` is one NoCompiler's model
(`procSpec7`, `writevSpec`) allows, with the same return, no memory writes, and the same output: LPS's
per-byte `WriteEv ch b` events are NoCompiler's one `write` event's bytes.

What the two models share, under `MemAgree` (a byte LPS can read is NoCompiler's byte there):

- the iovecs LPS imports (`import_iovecs`, on success) are NoCompiler's `(read64 iov+16j, read64 iov+16j+8)`,
  `j < n` (`import_ok`);
- LPS's gathered bytes (`writev_gathered`: the readable prefix of the iovecs capped at `MAX_RW_COUNT`) are a
  prefix of NoCompiler's `gather` and at most `MAX_RW_COUNT` (= `maxRW`) long (`gather_prefix_cap`, `gather_iovList`), so the
  prefix `ds` LPS writes is `(gather ..).take ds.length`;
- LPS's errors (EBADF, EFAULT, EINVAL) are among NoCompiler's `-n`, `1 ≤ n ≤ 4095`; with more than 1024
  iovecs both give exactly EINVAL.

Labels: NoCompiler's event is `.write (i.fd 0) bs` (a0's low 32 bits, user decision (6)); LPS's are
`WriteEv ch b` with `ch` the channel of fd `fd32 a0 = i.fd 0`. Under `ChanId` (a channel's id is its fd number,
as in LPS's initial table) `ch = i.fd 0`: the two labels are equal.
-/

namespace LPS.Bridge
open LPS.RiscvSemantics NoCompiler.Linux

/-- Memory: every byte LPS's syscall input can read is NoCompiler's byte at that address. -/
def MemAgree (i : NoCompiler.Linux.SyscallInput) (j : SyscallInput) : Prop :=
  ∀ a b, j.in_mem a = some b → i.mem a = b

/-- Every output channel in LPS's fd table is labelled by its fd (true of LPS's initial table, fds 0..2). -/
def ChanId (m : Model) : Prop := ∀ fd ch, fd_lookup (m_fds m) fd = some (.FdChannel ch) → ch = fd

/-! ### Memory reads -/

section Mem
variable {M : NoCompiler.Word → NoCompiler.Byte} {mp : word → Option byte}

theorem read_bytes_aux_agree (h : ∀ a b, mp a = some b → M a = b) :
    ∀ n a bs, read_bytes_aux mp a n = some bs → bs = NoCompiler.readBytes M a n := by
  intro n
  induction n with
  | zero => intro a bs hb; simp only [read_bytes_aux, Option.some.injEq] at hb; subst hb; rfl
  | succ n ih =>
    intro a bs hb
    simp only [read_bytes_aux] at hb
    cases hm : mp a with
    | none => rw [hm] at hb; cases hb
    | some b =>
      rw [hm] at hb
      cases hr : read_bytes_aux mp (a + 1) n with
      | none => rw [hr] at hb; cases hb
      | some r =>
        rw [hr] at hb
        simp only [Option.some.injEq] at hb
        subst hb
        simp only [NoCompiler.readBytes, h a b hm, ih _ _ hr]

theorem read_u64_agree (h : ∀ a b, mp a = some b → M a = b) {a w : word} (hr : read_u64 mp a = some w) :
    w = NoCompiler.read64 M a := by
  unfold read_u64 at hr
  rw [read_bytes_map_eq] at hr
  cases hb : read_bytes_aux mp a (word_to_nat (Z_to_bv 64 8)) with
  | none => rw [hb] at hr; cases hr
  | some bs =>
    rw [hb] at hr
    simp only [Option.some.injEq] at hr
    subst hr
    have h8 : word_to_nat (Z_to_bv 64 8) = 8 := by decide
    rw [h8] at hb
    rw [read_bytes_aux_agree h _ _ _ hb]
    unfold le_bytes_to_word NoCompiler.read64
    rw [bytes_le_to_Z_readBytes]
    unfold Z_to_bv
    rw [BitVec.ofInt_natCast]

theorem read_iovec_entry_agree (h : ∀ a b, mp a = some b → M a = b) {a base len : word}
    (he : read_iovec_entry mp a = .IovEntry base len) : base = NoCompiler.read64 M a ∧ len = NoCompiler.read64 M (a + 8) := by
  unfold read_iovec_entry at he
  cases h1 : read_u64 mp a with
  | none => rw [h1] at he; cases he
  | some b1 =>
    cases h2 : read_u64 mp (a + 8) with
    | none => rw [h1, h2] at he; cases he
    | some b2 =>
      rw [h1, h2] at he
      simp only at he
      split at he
      · cases he
      · cases he; exact ⟨read_u64_agree h h1, read_u64_agree h h2⟩

/-- The `n` iovecs at `a`, as NoCompiler reads them. -/
def iovList (M : NoCompiler.Word → NoCompiler.Byte) (a : NoCompiler.Word) : Nat → List (word × word)
  | 0 => []
  | n + 1 => (NoCompiler.read64 M a, NoCompiler.read64 M (a + 8)) :: iovList M (a + 16) n

/-- The bytes the iovecs `iovs` describe, in order. -/
def gatherIovs (M : NoCompiler.Word → NoCompiler.Byte) (iovs : List (word × word)) : List NoCompiler.Byte :=
  iovs.flatMap fun p => NoCompiler.readBytes M p.1 p.2.toNat

theorem copy_iovecs_aux_agree (h : ∀ a b, mp a = some b → M a = b) :
    ∀ n a r, copy_iovecs_aux mp a n = .ImpOk r → r = iovList M a n := by
  intro n
  induction n with
  | zero => intro a r hr; simp only [copy_iovecs_aux, iov_import.ImpOk.injEq] at hr; subst hr; rfl
  | succ n ih =>
    intro a r hr
    simp only [copy_iovecs_aux] at hr
    cases he : read_iovec_entry mp a with
    | IovFault => rw [he] at hr; cases hr
    | IovInval => rw [he] at hr; cases hr
    | IovEntry base len =>
      rw [he] at hr
      simp only at hr
      cases hc : copy_iovecs_aux mp (a + 16) n with
      | ImpFault => rw [hc] at hr; cases hr
      | ImpInval => rw [hc] at hr; cases hr
      | ImpOk r' =>
        rw [hc] at hr
        simp only [iov_import.ImpOk.injEq] at hr
        subst hr
        obtain ⟨rfl, rfl⟩ := read_iovec_entry_agree h he
        rw [ih _ _ hc]; rfl

theorem bv_eqb_false {a b : word} (h : a ≠ b) : bv_eqb a b = false := by
  cases hb : bv_eqb a b
  · rfl
  · exact absurd (bv_eqb_iff.1 hb) h

/-- An import that succeeds reads NoCompiler's iovecs. -/
theorem import_ok (h : ∀ a b, mp a = some b → M a = b) {a n : word} {iovs : List (word × word)}
    (hi : import_iovecs mp a n = .ImpOk iovs) : iovs = iovList M a (word_to_nat n) := by
  unfold import_iovecs at hi
  by_cases h1 : n = Z_to_bv 64 1
  · subst h1
    rw [if_pos (bv_eqb_iff.2 rfl)] at hi
    have hw : word_to_nat (Z_to_bv 64 1) = 1 := by decide
    rw [hw]
    split at hi
    · cases hi
    · cases he : read_iovec_entry mp a with
      | IovFault => rw [he] at hi; cases hi
      | IovInval => rw [he] at hi; cases hi
      | IovEntry base len =>
        rw [he] at hi
        simp only at hi
        split at hi
        · cases hi
        · cases hi
          obtain ⟨rfl, rfl⟩ := read_iovec_entry_agree h he
          rfl
  · rw [if_neg (by rw [bv_eqb_false h1]; simp)] at hi
    by_cases h0 : n = Z_to_bv 64 0
    · subst h0
      rw [if_pos (bv_eqb_iff.2 rfl)] at hi
      cases hi; rfl
    · rw [if_neg (by rw [bv_eqb_false h0]; simp)] at hi
      split at hi
      · cases hi
      split at hi
      · cases hi
      cases hc : copy_iovecs_aux mp a (word_to_nat n) with
      | ImpFault => rw [hc] at hi; cases hi
      | ImpInval => rw [hc] at hi; cases hi
      | ImpOk r =>
        rw [hc] at hi
        simp only at hi
        split at hi
        · cases hi; exact copy_iovecs_aux_agree h _ _ _ hc
        · cases hi

/-- More than `IOV_MAX` iovecs: EINVAL. -/
theorem import_inval {a n : word} (hn : 1024 < bv_unsigned n) : import_iovecs mp a n = .ImpInval := by
  unfold import_iovecs
  have h1 : n ≠ Z_to_bv 64 1 := by rintro rfl; revert hn; decide
  have h0 : n ≠ Z_to_bv 64 0 := by rintro rfl; revert hn; decide
  rw [bv_eqb_false h1, bv_eqb_false h0]
  have : IOV_MAX < bv_unsigned n := by unfold IOV_MAX; exact hn
  simp [this]

end Mem

/-! ### Gathering -/

section Gather
variable {M : NoCompiler.Word → NoCompiler.Byte} {mp : word → Option byte}

theorem readBytes_prefix (a : NoCompiler.Word) {n N : Nat} (h : n ≤ N) :
    NoCompiler.readBytes M a n <+: NoCompiler.readBytes M a N := by
  rw [← readBytes_take' M a N n h]; exact List.take_prefix _ _

theorem readable_aux_prefix (h : ∀ a b, mp a = some b → M a = b) :
    ∀ n a, readable_bytes_aux mp a n <+: NoCompiler.readBytes M a n := by
  intro n
  induction n with
  | zero => intro a; exact List.prefix_refl _
  | succ n ih =>
    intro a
    simp only [readable_bytes_aux, NoCompiler.readBytes]
    cases hm : mp a with
    | none => exact List.nil_prefix
    | some b => rw [h a b hm]; exact List.cons_prefix_cons.2 ⟨rfl, ih _⟩

theorem bv_unsigned_Z_to_bv (z : Int) (h0 : 0 ≤ z) (h1 : z < 2 ^ 64) : bv_unsigned (Z_to_bv 64 z) = z := by
  unfold bv_unsigned Z_to_bv
  rw [BitVec.toNat_ofInt]
  have : z % ((2 ^ 64 : Nat) : Int) = z := Int.emod_eq_of_lt h0 (by simpa using h1)
  rw [this]; omega

theorem bv_unsigned_nonneg (w : word) : 0 ≤ bv_unsigned w := by unfold bv_unsigned; omega
theorem bv_unsigned_lt (w : word) : bv_unsigned w < 2 ^ 64 := by
  unfold bv_unsigned; have := w.isLt; omega

theorem gather_prefix_cap_zero : ∀ iovs, gather_prefix mp (cap_iovecs_aux iovs 0) = [] := by
  intro iovs
  induction iovs with
  | nil => rfl
  | cons p r ih =>
    obtain ⟨base, len⟩ := p
    have hm : min (0 : Int) (bv_unsigned len) = 0 := by have := bv_unsigned_nonneg len; omega
    simp only [cap_iovecs_aux, hm, Int.sub_zero, gather_prefix]
    rw [readable_bytes_eq]
    have hw : word_to_nat (Z_to_bv 64 0) = 0 := by decide
    rw [hw]
    simp [readable_bytes_aux, ih]

/-- LPS's gathered bytes, from iovecs capped at `left`, are a prefix of the bytes the iovecs describe, and
    at most `left` long. -/
theorem gather_prefix_cap (h : ∀ a b, mp a = some b → M a = b) :
    ∀ iovs (left : Int), 0 ≤ left →
      gather_prefix mp (cap_iovecs_aux iovs left) <+: gatherIovs M iovs ∧
      ((gather_prefix mp (cap_iovecs_aux iovs left)).length : Int) ≤ left := by
  intro iovs
  induction iovs with
  | nil => intro left hl; exact ⟨List.nil_prefix, by simp [cap_iovecs_aux, gather_prefix]; exact hl⟩
  | cons p r ih =>
    intro left hl
    obtain ⟨base, len⟩ := p
    have hl0 := bv_unsigned_nonneg len
    have hl1 := bv_unsigned_lt len
    have hn : bv_unsigned (Z_to_bv 64 (min left (bv_unsigned len))) = min left (bv_unsigned len) :=
      bv_unsigned_Z_to_bv _ (by omega) (by omega)
    have hw : word_to_nat (Z_to_bv 64 (min left (bv_unsigned len))) = (min left (bv_unsigned len)).toNat := by
      unfold word_to_nat; rw [hn]
    simp only [cap_iovecs_aux, gather_prefix]
    rw [readable_bytes_eq, hw, hn]
    have hpre : readable_bytes_aux mp base (min left (bv_unsigned len)).toNat <+:
        NoCompiler.readBytes M base len.toNat :=
      (readable_aux_prefix h _ base).trans (readBytes_prefix base (by unfold bv_unsigned at *; omega))
    have hg : gatherIovs M ((base, len) :: r) = NoCompiler.readBytes M base len.toNat ++ gatherIovs M r := by
      simp [gatherIovs]
    rw [hg]
    have hlen := (readable_aux_prefix (M := M) h (min left (bv_unsigned len)).toNat base).length_le
    rw [readBytes_length''] at hlen
    split
    · rename_i heq
      by_cases hc : min left (bv_unsigned len) = bv_unsigned len
      · -- the whole buffer read
        have heq' : readable_bytes_aux mp base (min left (bv_unsigned len)).toNat =
            NoCompiler.readBytes M base len.toNat := by
          apply hpre.eq_of_length
          rw [readBytes_length'']; unfold bv_unsigned at *; omega
        rw [heq']
        obtain ⟨ih1, ih2⟩ := ih (left - min left (bv_unsigned len)) (by omega)
        refine ⟨List.prefix_append_right_inj _ |>.2 ih1, ?_⟩
        rw [List.length_append, readBytes_length'']
        unfold bv_unsigned at *; omega
      · -- the cap reached
        have h0 : left - min left (bv_unsigned len) = 0 := by omega
        rw [h0, gather_prefix_cap_zero, List.append_nil]
        exact ⟨hpre.trans (List.prefix_append _ _), by omega⟩
    · exact ⟨hpre.trans (List.prefix_append _ _), by omega⟩

theorem iovs_total_nonneg : ∀ iovs : List (word × word), 0 ≤ iovs_total iovs := by
  intro iovs
  induction iovs with
  | nil => simp [iovs_total]
  | cons p r ih => simp only [iovs_total]; have := bv_unsigned_nonneg p.2; omega

/-- Capped iovecs of total length 0 describe no bytes. -/
theorem total_zero : ∀ iovs (left : Int), 0 < left → iovs_total (cap_iovecs_aux iovs left) = 0 →
    gatherIovs M iovs = [] := by
  intro iovs
  induction iovs with
  | nil => intro _ _ _; rfl
  | cons p r ih =>
    intro left hl ht
    obtain ⟨base, len⟩ := p
    have hl0 := bv_unsigned_nonneg len
    have hl1 := bv_unsigned_lt len
    simp only [cap_iovecs_aux, iovs_total] at ht
    rw [bv_unsigned_Z_to_bv _ (by omega) (by omega)] at ht
    have := iovs_total_nonneg (cap_iovecs_aux r (left - min left (bv_unsigned len)))
    have hz : bv_unsigned len = 0 := by omega
    have hz' : len.toNat = 0 := by unfold bv_unsigned at hz; omega
    have hm : left - min left (bv_unsigned len) = left := by omega
    rw [hm] at ht
    simp only [gatherIovs, List.flatMap_cons, hz', NoCompiler.readBytes, List.nil_append]
    exact ih left hl (by omega)

theorem iovBuf_succ (a : NoCompiler.Word) (j : Nat) : iovBuf M a (j + 1) = iovBuf M (a + 16) j := by
  unfold iovBuf
  have h16 : (16 : BitVec 64).toNat = 16 := rfl
  have e1 : a + BitVec.ofNat 64 (16 * (j + 1)) = a + 16 + BitVec.ofNat 64 (16 * j) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h16]; omega
  have e2 : a + BitVec.ofNat 64 (16 * (j + 1) + 8) = a + 16 + BitVec.ofNat 64 (16 * j + 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h16]; omega
  rw [e1, e2]

theorem gather_succ (a : NoCompiler.Word) (n : Nat) :
    gather M a (n + 1) = iovBuf M a 0 ++ gather M (a + 16) n := by
  simp only [gather, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, iovBuf_succ]

theorem gather_iovList (a : NoCompiler.Word) : ∀ n, gather M a n = gatherIovs M (iovList M a n) := by
  intro n
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [gather_succ, ih]
    simp [iovList, gatherIovs, iovBuf]

theorem iovcnt32_eq (w : word) (h : w.toNat < 2 ^ 32) : iovcnt32 w = w := by
  unfold iovcnt32 abi_low32 Z.modulo bv_unsigned Z_to_bv
  rw [Int.fmod_eq_emod_of_nonneg _ (by omega), Int.emod_eq_of_lt (by omega) (by omega),
    BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end Gather

/-! ### The two specs -/

theorem record_copyins_inv {reads : List (word × Nat)} {spec : Sys SyscallEffect} {j : SyscallInput}
    {m m' : Model} {eff : SyscallEffect} {evs : List event} (h : record_copyins reads spec j m (Ok eff m' evs)) :
    ∃ e0, spec j m (Ok e0 m' evs) ∧ eff = with_copyins (reads ++ e0.eff_copyins) e0 := by
  obtain ⟨x, m1, e1, e2, h1, h2, rfl⟩ := h
  have h2' : Ok eff m' e2 = Ok (with_copyins (reads ++ x.eff_copyins) x) m1 [] := h2
  cases h2'
  exact ⟨x, by simpa using h1, rfl⟩

theorem errno_ebadf : errno_ret EBADF = -(BitVec.ofNat 64 9) := by decide
theorem errno_efault : errno_ret EFAULT = -(BitVec.ofNat 64 14) := by decide
theorem errno_einval : errno_ret EINVAL = einval := by decide

/-- NoCompiler's errors on an open fd with at most 1024 iovecs: any `-n`, `1 ≤ n ≤ 4095`. -/
theorem nc_err {k : Kern} {i : NoCompiler.Linux.SyscallInput} (h66 : i.sysno = sysWritev) (hm : i.fd 0 ∈ k.fds)
    (hc : ¬ 1024 < (i.arg 2).toNat) (n : Nat) (h1 : 1 ≤ n) (h2 : n ≤ 4095) :
    procSpec7 k i (.ret { ret := -(BitVec.ofNat 64 n) } none) k := by
  rw [procSpec7_writev h66]
  refine ⟨rfl, ?_⟩
  rw [if_pos hm, if_neg hc]
  exact ⟨rfl, rfl, .inr ⟨n, h1, h2, rfl, rfl⟩⟩

/-- NoCompiler's writes on an open fd with at most 1024 iovecs: `r` bytes of the gathered ones. -/
theorem nc_write {k : Kern} {i : NoCompiler.Linux.SyscallInput} (h66 : i.sysno = sysWritev) (hm : i.fd 0 ∈ k.fds)
    (hc : ¬ 1024 < (i.arg 2).toNat) (r : Nat) (h1 : r ≤ (gather i.mem (i.arg 1) (i.arg 2).toNat).length)
    (h2 : r ≤ NoCompiler.maxRW) (h3 : 0 < (gather i.mem (i.arg 1) (i.arg 2).toNat).length → 0 < r) :
    procSpec7 k i (.ret { ret := BitVec.ofNat 64 r }
      (some (.write (i.fd 0) ((gather i.mem (i.arg 1) (i.arg 2).toNat).take r)))) k := by
  rw [procSpec7_writev h66]
  refine ⟨rfl, ?_⟩
  rw [if_pos hm, if_neg hc]
  exact ⟨rfl, rfl, .inl ⟨r, h1, h2, h3, rfl, rfl⟩⟩

/-- An LPS effect with no memory side but the bytes it read (`eff_copyins`). -/
def PlainEff (eff : SyscallEffect) : Prop :=
  eff.eff_writes = [] ∧ eff.eff_zeros = [] ∧ eff.eff_unmaps = [] ∧ eff.eff_copies = []

/-- NoCompiler's event (labelled `a0`) and LPS's events (labelled `ch`) record the same output: none, or the
    bytes `bs`, one `WriteEv` each. -/
def EvAgree (a0 ch : word) (ev : Option NoCompiler.Event) (evs : List event) : Prop :=
  (ev = none ∧ evs = []) ∨ ∃ bs, ev = some (.write a0 bs) ∧ evs = bs.map (event.WriteEv ch)

/-- `writev(fd, iov, n)`, the call musl's stdio makes: every outcome LPS's `syscall_spec` admits, on a closed fd
    or an fd LPS has as an output channel, is one NoCompiler's model allows, with the same return, no memory
    effect (LPS's `eff_copyins` is its read ledger, which NoCompiler does not track), the kernels unchanged,
    and the same output (`EvAgree`: NoCompiler's `write (fd32 a0) bs` is LPS's `WriteEv (fd32 a0) b`, `b ∈ bs`).

    Hypotheses: `hmem`, the bytes LPS reads are NoCompiler's; `hcid` (an invariant of LPS's runs from its
    initial table) and `hchan`, the fd is closed or a channel labelled by its number: LPS's other arms
    (files, pipes, /dev/null, sockets) are not covered; `hcnt`, `n < 2^32`: LPS reads the count's low 32
    bits (`iovcnt32`), NoCompiler all 64; `h0`, LPS's channel 0 (stdin) refuses writes with EBADF, which
    NoCompiler allows only for at most 1024 iovecs (above, NoCompiler's only outcome is EINVAL). -/
theorem writev_covers {k : Kern} {i : NoCompiler.Linux.SyscallInput} {j : SyscallInput} {m m' : Model}
    {eff : SyscallEffect} {evs : List event} (hr : InRel i j) (h66 : i.sysno = sysWritev) (hk : KernFd k m)
    (hmem : MemAgree i j) (hcid : ChanId m)
    (hchan : ∀ e, fd_lookup (m_fds m) (i.fd 0) = some e → ∃ ch, e = .FdChannel ch)
    (hcnt : (i.arg 2).toNat < 2 ^ 32) (h0 : i.fd 0 = 0 → (i.arg 2).toNat ≤ 1024)
    (hs : syscall_spec j m (Ok eff m' evs)) :
    m' = m ∧ PlainEff eff ∧
      ∃ ev, procSpec7 k i (.ret { ret := eff.eff_ret } ev) k ∧ EvAgree (i.fd 0) (i.fd 0) ev evs := by
  have hn : bv_unsigned j.in_sysno = 66 := by rw [hr.sysno, h66]; rfl
  have hfd : fd32 (in_arg j 0) = i.fd 0 := by rw [hr.args 0, fd32_eq_fd]
  have hlt := fd_lt i 0
  rw [lookup_arm_of (a := mkSpecArm 66 (fun i => writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i))
    (by simp [spec_table, lookup_arm, mkSpecArm]) j hn] at hs
  change writev_spec (fd32 (in_arg j 0)) (in_arg j 1) (in_arg j 2) j m (Ok eff m' evs) at hs
  unfold writev_spec at hs
  obtain ⟨x, m1, e1, e2, h1, hs, rfl⟩ := hs
  cases h1
  rw [bind_get_model, hfd, hr.args 1, hr.args 2, iovcnt32_eq _ hcnt] at hs
  simp only [List.nil_append]
  cases hl : fd_lookup (m_fds m) (i.fd 0) with
  | none =>
    rw [hl] at hs
    have hs' : Ok eff m' e2 = Ok (mkEffect (errno_ret EBADF) [] []) m [] := hs
    cases hs'
    have hm : i.fd 0 ∉ k.fds := fun h => by have := (hk.fds _ hlt).1 h; simp [hl] at this
    refine ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, none, ?_, .inl ⟨rfl, rfl⟩⟩
    rw [procSpec7_writev h66]
    exact ⟨rfl, by rw [if_neg hm, ebadf_eq]; rfl⟩
  | some e =>
    obtain ⟨ch, rfl⟩ := hchan e hl
    have hch : ch = i.fd 0 := hcid _ _ hl
    subst hch
    have hm : i.fd 0 ∈ k.fds := (hk.fds _ hlt).2 (by simp [hl])
    rw [hl] at hs
    simp only at hs
    by_cases hz : w_is0 (i.fd 0) = true
    · rw [if_pos hz] at hs
      have hs' : Ok eff m' e2 = Ok (mkEffect (errno_ret EBADF) [] []) m [] := hs
      cases hs'
      have hc : ¬ 1024 < (i.arg 2).toNat := by
        have := h0 (bv_eqb_iff.1 hz); omega
      refine ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, none, ?_, .inl ⟨rfl, rfl⟩⟩
      show procSpec7 k i (.ret { ret := errno_ret EBADF } none) k
      rw [errno_ebadf]; exact nc_err h66 hm hc 9 (by omega) (by omega)
    · rw [if_neg hz] at hs
      replace hs := record_copyins_inv hs
      obtain ⟨e0, hs, rfl⟩ := hs
      by_cases hbig : 1024 < (i.arg 2).toNat
      · rw [import_inval (by unfold bv_unsigned; omega)] at hs
        have hs' : Ok e0 m' e2 = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := hs
        cases hs'
        refine ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, none, ?_, .inl ⟨rfl, rfl⟩⟩
        show procSpec7 k i (.ret { ret := errno_ret EINVAL } none) k
        rw [procSpec7_writev h66]
        exact ⟨rfl, by rw [if_pos hm, if_pos hbig, errno_einval]⟩
      cases himp : import_iovecs j.in_mem (i.arg 1) (i.arg 2) with
      | ImpFault =>
        rw [himp] at hs
        have hs' : Ok e0 m' e2 = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := hs
        cases hs'
        refine ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, none, ?_, .inl ⟨rfl, rfl⟩⟩
        show procSpec7 k i (.ret { ret := errno_ret EFAULT } none) k
        rw [errno_efault]; exact nc_err h66 hm hbig 14 (by omega) (by omega)
      | ImpInval =>
        rw [himp] at hs
        have hs' : Ok e0 m' e2 = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := hs
        cases hs'
        refine ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, none, ?_, .inl ⟨rfl, rfl⟩⟩
        show procSpec7 k i (.ret { ret := errno_ret EINVAL } none) k
        rw [errno_einval]; exact nc_err h66 hm hbig 22 (by omega) (by omega)
      | ImpOk iovs0 =>
        rw [himp] at hs
        simp only at hs
        have hg : gather i.mem (i.arg 1) (i.arg 2).toNat = gatherIovs i.mem iovs0 := by
          rw [import_ok hmem himp, gather_iovList]; rfl
        obtain ⟨hpre, hcap⟩ := gather_prefix_cap hmem iovs0 MAX_RW_COUNT (by decide)
        change writev_gathered j.in_mem iovs0 <+: _ at hpre
        change ((writev_gathered j.in_mem iovs0).length : Int) ≤ _ at hcap
        by_cases ht : (iovs_total (cap_iovecs iovs0) == 0) = true
        · rw [if_pos ht] at hs
          have hs' : Ok e0 m' e2 = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := hs
          cases hs'
          have hz : gather i.mem (i.arg 1) (i.arg 2).toNat = [] := by
            rw [hg]; exact total_zero iovs0 MAX_RW_COUNT (by decide) (by simpa [cap_iovecs] using ht)
          refine ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, some (.write (i.fd 0) []), ?_, .inr ⟨[], rfl, rfl⟩⟩
          have := nc_write h66 hm hbig 0 (Nat.zero_le _) (by decide) (by rw [hz]; simp)
          rw [hz] at this; exact this
        rw [if_neg ht] at hs
        by_cases hb0 : ((writev_gathered j.in_mem iovs0).length == 0) = true
        · rw [if_pos hb0] at hs
          have hs' : Ok e0 m' e2 = Ok (mkEffect (errno_ret EFAULT) [] []) m [] := hs
          cases hs'
          refine ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, none, ?_, .inl ⟨rfl, rfl⟩⟩
          show procSpec7 k i (.ret { ret := errno_ret EFAULT } none) k
          rw [errno_efault]; exact nc_err h66 hm hbig 14 (by omega) (by omega)
        rw [if_neg hb0] at hs
        by_cases hae : addr_is_error_b (len_word (writev_gathered j.in_mem iovs0)) = true
        · rw [if_pos hae] at hs
          have : Ok e0 m' e2 = Unmodeled := hs
          cases this
        rw [if_neg hae] at hs
        obtain ⟨ds, m2, e3, e4, ⟨ds', ⟨hd1, hd2, hd3, hd4⟩, hdeq⟩, hs, rfl⟩ := hs
        cases hdeq
        obtain ⟨u, m3, e5, e6, hemit, hs, rfl⟩ := hs
        cases hemit
        replace hs := record_copyins_inv hs
        obtain ⟨e7, hs, rfl⟩ := hs
        have hs' : Ok e7 m' e6 = Ok (mkEffect (len_word ds) [] []) m [] := hs
        cases hs'
        -- the bytes LPS writes are a prefix of NoCompiler's gathered bytes
        have hdl : ds.length ≤ (writev_gathered j.in_mem iovs0).length := by
          have h := congrArg List.length hd4
          rw [List.length_take] at h; omega
        have hds : ds = (gather i.mem (i.arg 1) (i.arg 2).toNat).take ds.length := by
          rw [hg]
          have e := List.prefix_iff_eq_take.1 hpre
          calc ds = (writev_gathered j.in_mem iovs0).take ds.length := hd4
            _ = ((gatherIovs i.mem iovs0).take (writev_gathered j.in_mem iovs0).length).take ds.length := by
              rw [← e]
            _ = _ := by rw [List.take_take, Nat.min_eq_left hdl]
        have hgl : (writev_gathered j.in_mem iovs0).length ≤ (gather i.mem (i.arg 1) (i.arg 2).toNat).length := by
          rw [hg]; exact hpre.length_le
        refine ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, some (.write (i.fd 0) ds), ?_, .inr ⟨ds, rfl, by simp⟩⟩
        have := nc_write h66 hm hbig ds.length (by omega)
          (by unfold NoCompiler.maxRW; unfold MAX_RW_COUNT at hcap; omega)
          (fun _ => by omega)
        rw [← hds] at this
        show procSpec7 k i (.ret { ret := len_word ds } _) k
        unfold len_word Z_to_bv; rw [BitVec.ofInt_natCast]; exact this

end LPS.Bridge

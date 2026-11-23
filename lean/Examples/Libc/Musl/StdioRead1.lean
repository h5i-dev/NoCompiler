import Examples.Libc.Musl.StdioRead0

set_option maxRecDepth 20000
namespace NoCompiler.Libc.Musl.StdioRead
open NoCompiler NoCompiler.Linux NoCompiler.Libc NoCompiler.Libc.Musl NoCompiler.Libc.Musl.StdioWrite NoCompiler.Libc.Musl.Toread NoCompiler.Libc.Musl.StdioRead NoCompiler.Libc.Musl.StdioReadImg NoCompiler.Libc.Musl.SyscallRet

/-! ## `__stdio_read` (musl src/stdio/__stdio_read.c)

It asks the kernel for `len - 1` bytes into the destination and FILE's buffer size into the buffer (one
`readv`, or a `read` into the buffer when `len = 1`), calls `__syscall_ret`, then copies the buffer's first
byte to the destination's last. The proof is cut at the syscall: `sr_readv`/`sr_read` (the syscall and
`sr_retcall`), then `sr_pos` (bytes read) or `sr_np` (none, or an error), with `SrCommon` as the invariant. -/

theorem writeBytes_at (m : Word → Byte) (a : Word) (bs : List Byte) (j : Nat) (hj : j < bs.length)
    (hb : bs.length < 2 ^ 64) : writeBytes m a bs (a + BitVec.ofNat 64 j) = bs[j] := by
  induction bs generalizing a j with
  | nil => simp at hj
  | cons b bs ih =>
    cases j with
    | zero => simp [writeBytes]
    | succ j =>
      simp only [List.length_cons] at hj hb
      have hne : a + BitVec.ofNat 64 (j + 1) ≠ a := by
        intro h; have := congrArg BitVec.toNat h; simp [BitVec.toNat_add] at this; omega
      have e : a + BitVec.ofNat 64 (j + 1) = a + 1 + BitVec.ofNat 64 j := by
        apply BitVec.eq_of_toNat_eq; simp; omega
      simp only [writeBytes, hne, ite_false, List.getElem_cons_succ]
      rw [e]; exact ih _ _ (by omega) (by omega)

theorem writeBytes_out {m : Word → Byte} {a p : Word} {bs : List Byte} {n : Nat} (hn : bs.length ≤ n)
    (hp : ¬ (Region.mk a n).mem p) : writeBytes m a bs p = m p :=
  writeBytes_other m a bs p (by simp only [Region.mem] at hp; omega)

theorem readBytes_eq_of {m : Word → Byte} {a : Word} {L : List Byte} {n : Nat} (hn : L.length = n)
    (h : ∀ j (hj : j < n), m (a + BitVec.ofNat 64 j) = L[j]) : readBytes m a n = L := by
  apply List.ext_getElem (by rw [Auto.readBytes_length, hn])
  intro j h1 h2
  rw [Auto.getElem_readBytes]; exact h j (by rw [Auto.readBytes_length] at h1; exact h1)

/-- The two-buffer scatter of `__stdio_read`'s `readv`. -/
theorem applyWrites_scatter2 (m : Word → Byte) (a b : Word) (n n' : Nat) (ds : List Byte) :
    applyWrites m (scatter [(a, n), (b, n')] ds) = writeBytes (writeBytes m a (ds.take n)) b ((ds.drop n).take n') := by
  simp [scatter, applyWrites]

theorem scatter2_out {m : Word → Byte} {a b p : Word} {n n' : Nat} (ds : List Byte)
    (ha : ¬ (Region.mk a n).mem p) (hb : ¬ (Region.mk b n').mem p) :
    applyWrites m (scatter [(a, n), (b, n')] ds) p = m p := by
  rw [applyWrites_scatter2, writeBytes_out (by simp; omega) hb, writeBytes_out (by simp; omega) ha]

theorem scatter2_first {m : Word → Byte} {a b : Word} {n n' : Nat} (ds : List Byte)
    (hd : (Region.mk a n).Disjoint ⟨b, n'⟩) (hn : n < 2 ^ 64) (j : Nat) (hj : j < n) (hjd : j < ds.length) :
    applyWrites m (scatter [(a, n), (b, n')] ds) (a + BitVec.ofNat 64 j) = ds[j] := by
  rw [applyWrites_scatter2, writeBytes_out (by simp; omega) (Auto.not_mem_of_disjoint hd.symm hj),
    writeBytes_at _ _ _ _ (by simp; omega) (by simp; omega)]
  simp

theorem scatter2_second {m : Word → Byte} {a b : Word} {n n' : Nat} (ds : List Byte)
    (hn' : n' < 2 ^ 64) (j : Nat) (hj : j < n') (hjd : n + j < ds.length) :
    applyWrites m (scatter [(a, n), (b, n')] ds) (b + BitVec.ofNat 64 j) = ds[n + j] := by
  rw [applyWrites_scatter2, writeBytes_at _ _ _ _ (by simp; omega) (by simp; omega)]
  simp

/-- A FILE field after a store to a slot of an 80-byte frame below sp, and a slot after a store to a field. -/
theorem sr_field_after_slot {f sp : Word} (hFS : (Region.mk f 128).Disjoint ⟨sp - 80#64, 80⟩) (a b n : Nat)
    (h : decide (8 ≤ a) && decide (a ≤ 80) && decide (b + n ≤ 128) && decide (0 < n) = true)
    (m : Word → Byte) (v : Nat) :
    readLE (writeLE m (sp - BitVec.ofNat 64 a) v 8) (f + BitVec.ofNat 64 b) n = readLE m (f + BitVec.ofNat 64 b) n := by
  exact Lib.readLE_field_after_slot hFS a 8 b n (by simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega) m v

theorem sr_field_after_slot64 {f sp : Word} (hFS : (Region.mk f 128).Disjoint ⟨sp - 80#64, 80⟩) (a b : Nat)
    (h : decide (8 ≤ a) && decide (a ≤ 80) && decide (b + 8 ≤ 128) && decide (0 < 8) = true)
    (m : Word → Byte) (v : Nat) :
    read64 (writeLE m (sp - BitVec.ofNat 64 a) v 8) (f + BitVec.ofNat 64 b) = read64 m (f + BitVec.ofNat 64 b) := by
  unfold read64; rw [sr_field_after_slot hFS a b 8 h]

theorem sr_slot_after_field {f sp : Word} (hFS : (Region.mk f 128).Disjoint ⟨sp - 80#64, 80⟩) (a b n : Nat)
    (h : decide (8 ≤ b) && decide (b ≤ 80) && decide (a + n ≤ 128) && decide (0 < n) = true)
    (m : Word → Byte) (v : Nat) :
    read64 (writeLE m (f + BitVec.ofNat 64 a) v n) (sp - BitVec.ofNat 64 b) = read64 m (sp - BitVec.ofNat 64 b) := by
  exact Lib.read64_slot_after_field hFS a n b (by simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega) m v

/-- `__stdio_read`'s writable regions: FILE's first 128 bytes, its 64-byte frame and `__syscall_ret`'s 16 below,
    errno, the destination and FILE's buffer. -/
def stdioReadPerm (f buf len : Word) (s : State) : Perm :=
  { rd := [], wr := [⟨f, 128⟩, ⟨s.reg 2 - 80#64, 80⟩, ⟨s.reg 4 + 18446744073709551452#64, 4⟩, ⟨buf, len.toNat⟩,
      ⟨read64 s.mem (f + 88#64), (read64 s.mem (f + 96#64)).toNat⟩] }

/-- The five regions of `stdioReadPerm`, pairwise disjoint. -/
def StdioReadDisj (f buf len : Word) (s : State) : Prop :=
  let F : Region := ⟨f, 128⟩
  let S : Region := ⟨s.reg 2 - 80#64, 80⟩
  let E : Region := ⟨s.reg 4 + 18446744073709551452#64, 4⟩
  let B : Region := ⟨buf, len.toNat⟩
  let U : Region := ⟨read64 s.mem (f + 88#64), (read64 s.mem (f + 96#64)).toNat⟩
  F.Disjoint S ∧ E.Disjoint S ∧ E.Disjoint F ∧ B.Disjoint S ∧ B.Disjoint E ∧ B.Disjoint F ∧
    U.Disjoint S ∧ U.Disjoint E ∧ U.Disjoint F ∧ B.Disjoint U

/-- What a read of up to `N` bytes `ds` from `fd` did to the kernel: nothing (no file behind `fd`), or the file's
    next `N` bytes (`ds`), its offset moved on. -/
def ReadK (fd : Word) (N : Nat) (ds : List Byte) (k k' : Kern) : Prop :=
  (k.files.lookup fd = none ∧ k' = k) ∨
    (∃ fl, k.files.lookup fd = some fl ∧ ds = fl.chunk N ∧ k' = k.advance fd ds.length)

/-- No bytes after the offset of the file behind `fd`, if `fd` is open on one. -/
def FileEnd (fd : Word) (k : Kern) : Prop :=
  ∀ fl, k.files.lookup fd = some fl → fd ∈ k.fds → fl.data.length ≤ fl.off

/-- What reads `dss` from `fd` did to the kernel: nothing (no file behind `fd`), or they are the file's next
    bytes and its offset moved on past them. -/
def ReadsK (fd : Word) (dss : List (List Byte)) (k k' : Kern) : Prop :=
  (k.files.lookup fd = none ∧ k' = k) ∨
    (∃ fl, k.files.lookup fd = some fl ∧ dss.flatten = (fl.data.drop fl.off).take dss.flatten.length ∧
      k' = k.advance fd dss.flatten.length)

theorem lookup_map_advance (l : List (Word × OpenFile)) (fd : Word) (m : Nat) :
    (l.map fun p => if p.1 = fd then (p.1, { p.2 with off := p.2.off + m }) else p).lookup fd =
      (l.lookup fd).map fun fl => { fl with off := fl.off + m } := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨a, b⟩ := p
    by_cases h : a = fd
    · rw [h]; simp only [List.map_cons, ↓reduceIte, List.lookup, beq_self_eq_true, Option.map_some]
    · have h' : (fd == a) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact fun e => h e.symm
      rw [List.map_cons, if_neg h, List.lookup_cons, List.lookup_cons, ih]
      simp only [h', Bool.false_eq_true, ↓reduceIte]

theorem Kern.lookup_advance (k : Kern) (fd : Word) (m : Nat) :
    (k.advance fd m).files.lookup fd = (k.files.lookup fd).map fun fl => { fl with off := fl.off + m } :=
  lookup_map_advance _ _ _

theorem Kern.advance_zero (k : Kern) (fd : Word) : k.advance fd 0 = k := by
  cases k; simp [Kern.advance]

theorem Kern.advance_advance (k : Kern) (fd : Word) (a b : Nat) :
    (k.advance fd a).advance fd b = k.advance fd (a + b) := by
  simp only [Kern.advance, List.map_map]
  congr 1; apply List.map_congr_left; intro p _
  by_cases h : p.1 = fd <;> simp [h, Nat.add_assoc]

theorem ReadsK.nil (fd : Word) (k : Kern) : ReadsK fd [] k k := by
  cases h : k.files.lookup fd with
  | none => exact .inl ⟨h, rfl⟩
  | some fl => exact .inr ⟨fl, h, by simp, by simp [Kern.advance_zero]⟩

theorem ReadsK.perm {fd : Word} {dss : List (List Byte)} {k k' : Kern} (h : ReadsK fd dss k k') : k'.perm = k.perm := by
  rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩
  · rfl
  · rfl

theorem take_chunk_append (X : List Byte) (L M : Nat) (h : L ≤ X.length) :
    X.take L ++ (X.drop L).take M = X.take (L + (((X.drop L).take M).length)) := by
  rw [List.take_add]
  congr 1
  rw [List.take_eq_take_iff, List.length_take]
  omega

theorem ReadsK.snoc {fd : Word} {dss : List (List Byte)} {ds : List Byte} {N : Nat} {k k1 k2 : Kern}
    (h : ReadsK fd dss k k1) (h' : ReadK fd N ds k1 k2) : ReadsK fd (dss ++ [ds]) k k2 := by
  rcases h with ⟨hn, rfl⟩ | ⟨fl, hl, hf, rfl⟩
  · rcases h' with ⟨-, rfl⟩ | ⟨fl', hl', -, -⟩
    · exact .inl ⟨hn, rfl⟩
    · rw [hn] at hl'; cases hl'
  · rcases h' with ⟨hn, -⟩ | ⟨fl', hl', hd, rfl⟩
    · rw [Kern.lookup_advance, hl] at hn; cases hn
    · rw [Kern.lookup_advance, hl] at hl'
      cases hl'
      have hL : dss.flatten.length ≤ (fl.data.drop fl.off).length := by
        have := congrArg List.length hf; rw [List.length_take] at this; omega
      have hd' : ds = ((fl.data.drop fl.off).drop dss.flatten.length).take (min N maxRW) := by
        rw [hd]; simp only [OpenFile.chunk, List.drop_drop]
      refine .inr ⟨fl, hl, ?_, ?_⟩
      · simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append]
        generalize hLd : dss.flatten.length = L at hf hd' hL ⊢
        generalize hF : dss.flatten = F at hf ⊢
        rw [hd', hf]; exact take_chunk_append _ _ _ hL
      · simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append]
        rw [Kern.advance_advance]

theorem maxRW_pos : 0 < maxRW := by unfold maxRW; decide

/-- A read that returned nothing (of at least one byte asked) leaves the file, if any, at its end. -/
theorem FileEnd.of_nil {fd : Word} {N : Nat} {k1 k2 : Kern} (h : ReadK fd N [] k1 k2) (hN : 0 < N) : FileEnd fd k2 := by
  rcases h with ⟨hn, rfl⟩ | ⟨fl, hl, hd, rfl⟩
  · intro fl h; rw [hn] at h; cases h
  · intro fl' h _
    rw [List.length_nil, Kern.advance_zero, hl] at h
    cases h
    have h0 := congrArg List.length hd
    simp only [OpenFile.chunk, List.length_take, List.length_nil, List.length_drop] at h0
    have := maxRW_pos
    omega

theorem FileEnd.mono {fd : Word} {N : Nat} {ds : List Byte} {k1 k2 : Kern} (hE : FileEnd fd k1)
    (h : ReadK fd N ds k1 k2) : FileEnd fd k2 := by
  rcases h with ⟨-, rfl⟩ | ⟨fl, hl, -, rfl⟩
  · exact hE
  · intro fl' h hin
    rw [Kern.lookup_advance, hl] at h
    cases h
    have := hE fl hl hin
    simp only; omega

/-- `__stdio_read(f, buf, len)` at the process level, for
    `len ≥ 1` and a FILE with a buffer (`buf_size ≠ 0`). It asks the kernel for `len - 1` bytes into `buf` and
    `buf_size` more into FILE's buffer (one `readv`, or a `read` into the buffer if `len = 1`). Postcondition:
    the kernel unchanged; nothing written outside the 80 bytes below sp, errno, FILE's flags and rpos/rend, `buf`
    and FILE's buffer; and either the kernel returned bytes `ds` (the event `read fd ds`): none: F_EOF set, 0;
    at most `len - 1`: they are in `buf`, their count; more: the first `len` are in `buf`, the rest from the
    buffer's start, rpos = buffer + 1, rend after them, `len`; or an error (no event): F_ERR set, 0. -/
def stdioReadP : SpecP (Word × Word × Word) where
  pre := fun ⟨f, buf, len⟩ s k =>
    s.reg 10 = f ∧ s.reg 11 = buf ∧ s.reg 12 = len ∧ aligned f 8 ∧
    aligned (s.reg 4 + 18446744073709551452#64) 4 ∧ 0 < len.toNat ∧ read64 s.mem (f + 96#64) ≠ 0 ∧
    len.toNat + (read64 s.mem (f + 96#64)).toNat < 2 ^ 63 ∧ (fdOf s.mem f).toNat < 2 ^ 31 ∧
    (stdioReadPerm f buf len s).le k.perm ∧ StdioReadDisj f buf len s
  post := fun ⟨f, buf, len⟩ x y =>
    (∀ p, ¬ (Region.mk (x.1.reg 2 - 80#64) 80).mem p → ¬ (Region.mk (x.1.reg 4 + 18446744073709551452#64) 4).mem p →
      ¬ (Region.mk f 4).mem p → ¬ (Region.mk (f + 8#64) 16).mem p → ¬ (Region.mk buf len.toNat).mem p →
      ¬ (Region.mk (read64 x.1.mem (f + 88#64)) (read64 x.1.mem (f + 96#64)).toNat).mem p → y.1.mem p = x.1.mem p) ∧
    ((∃ ds : List Byte, ReadK (fdOf x.1.mem f) (len.toNat - 1 + (read64 x.1.mem (f + 96#64)).toNat) ds x.2 y.2 ∧
        ds.length ≤ len.toNat - 1 + (read64 x.1.mem (f + 96#64)).toNat ∧
        y.1.trace = x.1.trace ++ [.read (fdOf x.1.mem f) ds] ∧
        (ds = [] → y.1.reg 10 = 0 ∧ readLE y.1.mem f 4 = (BitVec.ofNat 32 (readLE x.1.mem f 4) ||| 16#32).toNat ∧
          read64 y.1.mem (f + 8#64) = read64 x.1.mem (f + 8#64) ∧ read64 y.1.mem (f + 16#64) = read64 x.1.mem (f + 16#64)) ∧
        (0 < ds.length → ds.length ≤ len.toNat - 1 → y.1.reg 10 = BitVec.ofNat 64 ds.length ∧
          readBytes y.1.mem buf ds.length = ds ∧ readLE y.1.mem f 4 = readLE x.1.mem f 4 ∧
          read64 y.1.mem (f + 8#64) = read64 x.1.mem (f + 8#64) ∧ read64 y.1.mem (f + 16#64) = read64 x.1.mem (f + 16#64)) ∧
        (len.toNat - 1 < ds.length → y.1.reg 10 = len ∧ readBytes y.1.mem buf len.toNat = ds.take len.toNat ∧
          readBytes y.1.mem (read64 x.1.mem (f + 88#64)) (ds.length - (len.toNat - 1)) = ds.drop (len.toNat - 1) ∧
          readLE y.1.mem f 4 = readLE x.1.mem f 4 ∧ read64 y.1.mem (f + 8#64) = read64 x.1.mem (f + 88#64) + 1#64 ∧
          read64 y.1.mem (f + 16#64) = read64 x.1.mem (f + 88#64) + BitVec.ofNat 64 (ds.length - (len.toNat - 1)))) ∨
     (y.2 = x.2 ∧ (∀ fl, x.2.files.lookup (fdOf x.1.mem f) = some fl → fdOf x.1.mem f ∉ x.2.fds) ∧
        y.1.trace = x.1.trace ∧ y.1.reg 10 = 0 ∧
        readLE y.1.mem f 4 = (BitVec.ofNat 32 (readLE x.1.mem f 4) ||| 32#32).toNat ∧
        read64 y.1.mem (f + 8#64) = read64 x.1.mem (f + 8#64) ∧ read64 y.1.mem (f + 16#64) = read64 x.1.mem (f + 16#64)))

/-- What holds at every cut of `__stdio_read`'s run from its entry state `s` (frame at sp - 64): s0 = f,
    s1 = len, s2 = buf, the other callee-saved registers as at entry, the four saved ones and iov[0].len in
    their slots, memory outside the 80 bytes below sp and errno as `m0`. -/
def SrCommon (s : State) (f buf len : Word) (m0 : Word → Byte) (u : State) : Prop :=
  u.exit = none ∧ u.reg 2 = s.reg 2 - 64#64 ∧ u.reg 8 = f ∧ u.reg 9 = len ∧ u.reg 18 = buf ∧
  (∀ q ∈ [(3 : Reg), 4, 19, 20, 21, 22, 23, 24, 25, 26, 27], u.reg q = s.reg q) ∧
  read64 u.mem (s.reg 2 - 8#64) = s.reg 1 ∧ read64 u.mem (s.reg 2 - 16#64) = s.reg 8 ∧
  read64 u.mem (s.reg 2 - 24#64) = s.reg 9 ∧ read64 u.mem (s.reg 2 - 32#64) = s.reg 18 ∧
  read64 u.mem (s.reg 2 - 56#64) = len - 1#64 ∧
  ∀ p, ¬ (Region.mk (s.reg 2 - 80#64) 80).mem p → ¬ (Region.mk (s.reg 4 + 18446744073709551452#64) 4).mem p →
    u.mem p = m0 p

theorem sext_or_16 (x : BitVec 32) : (x.signExtend 64 ||| 16#64).toNat % 2 ^ 32 = (x ||| 16#32).toNat := by
  have h : ((x.signExtend 64 ||| 16#64).setWidth 32) = x ||| 16#32 := NoCompiler.Libc.sext_or_16_setWidth x
  rw [← h, BitVec.toNat_setWidth]

theorem sr_slot_after_base {f sp : Word} (hFS : (Region.mk f 128).Disjoint ⟨sp - 80#64, 80⟩) (b : Nat)
    (h : decide (8 ≤ b) && decide (b ≤ 80) = true) (m : Word → Byte) (v : Nat) :
    read64 (writeLE m f v 4) (sp - BitVec.ofNat 64 b) = read64 m (sp - BitVec.ofNat 64 b) := by
  simpa using Lib.read64_slot_after_field hFS 0 4 b (by simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega) m v

/-- FILE's bytes agree with `m0` when memory does outside the stack and errno. -/
theorem sr_fileLE {s : State} {f : Word} {m m0 : Word → Byte}
    (hFS : (Region.mk f 128).Disjoint ⟨s.reg 2 - 80#64, 80⟩)
    (hEF : (Region.mk (s.reg 4 + 18446744073709551452#64) 4).Disjoint ⟨f, 128⟩)
    (hm : ∀ p, ¬ (Region.mk (s.reg 2 - 80#64) 80).mem p → ¬ (Region.mk (s.reg 4 + 18446744073709551452#64) 4).mem p →
      m p = m0 p) (o n : Nat) (h : o + n ≤ 128) :
    readLE m (f + BitVec.ofNat 64 o) n = readLE m0 (f + BitVec.ofNat 64 o) n := by
  apply readLE_congr; intro j hj
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact hm _ (Auto.not_mem_of_disjoint hFS.symm (by omega)) (Auto.not_mem_of_disjoint hEF (by omega))

/-- `__stdio_read` after a read that got nothing or failed (0x123c0, a0 = 0 or -1): F_EOF or F_ERR, 0. -/
theorem sr_np (f buf len : Word) (s : State) (k : Kern) (he : Entry dom __stdio_read_entry s)
    (hpre : stdioReadP.pre (f, buf, len) s k)
    (w : State) (hpc : w.pc = 0x123c0#64) (hc : SrCommon s f buf len s.mem w) (k0 : Kern)
    (hr : (w.reg 10 = 0 ∧ w.trace = s.trace ++ [.read (fdOf s.mem f) []] ∧
        ReadK (fdOf s.mem f) (len.toNat - 1 + (read64 s.mem (f + 96#64)).toNat) [] k0 k) ∨
      (w.reg 10 = -1 ∧ w.trace = s.trace ∧ k = k0 ∧
        ∀ fl, k0.files.lookup (fdOf s.mem f) = some fl → fdOf s.mem f ∉ k0.fds)) :
    PReachK img dom (fun y => Final dom y.1 ∧ stdioReadP.Done (f, buf, len) (s, k0) y) (w, k) := by
  have hsp := he.sp
  have hra4 := he.retAligned
  have hret := he.ret
  simp only [Reg.sp, Reg.ra] at hsp hra4 hret
  obtain ⟨ha0, ha1, ha2, hal, hale, hlen, hbs, hB, -, hle, dFS, dES, dEF, dBS, dBE, dBF, dUS, dUE, dUF, dBU⟩ := hpre
  obtain ⟨hx, h2, h8, h9, h18, hpr, s1, s2, s3, s4, s5, hfr⟩ := hc
  have dFS' : (Region.mk f 128).Disjoint ⟨s.reg 2 - 80#64, 80⟩ := dFS
  have hF := sr_fileLE dFS' dEF hfr
  have wF : ∀ o n, o + n ≤ 128 → k.perm.canWrite (f + BitVec.ofNat 64 o) n := fun o n h =>
    hle.write _ _ (.inr ⟨⟨f, 128⟩, by simp [stdioReadPerm], by simp only [Region.covers]; bv_omega⟩)
  have rS : ∀ o, 8 ≤ o → o ≤ 80 → k.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h3 =>
    Perm.canRead_of_canWrite (hle.write _ _ (.inr ⟨⟨s.reg 2 - 80#64, 80⟩, by simp [stdioReadPerm], by simp only [Region.covers]; bv_omega⟩))
  have al0 : aligned f 4 := sw_al4 hal
  have w0 : k.perm.canWrite f 4 := by have := wF 0 4 (by omega); simpa using this
  have hf0 : readLE w.mem f 4 = readLE s.mem f 4 := by have := hF 0 4 (by omega); simpa using this
  have eS : ∀ o, o ≤ 64 → s.reg 2 - 64#64 + BitVec.ofNat 64 o = s.reg 2 - BitVec.ofNat 64 (64 - o) := by
    intro o ho; bv_omega
  have e64 : s.reg 2 - 64#64 + 64#64 = s.reg 2 := by bv_omega
  have sb := sr_slot_after_base dFS'
  nocompiler_wstep [hx, hpc]
  have hpr' : ∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 8 → q ≠ 9 → q ≠ 18 → w.reg q = s.reg q := by
    intro q hq a b c d
    have : q ∈ [(3 : Reg), 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert a b c d; revert hq; revert q; decide
    exact hpr q this
  have tail : ∀ (c : Word) (hc : c = 16#64 ∨ c = 32#64) (u : State), u.pc = 0x123cc#64 → u.exit = none →
      u.mem = w.mem → u.reg 11 = c → (∀ q ∈ preservedRegs, u.reg q = w.reg q) → u.trace = w.trace →
      PReachK img dom (fun y => Final dom y.1 ∧ y.1.exit = none ∧ y.1.pc = s.reg 1 ∧
        Preserved s y.1 ∧ y.2 = k ∧ y.1.trace = w.trace ∧ y.1.reg 10 = 0 ∧
        y.1.mem = writeLE w.mem f (BitVec.toNat (BitVec.signExtend 64 (BitVec.ofNat 32 (readLE s.mem f 4)) ||| c)) 4) (u, k) := by
    intro c hc u hpcu hxu hmu h11 hpru htru
    have hu8 : u.reg 8 = f := by rw [hpru 8 (by decide), h8]
    have hu2 : u.reg 2 = s.reg 2 - 64#64 := by rw [hpru 2 (by decide), h2]
    nocompiler_wstep [hxu, hpcu, hu8, BitVec.add_zero, al0, hmu, hf0]
    refine ⟨Perm.canRead_of_canWrite w0, ?_⟩
    nocompiler_wstep [hxu]
    nocompiler_wstep [hxu, h11]
    nocompiler_wstep [hxu, hu8, BitVec.add_zero, al0]
    refine ⟨w0, ?_⟩
    nocompiler_wstep [hxu]
    nocompiler_wstep [hxu]
    nocompiler_wstep [hxu, hu2, eS 56 (by omega), sw_alS hsp 8 rfl, sb, hmu, s1]
    refine ⟨rS 8 (by omega) (by omega), ?_⟩
    nocompiler_wstep [hxu, hu2, eS 48 (by omega), sw_alS hsp 16 rfl, sb, hmu, s2]
    refine ⟨rS 16 (by omega) (by omega), ?_⟩
    nocompiler_wstep [hxu, hu2, eS 40 (by omega), sw_alS hsp 24 rfl, sb, hmu, s3]
    refine ⟨rS 24 (by omega) (by omega), ?_⟩
    nocompiler_wstep [hxu, hu2, eS 32 (by omega), sw_alS hsp 32 rfl, sb, hmu, s4]
    refine ⟨rS 32 (by omega) (by omega), ?_⟩
    nocompiler_wstep [hxu, hu2, e64]
    nocompiler_wstep [hxu, ret_mask hra4, hra4]
    refine .done ⟨.inl ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · simp only [nocompiler_state]; exact hret
    · simp only [nocompiler_state]; exact hxu
    · simp only [nocompiler_state]
    · intro q hq
      have hq' := hq
      simp only [preservedRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals (simp (disch := nocompiler_decide_closed) only [nocompiler_state])
      all_goals (first | rfl | (rw [hpru _ hq']; exact hpr' _ hq' (by decide) (by decide) (by decide) (by decide)))
    · simp only [nocompiler_state]; exact htru
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · simp only [nocompiler_state, hmu]
  have hframe : ∀ (c : Word) p, ¬ (Region.mk (s.reg 2 - 80#64) 80).mem p →
      ¬ (Region.mk (s.reg 4 + 18446744073709551452#64) 4).mem p → ¬ (Region.mk f 4).mem p →
      writeLE w.mem f (BitVec.toNat (BitVec.signExtend 64 (BitVec.ofNat 32 (readLE s.mem f 4)) ||| c)) 4 p = s.mem p := by
    intro c p h1 h2 h3
    rw [writeLE_of_not_mem (r := ⟨f, 4⟩) (by simp [Region.covers]) h3]; exact hfr p h1 h2
  have hfl : ∀ (c : Word), readLE (writeLE w.mem f (BitVec.toNat (BitVec.signExtend 64 (BitVec.ofNat 32 (readLE s.mem f 4)) ||| c)) 4) f 4 =
      (BitVec.signExtend 64 (BitVec.ofNat 32 (readLE s.mem f 4)) ||| c).toNat % 2 ^ 32 := by
    intro c; rw [readLE_writeLE_same _ _ _ (by omega)]
  have hfo : ∀ (c : Word) o, o ∈ [8, 16] → read64 (writeLE w.mem f (BitVec.toNat (BitVec.signExtend 64 (BitVec.ofNat 32 (readLE s.mem f 4)) ||| c)) 4) (f + BitVec.ofNat 64 o) =
      read64 s.mem (f + BitVec.ofNat 64 o) := by
    intro c o ho
    have ho' : o = 8 ∨ o = 16 := by simpa using ho
    unfold read64
    rw [readLE_writeLE_disj (R := ⟨f, 4⟩) (by simp only [Region.Disjoint]; rcases ho' with rfl | rfl <;> bv_omega) _ _ _ _
      (by simp [Region.covers]), hF o 8 (by rcases ho' with rfl | rfl <;> omega)]
  have fin : ∀ (c : Word) (hc : c = 16#64 ∨ c = 32#64) (u : State), u.pc = 0x123cc#64 → u.exit = none →
      u.mem = w.mem → u.reg 11 = c → (∀ q ∈ preservedRegs, u.reg q = w.reg q) → u.trace = w.trace →
      (∀ y : State, y.reg 10 = 0 → y.trace = w.trace →
        (∀ p, ¬ (Region.mk (s.reg 2 - 80#64) 80).mem p → ¬ (Region.mk (s.reg 4 + 18446744073709551452#64) 4).mem p →
          ¬ (Region.mk f 4).mem p → y.mem p = s.mem p) →
        readLE y.mem f 4 = (BitVec.signExtend 64 (BitVec.ofNat 32 (readLE s.mem f 4)) ||| c).toNat % 2 ^ 32 →
        read64 y.mem (f + 8#64) = read64 s.mem (f + 8#64) → read64 y.mem (f + 16#64) = read64 s.mem (f + 16#64) →
        stdioReadP.post (f, buf, len) (s, k0) (y, k)) →
      PReachK img dom (fun y => Final dom y.1 ∧ stdioReadP.Done (f, buf, len) (s, k0) y) (u, k) := by
    intro c hc u h1 h2 h3 h4 h5 h6 P
    refine PReachK.bind (Dom.sub_of_ranges (by decide)) ?_ (tail c hc u h1 h2 h3 h4 h5 h6)
    rintro ⟨y, ky⟩ ⟨hF', hxy, hpcy, hpy, rfl, htry, h10y, hmy⟩
    refine .done ⟨hF', .inl ⟨hxy, by rw [hpcy], hpy, P y h10y htry ?_ ?_ ?_ ?_⟩⟩
    · intro p a b c'; rw [hmy]; exact hframe c p a b c'
    · rw [hmy]; exact hfl c
    · rw [hmy]; have := hfo c 8 (by simp); simpa using this
    · rw [hmy]; have := hfo c 16 (by simp); simpa using this
  have hpw : ∀ (y : State) (q : Reg), q ∈ preservedRegs → q ≠ 11 → ∀ v, (y.setReg 11 v).reg q = y.reg q := by
    intro y q hq h11 v; exact State.reg_setReg_other _ _ _ _ h11
  rcases hr with ⟨h10, htr, hK⟩ | ⟨h10, htr, hK, hnf⟩
  · have hb : (w.reg 10 == 0) = true := by simp [h10]
    nocompiler_wstep [hx, hb]
    refine fin 16#64 (.inl rfl) _ (by simp only [nocompiler_state]) (by simp only [nocompiler_state]; exact hx)
      (by simp only [nocompiler_state]) (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
      (fun q hq => by simp only [State.setPc_reg]; exact State.reg_setReg_other _ _ _ _ (by revert hq; revert q; decide))
      (by simp only [nocompiler_state]) ?_
    intro y hy10 hytr hym hyf hy8 hy16
    refine ⟨?_, .inl ⟨[], hK, by simp, by rw [hytr, htr], fun _ => ⟨hy10, ?_, hy8, hy16⟩, fun h => absurd h (by simp),
      fun h => absurd h (by simp)⟩⟩
    · intro p a b c _ _ _; exact hym p a b c
    · rw [hyf, sext_or_16]
  · have hb : (w.reg 10 == 0) = false := by rw [h10]; decide
    nocompiler_wstep [hx, hb]
    nocompiler_wstep [hx]
    refine fin 32#64 (.inr rfl) _ (by simp only [nocompiler_state]) (by simp only [nocompiler_state]; exact hx)
      (by simp only [nocompiler_state]) (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
      (fun q hq => by
        have h11 : q ≠ 11 := by revert hq; revert q; decide
        repeat (first | rw [State.setPc_reg] | rw [State.reg_setReg_other _ _ _ _ h11]))
      (by simp only [nocompiler_state]) ?_
    intro y hy10 hytr hym hyf hy8 hy16
    refine ⟨?_, .inr ⟨hK, hnf, by rw [hytr, htr], hy10, ?_, hy8, hy16⟩⟩
    · intro p a b c _ _ _; exact hym p a b c
    · rw [hyf, sext_or_32]

/-- Memory after the kernel's read of `ds` (into `buf`, `len - 1` bytes, then FILE's buffer). -/
def srK (s : State) (f buf len : Word) (ds : List Byte) : Word → Byte :=
  applyWrites s.mem (scatter [(buf, len.toNat - 1), (read64 s.mem (f + 88#64), (read64 s.mem (f + 96#64)).toNat)] ds)

end NoCompiler.Libc.Musl.StdioRead

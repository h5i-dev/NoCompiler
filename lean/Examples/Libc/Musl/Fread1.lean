import Examples.Libc.Musl.Fread0
import Examples.Libc.Musl.MemcpyAt

set_option maxRecDepth 20000
namespace NoCompiler.Libc.Musl.Fread
open NoCompiler NoCompiler.Linux NoCompiler.Libc NoCompiler.Libc.Musl NoCompiler.Libc.Musl.StdioWrite NoCompiler.Libc.Musl.Toread NoCompiler.Libc.Musl.StdioRead NoCompiler.Libc.Musl.SyscallRet NoCompiler.Libc.Musl.Memcpy NoCompiler.Libc.Musl.Fread NoCompiler.Libc.Musl.FreadImg

/-! ## `fread` (musl src/stdio/fread.c), for `size = 1` on slen's stdin

The prologue (no lock: lock < 0), the copy of what is buffered (`memcpy`, by its specification), then the
loop of `__toread` and `f->read` (= `__stdio_read`, an indirect call: the region `freadD` includes it), by
`PReachK.loop` on the count left (`FrLoop`). Every exit delivers the stream's first `r` bytes (`FrOut`). -/

/-- `fread` with the function its `f->read` points to in slen (`__stdio_read`): the image's `fread_dom` has
    only its direct callees. -/
def freadD : Dom := fread_dom ++ __stdio_read_dom

/-- The count of bytes buffered for reading, `rend - rpos`, and those bytes. -/
def frAvail (m : Word → Byte) (f : Word) : Nat := (read64 m (f + 16#64) - read64 m (f + 8#64)).toNat
def frBuffered (m : Word → Byte) (f : Word) : List Byte := readBytes m (read64 m (f + 8#64)) (frAvail m f)

/-- A FILE in the state slen's stdin is in at every `fread`: f->read = `__stdio_read`, nothing buffered for
    writing, F_NORD clear, a buffer, no lock (lock < 0), the buffered bytes inside the buffer. -/
def StdinFile (f : Word) (m : Word → Byte) : Prop :=
  read64 m (f + 64#64) = 0x12308#64 ∧ read64 m (f + 40#64) = read64 m (f + 56#64) ∧
  read32 m f &&& 4#64 = 0 ∧ read64 m (f + 96#64) ≠ 0 ∧ 2 ^ 31 ≤ readLE m (f + 140#64) 4 ∧
  (frAvail m f = 0 ∨
    (Region.mk (read64 m (f + 8#64)) (frAvail m f)).within ⟨read64 m (f + 88#64), (read64 m (f + 96#64)).toNat⟩)

/-- `fread`'s writable regions: FILE's first 144 bytes, its 64-byte frame and the 80 of `__stdio_read`'s below,
    errno, the destination and FILE's buffer. -/
def freadPerm (dest n f : Word) (s : State) : Perm :=
  { rd := [], wr := [⟨f, 144⟩, ⟨s.reg 2 - 144#64, 144⟩, ⟨s.reg 4 + 18446744073709551452#64, 4⟩, ⟨dest, n.toNat⟩,
      ⟨read64 s.mem (f + 88#64), (read64 s.mem (f + 96#64)).toNat⟩] }

def FreadDisj (dest n f : Word) (s : State) : Prop :=
  let F : Region := ⟨f, 144⟩
  let S : Region := ⟨s.reg 2 - 144#64, 144⟩
  let E : Region := ⟨s.reg 4 + 18446744073709551452#64, 4⟩
  let B : Region := ⟨dest, n.toNat⟩
  let U : Region := ⟨read64 s.mem (f + 88#64), (read64 s.mem (f + 96#64)).toNat⟩
  F.Disjoint S ∧ E.Disjoint S ∧ E.Disjoint F ∧ B.Disjoint S ∧ B.Disjoint E ∧ B.Disjoint F ∧
    U.Disjoint S ∧ U.Disjoint E ∧ U.Disjoint F ∧ B.Disjoint U

/-- Memory `m` as at `s` outside what `fread(dest, 1, n, f)` may write. -/
def FrFrame (s : State) (dest n f : Word) (m : Word → Byte) : Prop :=
  ∀ p, ¬ (Region.mk (s.reg 2 - 144#64) 144).mem p → ¬ (Region.mk (s.reg 4 + 18446744073709551452#64) 4).mem p →
    ¬ (Region.mk f 4).mem p → ¬ (Region.mk (f + 8#64) 16).mem p → ¬ (Region.mk (f + 32#64) 32).mem p →
    ¬ (Region.mk (f + 136#64) 4).mem p → ¬ (Region.mk dest n.toNat).mem p →
    ¬ (Region.mk (read64 s.mem (f + 88#64)) (read64 s.mem (f + 96#64)).toNat).mem p → m p = s.mem p

/-- F_EOF set in FILE's flags. -/
def EofSet (m : Word → Byte) (f : Word) : Prop := read32 m f &&& 16#64 ≠ 0

/-- The kernel after the cuts of `fread` from `(s, k)` with reads `dss` (`ReadsK`), in memory `m`, at kernel
    `ku`; and F_EOF set at the cut means the file is at its end, if it did at entry. -/
def FrK (s : State) (f : Word) (k : Kern) (dss : List (List Byte)) (m : Word → Byte) (ku : Kern) : Prop :=
  ReadsK (fdOf s.mem f) dss k ku ∧
    ((EofSet s.mem f → FileEnd (fdOf s.mem f) k) → EofSet m f → FileEnd (fdOf s.mem f) ku)

theorem FrK_init {s : State} {f : Word} {k : Kern} {m : Word → Byte} (h : read32 m f = read32 s.mem f) :
    FrK s f k [] m k :=
  ⟨ReadsK.nil _ _, fun h0 he => h0 (by unfold EofSet at he ⊢; rw [← h]; exact he)⟩

theorem FrK_congr {s : State} {f : Word} {k ku : Kern} {dss : List (List Byte)} {m m' : Word → Byte}
    (h : read32 m' f = read32 m f) (hK : FrK s f k dss m ku) : FrK s f k dss m' ku :=
  ⟨hK.1, fun h0 he => hK.2 h0 (by unfold EofSet at he ⊢; rw [← h]; exact he)⟩

theorem FrK_step {s : State} {f : Word} {k ku ky : Kern} {dss : List (List Byte)} {ds : List Byte} {N : Nat}
    {m m' : Word → Byte} (hK : FrK s f k dss m ku) (hR : ReadK (fdOf s.mem f) N ds ku ky)
    (h : read32 m' f = read32 m f) : FrK s f k (dss ++ [ds]) m' ky :=
  ⟨hK.1.snoc hR, fun h0 he => FileEnd.mono (hK.2 h0 (by unfold EofSet at he ⊢; rw [← h]; exact he)) hR⟩

theorem FrK_end {s : State} {f : Word} {k ku : Kern} {dss : List (List Byte)} {m : Word → Byte}
    (hK : ReadsK (fdOf s.mem f) dss k ku) (hE : FileEnd (fdOf s.mem f) ku) : FrK s f k dss m ku :=
  ⟨hK, fun _ _ => hE⟩

/-- `fread(dest, 1, n, f)` on slen's stdin (`StdinFile`), at the process level,
    with memcpy's specification as a hypothesis. Postcondition: `StdinFile` again, memory as `FrFrame` says,
    and new events `read fd ds` for a list `dss`, the kernel's answers (`ReadsK`: no file behind `fd`, the kernel
    unchanged; or the file's next bytes, its offset moved on); with `S` the bytes buffered at entry followed by
    those, the result `r ≤ n`, the destination's first `r` bytes are `S`'s, the bytes buffered now are the rest
    of `S`, and none are buffered if `r < n`; and if F_EOF set means the file is at its end at entry, the same
    holds at exit, and `r < n` means the file is at its end (`FileEnd`: if `fd` is open on one). -/
def freadP : SpecP (Word × Word × Word) where
  pre := fun ⟨dest, n, f⟩ s k =>
    s.reg 10 = dest ∧ s.reg 11 = 1 ∧ s.reg 12 = n ∧ s.reg 13 = f ∧ aligned f 8 ∧
    aligned (s.reg 4 + 18446744073709551452#64) 4 ∧ StdinFile f s.mem ∧
    n.toNat + (read64 s.mem (f + 96#64)).toNat < 2 ^ 63 ∧ (fdOf s.mem f).toNat < 2 ^ 31 ∧
    (freadPerm dest n f s).le k.perm ∧ FreadDisj dest n f s
  post := fun ⟨dest, n, f⟩ x y =>
    StdinFile f y.1.mem ∧ FrFrame x.1 dest n f y.1.mem ∧
    ∃ dss : List (List Byte), ReadsK (fdOf x.1.mem f) dss x.2 y.2 ∧
      y.1.trace = x.1.trace ++ dss.map (Event.read (fdOf x.1.mem f)) ∧
      (y.1.reg 10).toNat ≤ n.toNat ∧
      readBytes y.1.mem dest (y.1.reg 10).toNat = (frBuffered x.1.mem f ++ dss.flatten).take (y.1.reg 10).toNat ∧
      frBuffered y.1.mem f = (frBuffered x.1.mem f ++ dss.flatten).drop (y.1.reg 10).toNat ∧
      ((y.1.reg 10).toNat < n.toNat → frAvail y.1.mem f = 0) ∧
      ((EofSet x.1.mem f → FileEnd (fdOf x.1.mem f) x.2) →
        (EofSet y.1.mem f → FileEnd (fdOf x.1.mem f) y.2) ∧ ((y.1.reg 10).toNat < n.toNat → FileEnd (fdOf x.1.mem f) y.2))

/-- `fread`'s epilogue (0x11c04): a0 = s1, the eight saved registers reloaded, back to ra. -/
theorem fr_epi (s : State) (k : Kern) (he : Entry freadD fread_entry s)
    (hle : (Perm.mk [] [⟨s.reg 2 - 144#64, 144⟩]).le k.perm)
    (u : State) (hpc : u.pc = 0x11c04#64) (hx : u.exit = none) (h2 : u.reg 2 = s.reg 2 - 64#64)
    (hpr : ∀ q ∈ [(3 : Reg), 4, 23, 24, 25, 26, 27], u.reg q = s.reg q)
    (s1 : read64 u.mem (s.reg 2 - 8#64) = s.reg 1) (s2 : read64 u.mem (s.reg 2 - 16#64) = s.reg 8)
    (s3 : read64 u.mem (s.reg 2 - 24#64) = s.reg 9) (s4 : read64 u.mem (s.reg 2 - 32#64) = s.reg 18)
    (s5 : read64 u.mem (s.reg 2 - 40#64) = s.reg 19) (s6 : read64 u.mem (s.reg 2 - 48#64) = s.reg 20)
    (s7 : read64 u.mem (s.reg 2 - 56#64) = s.reg 21) (s8 : read64 u.mem (s.reg 2 - 64#64) = s.reg 22) :
    PReachK img freadD (fun y => Final freadD y.1 ∧ y.1.exit = none ∧ y.1.pc = s.reg 1 ∧
      Preserved s y.1 ∧ y.2 = k ∧ y.1.trace = u.trace ∧ y.1.reg 10 = u.reg 9 ∧ y.1.mem = u.mem) (u, k) := by
  have hsp := he.sp
  have hra4 := he.retAligned
  have hret := he.ret
  simp only [Reg.sp, Reg.ra] at hsp hra4 hret
  have rS : ∀ o, 8 ≤ o → o ≤ 144 → k.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h3 =>
    Perm.canRead_of_canWrite (hle.write _ _ (.inr ⟨⟨s.reg 2 - 144#64, 144⟩, by simp, by simp only [Region.covers]; bv_omega⟩))
  have eS : ∀ o, o ≤ 64 → s.reg 2 - 64#64 + BitVec.ofNat 64 o = s.reg 2 - BitVec.ofNat 64 (64 - o) := by
    intro o ho; bv_omega
  have e64 : s.reg 2 - 64#64 + 64#64 = s.reg 2 := by bv_omega
  nocompiler_run_n 11 [hx, hpc, h2, eS 56 (by omega), sw_alS hsp 8 rfl, s1, eS 48 (by omega), sw_alS hsp 16 rfl, s2, eS 40 (by omega), sw_alS hsp 24 rfl, s3, eS 32 (by omega), sw_alS hsp 32 rfl, s4, eS 24 (by omega), sw_alS hsp 40 rfl, s5, eS 16 (by omega), sw_alS hsp 48 rfl, s6, eS 8 (by omega), sw_alS hsp 56 rfl, s7, BitVec.add_zero, sw_alS hsp 64 rfl, s8, e64, ret_mask hra4, hra4] using [rS]
  refine .done ⟨.inl ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · simp only [nocompiler_state]; exact hret
  · simp only [nocompiler_state]; exact hx
  · simp only [nocompiler_state]
  · intro q hq
    have hq' := hq
    simp only [preservedRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp (disch := nocompiler_decide_closed) only [nocompiler_state])
    all_goals (first | rfl | exact hpr _ (by decide))
  · simp only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp only [nocompiler_state]

/-- What holds at every cut of `fread(dest, 1, n, f)`'s run from `s` (frame at sp - 64): s0 = f, s1 = n,
    s2 = 1 (size), s4 = 0 (not locked), s6 = n, the callee-saved registers it does not use as at entry, the
    eight saved ones in their slots. -/
def FrSlots (s : State) (u : State) : Prop :=
  (∀ q ∈ [(3 : Reg), 4, 23, 24, 25, 26, 27], u.reg q = s.reg q) ∧
  read64 u.mem (s.reg 2 - 8#64) = s.reg 1 ∧ read64 u.mem (s.reg 2 - 16#64) = s.reg 8 ∧
  read64 u.mem (s.reg 2 - 24#64) = s.reg 9 ∧ read64 u.mem (s.reg 2 - 32#64) = s.reg 18 ∧
  read64 u.mem (s.reg 2 - 40#64) = s.reg 19 ∧ read64 u.mem (s.reg 2 - 48#64) = s.reg 20 ∧
  read64 u.mem (s.reg 2 - 56#64) = s.reg 21 ∧ read64 u.mem (s.reg 2 - 64#64) = s.reg 22

def FrCommon (s : State) (n f : Word) (u : State) : Prop :=
  u.exit = none ∧ u.reg 2 = s.reg 2 - 64#64 ∧ u.reg 8 = f ∧ u.reg 9 = n ∧ u.reg 18 = 1 ∧ u.reg 20 = 0 ∧
  u.reg 22 = n ∧ FrSlots s u

/-- The bytes `fread` delivers from: those buffered at entry, then those of the reads. -/
def frStream (s : State) (f : Word) (dss : List (List Byte)) : List Byte := frBuffered s.mem f ++ dss.flatten

/-- How `fread` ends, `r` bytes delivered, in memory `m`. -/
def FrOut (s : State) (dest n f : Word) (dss : List (List Byte)) (r : Nat) (m : Word → Byte) : Prop :=
  StdinFile f m ∧ FrFrame s dest n f m ∧ r ≤ n.toNat ∧ readBytes m dest r = (frStream s f dss).take r ∧
  frBuffered m f = (frStream s f dss).drop r ∧ (r < n.toNat → frAvail m f = 0)

theorem fr_done (dest n f : Word) (s : State) (k : Kern) (he : Entry freadD fread_entry s)
    (hpre : freadP.pre (dest, n, f) s k) (u : State) (hpc : u.pc = 0x11c04#64) (hx : u.exit = none)
    (h2 : u.reg 2 = s.reg 2 - 64#64) (hs : FrSlots s u) (r : Nat) (hr : r < 2 ^ 64) (h9 : u.reg 9 = BitVec.ofNat 64 r) (dss : List (List Byte))
    (htr : u.trace = s.trace ++ dss.map (Event.read (fdOf s.mem f))) (ho : FrOut s dest n f dss r u.mem)
    (ku : Kern) (hK : FrK s f k dss u.mem ku)
    (hEnd : r < n.toNat → (EofSet s.mem f → FileEnd (fdOf s.mem f) k) → FileEnd (fdOf s.mem f) ku) :
    PReachK img freadD (fun y => Final freadD y.1 ∧ freadP.Done (dest, n, f) (s, k) y) (u, ku) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hle, -⟩ := hpre
  have hle : (freadPerm dest n f s).le ku.perm := by rw [hK.1.perm]; exact hle
  obtain ⟨hpr, s1, s2, s3, s4, s5, s6, s7, s8⟩ := hs
  have hle' : (Perm.mk [] [⟨s.reg 2 - 144#64, 144⟩]).le ku.perm :=
    Perm.le_trans (Perm.le_of (by simp) (fun r hr => ⟨r, by simp [freadPerm] at hr ⊢; exact .inr (.inl hr), Region.within_refl _⟩)) hle
  refine PReachK.bind (Dom.sub_of_ranges (by decide)) ?_ (fr_epi s ku he hle' u hpc hx h2 hpr s1 s2 s3 s4 s5 s6 s7 s8)
  rintro ⟨y, ky⟩ ⟨hF', hxy, hpcy, hpy, rfl, htry, h10y, hmy⟩
  have hrr : (y.reg 10).toNat = r := by rw [h10y, h9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := ho
  refine .done ⟨hF', .inl ⟨hxy, by rw [hpcy], hpy, by rw [hmy]; exact o1, by rw [hmy]; exact o2,
    dss, hK.1, by rw [htry, htr], ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hrr]; exact o3
  · rw [hrr, hmy]; exact o4
  · rw [hrr, hmy]; exact o5
  · rw [hrr, hmy]; exact o6
  · rw [hrr, hmy]; exact fun h0 => ⟨hK.2 h0, fun hr => hEnd hr h0⟩

/-- `fread` after delivering all `n` (0x11bd8, s5 = 0). -/
theorem fr_exit_full (dest n f : Word) (s : State) (k : Kern) (he : Entry freadD fread_entry s)
    (hpre : freadP.pre (dest, n, f) s k) (u : State) (hpc : u.pc = 0x11bd8#64) (hc : FrCommon s n f u)
    (dss : List (List Byte)) (htr : u.trace = s.trace ++ dss.map (Event.read (fdOf s.mem f)))
    (ho : FrOut s dest n f dss n.toNat u.mem) (ku : Kern) (hK : FrK s f k dss u.mem ku) :
    PReachK img freadD (fun y => Final freadD y.1 ∧ freadP.Done (dest, n, f) (s, k) y) (u, ku) := by
  have hx := hc.1
  have h20 : u.reg 20 = 0 := hc.2.2.2.2.2.1
  have h9 : u.reg 9 = n := hc.2.2.2.1
  have hb : (u.reg 20 == 0) = true := by rw [h20]; rfl
  nocompiler_run_n 1 [hx, hpc, hb] using []
  refine fr_done dest n f s k he hpre _ ?_ ?_ ?_ ?_ n.toNat n.isLt ?_ dss ?_ ?_ ku ?_ (fun h _ => absurd h (Nat.lt_irrefl _))
  · simp only [nocompiler_state]
  · simp only [nocompiler_state]; exact hx
  · simp only [nocompiler_state]; exact hc.2.1
  · simpa [FrSlots] using hc.2.2.2.2.2.2.2
  · simp only [nocompiler_state, h9, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [nocompiler_state]; exact htr
  · simp only [nocompiler_state]; exact ho
  · simp only [nocompiler_state]; exact hK

/-- `fread` after a short delivery (0x11bec, s5 = `l` left, `c` delivered): a0 = (n - l) / 1. -/
theorem fr_exit_part (dest n f : Word) (s : State) (k : Kern) (he : Entry freadD fread_entry s)
    (hpre : freadP.pre (dest, n, f) s k) (u : State) (hpc : u.pc = 0x11bec#64) (hc : FrCommon s n f u)
    (c l : Nat) (hcl : c + l = n.toNat) (h21 : u.reg 21 = BitVec.ofNat 64 l)
    (dss : List (List Byte)) (htr : u.trace = s.trace ++ dss.map (Event.read (fdOf s.mem f)))
    (ho : FrOut s dest n f dss c u.mem) (ku : Kern) (hK : FrK s f k dss u.mem ku)
    (hEnd : (EofSet s.mem f → FileEnd (fdOf s.mem f) k) → FileEnd (fdOf s.mem f) ku) :
    PReachK img freadD (fun y => Final freadD y.1 ∧ freadP.Done (dest, n, f) (s, k) y) (u, ku) := by
  have hc' := hc
  obtain ⟨hx, -, -, h9, h18, h20, h22, -⟩ := hc'
  have hb : (u.reg 20 == 0) = true := by rw [h20]; rfl
  have hsub : n - BitVec.ofNat 64 l = BitVec.ofNat 64 c := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hdiv : rvDivu (BitVec.ofNat 64 c) 1 = BitVec.ofNat 64 c := by simp [rvDivu]
  nocompiler_run_n 3 [hx, hpc, hb, h22, h21, hsub, h18, hdiv] using []
  obtain ⟨_, a2, _, _, _, _, _, apr, b1, b2, b3, b4, b5, b6, b7, b8⟩ := hc
  refine fr_done dest n f s k he hpre _ ?_ ?_ ?_ ⟨fun q hq => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ c (by omega) ?_ dss ?_ ?_ ku ?_ (fun _ h => hEnd h)
  · simp only [nocompiler_state]
  · simp only [nocompiler_state]; exact hx
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact a2
  · obtain ⟨h10', h9'⟩ := (show ∀ q ∈ [(3 : Reg), 4, 23, 24, 25, 26, 27], q ≠ 10 ∧ q ≠ 9 by decide) q hq
    simp only [State.setPc_reg]
    rw [State.reg_setReg_other _ _ _ _ h9', State.setPc_reg, State.reg_setReg_other _ _ _ _ h10', State.setPc_reg]
    exact apr q hq
  · simp only [nocompiler_state]; exact b1
  · simp only [nocompiler_state]; exact b2
  · simp only [nocompiler_state]; exact b3
  · simp only [nocompiler_state]; exact b4
  · simp only [nocompiler_state]; exact b5
  · simp only [nocompiler_state]; exact b6
  · simp only [nocompiler_state]; exact b7
  · simp only [nocompiler_state]; exact b8
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp only [nocompiler_state]; exact htr
  · simp only [nocompiler_state]; exact ho
  · simp only [nocompiler_state]; exact hK

/-- At `fread`'s loop head (0x11ba4): `c` bytes delivered, `l` left (`c + l = n`, `l > 0`), none buffered,
    the destination's first `c` bytes the stream's (all of it: it has `c`). -/
def FrLoop (s : State) (dest n f : Word) (c l : Nat) (dss : List (List Byte)) (u : State) : Prop :=
  FrCommon s n f u ∧ u.reg 19 = dest + BitVec.ofNat 64 c ∧ u.reg 21 = BitVec.ofNat 64 l ∧ c + l = n.toNat ∧
  0 < l ∧ u.trace = s.trace ++ dss.map (Event.read (fdOf s.mem f)) ∧ StdinFile f u.mem ∧
  FrFrame s dest n f u.mem ∧ frAvail u.mem f = 0 ∧ readBytes u.mem dest c = frStream s f dss

theorem FrOut_of_loop {s : State} {dest n f : Word} {c l : Nat} {dss : List (List Byte)} {u : State}
    (h : FrLoop s dest n f c l dss u) : FrOut s dest n f dss c u.mem := by
  obtain ⟨-, -, -, hcl, hl, -, hS, hF, hA, hB⟩ := h
  have hlen : (frStream s f dss).length = c := by rw [← hB, Auto.readBytes_length]
  refine ⟨hS, hF, by omega, ?_, ?_, fun _ => hA⟩
  · rw [hB, List.take_of_length_le (by omega)]
  · rw [List.drop_of_length_le (by omega)]; simp [frBuffered, hA, readBytes]

/-- A byte of a region disjoint from FILE's 144 bytes is in none of its fields. -/
theorem not_field_of_disj {R : Region} {f p : Word} (hd : R.Disjoint ⟨f, 144⟩) (hp : R.mem p) (o len : Nat)
    (h : o + len ≤ 144) : ¬ (Region.mk (f + BitVec.ofNat 64 o) len).mem p := by
  simp only [Region.Disjoint, Region.mem] at *; bv_omega

theorem not_sub_of_disj {R : Region} {sp p : Word} (hd : R.Disjoint ⟨sp - 144#64, 144⟩) (hp : R.mem p) (a len : Nat)
    (h1 : len ≤ a) (h : a ≤ 144) : ¬ (Region.mk (sp - BitVec.ofNat 64 a) len).mem p := by
  simp only [Region.Disjoint, Region.mem] at *; bv_omega

theorem mem_sub_of {R : Region} {p : Word} (n' : Nat) (hn : n' ≤ R.size) (hp : (Region.mk R.base n').mem p) : R.mem p := by
  simp only [Region.mem] at *; omega

theorem file_mem (f : Word) (o j : Nat) (h : o + j < 144) :
    (Region.mk f 144).mem (f + BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
  simp only [Region.mem]; bv_omega

theorem field_byte_out (f : Word) (o j a len : Nat) (h : o + j + 1 ≤ a ∨ (a + len ≤ o + j ∧ o + j < 144)) (ha : a + len ≤ 144 := by omega) :
    ¬ (Region.mk (f + BitVec.ofNat 64 a) len).mem (f + BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
  simp only [Region.mem]; bv_omega

/-- A FILE byte outside the fields `fread` and its callees write. -/
theorem fr_file_byte {s : State} {dest n f : Word} (hD : FreadDisj dest n f s) (o j : Nat)
    (ho : (64 ≤ o ∧ o + j < 136) ∨ (140 ≤ o + j ∧ o + j < 144)) :
    ¬ (Region.mk (s.reg 2 - 144#64) 144).mem (f + BitVec.ofNat 64 o + BitVec.ofNat 64 j) ∧
    ¬ (Region.mk (s.reg 4 + 18446744073709551452#64) 4).mem (f + BitVec.ofNat 64 o + BitVec.ofNat 64 j) ∧
    ¬ (Region.mk f 4).mem (f + BitVec.ofNat 64 o + BitVec.ofNat 64 j) ∧
    ¬ (Region.mk (f + 8#64) 16).mem (f + BitVec.ofNat 64 o + BitVec.ofNat 64 j) ∧
    ¬ (Region.mk (f + 32#64) 32).mem (f + BitVec.ofNat 64 o + BitVec.ofNat 64 j) ∧
    ¬ (Region.mk (f + 136#64) 4).mem (f + BitVec.ofNat 64 o + BitVec.ofNat 64 j) ∧
    ¬ (Region.mk dest n.toNat).mem (f + BitVec.ofNat 64 o + BitVec.ofNat 64 j) ∧
    ¬ (Region.mk (read64 s.mem (f + 88#64)) (read64 s.mem (f + 96#64)).toNat).mem (f + BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
  obtain ⟨dFS, dES, dEF, dBS, dBE, dBF, dUS, dUE, dUF, dBU⟩ := hD
  have hin := file_mem f o j (by omega)
  exact ⟨not_mem_of_mem_disj dFS.symm hin, not_mem_of_mem_disj dEF hin, by simpa using field_byte_out f o j 0 4 (by omega),
    field_byte_out f o j 8 16 (by omega), field_byte_out f o j 32 32 (by omega), field_byte_out f o j 136 4 (by omega),
    not_mem_of_mem_disj dBF hin, not_mem_of_mem_disj dUF hin⟩

abbrev FrQ (dest n f : Word) (s : State) (k : Kern) : State × Kern → Prop :=
  fun y => Final freadD y.1 ∧ freadP.Done (dest, n, f) (s, k) y

theorem FrLoop_setPc {s : State} {dest n f : Word} {c l : Nat} {dss : List (List Byte)} {u : State} (a : Word)
    (h : FrLoop s dest n f c l dss u) : FrLoop s dest n f c l dss (u.setPc a) := by
  simpa [FrLoop, FrCommon, FrSlots] using h

theorem frAvail_of_eq {m : Word → Byte} {f : Word} (h : read64 m (f + 8#64) = read64 m (f + 16#64)) : frAvail m f = 0 := by
  simp [frAvail, h]

theorem not_frame16 {sp p : Word} (h : ¬ (Region.mk (sp - 144#64) 144).mem p) : ¬ (Region.mk (sp - 64#64 - 16#64) 16).mem p := by
  simp only [Region.mem] at *; bv_omega

theorem not_in_F_sub {f p : Word} (h : ¬ (Region.mk f 144).mem p) (a len : Nat) (ha : a + len ≤ 144) :
    ¬ (Region.mk (f + BitVec.ofNat 64 a) len).mem p := by
  simp only [Region.mem] at *; bv_omega

theorem fr_slot_ok {f sp : Word} (dFS : (Region.mk f 144).Disjoint ⟨sp - 144#64, 144⟩) (o j : Nat) (hj : j < 8)
    (h1 : 8 ≤ o) (h3 : o ≤ 64) :
    ¬ (Region.mk f 4).mem (sp - BitVec.ofNat 64 o + BitVec.ofNat 64 j) ∧
    ¬ (Region.mk (f + 8#64) 16).mem (sp - BitVec.ofNat 64 o + BitVec.ofNat 64 j) ∧
    ¬ (Region.mk (f + 32#64) 32).mem (sp - BitVec.ofNat 64 o + BitVec.ofNat 64 j) ∧
    ¬ (Region.mk (f + 136#64) 4).mem (sp - BitVec.ofNat 64 o + BitVec.ofNat 64 j) ∧
    ¬ (Region.mk (sp - 64#64 - 16#64) 16).mem (sp - BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
  have hin : (Region.mk (sp - 144#64) 144).mem (sp - BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
    simp only [Region.mem]; bv_omega
  have hnF := not_mem_of_mem_disj dFS hin
  refine ⟨by simpa using not_in_F_sub hnF 0 4 (by omega), not_in_F_sub hnF 8 16 (by omega),
    not_in_F_sub hnF 32 32 (by omega), not_in_F_sub hnF 136 4 (by omega), ?_⟩
  simp only [Region.mem]; bv_omega

theorem liftQ {R : State × Kern → Prop} {dest n f : Word} {s : State} {k : Kern} {x : State × Kern}
    (h : PReachK img freadD (FrQ dest n f s k) x) : PReachK img freadD (fun y => FrQ dest n f s k y ∨ R y) x :=
  PReachK.bind (Dom.sub_of_ranges (by decide)) (fun y hy => .done (.inl hy)) h

/-- The call of `__toread` at `fread`'s loop head; `-1` (F_EOF) ends `fread`, else on at 0x11bb4. -/
theorem fr_toread (dest n f : Word) (s : State) (k : Kern) (he : Entry freadD fread_entry s)
    (hpre : freadP.pre (dest, n, f) s k) (c l : Nat) (dss : List (List Byte))
    (u : State) (hpc : u.pc = 0x11ba4#64) (hL : FrLoop s dest n f c l dss u) (ku : Kern)
    (hK : FrK s f k dss u.mem ku) (R : State × Kern → Prop)
    (K : ∀ w, w.pc = 0x11bb4#64 → FrLoop s dest n f c l dss w → FrK s f k dss w.mem ku →
      PReachK img freadD (fun y => FrQ dest n f s k y ∨ R y) (w, ku)) :
    PReachK img freadD (fun y => FrQ dest n f s k y ∨ R y) (u, ku) := by
  have hsp := he.sp
  simp only [Reg.sp] at hsp
  have hpre' := hpre
  obtain ⟨-, -, -, -, hal, -, -, -, -, hle, hD⟩ := hpre'
  have hle : (freadPerm dest n f s).le ku.perm := by rw [hK.1.perm]; exact hle
  have hD' := hD
  obtain ⟨dFS, dES, dEF, dBS, dBE, dBF, dUS, dUE, dUF, dBU⟩ := hD'
  have hL' := hL
  obtain ⟨⟨hx, h2, h8, h9, h18, h20, h22, hsl⟩, h19, h21, hcl, hl0, htr, hS, hFr, hA, hB⟩ := hL'
  have hS' := hS
  obtain ⟨hS64, hSw, hSn, hSb, hSl, -⟩ := hS'
  nocompiler_run_n 3 [hx, hpc] using []
  refine VerifiedProc.call frd_toread_lib f ⟨?_, ?_, ?_, ?_, ?_⟩ ⟨?_, hal, ?_, ?_, ?_⟩ (Dom.sub_of_ranges (by decide)) ?_
  · simp only [nocompiler_state]; rfl
  · simp only [nocompiler_state]; exact hx
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] <;> decide
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] <;> decide
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.sp, h2]; exact sr_al64 hsp
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h8]
  · simp only [nocompiler_state]; exact hSw
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h2]
    refine Perm.le_trans (Perm.le_of (by simp) ?_) hle
    intro r hr
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨f, 144⟩, by simp [freadPerm], Region.within_refl _⟩
    · exact ⟨⟨s.reg 2 - 144#64, 144⟩, by simp [freadPerm], by simp only [Region.within]; bv_omega⟩
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h2]
    have : (Region.mk f 144).Disjoint ⟨s.reg 2 - 144#64, 144⟩ := dFS
    simp only [Region.Disjoint] at this ⊢; bv_omega
  rintro ⟨w, kw⟩ (⟨hxw, hpcw, hpresw, hk, htrw, hfrw, h32, h40, h56, hnord, hclr⟩ | ⟨_, hex⟩)
  rotate_left
  · exact hex.elim
  simp only at hxw hpcw hpresw hk htrw hfrw h32 h40 h56 hnord hclr
  simp (disch := nocompiler_decide_closed) only [nocompiler_state, h2] at hfrw hclr hnord
  rw [hk]
  obtain ⟨h8w, h16w, ha0w, hflw⟩ := hclr hSn
  have hpcw' : w.pc = 0x11bb0#64 := by rw [hpcw]; simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra]
  have hwr : ∀ q ∈ preservedRegs, w.reg q = u.reg q := by
    intro q hq; rw [hpresw q hq]
    obtain ⟨h1, h10⟩ := (show ∀ q ∈ preservedRegs, q ≠ 1 ∧ q ≠ 10 by decide) q hq
    repeat (first | rw [State.setPc_reg] | rw [State.reg_setReg_other _ _ _ _ h1] | rw [State.reg_setReg_other _ _ _ _ h10])
  have htrw' : w.trace = u.trace := by rw [htrw]; simp only [nocompiler_state]
  have dFS' : (Region.mk f 144).Disjoint ⟨s.reg 2 - 144#64, 144⟩ := dFS
  have hagF : ∀ o len, (64 ≤ o ∧ o + len ≤ 136) ∨ (140 ≤ o ∧ o + len ≤ 144) →
      readLE w.mem (f + BitVec.ofNat 64 o) len = readLE u.mem (f + BitVec.ofNat 64 o) len := by
    intro o len ho
    apply readLE_congr; intro j hj
    have hb := fr_file_byte hD o j (by omega)
    exact hfrw _ hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2.1 (not_frame16 hb.1)
  have hslot : ∀ o, 8 ≤ o → o ≤ 64 → read64 w.mem (s.reg 2 - BitVec.ofNat 64 o) = read64 u.mem (s.reg 2 - BitVec.ofNat 64 o) := by
    intro o h1 h3
    apply read64_congr_on; intro j hj
    obtain ⟨a1, a2, a3, a4, a5⟩ := fr_slot_ok dFS' o j hj h1 h3
    exact hfrw _ a1 a2 a3 a4 a5
  have hfr' : ∀ p, ¬ (Region.mk (s.reg 2 - 144#64) 144).mem p → ¬ (Region.mk f 144).mem p → w.mem p = u.mem p := by
    intro p h1 h2'
    exact hfrw p (by simpa using not_in_F_sub h2' 0 4 (by omega)) (not_in_F_sub h2' 8 16 (by omega)) (not_in_F_sub h2' 32 32 (by omega))
      (not_in_F_sub h2' 136 4 (by omega)) (not_frame16 h1)
  have hLw : FrLoop s dest n f c l dss w := by
    refine ⟨⟨hxw, ?_, ?_, ?_, ?_, ?_, ?_, ⟨fun q hq => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩, ?_, ?_, hcl, hl0, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hwr 2 (by decide), h2]
    · rw [hwr 8 (by decide), h8]
    · rw [hwr 9 (by decide), h9]
    · rw [hwr 18 (by decide), h18]
    · rw [hwr 20 (by decide), h20]
    · rw [hwr 22 (by decide), h22]
    · rw [hwr q (by revert hq; revert q; decide)]; exact hsl.1 q hq
    · rw [hslot 8 (by omega) (by omega)]; exact hsl.2.1
    · rw [hslot 16 (by omega) (by omega)]; exact hsl.2.2.1
    · rw [hslot 24 (by omega) (by omega)]; exact hsl.2.2.2.1
    · rw [hslot 32 (by omega) (by omega)]; exact hsl.2.2.2.2.1
    · rw [hslot 40 (by omega) (by omega)]; exact hsl.2.2.2.2.2.1
    · rw [hslot 48 (by omega) (by omega)]; exact hsl.2.2.2.2.2.2.1
    · rw [hslot 56 (by omega) (by omega)]; exact hsl.2.2.2.2.2.2.2.1
    · rw [hslot 64 (by omega) (by omega)]; exact hsl.2.2.2.2.2.2.2.2
    · rw [hwr 19 (by decide), h19]
    · rw [hwr 21 (by decide), h21]
    · rw [htrw', htr]
    · refine ⟨?_, by rw [h40, h56], ?_, ?_, ?_, .inl (frAvail_of_eq (by rw [h8w, h16w]))⟩
      · unfold read64; rw [hagF 64 8 (by omega)]; exact hS64
      · unfold read32; rw [hflw]; exact hSn
      · unfold read64; rw [hagF 96 8 (by omega)]; exact hSb
      · rw [hagF 140 4 (by omega)]; exact hSl
    · intro p a1 a2 a3 a4 a5 a6 a7 a8
      rw [hfrw p a3 a4 a5 a6 (not_frame16 a1)]; exact hFr p a1 a2 a3 a4 a5 a6 a7 a8
    · exact frAvail_of_eq (by rw [h8w, h16w])
    · rw [← hB]
      apply readBytes_congr; intro j hj
      have hin : (Region.mk dest n.toNat).mem (dest + BitVec.ofNat 64 j) := by simp only [Region.mem]; bv_omega
      exact hfr' _ (not_mem_of_mem_disj dBS.symm hin) (not_mem_of_mem_disj dBF.symm hin)
  by_cases hE : read32 u.mem f &&& 16#64 = 0
  · have hb : (w.reg 10 != 0) = false := by rw [ha0w, if_pos hE]; rfl
    nocompiler_run_n 1 [hxw, hpcw', hb] using []
    exact K _ (by simp only [nocompiler_state]) (FrLoop_setPc _ hLw)
      (by simp only [nocompiler_state]; exact FrK_congr (by unfold read32; rw [hflw]) hK)
  · have hb : (w.reg 10 != 0) = true := by rw [ha0w, if_neg hE]; rfl
    nocompiler_run_n 1 [hxw, hpcw', hb] using []
    have hLw' := FrLoop_setPc 0x11bec#64 hLw
    exact liftQ (fr_exit_part dest n f s k he hpre _ (by simp only [nocompiler_state]) hLw'.1 c l hcl hLw'.2.2.1 dss
      hLw'.2.2.2.2.2.1 (FrOut_of_loop hLw') ku
      (by simp only [nocompiler_state]; exact FrK_congr (by unfold read32; rw [hflw]) hK) (fun h0 => hK.2 h0 hE))

end NoCompiler.Libc.Musl.Fread

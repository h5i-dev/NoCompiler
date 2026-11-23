import Examples.Libc.Musl.Fread1
import NoCompiler.Lib.Sext
import NoCompiler.Lib.Signed

set_option maxRecDepth 20000
namespace NoCompiler.Libc.Musl.Fread
open NoCompiler NoCompiler.Linux NoCompiler.Libc NoCompiler.Libc.Musl NoCompiler.Libc.Musl.StdioWrite NoCompiler.Libc.Musl.Toread NoCompiler.Libc.Musl.StdioRead NoCompiler.Libc.Musl.SyscallRet NoCompiler.Libc.Musl.Memcpy NoCompiler.Libc.Musl.Fread NoCompiler.Libc.Musl.FreadImg

theorem covers_field (f : Word) (o len : Nat) (h : o + len ≤ 144) : (Region.mk f 144).covers (f + BitVec.ofNat 64 o) len := by
  simp only [Region.covers]; bv_omega

theorem fr_frame_field {s : State} {dest n f : Word} {m : Word → Byte} (hD : FreadDisj dest n f s)
    (hFr : FrFrame s dest n f m) (o len : Nat) (ho : (64 ≤ o ∧ o + len ≤ 136) ∨ (140 ≤ o ∧ o + len ≤ 144)) :
    readLE m (f + BitVec.ofNat 64 o) len = readLE s.mem (f + BitVec.ofNat 64 o) len := by
  apply readLE_congr; intro j hj
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := fr_file_byte hD o j (by omega)
  exact hFr _ a1 a2 a3 a4 a5 a6 a7 a8

theorem disj_mono {a b a' b' : Word} {n m n' m' : Nat} (h : (Region.mk a n).Disjoint ⟨b, m⟩)
    (h1 : (Region.mk a' n').within ⟨a, n⟩) (h2 : (Region.mk b' m').within ⟨b, m⟩) (hn : 0 < n') (hm : 0 < m') :
    (Region.mk a' n').Disjoint ⟨b', m'⟩ := by
  simp only [Region.Disjoint, Region.within] at *; bv_omega

theorem within_sub_c {dest n : Word} (c l : Nat) (h : c + l = n.toNat) :
    (Region.mk (dest + BitVec.ofNat 64 c) l).within ⟨dest, n.toNat⟩ := by
  have := n.isLt; simp only [Region.within]; bv_omega

theorem within_s80 (sp : Word) : (Region.mk (sp - 64#64 - 80#64) 80).within ⟨sp - 144#64, 144⟩ := by
  simp only [Region.within]; bv_omega

theorem within_f128 (f : Word) : (Region.mk f 128).within ⟨f, 144⟩ := by
  simp only [Region.within]; bv_omega

/-- `__stdio_read`'s precondition at `fread`'s call of `f->read(f, dest + c, l)`. -/
theorem fr_sread_pre (dest n f : Word) (s : State) (k : Kern) (hpre : freadP.pre (dest, n, f) s k) (c l : Nat)
    (hcl : c + l = n.toNat) (hl0 : 0 < l) (z : State) (h10 : z.reg 10 = f) (h11 : z.reg 11 = dest + BitVec.ofNat 64 c)
    (h12 : z.reg 12 = BitVec.ofNat 64 l) (h2 : z.reg 2 = s.reg 2 - 64#64) (h4 : z.reg 4 = s.reg 4)
    (hfb : read64 z.mem (f + 88#64) = read64 s.mem (f + 88#64)) (hbs : read64 z.mem (f + 96#64) = read64 s.mem (f + 96#64))
    (hfd : fdOf z.mem f = fdOf s.mem f) (k' : Kern) (hkp : k'.perm = k.perm) :
    stdioReadP.pre (f, dest + BitVec.ofNat 64 c, BitVec.ofNat 64 l) z k' := by
  obtain ⟨-, -, -, -, hal, hale, hS, hB, hfdn, hle, hD⟩ := hpre
  obtain ⟨dFS, dES, dEF, dBS, dBE, dBF, dUS, dUE, dUF, dBU⟩ := hD
  have hn := n.isLt
  have hl' : (BitVec.ofNat 64 l).toNat = l := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hbs0 : 0 < (read64 s.mem (f + 96#64)).toNat := by
    rcases Nat.eq_zero_or_pos (read64 s.mem (f + 96#64)).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hS.2.2.2.1
    · exact h
  have wB := within_sub_c (dest := dest) c l hcl
  have wS := within_s80 (s.reg 2)
  have wF := within_f128 f
  have wE := Region.within_refl (Region.mk (s.reg 4 + 18446744073709551452#64) 4)
  have wU := Region.within_refl (Region.mk (read64 s.mem (f + 88#64)) (read64 s.mem (f + 96#64)).toNat)
  refine ⟨h10, h11, h12, hal, by rw [h4]; exact hale, by rw [hl']; exact hl0, by rw [hbs]; exact hS.2.2.2.1,
    by rw [hl', hbs]; omega, by rw [hfd]; exact hfdn, ?_, ?_⟩
  · refine Perm.le_trans (Perm.le_of (by simp [stdioReadPerm]) ?_) (by rw [hkp]; exact hle)
    intro r hr
    simp only [stdioReadPerm, h2, h4, hfb, hbs, hl', List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [freadPerm], wF⟩
    · exact ⟨_, by simp [freadPerm], wS⟩
    · exact ⟨_, by simp [freadPerm], wE⟩
    · exact ⟨_, by simp [freadPerm], wB⟩
    · exact ⟨_, by simp [freadPerm], wU⟩
  · simp only [StdioReadDisj, h2, h4, hfb, hbs, hl']
    exact ⟨disj_mono dFS wF wS (by omega) (by omega), disj_mono dES wE wS (by omega) (by omega),
      disj_mono dEF wE wF (by omega) (by omega), disj_mono dBS wB wS hl0 (by omega), disj_mono dBE wB wE hl0 (by omega),
      disj_mono dBF wB wF hl0 (by omega), disj_mono dUS wU wS hbs0 (by omega), disj_mono dUE wU wE hbs0 (by omega),
      disj_mono dUF wU wF hbs0 (by omega), disj_mono dBU wB wU hl0 hbs0⟩

theorem FrCommon_setPc {s : State} {n f : Word} {u : State} (a : Word) (h : FrCommon s n f u) :
    FrCommon s n f (u.setPc a) := by
  simpa [FrCommon, FrSlots] using h

theorem FrCommon_setReg {s : State} {n f : Word} {u : State} (q : Reg) (hq : q = 19 ∨ q = 21) (v : Word)
    (h : FrCommon s n f u) : FrCommon s n f (u.setReg q v) := by
  obtain ⟨a1, a2, a8, a9, a18, a20, a22, apr, b1, b2, b3, b4, b5, b6, b7, b8⟩ := h
  have hne : ∀ r ∈ [(2 : Reg), 8, 9, 18, 20, 22, 3, 4, 23, 24, 25, 26, 27], r ≠ q := by
    rcases hq with rfl | rfl <;> decide
  refine ⟨by simpa using a1, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, by simpa using b1, by simpa using b2, by simpa using b3,
    by simpa using b4, by simpa using b5, by simpa using b6, by simpa using b7, by simpa using b8⟩
  · rw [State.reg_setReg_other _ _ _ _ (hne 2 (by simp))]; exact a2
  · rw [State.reg_setReg_other _ _ _ _ (hne 8 (by simp))]; exact a8
  · rw [State.reg_setReg_other _ _ _ _ (hne 9 (by simp))]; exact a9
  · rw [State.reg_setReg_other _ _ _ _ (hne 18 (by simp))]; exact a18
  · rw [State.reg_setReg_other _ _ _ _ (hne 20 (by simp))]; exact a20
  · rw [State.reg_setReg_other _ _ _ _ (hne 22 (by simp))]; exact a22
  · have hne' : ∀ r ∈ [(3 : Reg), 4, 23, 24, 25, 26, 27], r ≠ q := by rcases hq with rfl | rfl <;> decide
    rw [State.reg_setReg_other _ _ _ _ (hne' r hr)]; exact apr r hr

theorem ofNat_ne_zero' (r : Nat) (h1 : 0 < r) (h2 : r < 2 ^ 64) : BitVec.ofNat 64 r ≠ 0 := by
  intro h; have := congrArg BitVec.toNat h; simp at this; omega

theorem availC (fb : Word) (m : Nat) (hm : 1 ≤ m) (hm' : m < 2 ^ 64) :
    (fb + BitVec.ofNat 64 m - (fb + 1#64)).toNat = m - 1 := by
  bv_omega

theorem withinC (fb : Word) (bs m : Nat) (h : m + 1 ≤ bs) (hb : bs < 2 ^ 64 := by omega) :
    (Region.mk (fb + 1#64) m).within ⟨fb, bs⟩ := by
  simp only [Region.within]; bv_omega

theorem FrCommon_mod {s : State} {n f : Word} {u : State} (h : FrCommon s n f u) (y : State)
    (hx : y.exit = u.exit) (hm : y.mem = u.mem)
    (hr : ∀ r ∈ [(2 : Reg), 8, 9, 18, 20, 22, 3, 4, 23, 24, 25, 26, 27], y.reg r = u.reg r) : FrCommon s n f y := by
  obtain ⟨a1, a2, a8, a9, a18, a20, a22, apr, b1, b2, b3, b4, b5, b6, b7, b8⟩ := h
  refine ⟨by rw [hx]; exact a1, by rw [hr 2 (by simp)]; exact a2, by rw [hr 8 (by simp)]; exact a8,
    by rw [hr 9 (by simp)]; exact a9, by rw [hr 18 (by simp)]; exact a18, by rw [hr 20 (by simp)]; exact a20,
    by rw [hr 22 (by simp)]; exact a22, fun q hq => by
      rw [hr q ((show ∀ q ∈ [(3 : Reg), 4, 23, 24, 25, 26, 27], q ∈ [(2 : Reg), 8, 9, 18, 20, 22, 3, 4, 23, 24, 25, 26, 27] by decide) q hq)]
      exact apr q hq,
    by rw [hm]; exact b1, by rw [hm]; exact b2, by rw [hm]; exact b3, by rw [hm]; exact b4, by rw [hm]; exact b5,
    by rw [hm]; exact b6, by rw [hm]; exact b7, by rw [hm]; exact b8⟩

theorem avail_sub (rpos rend : Word) (K : Nat) (h : K ≤ (rend - rpos).toNat) :
    (rend - (rpos + BitVec.ofNat 64 K)).toNat = (rend - rpos).toNat - K := by
  have := (rend - rpos).isLt; bv_omega

theorem mem_of_within {a b : Word} {n m : Nat} (h : (Region.mk a n).within ⟨b, m⟩) (j : Nat) (hj : j < n) :
    (Region.mk b m).mem (a + BitVec.ofNat 64 j) := by
  simp only [Region.within, Region.mem] at *; bv_omega

theorem within_shift {a b : Word} {n m : Nat} (h : (Region.mk a n).within ⟨b, m⟩) (K : Nat) (hK : K ≤ n) :
    (Region.mk (a + BitVec.ofNat 64 K) (n - K)).within ⟨b, m⟩ := by
  simp only [Region.within] at *; bv_omega

theorem FrCommon_mod' {s : State} {n f : Word} {u : State} (h : FrCommon s n f u) (y : State)
    (hx : y.exit = u.exit)
    (hs : ∀ o, 8 ≤ o → o ≤ 64 → read64 y.mem (s.reg 2 - BitVec.ofNat 64 o) = read64 u.mem (s.reg 2 - BitVec.ofNat 64 o))
    (hr : ∀ r ∈ [(2 : Reg), 8, 9, 18, 20, 22, 3, 4, 23, 24, 25, 26, 27], y.reg r = u.reg r) : FrCommon s n f y := by
  obtain ⟨a1, a2, a8, a9, a18, a20, a22, apr, b1, b2, b3, b4, b5, b6, b7, b8⟩ := h
  refine ⟨by rw [hx]; exact a1, by rw [hr 2 (by simp)]; exact a2, by rw [hr 8 (by simp)]; exact a8,
    by rw [hr 9 (by simp)]; exact a9, by rw [hr 18 (by simp)]; exact a18, by rw [hr 20 (by simp)]; exact a20,
    by rw [hr 22 (by simp)]; exact a22, fun q hq => by
      rw [hr q ((show ∀ q ∈ [(3 : Reg), 4, 23, 24, 25, 26, 27], q ∈ [(2 : Reg), 8, 9, 18, 20, 22, 3, 4, 23, 24, 25, 26, 27] by decide) q hq)]
      exact apr q hq,
    by rw [hs 8 (by omega) (by omega)]; exact b1, by rw [hs 16 (by omega) (by omega)]; exact b2,
    by rw [hs 24 (by omega) (by omega)]; exact b3, by rw [hs 32 (by omega) (by omega)]; exact b4,
    by rw [hs 40 (by omega) (by omega)]; exact b5, by rw [hs 48 (by omega) (by omega)]; exact b6,
    by rw [hs 56 (by omega) (by omega)]; exact b7, by rw [hs 64 (by omega) (by omega)]; exact b8⟩

theorem readLE_lt' (m : Word → Byte) (a : Word) (n : Nat) : readLE m a n < 256 ^ n := by
  induction n generalizing a with
  | zero => simp [readLE]
  | succ n ih => simp only [readLE, Nat.pow_succ]; have := ih (a + 1); have := (m a).isLt; omega

theorem nord_or (r : Nat) (hr : r < 2 ^ 32) (c : BitVec 32) (hc : c &&& 4#32 = 0) (h : BitVec.ofNat 64 r &&& 4#64 = 0) :
    BitVec.ofNat 64 (BitVec.ofNat 32 r ||| c).toNat &&& 4#64 = 0 := NoCompiler.Libc.ofNat_or_and4_eq_zero r hr c hc h

theorem not_s80 {sp p : Word} (h : ¬ (Region.mk (sp - 144#64) 144).mem p) : ¬ (Region.mk (sp - 64#64 - 80#64) 80).mem p := by
  simp only [Region.mem] at *; bv_omega

theorem not_sub_dest {dest n p : Word} (c l : Nat) (hcl : c + l = n.toNat) (h : ¬ (Region.mk dest n.toNat).mem p) :
    ¬ (Region.mk (dest + BitVec.ofNat 64 c) l).mem p := by
  have := n.isLt; simp only [Region.mem] at *; bv_omega

theorem dest_low_out {dest : Word} (c l j : Nat) (hj : j < c) (h : c + l < 2 ^ 64) :
    ¬ (Region.mk (dest + BitVec.ofNat 64 c) l).mem (dest + BitVec.ofNat 64 j) := by
  simp only [Region.mem]; bv_omega

theorem slot_out80 (sp : Word) (o j : Nat) (hj : j < 8) (h1 : 8 ≤ o) (h3 : o ≤ 64) :
    ¬ (Region.mk (sp - 64#64 - 80#64) 80).mem (sp - BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
  simp only [Region.mem]; bv_omega

theorem slot_in144 (sp : Word) (o j : Nat) (hj : j < 8) (h1 : 8 ≤ o) (h3 : o ≤ 64) :
    (Region.mk (sp - 144#64) 144).mem (sp - BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
  simp only [Region.mem]; bv_omega

theorem dest_in {dest n : Word} (j : Nat) (hj : j < n.toNat) : (Region.mk dest n.toNat).mem (dest + BitVec.ofNat 64 j) := by
  have := n.isLt; simp only [Region.mem]; bv_omega

theorem readBytes_succ_drop (m : Word → Byte) (a : Word) (k : Nat) :
    readBytes m (a + 1#64) k = (readBytes m a (k + 1)).drop 1 := by
  simp [readBytes]

/-- The call `f->read(f, dest + c, l)` (= `__stdio_read`) from 0x11bb4, and what follows. -/
theorem fr_sread (dest n f : Word) (s : State) (k : Kern) (he : Entry freadD fread_entry s)
    (hpre : freadP.pre (dest, n, f) s k) (c l : Nat) (dss : List (List Byte))
    (w : State) (hpc : w.pc = 0x11bb4#64) (hL : FrLoop s dest n f c l dss w) (ku : Kern)
    (hK : FrK s f k dss w.mem ku) :
    PReachK img freadD (fun y => FrQ dest n f s k y ∨ ∃ c' l' dss', l' < l ∧ FrK s f k dss' y.1.mem y.2 ∧
      y.1.pc = 0x11ba4#64 ∧ FrLoop s dest n f c' l' dss' y.1) (w, ku) := by
  have hsp := he.sp
  simp only [Reg.sp] at hsp
  have hpre' := hpre
  obtain ⟨-, -, -, -, hal, hale, -, hB, -, hle, hD⟩ := hpre'
  have hle : (freadPerm dest n f s).le ku.perm := by rw [hK.1.perm]; exact hle
  have hD' := hD
  obtain ⟨dFS, dES, dEF, dBS, dBE, dBF, dUS, dUE, dUF, dBU⟩ := hD'
  have hL' := hL
  obtain ⟨⟨hx, h2, h8, h9, h18, h20, h22, hsl⟩, h19, h21, hcl, hl0, htr, hS, hFr, hA, hBy⟩ := hL'
  have hS' := hS
  obtain ⟨hS64, hSw, hSn, hSb, hSl, -⟩ := hS'
  have h4 : w.reg 4 = s.reg 4 := hsl.1 4 (by decide)
  have hn := n.isLt
  have hlt : l < 2 ^ 64 := by omega
  have hl' : (BitVec.ofNat 64 l).toNat = l := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hfb : read64 w.mem (f + 88#64) = read64 s.mem (f + 88#64) := by unfold read64; rw [fr_frame_field hD hFr 88 8 (by omega)]
  have hbs : read64 w.mem (f + 96#64) = read64 s.mem (f + 96#64) := by unfold read64; rw [fr_frame_field hD hFr 96 8 (by omega)]
  have hfd : fdOf w.mem f = fdOf s.mem f := by unfold fdOf; rw [fr_frame_field hD hFr 120 4 (by omega)]
  have rF64 : ku.perm.canRead (f + 64#64) 8 := Perm.canRead_of_canWrite
    (hle.write _ _ (.inr ⟨⟨f, 144⟩, by simp [freadPerm], covers_field f 64 8 (by omega)⟩))
  have al64 : aligned (f + 64#64) 8 := sw_alF hal 64 rfl
  nocompiler_run_n 1 [hx, hpc, h8, al64, hS64] using [rF64]
  nocompiler_run_n 4 [hx] using [rF64]
  refine VerifiedProc.call frd_stdio_read_lib (f, dest + BitVec.ofNat 64 c, BitVec.ofNat 64 l) ⟨?_, ?_, ?_, ?_, ?_⟩
    (fr_sread_pre dest n f s k hpre c l hcl hl0 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ku hK.1.perm) (Dom.sub_of_ranges (by decide)) ?_
  · simp only [nocompiler_state]; rfl
  · simp only [nocompiler_state]; exact hx
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] <;> decide
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] <;> decide
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.sp, h2]; exact sr_al64 hsp
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h8]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h19]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h21]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h2]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h4]
  · simp only [nocompiler_state]; exact hfb
  · simp only [nocompiler_state]; exact hbs
  · simp only [nocompiler_state]; exact hfd
  rintro ⟨y, ky⟩ (⟨hxy, hpcy, hpresy, hfry, hcase⟩ | ⟨_, hex⟩)
  rotate_left
  · exact hex.elim
  simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra, h2, h4, hfb, hbs, hfd, hl'] at hxy hpcy hpresy hfry hcase
  have hyr : ∀ q ∈ preservedRegs, y.reg q = w.reg q := by
    intro q hq; rw [hpresy q hq]
    obtain ⟨a1, a10, a11, a12, a13⟩ := (show ∀ q ∈ preservedRegs, q ≠ 1 ∧ q ≠ 10 ∧ q ≠ 11 ∧ q ≠ 12 ∧ q ≠ 13 by decide) q hq
    repeat (first | rw [State.setPc_reg] | rw [State.reg_setReg_other _ _ _ _ a1] | rw [State.reg_setReg_other _ _ _ _ a10] | rw [State.reg_setReg_other _ _ _ _ a11] | rw [State.reg_setReg_other _ _ _ _ a12] | rw [State.reg_setReg_other _ _ _ _ a13])
  have hyw : ∀ p, ¬ (Region.mk (s.reg 2 - 144#64) 144).mem p → ¬ (Region.mk (s.reg 4 + 18446744073709551452#64) 4).mem p →
      ¬ (Region.mk f 4).mem p → ¬ (Region.mk (f + 8#64) 16).mem p → ¬ (Region.mk dest n.toNat).mem p →
      ¬ (Region.mk (read64 s.mem (f + 88#64)) (read64 s.mem (f + 96#64)).toNat).mem p → y.mem p = w.mem p :=
    fun p a1 a2 a3 a4 a5 a6 => hfry p (not_s80 a1) a2 a3 a4 (not_sub_dest c l hcl a5) a6
  have hFy : ∀ o len, 24 ≤ o → o + len ≤ 144 → readLE y.mem (f + BitVec.ofNat 64 o) len = readLE w.mem (f + BitVec.ofNat 64 o) len := by
    intro o len h1 h3
    apply readLE_congr; intro j hj
    have hin := file_mem f o j (by omega)
    exact hyw _ (not_mem_of_mem_disj dFS.symm hin) (not_mem_of_mem_disj dEF hin)
      (by simpa using field_byte_out f o j 0 4 (by omega)) (field_byte_out f o j 8 16 (by omega))
      (not_mem_of_mem_disj dBF hin) (not_mem_of_mem_disj dUF hin)
  have hslot : ∀ o, 8 ≤ o → o ≤ 64 → read64 y.mem (s.reg 2 - BitVec.ofNat 64 o) = read64 w.mem (s.reg 2 - BitVec.ofNat 64 o) := by
    intro o h1 h3
    apply read64_congr_on; intro j hj
    have hin := slot_in144 (s.reg 2) o j hj h1 h3
    have hnF := not_mem_of_mem_disj dFS hin
    exact hfry _ (slot_out80 _ o j hj h1 h3) (not_mem_of_mem_disj dES hin) (by simpa using not_in_F_sub hnF 0 4 (by omega))
      (not_in_F_sub hnF 8 16 (by omega)) (not_sub_dest c l hcl (not_mem_of_mem_disj dBS hin)) (not_mem_of_mem_disj dUS hin)
  have hdest : readBytes y.mem dest c = readBytes w.mem dest c := by
    apply readBytes_congr; intro j hj
    have hin := dest_in (dest := dest) (n := n) j (by omega)
    have hnF := not_mem_of_mem_disj dBF.symm hin
    exact hfry _ (not_s80 (not_mem_of_mem_disj dBS.symm hin)) (not_mem_of_mem_disj dBE.symm hin)
      (by simpa using not_in_F_sub hnF 0 4 (by omega)) (not_in_F_sub hnF 8 16 (by omega))
      (dest_low_out c l j hj (by omega)) (not_mem_of_mem_disj dBU.symm hin)
  have hFry : FrFrame s dest n f y.mem := by
    intro p a1 a2 a3 a4 a5 a6 a7 a8
    rw [hyw p a1 a2 a3 a4 a7 a8]; exact hFr p a1 a2 a3 a4 a5 a6 a7 a8
  have hSy : read32 y.mem f &&& 4#64 = 0 → (frAvail y.mem f = 0 ∨
      (Region.mk (read64 y.mem (f + 8#64)) (frAvail y.mem f)).within ⟨read64 y.mem (f + 88#64), (read64 y.mem (f + 96#64)).toNat⟩) →
      StdinFile f y.mem := by
    intro hn ha
    refine ⟨?_, ?_, hn, ?_, ?_, ha⟩
    · unfold read64; rw [hFy 64 8 (by omega) (by omega)]; exact hS64
    · unfold read64; rw [hFy 40 8 (by omega) (by omega), hFy 56 8 (by omega) (by omega)]; exact hSw
    · unfold read64; rw [hFy 96 8 (by omega) (by omega)]; exact hSb
    · rw [hFy 140 4 (by omega) (by omega)]; exact hSl
  have hyc : FrSlots s y := by
    refine ⟨fun q hq => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hyr q (by revert hq; revert q; decide)]; exact hsl.1 q hq
    · rw [hslot 8 (by omega) (by omega)]; exact hsl.2.1
    · rw [hslot 16 (by omega) (by omega)]; exact hsl.2.2.1
    · rw [hslot 24 (by omega) (by omega)]; exact hsl.2.2.2.1
    · rw [hslot 32 (by omega) (by omega)]; exact hsl.2.2.2.2.1
    · rw [hslot 40 (by omega) (by omega)]; exact hsl.2.2.2.2.2.1
    · rw [hslot 48 (by omega) (by omega)]; exact hsl.2.2.2.2.2.2.1
    · rw [hslot 56 (by omega) (by omega)]; exact hsl.2.2.2.2.2.2.2.1
    · rw [hslot 64 (by omega) (by omega)]; exact hsl.2.2.2.2.2.2.2.2
  have hyC : FrCommon s n f y := ⟨hxy, by rw [hyr 2 (by decide), h2], by rw [hyr 8 (by decide), h8],
    by rw [hyr 9 (by decide), h9], by rw [hyr 18 (by decide), h18], by rw [hyr 20 (by decide), h20],
    by rw [hyr 22 (by decide), h22], hyc⟩
  have hlen : (frStream s f dss).length = c := by rw [← hBy, Auto.readBytes_length]
  have hrl := readLE_lt' w.mem f 4
  have hwn : BitVec.ofNat 64 (readLE w.mem f 4) &&& 4#64 = 0 := hSn
  have hy19 : y.reg 19 = dest + BitVec.ofNat 64 c := by rw [hyr 19 (by decide), h19]
  have hy21 : y.reg 21 = BitVec.ofNat 64 l := by rw [hyr 21 (by decide), h21]
  have hOut : ∀ dss', frStream s f dss' = frStream s f dss → StdinFile f y.mem → frAvail y.mem f = 0 →
      FrOut s dest n f dss' c y.mem := by
    intro dss' hst hS' hA'
    refine ⟨hS', hFry, by omega, ?_, ?_, fun _ => hA'⟩
    · rw [hst, hdest, hBy, List.take_of_length_le (by omega)]
    · rw [hst, List.drop_of_length_le (by omega)]; simp [frBuffered, hA', readBytes]
  have hAv : read64 y.mem (f + 8#64) = read64 w.mem (f + 8#64) → read64 y.mem (f + 16#64) = read64 w.mem (f + 16#64) →
      frAvail y.mem f = 0 := by
    intro e1 e2; unfold frAvail; rw [e1, e2]; exact hA
  have hpcy' : y.pc = 0x11bc8#64 := hpcy
  have hN0 : 0 < l - 1 + (read64 s.mem (f + 96#64)).toNat := by
    have : (read64 s.mem (f + 96#64)).toNat ≠ 0 := fun h => hSb (by rw [hbs]; exact BitVec.eq_of_toNat_eq (by simpa using h))
    omega
  rcases hcase with ⟨ds, hRK, hdl, htry, hA0, hB0, hC0⟩ | ⟨hky, hnf, htry, h10y, hfly, h8y, h16y⟩
  · by_cases hds : ds = []
    · subst hds
      obtain ⟨h10y, hfly, h8y, h16y⟩ := hA0 rfl
      have hb : (y.reg 10 == 0) = true := by rw [h10y]; rfl
      nocompiler_run_n 1 [hxy, hpcy', hb] using [rF64]
      have hav := hAv h8y h16y
      have hS' : StdinFile f y.mem := hSy (by unfold read32; rw [hfly]; exact nord_or _ hrl _ (by decide) hwn) (.inl hav)
      have hFE := FileEnd.of_nil hRK hN0
      exact liftQ (fr_exit_part dest n f s k he hpre _ (by simp only [nocompiler_state]) (FrCommon_setPc 0x11bec#64 hyC) c l hcl
        (by simp only [nocompiler_state]; exact hy21) (dss ++ [[]])
        (by simp only [nocompiler_state]; rw [htry, htr]; simp) (hOut _ (by simp [frStream]) hS' hav) ky
        (FrK_end (hK.1.snoc hRK) hFE) (fun _ => hFE))
    · have hpos : 0 < ds.length := List.length_pos_iff.mpr hds
      have hstr : frStream s f (dss ++ [ds]) = frStream s f dss ++ ds := by simp [frStream, List.flatten_append]
      have htr' : y.trace = s.trace ++ (dss ++ [ds]).map (Event.read (fdOf s.mem f)) := by rw [htry, htr]; simp
      by_cases hle : ds.length ≤ l - 1
      · obtain ⟨h10y, hrb, hfly, h8y, h16y⟩ := hB0 hpos hle
        have hdsl : ds.length < 2 ^ 64 := Nat.lt_of_le_of_lt hle (by omega)
        have hb : (y.reg 10 == 0) = false := by
          rw [h10y]; simpa using ofNat_ne_zero' _ hpos hdsl
        have hsubB : BitVec.ofNat 64 l - BitVec.ofNat 64 ds.length = BitVec.ofNat 64 (l - ds.length) := by
          apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
        have haddB : dest + BitVec.ofNat 64 c + BitVec.ofNat 64 ds.length = dest + BitVec.ofNat 64 (c + ds.length) := by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        have hb2 : (BitVec.ofNat 64 (l - ds.length) != 0) = true := by
          simpa using ofNat_ne_zero' (l - ds.length) (by omega) (by omega)
        nocompiler_run_n 1 [hxy, hpcy', hb] using [rF64]
        nocompiler_run_n 1 [hxy, hy21, h10y, hsubB] using [rF64]
        nocompiler_run_n 1 [hxy, hy19, h10y, haddB] using [rF64]
        nocompiler_run_n 1 [hxy, hb2] using [rF64]
        have hav := hAv h8y h16y
        have hS' : StdinFile f y.mem := hSy (by unfold read32; rw [hfly]; exact hwn) (.inl hav)
        refine .done (.inr ⟨c + ds.length, l - ds.length, dss ++ [ds], by omega,
          by simp only [nocompiler_state]; exact FrK_step hK hRK (by unfold read32; rw [hfly]), by simp only [nocompiler_state],
          ⟨FrCommon_setPc _ (FrCommon_setReg 19 (.inl rfl) _ (FrCommon_setPc _ (FrCommon_setReg 21 (.inr rfl) _ (FrCommon_setPc _ hyC)))),
            ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩⟩)
        · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
        · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
        · simp only [nocompiler_state]; exact htr'
        · simp only [nocompiler_state]; exact hS'
        · simp only [nocompiler_state]; exact hFry
        · simp only [nocompiler_state]; exact hav
        · simp only [nocompiler_state]
          rw [readBytes_add, hdest, hBy, hrb, hstr]
      · obtain ⟨h10y, hrb, hbuf, hfly, h8y, h16y⟩ := hC0 (by omega)
        have hb : (y.reg 10 == 0) = false := by
          rw [h10y]; simpa using ofNat_ne_zero' l hl0 hlt
        have hb2 : (BitVec.ofNat 64 l - BitVec.ofNat 64 l != 0) = false := by simp
        nocompiler_run_n 1 [hxy, hpcy', hb] using [rF64]
        nocompiler_run_n 1 [hxy, hy21, h10y] using [rF64]
        nocompiler_run_n 1 [hxy] using [rF64]
        nocompiler_run_n 1 [hxy, hb2] using [rF64]
        have hm : 1 ≤ ds.length - (l - 1) := by omega
        have hbs0 := hdl
        have hav : frAvail y.mem f = ds.length - l := by
          unfold frAvail; rw [h8y, h16y]; exact (availC _ _ hm (by omega)).trans (by omega)
        have h88 : read64 y.mem (f + 88#64) = read64 s.mem (f + 88#64) := by
          unfold read64; rw [hFy 88 8 (by omega) (by omega)]; exact hfb
        have h96 : read64 y.mem (f + 96#64) = read64 s.mem (f + 96#64) := by
          unfold read64; rw [hFy 96 8 (by omega) (by omega)]; exact hbs
        have hS' : StdinFile f y.mem := hSy (by unfold read32; rw [hfly]; exact hwn)
          (.inr (by rw [hav, h8y, h88, h96]; exact withinC _ _ _ (by omega)))
        refine liftQ (fr_exit_full dest n f s k he hpre _ (by simp only [nocompiler_state])
          (FrCommon_setPc _ (FrCommon_setReg 19 (.inl rfl) _ (FrCommon_setPc _ (FrCommon_setReg 21 (.inr rfl) _ (FrCommon_setPc _ hyC)))))
          (dss ++ [ds]) (by simp only [nocompiler_state]; exact htr') ?_ ky
          (by simp only [nocompiler_state]; exact FrK_step hK hRK (by unfold read32; rw [hfly])))
        simp only [nocompiler_state]
        refine ⟨hS', hFry, Nat.le_refl _, ?_, ?_, fun h => absurd h (Nat.lt_irrefl _)⟩
        · rw [← hcl, readBytes_add, hdest, hBy, hrb, hstr, ← hlen, List.take_length_add_append]
        · unfold frBuffered
          rw [hav, h8y, ← hcl, hstr, ← hlen, List.drop_length_add_append, readBytes_succ_drop,
            show ds.length - l + 1 = ds.length - (l - 1) by omega, hbuf, List.drop_drop]
          exact congrArg (List.drop · ds) (by omega)
  · have hb : (y.reg 10 == 0) = true := by rw [h10y]; rfl
    nocompiler_run_n 1 [hxy, hpcy', hb] using [rF64]
    have hav := hAv h8y h16y
    have hS' : StdinFile f y.mem := hSy (by unfold read32; rw [hfly]; exact nord_or _ hrl _ (by decide) hwn) (.inl hav)
    have hFE : FileEnd (fdOf s.mem f) ku := fun fl h hin => absurd hin (hnf fl h)
    rw [hky]
    exact liftQ (fr_exit_part dest n f s k he hpre _ (by simp only [nocompiler_state]) (FrCommon_setPc 0x11bec#64 hyC) c l hcl
      (by simp only [nocompiler_state]; exact hy21) dss
      (by simp only [nocompiler_state]; rw [htry, htr]) (hOut _ rfl hS' hav) ku (FrK_end hK.1 hFE) (fun _ => hFE))

/-- `fread`'s loop, from its head to the end, by the count left. -/
theorem fr_loop (dest n f : Word) (s : State) (k : Kern) (he : Entry freadD fread_entry s)
    (hpre : freadP.pre (dest, n, f) s k) :
    ∀ x : State × Kern, (∃ c l dss, FrK s f k dss x.1.mem x.2 ∧ x.1.pc = 0x11ba4#64 ∧ FrLoop s dest n f c l dss x.1) →
      PReachK img freadD (FrQ dest n f s k) x := by
  refine PReachK.loop _ (fun x => (x.1.reg 21).toNat) ?_
  rintro ⟨u, ku⟩ ⟨c, l, dss, hku, hpc, hL⟩
  simp only at hku hpc hL
  have hl : (u.reg 21).toNat = l := by
    rw [hL.2.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := n.isLt; have := hL.2.2.2.1; omega)]
  refine fr_toread dest n f s k he hpre c l dss u hpc hL ku hku _ (fun w hpw hLw hKw => ?_)
  refine PReachK.bind (Dom.sub_of_ranges (by decide)) ?_ (fr_sread dest n f s k he hpre c l dss w hpw hLw ku hKw)
  rintro y (hq | ⟨c', l', dss', hlt, hk, hpcy, hLy⟩)
  · exact .done (.inl hq)
  · refine .done (.inr ⟨⟨c', l', dss', hk, hpcy, hLy⟩, ?_⟩)
    simp only
    rw [hl, hLy.2.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := n.isLt; have := hLy.2.2.2.1; omega)]
    exact hlt

theorem lock_neg (r : Nat) (h1 : 2 ^ 31 ≤ r) (h2 : r < 2 ^ 32) :
    BitVec.slt (BitVec.signExtend 64 (BitVec.ofNat 32 r)) 0 = true := by
  have hv := Lib.toNat_signExtend_ofNat_of_ge (w := 32) (k := r) (by decide) (by simpa using h1) h2
  exact Lib.slt_of_neg_nonneg (by rw [hv]; omega) (by decide)

end NoCompiler.Libc.Musl.Fread

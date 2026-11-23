import Examples.Libc.Musl.Fwritex3
import NoCompiler.Lib.Signed
import NoCompiler.Lib.Sext

/-!
# `__fwritex` on slen's stdout, at the process level

The rule lemmas of `Examples.Libc.Fwritex` assembled for the case slen's `fwrite` makes: stdout before its
first write (wend = 0, so `__towrite` first), the data fits in the buffer and ends in '\n' (so the scan
stops at once and `f->write` = `__stdout_write` writes it all), then a 0-byte `memcpy`. The region
includes `__stdout_write` (the indirect call `f->write`).
-/
set_option maxRecDepth 20000
namespace NoCompiler.Libc.Musl.Fwrite
open NoCompiler NoCompiler.Linux NoCompiler.Libc NoCompiler.Libc.Musl NoCompiler.Libc.Musl.StdioWrite NoCompiler.Libc.Musl.Memcpy NoCompiler.Libc.Musl.Towrite NoCompiler.Libc.Musl.StdoutWrite NoCompiler.Libc.Musl.Fwritex NoCompiler.Libc.Musl.Fwrite NoCompiler.Libc.Musl.FwriteImg


theorem lock_neg (r : Nat) (h1 : 2 ^ 31 ≤ r) (h2 : r < 2 ^ 32) :
    BitVec.slt (BitVec.signExtend 64 (BitVec.ofNat 32 r)) 0 = true := by
  have hv := Lib.toNat_signExtend_ofNat_of_ge (w := 32) (k := r) (by decide) (by simpa using h1) h2
  exact Lib.slt_of_neg_nonneg (by rw [hv]; omega) (by decide)

theorem readLE_lt' (m : Word → Byte) (a : Word) (n : Nat) : readLE m a n < 256 ^ n := by
  induction n generalizing a with
  | zero => simp [readLE]
  | succ n ih => simp only [readLE, Nat.pow_succ]; have := ih (a + 1); have := (m a).isLt; omega

theorem sr_al64 {sp : Word} (h : aligned sp 16) : aligned (sp - 64#64) 16 := by unfold aligned at *; bv_omega

theorem not_mem_of_mem_disj {r r' : Region} {x : Word} (hd : r.Disjoint r') (hx : r'.mem x) : ¬ r.mem x := by
  simp only [Region.Disjoint, Region.mem] at *; bv_omega

def fwrite_dom : Dom := [(0x11c3c#64, 240), (0x11d2c#64, 92), (0x11fe8#64, 316), (0x12124#64, 204), (0x121f0#64, 84), (0x125dc#64, 1044)]
def fwrite_entry : Word := 0x12124#64

/-- `__fwritex` with the function `f->write` points to for slen's stdout (`__stdout_write`). -/
def fwxD : Dom := __fwritex_dom ++ __stdout_write_dom

/-- `__fwritex(src, l, f)` on a FILE like slen's stdout before its first write (wend = 0, F_NOWR clear,
    f->write = `__stdout_write`, line buffered: lbf ≥ 0), when `l` fits in the buffer and the data ends in
    '\n' (slen's output line). Postcondition: the kernel unchanged; nothing written outside FILE's 152
    bytes, the 192 bytes below sp and errno; new events that are writes to `f->fd` of all `l` bytes (a0 = l)
    or of a prefix of `n < l` (a0 = n); afterwards nothing buffered (wpos = wbase) and rpos = rend. -/
def fwxStdoutP : SpecP (Word × Word × Word) where
  pre := fun ⟨src, l, f⟩ s k =>
    s.reg 10 = src ∧ s.reg 11 = l ∧ s.reg 12 = f ∧ aligned f 8 ∧ aligned (s.reg 4 + 18446744073709551452#64) 4 ∧
    read64 s.mem (f + 32#64) = 0 ∧ read32 s.mem f &&& 8#64 = 0 ∧ read64 s.mem (f + 72#64) = 0x1240c#64 ∧
    l.toNat ≤ (read64 s.mem (f + 96#64)).toNat ∧ readLE s.mem (f + 144#64) 4 < 2 ^ 31 ∧
    0 < l.toNat ∧ l.toNat < 2 ^ 62 ∧ s.mem (src + BitVec.ofNat 64 (l.toNat - 1)) = 10#8 ∧
    (Perm.mk [⟨src, l.toNat⟩] [⟨f, 152⟩, ⟨s.reg 2 - 192#64, 192⟩, ⟨s.reg 4 + 18446744073709551452#64, 4⟩]).le k.perm ∧
    (Region.mk f 152).Disjoint ⟨s.reg 2 - 192#64, 192⟩ ∧
    (Region.mk (s.reg 4 + 18446744073709551452#64) 4).Disjoint ⟨s.reg 2 - 192#64, 192⟩ ∧
    (Region.mk (s.reg 4 + 18446744073709551452#64) 4).Disjoint ⟨f, 152⟩ ∧
    (Region.mk src l.toNat).Disjoint ⟨s.reg 2 - 192#64, 192⟩ ∧
    (Region.mk src l.toNat).Disjoint ⟨s.reg 4 + 18446744073709551452#64, 4⟩ ∧
    (Region.mk src l.toNat).Disjoint ⟨f, 152⟩ ∧
    (Region.mk (read64 s.mem (f + 88#64)) (read64 s.mem (f + 96#64)).toNat).Disjoint ⟨s.reg 2 - 192#64, 192⟩ ∧
    (Region.mk (read64 s.mem (f + 88#64)) (read64 s.mem (f + 96#64)).toNat).Disjoint ⟨s.reg 4 + 18446744073709551452#64, 4⟩ ∧
    (Region.mk (read64 s.mem (f + 88#64)) (read64 s.mem (f + 96#64)).toNat).Disjoint ⟨f, 152⟩ ∧
    (Region.mk 0#64 1).Disjoint ⟨s.reg 2 - 192#64, 192⟩ ∧ (Region.mk 0#64 1).Disjoint ⟨f, 152⟩ ∧
    (fdOf s.mem f).toNat < 2 ^ 31
  post := fun ⟨src, l, f⟩ x y =>
    y.2 = x.2 ∧
    (∀ p, ¬ (Region.mk f 152).mem p → ¬ (Region.mk (x.1.reg 2 - 192#64) 192).mem p →
      ¬ (Region.mk (x.1.reg 4 + 18446744073709551452#64) 4).mem p → y.1.mem p = x.1.mem p) ∧
    read64 y.1.mem (f + 40#64) = read64 y.1.mem (f + 56#64) ∧ read64 y.1.mem (f + 8#64) = read64 y.1.mem (f + 16#64) ∧
    readLE y.1.mem (f + 140#64) 4 = readLE x.1.mem (f + 140#64) 4 ∧
    ∃ evs, y.1.trace = x.1.trace ++ evs ∧
      ((WritesOf (fdOf x.1.mem f) evs (readBytes x.1.mem src l.toNat) ∧ y.1.reg 10 = l) ∨
       (∃ n, n < l.toNat ∧ WritesOf (fdOf x.1.mem f) evs ((readBytes x.1.mem src l.toNat).take n) ∧
         y.1.reg 10 = BitVec.ofNat 64 n))

theorem fw_byte_not64 {f sp : Word} (h : (Region.mk f 152).Disjoint ⟨sp - 192#64, 192⟩) (j : Nat) (hj : j < 152) :
    ¬ (Region.mk (sp - 64#64) 64).mem (f + BitVec.ofNat 64 j) := by
  simp only [Region.Disjoint, Region.mem] at *; bv_omega

theorem chain_n112 {sp p : Word} (h : ¬ (Region.mk (sp - 192#64) 192).mem p) :
    ¬ (Region.mk (sp - 64#64 - 16#64 - 112#64) 112).mem p := by simp only [Region.mem] at *; bv_omega
theorem chain_n16 {sp p : Word} (h : ¬ (Region.mk (sp - 192#64) 192).mem p) :
    ¬ (Region.mk (sp - 64#64 - 16#64) 16).mem p := by simp only [Region.mem] at *; bv_omega
theorem chain_n64 {sp p : Word} (h : ¬ (Region.mk (sp - 192#64) 192).mem p) :
    ¬ (Region.mk (sp - 64#64) 64).mem p := by simp only [Region.mem] at *; bv_omega
theorem chain_nF140 {f p : Word} (h : ¬ (Region.mk f 152).mem p) : ¬ (Region.mk f 140).mem p := by
  simp only [Region.mem] at *; omega
theorem chain_nf {f p : Word} (h : ¬ (Region.mk f 152).mem p) (o n : Nat) (ho : o + n ≤ 152) :
    ¬ (Region.mk (f + BitVec.ofNat 64 o) n).mem p := by simp only [Region.mem] at *; bv_omega

theorem file_mem152 (f : Word) (o j : Nat) (h : o + j < 152) :
    (Region.mk f 152).mem (f + BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
  simp only [Region.mem]; bv_omega
theorem fbyte_out (f : Word) (o j a len : Nat) (h : o + j + 1 ≤ a ∨ (a + len ≤ o + j ∧ o + j < 152)) (ha : a + len ≤ 152 := by omega) :
    ¬ (Region.mk (f + BitVec.ofNat 64 a) len).mem (f + BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
  simp only [Region.mem]; bv_omega
theorem slot_in192 (sp : Word) (o j : Nat) (hj : j < 8) (h1 : 8 ≤ o) (h3 : o ≤ 56) :
    (Region.mk (sp - 192#64) 192).mem (sp - BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
  simp only [Region.mem]; bv_omega
theorem slot_out112 (sp : Word) (o j : Nat) (hj : j < 8) (h1 : 8 ≤ o) (h3 : o ≤ 56) :
    ¬ (Region.mk (sp - 64#64 - 16#64 - 112#64) 112).mem (sp - BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
  simp only [Region.mem]; bv_omega
theorem slot_out16 (sp : Word) (o j : Nat) (hj : j < 8) (h1 : 8 ≤ o) (h3 : o ≤ 56) :
    ¬ (Region.mk (sp - 64#64 - 16#64) 16).mem (sp - BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
  simp only [Region.mem]; bv_omega

theorem disj0_S {a sp : Word} {n : Nat} (h : (Region.mk a n).Disjoint ⟨sp - 192#64, 192⟩) (hn : 0 < n := by omega) :
    (Region.mk a 0).Disjoint ⟨sp - 64#64, 64⟩ := by
  simp only [Region.Disjoint] at *; bv_omega
theorem disj0_F {a f : Word} {n : Nat} (h : (Region.mk a n).Disjoint ⟨f, 152⟩) (hn : 0 < n := by omega) :
    (Region.mk a 0).Disjoint ⟨f + 40#64, 8⟩ := by
  simp only [Region.Disjoint] at *; bv_omega

theorem disj40 {f sp : Word} (h : (Region.mk f 152).Disjoint ⟨sp - 192#64, 192⟩) :
    (Region.mk (f + 40#64) 8).Disjoint ⟨sp - 64#64, 64⟩ := by
  simp only [Region.Disjoint] at *; bv_omega

theorem lbf_nonneg (r : Nat) (h : r < 2 ^ 31) :
    BitVec.slt ((BitVec.ofNat 32 r).signExtend 64) 0 = false := by
  have hv := Lib.toNat_signExtend_ofNat_of_lt (w := 32) (k := r) (by decide) (by decide) (by simpa using h)
  rw [Lib.slt_of_small (by rw [hv]; omega) (by decide), hv]
  simp

theorem __fwritex_stdout_verified (hM : VerifiedProc img memcpy_dom 0x125dc#64 memcpySpec) :
    VerifiedProc img fwxD 0x11fe8#64 fwxStdoutP := by
  rintro ⟨src, l, f⟩ s k he hpre
  have hpre' := hpre
  obtain ⟨ha0, ha1, ha2, hal, hale, hwend, hnowr, hw72, hfit, hlbf, hl0, hl62, hnl, hle,
    dFS, dES, dEF, dCS, dCE, dCF, dUS, dUE, dUF, d0S, d0F, hfdS⟩ := hpre'
  have hsp := he.sp
  simp only [Reg.sp] at hsp
  have hD : __fwritex_dom.sub fwxD := Dom.sub_of_ranges (by decide)
  have wS : ∀ a n, n ≤ a → a ≤ 192 → k.perm.canWrite (s.reg 2 - BitVec.ofNat 64 a) n := fun a n h1 h2 =>
    hle.write _ _ (.inr ⟨⟨s.reg 2 - 192#64, 192⟩, by simp, by simp only [Region.covers]; bv_omega⟩)
  have wF : ∀ o n, o + n ≤ 152 → k.perm.canWrite (f + BitVec.ofNat 64 o) n := fun o n h =>
    hle.write _ _ (.inr ⟨⟨f, 152⟩, by simp, by simp only [Region.covers]; bv_omega⟩)
  have hrd : ∀ o, 8 ≤ o → o ≤ 56 → k.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h3 =>
    Perm.canRead_of_canWrite (wS o 8 h1 (by omega))
  have hF64 : (Region.mk f 144).Disjoint ⟨s.reg 2 - 64#64, 64⟩ := by
    simp only [Region.Disjoint] at dFS ⊢; bv_omega
  have hF32 : (Region.mk (f + 32#64) 8).Disjoint ⟨s.reg 2 - 64#64, 64⟩ := by
    simp only [Region.Disjoint] at dFS ⊢; bv_omega
  refine fw_entry_tw s k fwxD hD he hrd src l f ha0 ha1 ha2 hal (fun o h1 h3 => wS o 8 h1 (by omega))
    (Perm.canRead_of_canWrite (by simpa using wF 32 8 (by omega))) (sw_alF hal 32 rfl) hF32 hF64 ?_ hwend _ ?_ ?_
  · intro z hz2
    refine Perm.le_trans (Perm.le_of ?_ ?_) hle
    · intro r hr
      simp [Spec.perm, towriteSpec] at hr
      subst hr
      exact ⟨⟨f, 152⟩, by simp, by simp only [Region.within]; bv_omega⟩
    intro r hr
    simp [Spec.perm, towriteSpec, Spec.stackRegion] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨f, 152⟩, by simp, by simp only [Region.within]; bv_omega⟩
    · exact ⟨⟨f, 152⟩, by simp, by simp only [Region.within]; bv_omega⟩
    · exact ⟨⟨s.reg 2 - 192#64, 192⟩, by simp, by simp only [Region.within, Reg.sp, hz2]; bv_omega⟩
  · intro z hz w hpost hne
    exfalso; apply hne
    have hfl : read32 z.mem f = read32 s.mem f := by
      have hz11 := hz.2.2.2.2.2.2.2.2.2.2.1
      unfold read32
      rw [readLE_congr (m' := s.mem) (fun j hj => hz11 _ (fw_byte_not64 dFS j (by omega)))]
    exact (hpost.1 (by rw [hfl]; exact hnowr)).1
  intro z hz w hpost h0 hfrw u hpcu hkeep h12u htru
  have hz11 := hz.2.2.2.2.2.2.2.2.2.2.1
  have hzF : ∀ o len, o + len ≤ 152 → readLE z.mem (f + BitVec.ofNat 64 o) len = readLE s.mem (f + BitVec.ofNat 64 o) len := by
    intro o len h
    apply readLE_congr; intro j hj
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hz11 _ (fw_byte_not64 dFS (o + j) (by omega))
  have hfl : read32 z.mem f = read32 s.mem f := by
    unfold read32; have := hzF 0 4 (by omega); simp only [BitVec.add_zero] at this; rw [this]
  obtain ⟨-, hwp, hwb, hwe, hrp, hre, h72w, h120w, h88w⟩ := hpost.1 (by rw [hfl]; exact hnowr)
  simp only [F_wpos, F_wbase, F_wend, F_rpos, F_rend, F_buf, F_buf_size] at hwp hwb hwe hrp hre
  have z88 : read64 z.mem (f + 88#64) = read64 s.mem (f + 88#64) := by unfold read64; rw [hzF 88 8 (by omega)]
  have z96 : read64 z.mem (f + 96#64) = read64 s.mem (f + 96#64) := by unfold read64; rw [hzF 96 8 (by omega)]
  rw [z88] at hwp hwb hwe h88w
  rw [z96] at hwe
  have w144 : readLE w.mem (f + 144#64) 4 = readLE s.mem (f + 144#64) 4 := by
    rw [readLE_congr (m' := z.mem) (fun j hj => hfrw _ (by simp only [Region.mem]; bv_omega))]
    have := hzF 144 4 (by omega); simpa using this
  have hr40 : k.perm.canRead (f + 40#64) 8 := Perm.canRead_of_canWrite (by simpa using wF 40 8 (by omega))
  have hr144 : k.perm.canRead (f + 144#64) 4 := Perm.canRead_of_canWrite (by simpa using wF 144 4 (by omega))
  have hfit' : (read64 w.mem (f + 32#64) - read64 w.mem (f + 40#64)).ult l = false := by
    rw [hwe, hwp, show read64 s.mem (f + 88#64) + read64 s.mem (f + 96#64) - read64 s.mem (f + 88#64) =
      read64 s.mem (f + 96#64) by bv_omega]
    simp only [BitVec.ult, decide_eq_false_iff_not, Nat.not_lt]; exact hfit
  have hlbf' : BitVec.slt ((BitVec.ofNat 32 (readLE w.mem (f + 144#64) 4)).signExtend 64) 0 = false := by
    rw [w144]; exact lbf_nonneg _ hlbf
  refine fw_mid s k fwxD hD f src l w.mem hr40 (sw_alF hal 40 rfl) hr144 (by unfold aligned at *; bv_omega) _ u hpcu hkeep h12u
    (fun u' _ _ h => absurd h (by rw [hfit']; decide)) (fun u' _ _ _ _ h => absurd h (by rw [hlbf']; decide)) ?_
  intro u' hpc' hk' h10' _ _ h20' h21' h11'
  have hsrcW : ∀ t, t < l.toNat → w.mem (src + BitVec.ofNat 64 t) = s.mem (src + BitVec.ofNat 64 t) := by
    intro t ht
    rw [hfrw _ (fun h => by
      have := Auto.not_mem_of_disjoint (R := ⟨f, 152⟩) dCF.symm ht
      simp only [Region.mem] at h this; omega)]
    exact hz11 _ (fun h => Auto.not_mem_of_disjoint (R := ⟨s.reg 2 - 192#64, 192⟩) dCS.symm ht
      (by simp only [Region.mem] at h ⊢; bv_omega))
  have hrs : ∀ t, t < l.toNat → k.perm.canRead (src + BitVec.ofNat 64 t) 1 := fun t ht =>
    hle.read _ _ (.inr ⟨⟨src, l.toNat⟩, by simp, by simp only [Region.covers]; bv_omega⟩)
  refine fw_scan s k fwxD hD f src l w.mem (by omega) hrs _ ?_ ?_ u' 0 hpc' hk' (Nat.zero_le _)
    (by rw [h20']) (by rw [h21']; simp) h11' (fun t h1 h2 => absurd h1 (by omega))
  · intro u0 _ _ hno
    exact absurd (by rw [hsrcW _ (by omega)]; exact hnl) (hno (l.toNat - 1) (by omega))
  intro u1 j hpc1 hk1 hj h20 h21 _ hno
  have hj0 : j = 0 := by
    rcases Nat.eq_zero_or_pos j with h | h
    · exact h
    exfalso
    exact hno (l.toNat - 1) (by omega) (by omega) (by rw [hsrcW _ (by omega)]; exact hnl)
  subst hj0
  have he72 : read64 w.mem (f + 72#64) = 0x1240c#64 := by
    rw [h72w]; unfold read64; rw [hzF 72 8 (by omega)]; exact hw72
  have hr72 : k.perm.canRead (f + 72#64) 8 := Perm.canRead_of_canWrite (by simpa using wF 72 8 (by omega))
  refine fw_write s k fwxD hD f src l w.mem (stdoutWriteSpec stdioWriteSpecF) 0x1240c#64 __stdout_write_dom
    __stdout_write_full (Dom.sub_of_ranges (by decide)) (by decide) hsp (by decide) hr72 (sw_alF hal 72 rfl) he72 _
    u1 0 hpc1 hk1 hj h20 h21 ?_ ?_
  · intro z2 hc2
    obtain ⟨-, -, -, c10, c11, c12, -, cpr, cm, -⟩ := hc2
    obtain ⟨-, k2, -, -, -, km, kpr, -⟩ := hk1
    have z2r2 : z2.reg 2 = s.reg 2 - 64#64 := by rw [cpr 2 (by decide) (by decide), k2]
    have z2r4 : z2.reg 4 = s.reg 4 := by rw [cpr 4 (by decide) (by decide), kpr 4 (by decide)]
    have e192 : s.reg 2 - 64#64 - 128#64 = s.reg 2 - 192#64 := by bv_omega
    have hpend : stdioPend z2.mem f = 0 := by
      unfold stdioPend; rw [cm, km, hwp, hwb]; simp
    have hlt : (BitVec.ofNat 64 (l.toNat - 0)).toNat = l.toNat := by
      rw [Nat.sub_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hfd2 : (fdOf z2.mem f).toNat < 2 ^ 31 := by
      unfold fdOf at hfdS ⊢; rw [cm, km, h120w, hzF 120 4 (by omega)]; exact hfdS
    refine stdout_pre_at z2 k f src _ c10 c11 c12 hal hfd2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [z2r2, z2r4, e192]
      refine Perm.le_trans (Perm.le_of (by simp) ?_) hle
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, Region.within_refl _⟩
      · exact ⟨⟨s.reg 2 - 192#64, 192⟩, by simp, by simp only [Region.within]; bv_omega⟩
      · exact ⟨_, by simp, Region.within_refl _⟩
    · rw [z2r2, e192]; exact disj_shrink_r dFS (by omega)
    · rw [z2r2, z2r4, e192]; exact disj_shrink_r dES (by omega)
    · rw [z2r4]; exact dEF
    · rw [z2r4]; exact hale
    · rw [hpend, z2r2, e192, cm, km, hwb]; exact disj_shrink_l (disj_shrink_r dUS (by omega)) (by omega)
    · rw [hpend, z2r4, cm, km, hwb]; exact disj_shrink_l dUE (by omega)
    · rw [hlt, z2r2, e192]; exact disj_shrink_r dCS (by omega)
    · rw [hlt, z2r4]; exact dCE
    · rw [hpend, hlt]; omega
  · intro z2 hc2 w2 hdone
    obtain ⟨c1, c2, c3, c10, c11, c12, c19, cpr, cm, ctr⟩ := hc2
    have hk1' := hk1
    obtain ⟨-, k2, k8, k9, k18, km, kpr, ktr⟩ := hk1'
    have z2r2 : z2.reg 2 = s.reg 2 - 64#64 := by rw [cpr 2 (by decide) (by decide), k2]
    have z2r4 : z2.reg 4 = s.reg 4 := by rw [cpr 4 (by decide) (by decide), kpr 4 (by decide)]
    have hlt : (BitVec.ofNat 64 (l.toNat - 0)).toNat = l.toNat := by
      rw [Nat.sub_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rcases hdone with ⟨hxw, hpcw, hpresw, z3, w3, hcall, ⟨⟨hk3, evs, htr3, hfr3, hcase⟩, hfr16⟩, hm2, ht2, ha2', hk2⟩ |
      ⟨_, z3, _, hex⟩
    rotate_left
    · exact hex.elim
    obtain ⟨d1, d2, d3, d10, d11, d12, d1r, d2r, dsame, wsz, lbf, dm, dc1, dc2⟩ := hcall
    have hws : ∀ ws, wsz = some ws → ws.length = 8 := by
      intro ws hw
      by_cases hf : read8 z2.mem f &&& 64#64 = 0#64
      · rcases dc2 hf with ⟨h, _⟩ | ⟨ws', hl, h, _⟩
        · rw [h] at hw; cases hw
        · rw [h] at hw; cases hw; exact hl
      · rw [(dc1 hf).1] at hw; cases hw
    have z3r2 : z3.reg 2 = s.reg 2 - 64#64 - 16#64 := by simpa [Reg.sp, z2r2] using d2r
    have z3r4 : z3.reg 4 = s.reg 4 := by rw [← z2r4]; exact dsame 4 (by decide)
    -- the memory chain
    have hchain : ∀ p, ¬ (Region.mk f 152).mem p → ¬ (Region.mk (s.reg 2 - 192#64) 192).mem p →
        ¬ (Region.mk (s.reg 4 + 18446744073709551452#64) 4).mem p → w2.1.mem p = s.mem p := by
      intro p a1 a2 a3
      rw [hm2, hfr3 p (by rw [z3r2]; exact chain_n112 a2) (by rw [z3r4]; exact a3) (by simpa using chain_nf a1 0 4 (by omega))
        (chain_nf a1 32 16 (by omega)) (chain_nf a1 56 8 (by omega)), dm,
        stdoutMem_agree z2 f wsz lbf hws p (by rw [z2r2]; exact chain_n16 a2) (chain_nf a1 72 8 (by omega))
          (chain_nf a1 144 4 (by omega)), cm, km, hfrw p (chain_nF140 a1), hz11 p (chain_n64 a2)]
    -- FILE bytes outside the fields __stdio_write, __stdout_write and __towrite write: as after __towrite
    have hF3 : ∀ o len, (8 ≤ o ∧ o + len ≤ 32) ∨ (64 ≤ o ∧ o + len ≤ 72) ∨ (80 ≤ o ∧ o + len ≤ 144) →
        readLE w2.1.mem (f + BitVec.ofNat 64 o) len = readLE w.mem (f + BitVec.ofNat 64 o) len := by
      intro o len ho
      apply readLE_congr; intro j hj
      have hin := file_mem152 f o j (by omega)
      have hnS := not_mem_of_mem_disj dFS.symm hin
      rw [hm2, hfr3 _ (by rw [z3r2]; exact chain_n112 hnS) (by rw [z3r4]; exact not_mem_of_mem_disj dEF hin)
        (by simpa using fbyte_out f o j 0 4 (by omega)) (fbyte_out f o j 32 16 (by omega)) (fbyte_out f o j 56 8 (by omega)),
        dm, stdoutMem_agree z2 f wsz lbf hws _ (by rw [z2r2]; exact chain_n16 hnS) (fbyte_out f o j 72 8 (by omega))
          (fbyte_out f o j 144 4 (by omega)), cm, km]
    have hF3z : ∀ o len, (8 ≤ o ∧ o + len ≤ 32) ∨ (40 ≤ o ∧ o + len ≤ 72) ∨ (80 ≤ o ∧ o + len ≤ 144) →
        readLE z3.mem (f + BitVec.ofNat 64 o) len = readLE w.mem (f + BitVec.ofNat 64 o) len := by
      intro o len ho
      apply readLE_congr; intro j hj
      have hin := file_mem152 f o j (by omega)
      have hnS := not_mem_of_mem_disj dFS.symm hin
      rw [dm, stdoutMem_agree z2 f wsz lbf hws _ (by rw [z2r2]; exact chain_n16 hnS) (fbyte_out f o j 72 8 (by omega))
          (fbyte_out f o j 144 4 (by omega)), cm, km]
    have hslotS : ∀ o, 8 ≤ o → o ≤ 56 → read64 w2.1.mem (s.reg 2 - BitVec.ofNat 64 o) = read64 z.mem (s.reg 2 - BitVec.ofNat 64 o) := by
      intro o h1 h3; apply read64_congr_on; intro j hj
      have hin := slot_in192 (s.reg 2) o j hj h1 h3
      have hnF := not_mem_of_mem_disj dFS hin
      rw [hm2, hfr3 _ (by rw [z3r2]; exact slot_out112 _ o j hj h1 h3) (by rw [z3r4]; exact not_mem_of_mem_disj dES hin)
        (by simpa using chain_nf hnF 0 4 (by omega)) (chain_nf hnF 32 16 (by omega)) (chain_nf hnF 56 8 (by omega)),
        dm, stdoutMem_agree z2 f wsz lbf hws _ (by rw [z2r2]; exact slot_out16 _ o j hj h1 h3) (chain_nf hnF 72 8 (by omega))
          (chain_nf hnF 144 4 (by omega)), cm, km, hfrw _ (chain_nF140 hnF)]
    obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := hz.2.2.2.2.2.2.2.2.2.1
    have hw2r : ∀ q ∈ preservedRegs, q ≠ 19 → w2.1.reg q = u1.reg q := fun q hq h => by rw [hpresw q hq, cpr q hq h]
    have hb : FwBack s f src l (BitVec.ofNat 64 (l.toNat - 0)) 0 w2.1 := by
      refine ⟨by rw [hpcw, Reg.ra, c3], hxw, by rw [hw2r 2 (by decide) (by decide), k2], by rw [hw2r 8 (by decide) (by decide), k8],
        by rw [hw2r 9 (by decide) (by decide), k9], by rw [hw2r 18 (by decide) (by decide), k18],
        by rw [hpresw 19 (by decide), c19], by rw [hw2r 20 (by decide) (by decide), h20],
        by rw [hw2r 21 (by decide) (by decide), h21], fun q hq => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hw2r q (by revert hq; revert q; decide) (by revert hq; revert q; decide), kpr q hq]
      · rw [hslotS 8 (by omega) (by omega)]; exact t1
      · rw [hslotS 16 (by omega) (by omega)]; exact t2
      · rw [hslotS 24 (by omega) (by omega)]; exact t3
      · rw [hslotS 32 (by omega) (by omega)]; exact t4
      · rw [hslotS 40 (by omega) (by omega)]; exact t5
      · rw [hslotS 48 (by omega) (by omega)]; exact t6
      · rw [hslotS 56 (by omega) (by omega)]; exact t7
    have z40 : read64 z3.mem (f + 40#64) = read64 s.mem (f + 88#64) := by
      unfold read64; rw [hF3z 40 8 (by omega)]; exact hwp
    have z56 : read64 z3.mem (f + 56#64) = read64 s.mem (f + 88#64) := by
      unfold read64; rw [hF3z 56 8 (by omega)]; exact hwb
    have hpz : stdioPend z3.mem f = 0 := by unfold stdioPend; rw [z40, z56]; simp
    have hbytes : stdioBytes z3.mem f src (BitVec.ofNat 64 (l.toNat - 0)) = readBytes s.mem src l.toNat := by
      unfold stdioBytes
      rw [show (read64 z3.mem (f + 40#64) - read64 z3.mem (f + 56#64)).toNat = 0 from hpz, hlt]
      simp only [readBytes, List.nil_append]
      apply readBytes_congr; intro j hj
      have hin : (Region.mk src l.toNat).mem (src + BitVec.ofNat 64 j) := by simp only [Region.mem]; bv_omega
      have hnF := not_mem_of_mem_disj dCF.symm hin
      rw [dm, stdoutMem_agree z2 f wsz lbf hws _ (by rw [z2r2]; exact chain_n16 (not_mem_of_mem_disj dCS.symm hin))
        (chain_nf hnF 72 8 (by omega)) (chain_nf hnF 144 4 (by omega)), cm, km]
      exact hsrcW j hj
    have hfd : fdOf z3.mem f = fdOf s.mem f := by
      unfold fdOf; rw [hF3z 120 4 (by omega), h120w, hzF 120 4 (by omega)]
    have h8w2 : read64 w2.1.mem (f + 8#64) = 0 := by unfold read64; rw [hF3 8 8 (by omega)]; exact hrp
    have h16w2 : read64 w2.1.mem (f + 16#64) = 0 := by unfold read64; rw [hF3 16 8 (by omega)]; exact hre
    have htrw2 : w2.1.trace = s.trace ++ evs := by rw [ht2, htr3, d3, ctr, ktr]
    have hww : read64 w2.1.mem (f + 40#64) = read64 w2.1.mem (f + 56#64) := by
      rw [hm2]; rcases hcase with ⟨-, -, -, a, b, -⟩ | ⟨-, -, -, -, -, a, b, -⟩ <;> rw [a, b]
    have hlock : readLE w2.1.mem (f + 140#64) 4 = readLE s.mem (f + 140#64) 4 := by
      rw [hF3 140 4 (by omega), readLE_congr (m' := z.mem) (fun j hj => hfrw _ (by simp only [Region.mem]; bv_omega))]
      exact hzF 140 4 (by omega)
    have hfin : ∀ y : State × Kern, y.2 = k → (∀ p, ¬ (Region.mk f 152).mem p → ¬ (Region.mk (s.reg 2 - 192#64) 192).mem p →
        ¬ (Region.mk (s.reg 4 + 18446744073709551452#64) 4).mem p → y.1.mem p = s.mem p) →
        read64 y.1.mem (f + 40#64) = read64 y.1.mem (f + 56#64) → read64 y.1.mem (f + 8#64) = read64 y.1.mem (f + 16#64) →
        readLE y.1.mem (f + 140#64) 4 = readLE s.mem (f + 140#64) 4 →
        y.1.trace = s.trace ++ evs →
        ((WritesOf (fdOf s.mem f) evs (readBytes s.mem src l.toNat) ∧ y.1.reg 10 = l) ∨
          (∃ n, n < l.toNat ∧ WritesOf (fdOf s.mem f) evs ((readBytes s.mem src l.toNat).take n) ∧
            y.1.reg 10 = BitVec.ofNat 64 n)) →
        y.1.exit = none → y.1.pc = s.reg 1 → Preserved s y.1 → fwxStdoutP.Done (src, l, f) (s, k) y := by
      intro y a1 a2 a3 a4 aL a5 a6 a7 a8 a9
      exact .inl ⟨a7, by rw [a8], a9, a1, a2, a3, a4, aL, evs, a5, a6⟩
    have hle0 : l = BitVec.ofNat 64 (l.toNat - 0) := by rw [Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hw2 : w2 = (w2.1, k) := Prod.ext rfl (by rw [hk2, hk3])
    rw [hw2]
    by_cases hlt' : (w2.1.reg 10).ult (BitVec.ofNat 64 (l.toNat - 0)) = true
    · refine fw_after_lt s k fwxD hD he hrd f src l _ 0 w2.1 hb hlt' _ ?_
      intro y hk hm ht ha hxy hpcy hpy
      refine hfin y hk (fun p a b c => by rw [hm]; exact hchain p a b c) (by rw [hm]; exact hww)
        (by rw [hm, h8w2, h16w2]) (by rw [hm]; exact hlock) (by rw [ht, htrw2]) ?_ hxy hpcy hpy
      rw [ha, ha2']
      rcases hcase with ⟨hw, h10, -⟩ | ⟨n, hn, hw, h10, -⟩
      · rw [ha2', h10] at hlt'; simp [BitVec.ult] at hlt'
      · rw [hbytes] at hn hw; rw [hfd] at hw
        have h10' : w3.1.reg 10 = BitVec.ofNat 64 n := by
          rw [h10, hpz]; rcases Nat.eq_zero_or_pos n with h0 | h0
          · rw [if_pos (by omega), h0]; rfl
          · rw [if_neg (by omega), Nat.sub_zero]
        rw [ha2', h10'] at hlt'
        simp only [BitVec.ult, decide_eq_true_eq] at hlt'
        rw [hlt] at hlt'
        simp only [Auto.readBytes_length] at hn
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hlt'
        simp only [Reg.a0]
        exact .inr ⟨n, by omega, hw, h10'⟩
    · have hge : (w2.1.reg 10).ult (BitVec.ofNat 64 (l.toNat - 0)) = false := by simpa using hlt'
      -- wpos after the write: the buffer (all written) or 0 (an error)
      have hwp2 : read64 w2.1.mem (f + 40#64) = read64 s.mem (f + 88#64) ∨ read64 w2.1.mem (f + 40#64) = 0 := by
        rw [hm2]; rcases hcase with ⟨-, -, -, a, -⟩ | ⟨-, -, -, -, -, a, -⟩
        · left; rw [a]; have := hF3z 88 8 (by omega); unfold read64 at h88w ⊢; rw [this]; exact h88w
        · right; exact a
      have hdS0 : (Region.mk (read64 w2.1.mem (f + 40#64)) 0).Disjoint ⟨s.reg 2 - 64#64, 64⟩ := by
        rcases hwp2 with h | h <;> rw [h]
        · exact disj0_S dUS
        · exact disj0_S d0S
      have hdF0 : (Region.mk (read64 w2.1.mem (f + 40#64)) 0).Disjoint ⟨f + 40#64, 8⟩ := by
        rcases hwp2 with h | h <;> rw [h]
        · exact disj0_F dUF
        · exact disj0_F d0F
      have hFS40 : (Region.mk (f + 40#64) 8).Disjoint ⟨s.reg 2 - 64#64, 64⟩ := disj40 dFS
      refine fw_after_ge s k fwxD hD he hM hrd f src l 0 (by omega) hl62 w2.1 hb hge (.inl rfl) (.inl rfl)
        (by simp [Region.Disjoint]) hdS0 hdF0 hFS40 hr40 (by simpa using wF 40 8 (by omega)) (sw_alF hal 40 rfl) _ ?_
      intro y hk ht ha hm _ h40 hxy hpcy hpy
      have hmy : ∀ p, ¬ (Region.mk f 152).mem p → y.1.mem p = w2.1.mem p := fun p hp =>
        hm p (by simp [Region.mem]) (chain_nf hp 40 8 (by omega))
      have hFy : ∀ o, o + 8 ≤ 40 ∨ (48 ≤ o ∧ o + 8 ≤ 152) → read64 y.1.mem (f + BitVec.ofNat 64 o) = read64 w2.1.mem (f + BitVec.ofNat 64 o) := by
        intro o ho; apply read64_congr_on; intro j hj
        exact hm _ (by simp [Region.mem]) (fbyte_out f o j 40 8 (by omega))
      refine hfin y hk (fun p a b c => by rw [hmy p a]; exact hchain p a b c) ?_ ?_ ?_ (by rw [ht, htrw2]) ?_ hxy hpcy hpy
      · rw [h40, hFy 56 (by omega), ← hww]; simp
      · rw [hFy 8 (by omega), hFy 16 (by omega), h8w2, h16w2]
      · rw [← hlock]; apply readLE_congr; intro j hj
        exact hm _ (by simp [Region.mem]) (fbyte_out f 140 j 40 8 (by omega))
      · rw [ha, ← hle0, BitVec.add_zero]
        rcases hcase with ⟨hw, -⟩ | ⟨n, hn, hw, h10, -⟩
        · rw [hbytes] at hw; rw [hfd] at hw; exact .inl ⟨hw, rfl⟩
        · rw [hbytes] at hn hw; rw [hfd] at hw
          simp only [Auto.readBytes_length] at hn
          have h10' : w3.1.reg 10 = BitVec.ofNat 64 n := by
            rw [h10, hpz]; rcases Nat.eq_zero_or_pos n with h0 | h0
            · rw [if_pos (by omega), h0]; rfl
            · rw [if_neg (by omega), Nat.sub_zero]
          rw [ha2', h10'] at hge
          simp only [BitVec.ult, decide_eq_false_iff_not, Nat.not_lt] at hge
          rw [hlt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hge
          have hnl : n = l.toNat := by omega
          rw [hnl, List.take_of_length_le (by simp [Auto.readBytes_length])] at hw
          exact .inl ⟨hw, rfl⟩

/-! ## `fwrite(src, 1, n, f)` (musl src/stdio/fwrite.c) for slen's output line: unlocked (lock < 0), so the
call of `__fwritex` and its result (`k / 1`). -/

end NoCompiler.Libc.Musl.Fwrite

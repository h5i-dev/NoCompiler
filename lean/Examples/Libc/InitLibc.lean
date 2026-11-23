import Examples.Libc.InitLibcPn
import NoCompiler.Linux.RunN
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage

/-- `A` has the entry (t, v). -/
def AuxHas (A : List (Word × Word)) (t v : Word) : Prop := ∃ i, ∃ h : i < A.length, A[i].1 = t ∧ A[i].2 = v

theorem aux_val (s : State) (b : Word) (A : List (Word × Word)) (M0 m : Word → Byte) (hst : ∀ i (hi : i < A.length),
      (A[i].1).toNat < 38 → read64 M0 (auxBase s + BitVec.ofNat 64 (8 * (A[i].1).toNat)) = A[i].2)
    (hK : AuxKeep s M0 m) (t : Nat) (ht : t < 38) (v : Word) (hA : AuxHas A (BitVec.ofNat 64 t) v) :
    read64 m (auxBase s + BitVec.ofNat 64 (8 * t)) = v := by
  obtain ⟨i, hi, h1, h2⟩ := hA
  have e : (A[i].1).toNat = t := by rw [h1, BitVec.toNat_ofNat]; omega
  rw [hK t ht, ← e, hst i hi (by omega), h2]

/-- What `__init_libc(envp, pn)` needs from slen's launch. -/
structure InitLibcPre (s : State) (k : Kern) (e : Word) (n : Nat) (A : List (Word × Word)) (P : Word) (S : List Byte) : Prop where
  a0 : s.reg 10 = e
  sp : aligned (s.reg 2) 16
  lo : 448 ≤ (s.reg 2).toNat
  env : EnvAt s k e n
  aux : AuxAt s k (e + BitVec.ofNat 64 (8 * (n + 1))) A
  str : StrAt s k P S
  pn : (s.reg 11 ≠ 0 ∧ P = s.reg 11) ∨ (s.reg 11 = 0 ∧ P ≠ 0 ∧ AuxHas A 31#64 P)
  phdr : AuxHas A 3#64 0x10040#64
  phent : AuxHas A 4#64 56#64
  phnum : AuxHas A 5#64 6#64
  uid : ∃ v, AuxHas A 11#64 v ∧ AuxHas A 12#64 v
  gid : ∃ v, AuxHas A 13#64 v ∧ AuxHas A 14#64 v
  secure : AuxHas A 23#64 0
  ph : PhdrLit s.mem
  bss : read64 s.mem 0x14020#64 = 0 ∧ read64 s.mem 0x14030#64 = 0 ∧ read64 s.mem 0x14038#64 = 0 ∧
    read64 s.mem 0x141c0#64 = 0 ∧ read64 s.mem 0x141a8#64 = 0
  wS : ∀ p n, (ilS s).covers p n → k.perm.canWrite p n
  wG : ∀ p n, ilG.covers p n → k.perm.canWrite p n
  wW : ∀ p n, tlW.covers p n → k.perm.canWrite p n
  rP : ∀ p n, (Region.mk 0x10040#64 336).covers p n → k.perm.canRead p n
  rS4 : k.perm.canRead 0x13fc8#64 4
  rSy : k.perm.canRead 0x13fe0#64 8
  dG : ilG.Disjoint (ilS s)
  dW : tlW.Disjoint (ilS s)
  dPh : (Region.mk 0x10040#64 336).Disjoint (ilS s)

/-- `__init_libc(envp, pn)` (musl src/env/__libc_start_main.c) for slen's launch: it sets tp to 0x14110 (through
    `__init_tls`), returns (the non-secure path: uid = euid, gid = egid, no AT_SECURE), the kernel and the trace
    unchanged, memory changed only on its stack (448 bytes below sp), in `.sbss` and in `tlW`. -/
def initLibcP : SpecP (Word × Word) where
  pre := fun ⟨e, _⟩ s k => ∃ n A P S, InitLibcPre s k e n A P S
  post := fun _ x y => y.2 = x.2 ∧ y.1.trace = x.1.trace ∧
    ∀ p, ¬ (ilS x.1).mem p → ¬ ilG.mem p → ¬ tlW.mem p → y.1.mem p = x.1.mem p

theorem il_frame_s (s : State) (P : Word) (m : Word → Byte) (hF : IlFrame (s.setReg 11 P) m) : IlFrame s m := by
  intro p a b c d
  have e : ilS (s.setReg 11 P) = ilS s := by simp only [ilS, State.reg_setReg_other _ _ _ _ (show (2 : Reg) ≠ 11 by decide)]
  rw [← e] at a; have := hF p a b c d; simpa only [nocompiler_state] using this

/-- A word of `tlW` that `__init_libc` does not write, as at entry. -/
theorem il_tlw_read (s : State) (m : Word → Byte) (hF : IlFrame s m) (hW : tlW.Disjoint (ilS s)) (a : Word)
    (ha : (a - 0x14018#64).toNat + 8 ≤ 448) (hG : ilG.Disjoint ⟨a, 8⟩) (hL : ilL.Disjoint ⟨a, 8⟩) (hP : ilP.Disjoint ⟨a, 8⟩) :
    read64 m a = read64 s.mem a := by
  apply read64_congr_on; intro j hj
  have hin : tlW.mem (a + BitVec.ofNat 64 j) := by simp only [tlW, Region.mem]; bv_omega
  exact hF _ (not_mem_of_mem_disj hW.symm hin) (not_mem_of_mem_disj hG (by simp only [Region.mem]; bv_omega))
    (not_mem_of_mem_disj hL (by simp only [Region.mem]; bv_omega)) (not_mem_of_mem_disj hP (by simp only [Region.mem]; bv_omega))

theorem perm_read_sub {Q : Perm} {a b : Word} {n m : Nat} (h : Q.canRead a n) (hn : 0 < n)
    (hc : (Region.mk a n).covers b m) : Q.canRead b m := by
  rcases h with h0 | ⟨r, hr, hcov⟩
  · omega
  · exact .inr ⟨r, hr, Region.covers_of_within hc hcov⟩

theorem il_tls_perm (s : State) (k : Kern) (e : Word) (n : Nat) (A : List (Word × Word)) (P : Word) (S : List Byte)
    (hI : InitLibcPre s k e n A P S) :
    (Perm.mk [⟨auxBase s + 24#64, 24⟩, ⟨0x10040#64, 336⟩, ⟨0x13fc8#64, 4⟩, ⟨0x13fe0#64, 8⟩]
      [⟨s.reg 2 - 384#64 - 64#64, 64⟩, tlW]).le k.perm := by
  have hlo := hI.lo
  refine ⟨fun a m h => ?_, fun a m h => ?_⟩
  · rcases h with h0 | ⟨r, hr, hc⟩
    · exact .inl h0
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl | rfl) | (rfl | rfl)
      · exact Perm.canRead_of_canWrite (hI.wS _ _ (Region.covers_of_within hc (by simp only [auxBase, ilS, Region.within]; bv_omega)))
      · exact hI.rP _ _ hc
      · exact perm_read_sub hI.rS4 (by omega) hc
      · exact perm_read_sub hI.rSy (by omega) hc
      · exact Perm.canRead_of_canWrite (hI.wS _ _ (Region.covers_of_within hc (by simp only [ilS, Region.within]; bv_omega)))
      · exact Perm.canRead_of_canWrite (hI.wW _ _ hc)
  · rcases h with h0 | ⟨r, hr, hc⟩
    · exact .inl h0
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hI.wS _ _ (Region.covers_of_within hc (by simp only [ilS, Region.within]; bv_omega))
      · exact hI.wW _ _ hc

theorem il_dis_slot (s : State) (hW : tlW.Disjoint (ilS s)) (hlo : 448 ≤ (s.reg 2).toNat) (o : Nat) (h1 : 8 ≤ o)
    (h2 : o ≤ 32) : (Region.mk (s.reg 2 - BitVec.ofNat 64 o) 8).Disjoint ⟨s.reg 2 - 448#64, 64⟩ ∧
      (Region.mk (s.reg 2 - BitVec.ofNat 64 o) 8).Disjoint tlW := by
  simp only [ilS, tlW, Region.Disjoint] at hW ⊢; constructor <;> constructor <;> bv_omega

theorem il_dis_aux (s : State) (hW : tlW.Disjoint (ilS s)) (hlo : 448 ≤ (s.reg 2).toNat) (t : Nat) (ht : t < 38) :
    (Region.mk (auxBase s + BitVec.ofNat 64 (8 * t)) 8).Disjoint ⟨s.reg 2 - 448#64, 64⟩ ∧
      (Region.mk (auxBase s + BitVec.ofNat 64 (8 * t)) 8).Disjoint tlW := by
  simp only [auxBase, ilS, tlW, Region.Disjoint] at hW ⊢; constructor <;> constructor <;> bv_omega

theorem il_e384' (sp : Word) : sp - 384#64 + 384#64 = sp := by bv_omega

/-- After `__init_tls` returned (0x11410): `__init_ssp` (a `ret`), the non-secure check, the epilogue. -/
theorem il_end (s : State) (k : Kern) (e : Word) (n : Nat) (A : List (Word × Word)) (P : Word) (S : List Byte)
    (hI : InitLibcPre s k e n A P S) (hret : ¬ initLibcD.mem (s.reg 1)) (hra4 : aligned (s.reg 1) 4)
    (v : State) (hpc : v.pc = 0x11410#64) (hx : v.exit = none) (h2 : v.reg 2 = s.reg 2 - 384#64)
    (h4 : v.reg 4 = 0x14110#64)
    (hpr : ∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 4 → q ≠ 8 → q ≠ 9 → q ≠ 18 → v.reg q = s.reg q)
    (s1 : read64 v.mem (s.reg 2 - 8#64) = s.reg 1) (s2 : read64 v.mem (s.reg 2 - 16#64) = s.reg 8)
    (s3 : read64 v.mem (s.reg 2 - 24#64) = s.reg 9) (s4 : read64 v.mem (s.reg 2 - 32#64) = s.reg 18)
    (hav : ∀ t, t < 38 → ∀ w, AuxHas A (BitVec.ofNat 64 t) w → read64 v.mem (auxBase s + BitVec.ofNat 64 (8 * t)) = w)
    (htr : v.trace = s.trace) (hm : ∀ p, ¬ (ilS s).mem p → ¬ ilG.mem p → ¬ tlW.mem p → v.mem p = s.mem p) :
    PReachK code initLibcD (fun z => Final initLibcD z.1 ∧ initLibcP.Done (e, s.reg 11) (s.setReg 4 0x14110#64, k) z) (v, k) := by
  have hlo := hI.lo
  have hsp := hI.sp
  have rS : ∀ o, 8 ≤ o → o ≤ 384 → k.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h3 =>
    Perm.canRead_of_canWrite (hI.wS _ _ (by simp only [ilS, Region.covers]; bv_omega))
  obtain ⟨e25, a25, r25⟩ := il_auxslot s k hI.wS hsp hlo 25 (by omega)
  obtain ⟨e11, a11, r11⟩ := il_auxslot s k hI.wS hsp hlo 11 (by omega)
  obtain ⟨e12, a12, r12⟩ := il_auxslot s k hI.wS hsp hlo 12 (by omega)
  obtain ⟨e13, a13, r13⟩ := il_auxslot s k hI.wS hsp hlo 13 (by omega)
  obtain ⟨e14, a14, r14⟩ := il_auxslot s k hI.wS hsp hlo 14 (by omega)
  obtain ⟨e23, a23, r23⟩ := il_auxslot s k hI.wS hsp hlo 23 (by omega)
  obtain ⟨vu, hu1, hu2⟩ := hI.uid
  obtain ⟨vg, hg1, hg2⟩ := hI.gid
  have v11 := hav 11 (by omega) vu hu1
  have v12 := hav 12 (by omega) vu hu2
  have v13 := hav 13 (by omega) vg hg1
  have v14 := hav 14 (by omega) vg hg2
  have v23 := hav 23 (by omega) 0 hI.secure
  simp only [show 48 + 8 * 25 = 248 from rfl] at e25
  simp only [show 48 + 8 * 11 = 136 from rfl] at e11
  simp only [show 48 + 8 * 12 = 144 from rfl] at e12
  simp only [show 48 + 8 * 13 = 152 from rfl] at e13
  simp only [show 48 + 8 * 14 = 160 from rfl] at e14
  simp only [show 48 + 8 * 23 = 232 from rfl] at e23
  have hbn : (vu != vu) = false := by simp
  have hb0 : ((vg ^^^ vg ||| 0#64) == 0#64) = true := by simp
  nocompiler_run_n 19 [hx, hpc, h2, e25, a25, show aligned (0x1141c#64 : Word) 4 by decide, ret_mask (show aligned (0x1141c#64 : Word) 4 by decide), e11, a11, v11, e12, a12, v12, hbn, e13, a13, v13, e14, a14, v14, e23, a23, v23, BitVec.xor_self, hb0, il_eS _ 376 (by omega), sw_alS hsp 8 rfl, s1, il_eS _ 368 (by omega), sw_alS hsp 16 rfl, s2, il_eS _ 360 (by omega), sw_alS hsp 24 rfl, s3, il_eS _ 352 (by omega), sw_alS hsp 32 rfl, s4, il_e384', ret_mask hra4, hra4] using [r25, r11, r12, r13, r14, r23, rS]
  refine .done ⟨.inl (by simp only [nocompiler_state]; exact hret), .inl ⟨by simp only [nocompiler_state]; exact hx,
    by simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra], ?_, rfl, ?_, ?_⟩⟩
  · intro q hq
    have hq' := hq
    simp only [preservedRegs, List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp (disch := nocompiler_decide_closed) only [nocompiler_state])
    all_goals (first | rfl | exact h4 | exact hpr _ hq (by decide) (by decide) (by decide) (by decide) (by decide))
  · simp only [nocompiler_state]; exact htr
  · intro p a b c
    have e : ilS (s.setReg 4 0x14110#64) = ilS s := by
      simp only [ilS, State.reg_setReg_other _ _ _ _ (show (2 : Reg) ≠ 4 by decide)]
    rw [e] at a
    simp only [nocompiler_state]; exact hm p a b c

/-- `__init_libc`'s tail (0x11404): `__init_tls(aux)`, `__init_ssp(aux[AT_RANDOM])`, the non-secure check, the
    return. -/
theorem il_tail (s : State) (k : Kern) (e : Word) (n : Nat) (A : List (Word × Word)) (P : Word) (S : List Byte)
    (hI : InitLibcPre s k e n A P S) (hret : ¬ initLibcD.mem (s.reg 1)) (hra4 : aligned (s.reg 1) 4)
    (M0 : Word → Byte) (hst : ∀ i (hi : i < A.length),
      (A[i].1).toNat < 38 → read64 M0 (auxBase s + BitVec.ofNat 64 (8 * (A[i].1).toNat)) = A[i].2)
    (y : State) (hpc : y.pc = 0x11404#64) (hC : IlCommon (s.setReg 11 P) y) (hAK : AuxKeep s M0 y.mem) :
    PReachK code initLibcD (fun z => Final initLibcD z.1 ∧ initLibcP.Done (e, s.reg 11) (s.setReg 4 0x14110#64, k) z) (y, k) := by
  have hx := hC.1
  have h2 : y.reg 2 = s.reg 2 - 384#64 := by
    have := hC.2.1; simpa only [nocompiler_state, State.reg_setReg_other _ _ _ _ (show (2 : Reg) ≠ 11 by decide)] using this
  have hF : IlFrame s y.mem := il_frame_s s P y.mem hC.2.2.2.2.2.2.2.2.1
  have hlo := hI.lo
  have hsp := hI.sp
  have av : ∀ t, t < 38 → ∀ v, AuxHas A (BitVec.ofNat 64 t) v → read64 y.mem (auxBase s + BitVec.ofNat 64 (8 * t)) = v :=
    fun t ht v hA => aux_val s 0 A M0 y.mem hst hAK t ht v hA
  nocompiler_run_n 3 [hx, hpc, h2] using []
  have haux : s.reg 2 - 384#64 + 48#64 = auxBase s := by simp only [auxBase]; bv_omega
  refine PReachK.bind (Dom.sub_of_ranges (by decide)) (fun w hw => ?_)
    (init_tls_verified (auxBase s) _ k ⟨by simp only [nocompiler_state]; rfl, by simp only [nocompiler_state]; exact hx,
      by simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra]; decide,
      by simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra],
      by simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.sp, h2]; unfold aligned at *; bv_omega⟩
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  rotate_left
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact haux
  · simp only [auxBase]; unfold aligned at *; bv_omega
  · simp only [nocompiler_state]; exact av 3 (by omega) _ hI.phdr
  · simp only [nocompiler_state]; exact av 4 (by omega) _ hI.phent
  · simp only [nocompiler_state]; exact av 5 (by omega) _ hI.phnum
  · simp only [nocompiler_state]
    refine PhdrLit_congr (fun p hp => hF p (not_mem_of_mem_disj hI.dPh.symm hp) ?_ ?_ ?_) hI.ph
    · exact not_mem_of_mem_disj (by simp only [ilG, Region.Disjoint]; decide) hp
    · exact not_mem_of_mem_disj (by simp only [ilL, Region.Disjoint]; decide) hp
    · exact not_mem_of_mem_disj (by simp only [ilP, Region.Disjoint]; decide) hp
  · simp only [nocompiler_state]
    rw [il_tlw_read s _ hF hI.dW _ (by decide) (by simp only [ilG, Region.Disjoint]; decide)
      (by simp only [ilL, Region.Disjoint]; decide) (by simp only [ilP, Region.Disjoint]; decide)]
    exact hI.bss.1
  · simp only [nocompiler_state]
    rw [il_tlw_read s _ hF hI.dW _ (by decide) (by simp only [ilG, Region.Disjoint]; decide)
      (by simp only [ilL, Region.Disjoint]; decide) (by simp only [ilP, Region.Disjoint]; decide)]
    exact hI.bss.2.1
  · simp only [nocompiler_state]
    rw [il_tlw_read s _ hF hI.dW _ (by decide) (by simp only [ilG, Region.Disjoint]; decide)
      (by simp only [ilL, Region.Disjoint]; decide) (by simp only [ilP, Region.Disjoint]; decide)]
    exact hI.bss.2.2.1
  · simp only [nocompiler_state]
    rw [il_tlw_read s _ hF hI.dW _ (by decide) (by simp only [ilG, Region.Disjoint]; decide)
      (by simp only [ilL, Region.Disjoint]; decide) (by simp only [ilP, Region.Disjoint]; decide)]
    exact hI.bss.2.2.2.1
  · simp only [nocompiler_state]
    rw [il_tlw_read s _ hF hI.dW _ (by decide) (by simp only [ilG, Region.Disjoint]; decide)
      (by simp only [ilL, Region.Disjoint]; decide) (by simp only [ilP, Region.Disjoint]; decide)]
    exact hI.bss.2.2.2.2
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h2]; exact il_tls_perm s k e n A P S hI
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h2, auxBase, Region.Disjoint]; constructor <;> bv_omega
  · have := hI.dPh
    simp (disch := nocompiler_decide_closed) only [nocompiler_state, h2, ilS, Region.Disjoint] at this ⊢
    constructor <;> bv_omega
  · have := hI.dW
    simp (disch := nocompiler_decide_closed) only [nocompiler_state, h2, ilS, tlW, Region.Disjoint] at this ⊢
    constructor <;> bv_omega
  obtain ⟨-, hw⟩ := hw
  rcases hw with ⟨hxw, hpcw, hpw, hk, htrw, hfrw⟩ | ⟨-, hon⟩
  rotate_left
  · exact hon.elim
  obtain ⟨wv, wk⟩ := w
  simp only at hxw hpcw hpw hk htrw hfrw
  subst hk
  obtain ⟨-, -, -, cpr, c1, c2, c3, c4, -, ct⟩ := hC
  have es : ∀ q : Reg, q ≠ 11 → (s.setReg 11 P).reg q = s.reg q := fun q h => State.reg_setReg_other _ _ _ _ h
  have hz2 : ∀ q : Reg, q ≠ 1 → q ≠ 10 → q ≠ 4 →
      (((((((y.setReg 10 (s.reg 2 - 384#64 + 48#64)).setPc 70664#64).setReg 1 70664#64).setPc 70668#64).setReg 1
        70672#64).setPc 71588#64).setReg 4 0x14110#64).reg q = y.reg q := by
    intro q a b c; simp only [State.setPc_reg, State.reg_setReg_other _ _ _ _ a, State.reg_setReg_other _ _ _ _ b,
      State.reg_setReg_other _ _ _ _ c]
  have hwr : ∀ p, ¬ (Region.mk (s.reg 2 - 448#64) 64).mem p → ¬ tlW.mem p → wv.mem p = y.mem p := by
    intro p a b
    have a' : ¬ (Region.mk (s.reg 2 - 384#64 - 64#64) 64).mem p := by
      rw [show s.reg 2 - 384#64 - 64#64 = s.reg 2 - 448#64 by bv_omega]; exact a
    have := hfrw p (by simp (disch := nocompiler_decide_closed) only [nocompiler_state, h2]; exact a') b
    simpa only [nocompiler_state] using this
  have hw64 : ∀ a, (Region.mk a 8).Disjoint ⟨s.reg 2 - 448#64, 64⟩ → (Region.mk a 8).Disjoint tlW →
      read64 wv.mem a = read64 y.mem a := by
    intro a d1 d2; apply read64_congr_on; intro j hj
    exact hwr _ (not_mem_of_mem_disj d1.symm (by simp only [Region.mem]; bv_omega))
      (not_mem_of_mem_disj d2.symm (by simp only [Region.mem]; bv_omega))
  have hsl : ∀ o, o = 8 ∨ o = 16 ∨ o = 24 ∨ o = 32 → read64 wv.mem (s.reg 2 - BitVec.ofNat 64 o) =
      read64 y.mem (s.reg 2 - BitVec.ofNat 64 o) := by
    intro o ho
    obtain ⟨d1, d2⟩ := il_dis_slot s hI.dW hlo o (by omega) (by omega)
    exact hw64 _ d1 d2
  refine il_end s wk e n A P S hI hret hra4 wv ?_ hxw ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hpcw]; simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra]
  · rw [hpw 2 (by decide), hz2 2 (by decide) (by decide) (by decide), h2]
  · rw [hpw 4 (by decide)]; simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · intro q hq a2 a4 a8 a9 a18
    have hne : q ≠ 1 ∧ q ≠ 10 ∧ q ≠ 11 := by revert hq; revert q; decide
    rw [hpw q hq, hz2 q hne.1 hne.2.1 a4, cpr q hq a2 a8 a9 a18, es q hne.2.2]
  · rw [hsl 8 (by omega)]; rw [es 2 (by decide), es 1 (by decide)] at c1; exact c1
  · rw [hsl 16 (by omega)]; rw [es 2 (by decide), es 8 (by decide)] at c2; exact c2
  · rw [hsl 24 (by omega)]; rw [es 2 (by decide), es 9 (by decide)] at c3; exact c3
  · rw [hsl 32 (by omega)]; rw [es 2 (by decide), es 18 (by decide)] at c4; exact c4
  · intro t ht w' hA
    obtain ⟨d1, d2⟩ := il_dis_aux s hI.dW hlo t ht
    rw [hw64 _ d1 d2]; exact av t ht w' hA
  · rw [htrw]; simp only [nocompiler_state]; simpa only [nocompiler_state] using ct
  · intro p a b c
    rw [hwr p (fun h => a (by simp only [ilS, Region.mem] at h ⊢; bv_omega)) c]
    exact hF p a b (not_ilL_of_tlW c) (not_ilP_of_tlW c)


/-- `__init_libc` (0x112f0) at the process level for slen's launch: it sets tp to 0x14110. -/
theorem init_libc_verified : VerifiedProcT code initLibcD __init_libc_entry initLibcP 0x14110#64 := by
  rintro ⟨e, pn⟩ s k he ⟨n, A, P, S, hI⟩
  have hpc := he.pc
  have hx := he.live
  have hra4 := he.retAligned
  have hret := he.ret
  simp only [__init_libc_entry] at hpc
  simp only [Reg.ra] at hra4 hret
  have hPd : ilP.Disjoint (ilS s) := by
    have := hI.dW; simp only [tlW, ilP, Region.Disjoint] at this ⊢; constructor <;> bv_omega
  have hwP : ∀ p n, ilP.covers p n → k.perm.canWrite p n := fun p m h =>
    hI.wW p m (Region.covers_of_within h (by simp only [ilP, tlW, Region.within]; decide))
  refine il_entry s k _ hpc hx hI.sp hI.lo hI.wS (fun v hpv hCv h9v => ?_)
  refine il_env s k e n hI.env hI.dG hI.wG _ v hpv hCv (by rw [h9v, hI.a0]) (fun v2 hpv2 hE2 => ?_)
  refine il_aux s k e _ A hI.aux hI.lo hI.sp hI.wS hI.dW hI.wW n rfl _ v2 hpv2 hE2 (fun u hpu hD => ?_)
  have hst := hD.2.2.2
  refine il_misc s k _ A P hI.lo hI.sp hI.wS hI.wG hwP hI.dG hPd hI.pn _ u hpu hD (fun v3 hpv3 hPn hAK => ?_)
  refine PReachK.bind (fun _ h => h) ?_ (il_pn s k P S hI.str hI.wG hI.dG hI.lo u.mem (v3, k) ⟨0, by omega, rfl, hpv3, hPn, hAK⟩)
  rintro ⟨y, ky⟩ ⟨hk, hpy, hCy, h18y, hAKy⟩
  simp only at hk hpy hCy h18y hAKy
  subst hk
  exact il_tail s ky e n A P S hI hret hra4 u.mem hst y hpy hCy hAKy

end Examples.Libc.Slen

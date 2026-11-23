import Examples.Libc.InitLibcAux
import NoCompiler.Linux.RunN
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage

/-- A NUL-terminated string `S` at `P`, readable, away from what `__init_libc` writes. -/
structure StrAt (s : State) (k : Kern) (P : Word) (S : List Byte) : Prop where
  bytes : readBytes s.mem P (S.length + 1) = S ++ [0]
  nz : 0 ∉ S
  fit : P.toNat + S.length + 1 < 2 ^ 64
  rd : ∀ i, i ≤ S.length → k.perm.canRead (P + BitVec.ofNat 64 i) 1
  dS : (Region.mk P (S.length + 1)).Disjoint (ilS s)
  dG : (Region.mk P (S.length + 1)).Disjoint ilG
  dL : (Region.mk P (S.length + 1)).Disjoint ilL
  dP : (Region.mk P (S.length + 1)).Disjoint ilP

/-- The program name loop's head (0x113f8) after `i` bytes: a1 = P + i + 1, a2 = '/', a0 = &__progname; s0 = P
    (`IlCommon` against `s` with a1 = P). -/
def IlPn (s : State) (P : Word) (i : Nat) (u : State) : Prop :=
  IlCommon (s.setReg 11 P) u ∧ u.reg 11 = P + BitVec.ofNat 64 (i + 1) ∧ u.reg 12 = 47#64 ∧ u.reg 10 = 0x13fe8#64 ∧
    u.reg 18 = 0x14198#64

/-- `aux[]` in `m` as in `M0`. -/
def AuxKeep (s : State) (M0 m : Word → Byte) : Prop :=
  ∀ t, t < 38 → read64 m (auxBase s + BitVec.ofNat 64 (8 * t)) = read64 M0 (auxBase s + BitVec.ofNat 64 (8 * t))

theorem auxkeep_write (s : State) (hlo : 448 ≤ (s.reg 2).toNat) (M0 m : Word → Byte) (Rg : Region)
    (hR : Rg.Disjoint (ilS s)) (p : Word) (v n : Nat) (hc : Rg.covers p n) (hK : AuxKeep s M0 m) :
    AuxKeep s M0 (writeLE m p v n) := by
  intro t ht; rw [← hK t ht]; apply read64_congr_on; intro j hj
  exact writeLE_of_not_mem hc (not_mem_of_mem_disj hR (aux_slot_in s t ht hlo j hj).1)

theorem il_auxslot (s : State) (k : Kern) (hw : ∀ p n, (ilS s).covers p n → k.perm.canWrite p n) (hsp : aligned (s.reg 2) 16)
    (hlo : 448 ≤ (s.reg 2).toNat) (o : Nat) (ho : o < 38) :
    s.reg 2 - 384#64 + BitVec.ofNat 64 (48 + 8 * o) = auxBase s + BitVec.ofNat 64 (8 * o) ∧
    aligned (auxBase s + BitVec.ofNat 64 (8 * o)) 8 ∧ k.perm.canRead (auxBase s + BitVec.ofNat 64 (8 * o)) 8 := by
  refine ⟨by simp only [auxBase]; bv_omega, by simp only [auxBase]; unfold aligned at *; bv_omega,
    Perm.canRead_of_canWrite (hw _ _ (by simp only [auxBase, ilS, Region.covers]; bv_omega))⟩

theorem IlCommon_congr (s u w : State) (hC : IlCommon s u) (h1 : w.exit = none) (h2 : w.reg 2 = u.reg 2)
    (h8 : w.reg 8 = u.reg 8) (hr : ∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 8 → q ≠ 9 → q ≠ 18 → w.reg q = u.reg q)
    (hm : w.mem = u.mem) (ht : w.trace = u.trace) : IlCommon s w := by
  obtain ⟨-, c2, c8, cpr, s1, s2, s3, s4, cf, ct⟩ := hC
  exact ⟨h1, h2 ▸ c2, h8 ▸ c8, fun q hq a b c d => (hr q hq a b c d).trans (cpr q hq a b c d),
    hm ▸ s1, hm ▸ s2, hm ▸ s3, hm ▸ s4, hm ▸ cf, ht ▸ ct⟩

theorem IlCommon_retarget (s u : State) (P : Word) (hC : IlCommon s u) (h8 : u.reg 8 = P) :
    IlCommon (s.setReg 11 P) u := by
  obtain ⟨c1, c2, -, cpr, s1, s2, s3, s4, cf, ct⟩ := hC
  have e : ∀ q : Reg, q ≠ 11 → (s.setReg 11 P).reg q = s.reg q := fun q h => State.reg_setReg_other _ _ _ _ h
  refine ⟨c1, by rw [e 2 (by decide)]; exact c2, by rw [h8]; simp (disch := nocompiler_decide_closed) only [nocompiler_state],
    fun q hq a b c d => by rw [e q (by revert hq; revert q; decide)]; exact cpr q hq a b c d,
    by rw [e 2 (by decide), e 1 (by decide)]; exact s1, by rw [e 2 (by decide), e 8 (by decide)]; exact s2,
    by rw [e 2 (by decide), e 9 (by decide)]; exact s3, by rw [e 2 (by decide), e 18 (by decide)]; exact s4, ?_,
    by simp only [nocompiler_state]; exact ct⟩
  intro p a b c d
  have : ilS (s.setReg 11 P) = ilS s := by simp only [ilS, e 2 (by decide)]
  rw [this] at a; simp only [nocompiler_state]; exact cf p a b c d

theorem IlCommon_retarget' (s u w : State) (P : Word) (hC : IlCommon s u) (h1 : w.exit = none) (h2 : w.reg 2 = u.reg 2)
    (h8 : w.reg 8 = P) (hr : ∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 8 → q ≠ 9 → q ≠ 18 → w.reg q = u.reg q)
    (hm : w.mem = u.mem) (ht : w.trace = u.trace) : IlCommon (s.setReg 11 P) w := by
  obtain ⟨-, c2, -, cpr, s1, s2, s3, s4, cf, ct⟩ := hC
  have e : ∀ q : Reg, q ≠ 11 → (s.setReg 11 P).reg q = s.reg q := fun q h => State.reg_setReg_other _ _ _ _ h
  refine ⟨h1, by rw [e 2 (by decide), h2]; exact c2, by rw [h8]; simp (disch := nocompiler_decide_closed) only [nocompiler_state],
    fun q hq a b c d => by rw [e q (by revert hq; revert q; decide), hr q hq a b c d]; exact cpr q hq a b c d,
    by rw [e 2 (by decide), e 1 (by decide), hm]; exact s1, by rw [e 2 (by decide), e 8 (by decide), hm]; exact s2,
    by rw [e 2 (by decide), e 9 (by decide), hm]; exact s3, by rw [e 2 (by decide), e 18 (by decide), hm]; exact s4, ?_,
    by simp only [nocompiler_state]; rw [ht]; exact ct⟩
  intro p a b c d
  have : ilS (s.setReg 11 P) = ilS s := by simp only [ilS, e 2 (by decide)]
  rw [this] at a; simp only [nocompiler_state]; rw [hm]; exact cf p a b c d

/-- 0x113cc..0x113f4: __progname_full = __progname = P; a1 = P + 1, a2 = '/'; then the name loop's head. -/
theorem il_misc3 (s : State) (k : Kern) (P : Word) (hwG : ∀ p n, ilG.covers p n → k.perm.canWrite p n)
    (hGd : ilG.Disjoint (ilS s)) (R : State × Kern → Prop) (w : State) (hpc : w.pc = 0x113cc#64)
    (hC : IlCommon (s.setReg 11 P) w) (h18 : w.reg 18 = 0x14198#64) (hlo : 448 ≤ (s.reg 2).toNat)
    (M0 : Word → Byte) (hK : AuxKeep s M0 w.mem)
    (K : ∀ v, v.pc = 0x113f8#64 → IlPn s P 0 v → AuxKeep s M0 v.mem → PReachK code initLibcD R (v, k)) :
    PReachK code initLibcD R (w, k) := by
  have hx := hC.1
  have h8 := hC.2.2.1
  simp (disch := nocompiler_decide_closed) only [nocompiler_state] at h8
  have hGd' : ilG.Disjoint (ilS (s.setReg 11 P)) := by simp only [ilS]; simpa only [ilS, State.reg_setReg_other _ _ _ _ (show (2 : Reg) ≠ 11 by decide)] using hGd
  nocompiler_run_n 6 [hx, hpc, h8, show aligned (0x13ff0#64 : Word) 8 by decide, show aligned (0x13fe8#64 : Word) 8 by decide] using [hwG]
  iterate 3 nocompiler_wstep [hx, h8]
  have hC1 : IlCommon (s.setReg 11 P) (w.setMem (writeLE w.mem 0x13ff0#64 P.toNat 8)) :=
    IlCommon_storeG _ hGd' w hC 0x13ff0#64 P.toNat 8 (by simp only [ilG, Region.covers]; decide) _
      (by simp only [nocompiler_state]; exact hx) (by simp only [nocompiler_state]) (by simp only [nocompiler_state])
      (fun q _ _ _ _ _ => by simp only [nocompiler_state]) (by simp only [nocompiler_state]) (by simp only [nocompiler_state])
  refine K _ (by simp only [nocompiler_state]) ⟨IlCommon_storeG _ hGd' _ hC1 0x13fe8#64 P.toNat 8
      (by simp only [ilG, Region.covers]; decide) _ (by simp only [nocompiler_state]; exact hx)
      (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
      (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) (fun q hq a2 a8 a9 a18 => ?_)
      (by simp only [nocompiler_state]) (by simp only [nocompiler_state]), ?_, ?_, ?_, ?_⟩ ?_
  · have hne : q ≠ 10 ∧ q ≠ 11 ∧ q ≠ 12 := by revert hq; revert q; decide
    simp only [State.setPc_reg, State.setMem_reg, State.reg_setReg_other _ _ _ _ hne.1, State.reg_setReg_other _ _ _ _ hne.2.1,
      State.reg_setReg_other _ _ _ _ hne.2.2]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h18
  · simp only [nocompiler_state]
    exact auxkeep_write s hlo M0 _ ilG hGd _ _ _ (by simp only [ilG, Region.covers]; decide)
      (auxkeep_write s hlo M0 _ ilG hGd _ _ _ (by simp only [ilG, Region.covers]; decide) hK)

/-- 0x113b0..0x113f4: libc.page_size, the program name `P`, __progname_full, __progname; the name loop's head. -/
theorem il_misc2 (s : State) (k : Kern) (P : Word) (hlo : 448 ≤ (s.reg 2).toNat) (hsp : aligned (s.reg 2) 16)
    (hw : ∀ p n, (ilS s).covers p n → k.perm.canWrite p n)
    (hwG : ∀ p n, ilG.covers p n → k.perm.canWrite p n) (hwP : ∀ p n, ilP.covers p n → k.perm.canWrite p n)
    (hGd : ilG.Disjoint (ilS s)) (hPd : ilP.Disjoint (ilS s))
    (R : State × Kern → Prop) (v : State) (hpc : v.pc = 0x113b0#64) (hC : IlCommon s v) (h18 : v.reg 18 = 0x14198#64)
    (hP : (s.reg 11 ≠ 0 ∧ P = s.reg 11) ∨ (s.reg 11 = 0 ∧ P ≠ 0 ∧ read64 v.mem (auxBase s + BitVec.ofNat 64 (8 * 31)) = P))
    (M0 : Word → Byte) (hK : AuxKeep s M0 v.mem)
    (K : ∀ w, w.pc = 0x113f8#64 → IlPn s P 0 w → AuxKeep s M0 w.mem → PReachK code initLibcD R (w, k)) :
    PReachK code initLibcD R (v, k) := by
  have hx := hC.1
  have h2 := hC.2.1
  have h8 := hC.2.2.1
  obtain ⟨e6, a6, r6⟩ := il_auxslot s k hw hsp hlo 6 (by omega)
  obtain ⟨e31, a31, r31⟩ := il_auxslot s k hw hsp hlo 31 (by omega)
  simp only [show 48 + 8 * 6 = 96 from rfl] at e6
  simp only [show 48 + 8 * 31 = 296 from rfl] at e31
  nocompiler_run_n 2 [hx, hpc, h2, e6, a6, h18, show aligned (0x141c8#64 : Word) 8 by decide] using [r6, hwP, r31]
  have hC1 : IlCommon s (v.setMem (writeLE v.mem 0x141c8#64 (read64 v.mem (auxBase s + 48#64)).toNat 8)) :=
    IlCommon_storeW s ilP (.inr rfl) hPd v hC 0x141c8#64 (read64 v.mem (auxBase s + 48#64)).toNat 8 (by simp only [ilP, Region.covers]; decide) _
      (by simp only [nocompiler_state]; exact hx) (by simp only [nocompiler_state]) (by simp only [nocompiler_state])
      (fun q _ _ _ _ _ => by simp only [nocompiler_state]) (by simp only [nocompiler_state]) (by simp only [nocompiler_state])
  rcases hP with ⟨hpn, rfl⟩ | ⟨hpn, hPz, h31⟩
  · have hb : (s.reg 11 != 0) = true := by simpa using hpn
    nocompiler_run_n 2 [hx, h8, hb] using [r6, hwP, r31]
    refine il_misc3 s k _ hwG hGd R _ (by simp only [nocompiler_state]) (IlCommon_retarget s _ _ ?_ ?_) ?_ hlo M0
      (by simp only [nocompiler_state]; exact auxkeep_write s hlo M0 _ ilP hPd _ _ _ (by simp only [ilP, Region.covers]; decide) hK) K
    · refine IlCommon_congr s _ _ hC1 (by simp only [nocompiler_state]; exact hx)
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) (fun q hq _ _ _ _ => ?_)
        (by simp only [nocompiler_state]) (by simp only [nocompiler_state])
      have h10 : q ≠ 10 := by revert hq; revert q; decide
      simp only [State.setPc_reg, State.setMem_reg, State.reg_setReg_other _ _ _ _ h10]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h8
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h18
  · have hb : (s.reg 11 != 0) = false := by rw [hpn]; rfl
    have hr31 : read64 (writeLE v.mem 0x141c8#64 (read64 v.mem (auxBase s + 48#64)).toNat 8)
        (auxBase s + BitVec.ofNat 64 (8 * 31)) = P := by
      rw [rd_wr (by have := hPd; simp only [ilP, ilS, auxBase, Region.Disjoint] at this ⊢; constructor <;> bv_omega)]; exact h31
    have hbP : (P != 0) = true := by simpa using hPz
    nocompiler_run_n 3 [hx, h8, hb, h2, e31, a31, hr31, hbP] using [r6, hwP, r31]
    refine il_misc3 s k P hwG hGd R _ (by simp only [nocompiler_state])
      (IlCommon_retarget' s _ _ P hC1 (by simp only [nocompiler_state]; exact hx)
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) (fun q hq _ a8 _ _ => ?_)
        (by simp only [nocompiler_state]) (by simp only [nocompiler_state]))
      (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h18) hlo M0
      (by simp only [nocompiler_state]; exact auxkeep_write s hlo M0 _ ilP hPd _ _ _ (by simp only [ilP, Region.covers]; decide) hK) K
    have h10 : q ≠ 10 := by revert hq; revert q; decide
    simp only [State.setPc_reg, State.setMem_reg, State.reg_setReg_other _ _ _ _ h10, State.reg_setReg_other _ _ _ _ a8]

/-- 0x1137c..0x113f4: __hwcap, __sysinfo (if aux[AT_SYSINFO]), libc.page_size, the program name `P` (argv[0], else
    AT_EXECFN), __progname_full and __progname; then the name loop's head. -/
theorem il_misc (s : State) (k : Kern) (b : Word) (A : List (Word × Word)) (P : Word) (hlo : 448 ≤ (s.reg 2).toNat)
    (hsp : aligned (s.reg 2) 16) (hw : ∀ p n, (ilS s).covers p n → k.perm.canWrite p n)
    (hwG : ∀ p n, ilG.covers p n → k.perm.canWrite p n) (hwP : ∀ p n, ilP.covers p n → k.perm.canWrite p n)
    (hGd : ilG.Disjoint (ilS s)) (hPd : ilP.Disjoint (ilS s))
    (hP : (s.reg 11 ≠ 0 ∧ P = s.reg 11) ∨ (s.reg 11 = 0 ∧ P ≠ 0 ∧ ∃ i, ∃ hi : i < A.length, A[i].1 = 31#64 ∧ A[i].2 = P))
    (R : State × Kern → Prop) (u : State) (hpc : u.pc = 0x1137c#64) (hD : IlAuxDone s b A u)
    (K : ∀ v, v.pc = 0x113f8#64 → IlPn s P 0 v → AuxKeep s u.mem v.mem → PReachK code initLibcD R (v, k)) :
    PReachK code initLibcD R (u, k) := by
  obtain ⟨hC, h18, h9, hst⟩ := hD
  have hx := hC.1
  have h2 := hC.2.1
  have h8 := hC.2.2.1
  obtain ⟨e16, a16, r16⟩ := il_auxslot s k hw hsp hlo 16 (by omega)
  obtain ⟨e32, a32, r32⟩ := il_auxslot s k hw hsp hlo 32 (by omega)
  obtain ⟨e6, a6, r6⟩ := il_auxslot s k hw hsp hlo 6 (by omega)
  obtain ⟨e31, a31, r31⟩ := il_auxslot s k hw hsp hlo 31 (by omega)
  simp only [show 48 + 8 * 16 = 176 from rfl] at e16
  simp only [show 48 + 8 * 32 = 304 from rfl] at e32
  simp only [show 48 + 8 * 6 = 96 from rfl] at e6
  simp only [show 48 + 8 * 31 = 296 from rfl] at e31
  nocompiler_run_n 5 [hx, hpc, h2, e16, a16, e32, a32, show aligned (0x13ff8#64 : Word) 8 by decide] using [r16, r32, hwG]
  have hgs : ∀ (m : Word → Byte) (p : Word) (v : Nat), ilG.covers p 8 →
      read64 (writeLE m p v 8) (auxBase s + BitVec.ofNat 64 (8 * 31)) = read64 m (auxBase s + BitVec.ofNat 64 (8 * 31)) := by
    intro m p v hc; apply read64_congr_on; intro j hj
    exact writeLE_of_not_mem hc (not_mem_of_mem_disj hGd (aux_slot_in s 31 (by omega) hlo j hj).1)
  have h31 : s.reg 11 = 0 → read64 u.mem (auxBase s + BitVec.ofNat 64 (8 * 31)) = P := by
    intro hz
    rcases hP with ⟨hn, -⟩ | ⟨-, -, i, hi, ht, hv⟩
    · exact absurd hz hn
    · have := hst i hi (by rw [ht]; decide); rw [ht] at this; simpa [hv] using this
  have hC1 : IlCommon s (u.setMem (writeLE u.mem 0x13ff8#64 (read64 u.mem (auxBase s + 128#64)).toNat 8)) :=
    IlCommon_storeG s hGd u hC 0x13ff8#64 (read64 u.mem (auxBase s + 128#64)).toNat 8 (by simp only [ilG, Region.covers]; decide) _ (by simp only [nocompiler_state]; exact hx)
      (by simp only [nocompiler_state]) (by simp only [nocompiler_state]) (fun q _ _ _ _ _ => by simp only [nocompiler_state])
      (by simp only [nocompiler_state]) (by simp only [nocompiler_state])
  have hP' : ∀ (v : State), v.mem = writeLE u.mem 0x13ff8#64 (read64 u.mem (auxBase s + 128#64)).toNat 8 ∨
      (∃ m', m' = writeLE u.mem 0x13ff8#64 (read64 u.mem (auxBase s + 128#64)).toNat 8 ∧
        v.mem = writeLE m' 0x13fe0#64 (read64 u.mem (auxBase s + 256#64)).toNat 8) →
      (s.reg 11 ≠ 0 ∧ P = s.reg 11) ∨ (s.reg 11 = 0 ∧ P ≠ 0 ∧ read64 v.mem (auxBase s + BitVec.ofNat 64 (8 * 31)) = P) := by
    intro v hv
    rcases hP with h | ⟨hz, hPz, -⟩
    · exact .inl h
    · refine .inr ⟨hz, hPz, ?_⟩
      rcases hv with hv | ⟨m', rfl, hv⟩
      · rw [hv, hgs _ _ _ (by simp only [ilG, Region.covers]; decide)]; exact h31 hz
      · rw [hv, hgs _ _ _ (by simp only [ilG, Region.covers]; decide), hgs _ _ _ (by simp only [ilG, Region.covers]; decide)]
        exact h31 hz
  by_cases hsy : read64 u.mem (auxBase s + BitVec.ofNat 64 (8 * 32)) = 0
  · have hb : (read64 u.mem (auxBase s + BitVec.ofNat 64 (8 * 32)) == 0) = true := by rw [hsy]; rfl
    nocompiler_run_n 1 [hx, hb] using [r16, r32, hwG]
    refine il_misc2 s k P hlo hsp hw hwG hwP hGd hPd R _ (by simp only [nocompiler_state])
      (IlCommon_congr s _ _ hC1 (by simp only [nocompiler_state]; exact hx) (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) (fun q hq _ _ _ _ => ?_)
        (by simp only [nocompiler_state]) (by simp only [nocompiler_state]))
      (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h18)
      (hP' _ (.inl (by simp only [nocompiler_state]))) u.mem
      (by simp only [nocompiler_state]; exact auxkeep_write s hlo u.mem _ ilG hGd _ _ _ (by simp only [ilG, Region.covers]; decide) (fun _ _ => rfl)) K
    have hne : q ≠ 10 ∧ q ≠ 11 ∧ q ≠ 12 := by revert hq; revert q; decide
    simp only [State.setPc_reg, State.setMem_reg, State.reg_setReg_other _ _ _ _ hne.1, State.reg_setReg_other _ _ _ _ hne.2.1,
      State.reg_setReg_other _ _ _ _ hne.2.2]
  · have hb : (read64 u.mem (auxBase s + BitVec.ofNat 64 (8 * 32)) == 0) = false := by simpa using hsy
    nocompiler_run_n 5 [hx, hb, show aligned (0x13fe0#64 : Word) 8 by decide] using [r16, r32, hwG]
    refine il_misc2 s k P hlo hsp hw hwG hwP hGd hPd R _ (by simp only [nocompiler_state])
      (IlCommon_congr s _ _ (IlCommon_storeG s hGd _ hC1 0x13fe0#64 (read64 u.mem (auxBase s + 256#64)).toNat 8
          (by simp only [ilG, Region.covers]; decide) (u.setMem (writeLE (writeLE u.mem 0x13ff8#64 (read64 u.mem (auxBase s + 128#64)).toNat 8)
            0x13fe0#64 (read64 u.mem (auxBase s + 256#64)).toNat 8))
          (by simp only [nocompiler_state]; exact hx) (by simp only [nocompiler_state]) (by simp only [nocompiler_state])
          (fun q _ _ _ _ _ => by simp only [nocompiler_state]) (by simp only [nocompiler_state]) (by simp only [nocompiler_state]))
        (by simp only [nocompiler_state]; exact hx) (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) (fun q hq _ _ _ _ => ?_)
        (by simp only [nocompiler_state]) (by simp only [nocompiler_state]))
      (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h18)
      (hP' _ (.inr ⟨_, rfl, by simp only [nocompiler_state]⟩)) u.mem
      (by simp only [nocompiler_state]
          exact auxkeep_write s hlo u.mem _ ilG hGd _ _ _ (by simp only [ilG, Region.covers]; decide)
            (auxkeep_write s hlo u.mem _ ilG hGd _ _ _ (by simp only [ilG, Region.covers]; decide) (fun _ _ => rfl))) K
    have hne : q ≠ 10 ∧ q ≠ 11 ∧ q ≠ 12 := by revert hq; revert q; decide
    simp only [State.setPc_reg, State.setMem_reg, State.reg_setReg_other _ _ _ _ hne.1, State.reg_setReg_other _ _ _ _ hne.2.1,
      State.reg_setReg_other _ _ _ _ hne.2.2]

end Examples.Libc.Slen

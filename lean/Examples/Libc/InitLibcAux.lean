import Examples.Libc.InitLibcEnv
import NoCompiler.Linux.RunN
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage

/-- The auxv (type, value) pairs `A` (types nonzero and distinct) and the AT_NULL type after them at `b`,
    away from what `__init_libc` writes, readable. -/
structure AuxAt (s : State) (k : Kern) (b : Word) (A : List (Word × Word)) : Prop where
  ty : ∀ j (h : j < A.length), read64 s.mem (b + BitVec.ofNat 64 (16 * j)) = A[j].1
  va : ∀ j (h : j < A.length), read64 s.mem (b + BitVec.ofNat 64 (16 * j + 8)) = A[j].2
  nz : ∀ j (h : j < A.length), A[j].1 ≠ 0
  nul : read64 s.mem (b + BitVec.ofNat 64 (16 * A.length)) = 0
  nd : (A.map Prod.fst).Nodup
  ne : A ≠ []
  fit : b.toNat + 16 * A.length + 8 < 2 ^ 64
  al : aligned b 8
  rd : ∀ o, o ≤ 16 * A.length → o % 8 = 0 → k.perm.canRead (b + BitVec.ofNat 64 o) 8
  dS : (Region.mk b (16 * A.length + 8)).Disjoint (ilS s)
  dG : (Region.mk b (16 * A.length + 8)).Disjoint ilG
  dW : (Region.mk b (16 * A.length + 8)).Disjoint tlW

/-- `__init_libc`'s `aux[]` array: 38 words at sp - 336. -/
def auxBase (s : State) : Word := s.reg 2 - 336#64

/-- The auxv loop at 0x11368 (`bltu a2, a0`) at entry `j`: its type in a0, a1 at entry j + 1, a2 = 37, a3 = aux,
    s2 = &libc; the entries before `j` with a type below 38 stored in `aux[]`. -/
def IlAux (s : State) (b : Word) (A : List (Word × Word)) (j : Nat) (u : State) : Prop :=
  IlCommon s u ∧ ∃ h : j < A.length, u.reg 10 = A[j].1 ∧ u.reg 11 = b + BitVec.ofNat 64 (16 * (j + 1)) ∧
    u.reg 12 = 37#64 ∧ u.reg 13 = auxBase s ∧ u.reg 9 = b ∧ u.reg 18 = 0x14198#64 ∧
    ∀ i (hi : i < j), (A[i].1).toNat < 38 → read64 u.mem (auxBase s + BitVec.ofNat 64 (8 * (A[i].1).toNat)) = A[i].2

/-- After the auxv loop (0x1137c): all entries with a type below 38 stored. -/
def IlAuxDone (s : State) (b : Word) (A : List (Word × Word)) (u : State) : Prop :=
  IlCommon s u ∧ u.reg 18 = 0x14198#64 ∧ u.reg 9 = b ∧
    ∀ i (hi : i < A.length), (A[i].1).toNat < 38 → read64 u.mem (auxBase s + BitVec.ofNat 64 (8 * (A[i].1).toNat)) = A[i].2

theorem aux_slot_in (s : State) (t : Nat) (ht : t < 38) (hlo : 448 ≤ (s.reg 2).toNat) (j : Nat) (hj : j < 8) :
    (ilS s).mem (auxBase s + BitVec.ofNat 64 (8 * t) + BitVec.ofNat 64 j) ∧
    (auxBase s + BitVec.ofNat 64 (8 * t) + BitVec.ofNat 64 j - (s.reg 2 - 448#64)).toNat < 416 := by
  simp only [auxBase, ilS, Region.mem]; constructor <;> bv_omega

/-- A store into `aux[t]` keeps `IlCommon`. -/
theorem IlCommon_storeAux (s : State) (hlo : 448 ≤ (s.reg 2).toNat) (u : State) (hC : IlCommon s u) (t : Nat) (ht : t < 38)
    (v : Nat) (w : State) (h1 : w.exit = none) (h2 : w.reg 2 = u.reg 2) (h8 : w.reg 8 = u.reg 8)
    (hr : ∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 8 → q ≠ 9 → q ≠ 18 → w.reg q = u.reg q)
    (hm : w.mem = writeLE u.mem (auxBase s + BitVec.ofNat 64 (8 * t)) v 8) (ht' : w.trace = u.trace) : IlCommon s w := by
  obtain ⟨-, c2, c8, cpr, s1, s2, s3, s4, cf, ct⟩ := hC
  have hc : (ilS s).covers (auxBase s + BitVec.ofNat 64 (8 * t)) 8 := by simp only [auxBase, ilS, Region.covers]; bv_omega
  have hsl : ∀ o, o = 8 ∨ o = 16 ∨ o = 24 ∨ o = 32 → read64 w.mem (s.reg 2 - BitVec.ofNat 64 o) = read64 u.mem (s.reg 2 - BitVec.ofNat 64 o) := by
    intro o ho; rw [hm]; apply rd_wr
    simp only [auxBase, Region.Disjoint]; rcases ho with rfl | rfl | rfl | rfl <;> constructor <;> bv_omega
  refine ⟨h1, by rw [h2]; exact c2, by rw [h8]; exact c8, fun q hq a b c d => by rw [hr q hq a b c d]; exact cpr q hq a b c d,
    by rw [hsl 8 (by simp)]; exact s1, by rw [hsl 16 (by simp)]; exact s2, by rw [hsl 24 (by simp)]; exact s3,
    by rw [hsl 32 (by simp)]; exact s4, ?_, by rw [ht']; exact ct⟩
  intro q a b c d; rw [hm, writeLE_of_not_mem hc a]; exact cf q a b c d

theorem aux_read_ne (s : State) (m : Word → Byte) (t t' : Nat) (ht : t < 38) (ht' : t' < 38) (hne : t ≠ t') (v : Nat)
    (hlo : 448 ≤ (s.reg 2).toNat) :
    read64 (writeLE m (auxBase s + BitVec.ofNat 64 (8 * t)) v 8) (auxBase s + BitVec.ofNat 64 (8 * t')) =
      read64 m (auxBase s + BitVec.ofNat 64 (8 * t')) := by
  apply rd_wr; simp only [auxBase, Region.Disjoint]
  rcases Nat.lt_or_gt_of_ne hne with h | h <;> constructor <;> bv_omega

theorem aux_read (s : State) (k : Kern) (b : Word) (A : List (Word × Word)) (hA : AuxAt s k b A) (m : Word → Byte)
    (hm : IlFrame s m) (o : Nat) (ho : o ≤ 16 * A.length) :
    read64 m (b + BitVec.ofNat 64 o) = read64 s.mem (b + BitVec.ofNat 64 o) := by
  apply read64_congr_on; intro j hj
  have hin : (Region.mk b (16 * A.length + 8)).mem (b + BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
    have := hA.fit; simp only [Region.mem]; bv_omega
  exact hm _ (not_mem_of_mem_disj hA.dS.symm hin) (not_mem_of_mem_disj hA.dG.symm hin)
    (not_ilL_of_tlW (not_mem_of_mem_disj hA.dW.symm hin)) (not_ilP_of_tlW (not_mem_of_mem_disj hA.dW.symm hin))

/-- At 0x1135c: entries through `j` handled, a1 at entry j + 1. -/
def IlAuxN (s : State) (b : Word) (A : List (Word × Word)) (j : Nat) (u : State) : Prop :=
  IlCommon s u ∧ j < A.length ∧ u.reg 11 = b + BitVec.ofNat 64 (16 * (j + 1)) ∧
    u.reg 12 = 37#64 ∧ u.reg 13 = auxBase s ∧ u.reg 9 = b ∧ u.reg 18 = 0x14198#64 ∧
    ∀ i (hi : i ≤ j) (hi' : i < A.length), (A[i].1).toNat < 38 →
      read64 u.mem (auxBase s + BitVec.ofNat 64 (8 * (A[i].1).toNat)) = A[i].2

theorem il_aux_next (s : State) (k : Kern) (b : Word) (A : List (Word × Word)) (hA : AuxAt s k b A) (j : Nat)
    (u : State) (hpc : u.pc = 0x1135c#64) (hN : IlAuxN s b A j u) :
    PReachK code initLibcD (fun y => (y.2 = k ∧ y.1.pc = 0x1137c#64 ∧ IlAuxDone s b A y.1) ∨
      ((y.2 = k ∧ y.1.pc = 0x11368#64 ∧ IlAux s b A (j + 1) y.1))) (u, k) := by
  obtain ⟨hC, hj, h11, h12, h13, h9, h18, hst⟩ := hN
  have hx := hC.1
  have hfit := hA.fit
  have hr := aux_read s k b A hA u.mem hC.2.2.2.2.2.2.2.2.1 (16 * (j + 1)) (by omega)
  have al : aligned (b + BitVec.ofNat 64 (16 * (j + 1))) 8 := by have := hA.al; unfold aligned at *; bv_omega
  nocompiler_run_n 2 [hx, hpc, h11, al] using [hA.rd]
  have hadd : b + BitVec.ofNat 64 (16 * (j + 1)) + 16#64 = b + BitVec.ofNat 64 (16 * (j + 1 + 1)) := by
    rw [BitVec.add_assoc, show (16#64 : Word) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add]; congr 2
  have hC' : ∀ v : State, v.exit = none → v.reg 2 = u.reg 2 → v.reg 8 = u.reg 8 → v.mem = u.mem → v.trace = u.trace →
      (∀ q ∈ preservedRegs, q ≠ 9 → q ≠ 18 → v.reg q = u.reg q) → IlCommon s v := by
    intro v a1 a2 a3 a4 a5 a6
    obtain ⟨-, c2, c8, cpr, s1, s2, s3, s4, cf, ct⟩ := hC
    refine ⟨a1, by rw [a2]; exact c2, by rw [a3]; exact c8, fun q hq b2 b8 b9 b18 => by rw [a6 q hq b9 b18]; exact cpr q hq b2 b8 b9 b18,
      by rw [a4]; exact s1, by rw [a4]; exact s2, by rw [a4]; exact s3, by rw [a4]; exact s4, by rw [a4]; exact cf,
      by rw [a5]; exact ct⟩
  rcases Nat.lt_or_ge (j + 1) A.length with hlt | hge
  · have hb : (read64 s.mem (b + BitVec.ofNat 64 (16 * (j + 1))) == 0) = false := by
      rw [hA.ty (j + 1) hlt]; simpa using hA.nz (j + 1) hlt
    nocompiler_run_n 1 [hx, hr, hb] using [hA.rd]
    refine .done (.inr ⟨rfl, by simp only [nocompiler_state], hC' _ (by simp only [nocompiler_state]; exact hx)
      (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
      (by simp only [nocompiler_state]) (by simp only [nocompiler_state]) (fun q hq a9 a18 => ?_), hlt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    · have hne : q ≠ 10 ∧ q ≠ 11 := by revert hq; revert q; decide
      simp only [State.setPc_reg, State.reg_setReg_other _ _ _ _ hne.1, State.reg_setReg_other _ _ _ _ hne.2]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, hr]; exact hA.ty (j + 1) hlt
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact hadd
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h13
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h9
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h18
    · intro i hi hlt38; simp only [nocompiler_state]; exact hst i (by omega) (by omega) hlt38
  · have hb : (read64 s.mem (b + BitVec.ofNat 64 (16 * (j + 1))) == 0) = true := by
      rw [show j + 1 = A.length by omega, hA.nul]; rfl
    nocompiler_run_n 1 [hx, hr, hb] using [hA.rd]
    refine .done (.inl ⟨rfl, by simp only [nocompiler_state], hC' _ (by simp only [nocompiler_state]; exact hx)
      (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
      (by simp only [nocompiler_state]) (by simp only [nocompiler_state]) (fun q hq a9 a18 => ?_), ?_, ?_, ?_⟩)
    · have hne : q ≠ 10 ∧ q ≠ 11 := by revert hq; revert q; decide
      simp only [State.setPc_reg, State.reg_setReg_other _ _ _ _ hne.1, State.reg_setReg_other _ _ _ _ hne.2]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h18
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h9
    · intro i hi hlt38; simp only [nocompiler_state]; exact hst i (by omega) hi hlt38

theorem aux_types_ne (A : List (Word × Word)) (hnd : (A.map Prod.fst).Nodup) (i j : Nat) (hi : i < A.length)
    (hj : j < A.length) (hij : i ≠ j) : (A[i].1).toNat ≠ (A[j].1).toNat := by
  intro h
  have h' : (A.map Prod.fst)[i]'(by simpa using hi) = (A.map Prod.fst)[j]'(by simpa using hj) := by
    simp only [List.getElem_map]; exact BitVec.eq_of_toNat_eq h
  exact hij (hnd.eq_of_getElem_eq _ _ h')

theorem aux_shl (x a : Word) (h : x.toNat < 38) : (x <<< 3) + a = a + BitVec.ofNat 64 (8 * x.toNat) := by
  rw [BitVec.add_comm]; congr 1; apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega

theorem il_aux_iter (s : State) (k : Kern) (b : Word) (A : List (Word × Word)) (hA : AuxAt s k b A) (j : Nat)
    (hlo : 448 ≤ (s.reg 2).toNat) (hsp : aligned (s.reg 2) 16) (hw : ∀ p n, (ilS s).covers p n → k.perm.canWrite p n)
    (u : State) (hpc : u.pc = 0x11368#64) (hI : IlAux s b A j u) (R : State × Kern → Prop)
    (K : ∀ v, v.pc = 0x1135c#64 → IlAuxN s b A j v → PReachK code initLibcD R (v, k)) :
    PReachK code initLibcD R (u, k) := by
  obtain ⟨hC, hj, h10, h11, h12, h13, h9, h18, hst⟩ := hI
  have hx := hC.1
  have hfit := hA.fit
  have hC' : ∀ v : State, v.exit = none → v.reg 2 = u.reg 2 → v.reg 8 = u.reg 8 → v.mem = u.mem → v.trace = u.trace →
      (∀ q ∈ preservedRegs, q ≠ 9 → q ≠ 18 → v.reg q = u.reg q) → IlCommon s v := by
    intro v a1 a2 a3 a4 a5 a6
    obtain ⟨-, c2, c8, cpr, s1, s2, s3, s4, cf, ct⟩ := hC
    refine ⟨a1, by rw [a2]; exact c2, by rw [a3]; exact c8, fun q hq b2 b8 b9 b18 => by rw [a6 q hq b9 b18]; exact cpr q hq b2 b8 b9 b18,
      by rw [a4]; exact s1, by rw [a4]; exact s2, by rw [a4]; exact s3, by rw [a4]; exact s4, by rw [a4]; exact cf,
      by rw [a5]; exact ct⟩
  by_cases ht : (A[j].1).toNat < 38
  · have hb : BitVec.ult (37#64) (A[j].1) = false := by simp only [BitVec.ult, decide_eq_false_iff_not]; show ¬ 37 < _; omega
    have ea : b + BitVec.ofNat 64 (16 * (j + 1)) + 18446744073709551608#64 = b + BitVec.ofNat 64 (16 * j + 8) := by bv_omega
    have hr := aux_read s k b A hA u.mem hC.2.2.2.2.2.2.2.2.1 (16 * j + 8) (by omega)
    have al : aligned (b + BitVec.ofNat 64 (16 * j + 8)) 8 := by have := hA.al; unfold aligned at *; bv_omega
    have alS : aligned (auxBase s + BitVec.ofNat 64 (8 * (A[j].1).toNat)) 8 := by
      simp only [auxBase]; unfold aligned at *; bv_omega
    nocompiler_wstep [hx, hpc, h10, h12, hb]
    nocompiler_wstep [hx, h11, ea, al, hr]
    refine ⟨hA.rd _ (by omega) (by omega), ?_⟩
    nocompiler_wstep [hx, h10, h13, aux_shl _ _ ht]
    nocompiler_wstep [hx, alS]
    refine ⟨hw _ _ (by simp only [auxBase, ilS, Region.covers]; bv_omega), ?_⟩
    nocompiler_wstep [hx]
    refine K _ (by simp only [nocompiler_state]) ⟨?_, hj, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine IlCommon_storeAux s hlo u hC _ ht (read64 s.mem (b + BitVec.ofNat 64 (16 * j + 8))).toNat _ (by simp only [nocompiler_state]; exact hx)
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
        (fun q hq a2 a8 a9 a18 => ?_) (by simp only [nocompiler_state]) (by simp only [nocompiler_state])
      have hne : q ≠ 10 ∧ q ≠ 14 := by revert hq; revert q; decide
      simp only [State.setPc_reg, State.setMem_reg, State.reg_setReg_other _ _ _ _ hne.1, State.reg_setReg_other _ _ _ _ hne.2]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h11
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h13
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h9
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h18
    · intro i hi hi' hlt38
      simp only [nocompiler_state]
      rcases Nat.lt_or_ge i j with hij | hij
      · rw [aux_read_ne s _ _ _ ht hlt38 (aux_types_ne A hA.nd j i hj hi' (by omega)).symm.symm _ hlo]
        exact hst i hij hlt38
      · have : i = j := by omega
        subst this
        rw [Auto.read64_writeLE_same']; simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]; rw [hA.va i hi']
  · have hb : BitVec.ult (37#64) (A[j].1) = true := by simp only [BitVec.ult, decide_eq_true_eq]; show 37 < _; omega
    nocompiler_wstep [hx, hpc, h10, h12, hb]
    refine K _ (by simp only [nocompiler_state]) ⟨hC' _ (by simp only [nocompiler_state]; exact hx) (by simp only [nocompiler_state])
      (by simp only [nocompiler_state]) (by simp only [nocompiler_state]) (by simp only [nocompiler_state])
      (fun q hq _ _ => by simp only [nocompiler_state]), hj, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [nocompiler_state]; exact h11
    · simp only [nocompiler_state]; exact h12
    · simp only [nocompiler_state]; exact h13
    · simp only [nocompiler_state]; exact h9
    · simp only [nocompiler_state]; exact h18
    · intro i hi hi' hlt38
      simp only [nocompiler_state]
      rcases Nat.lt_or_ge i j with hij | hij
      · exact hst i hij hlt38
      · have : i = j := by omega
        subst this; exact absurd hlt38 ht

/-- A store into `libc.auxv` or `libc.page_size` keeps `IlCommon`. -/
theorem IlCommon_storeW (s : State) (R : Region) (hR : R = ilL ∨ R = ilP) (hWd : R.Disjoint (ilS s)) (u : State)
    (hC : IlCommon s u) (p : Word) (v n : Nat) (hc : R.covers p n) (w : State) (h1 : w.exit = none) (h2 : w.reg 2 = u.reg 2) (h8 : w.reg 8 = u.reg 8)
    (hr : ∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 8 → q ≠ 9 → q ≠ 18 → w.reg q = u.reg q)
    (hm : w.mem = writeLE u.mem p v n) (ht : w.trace = u.trace) : IlCommon s w := by
  obtain ⟨-, c2, c8, cpr, s1, s2, s3, s4, cf, ct⟩ := hC
  have hsl : ∀ o, o = 8 ∨ o = 16 ∨ o = 24 ∨ o = 32 → read64 w.mem (s.reg 2 - BitVec.ofNat 64 o) = read64 u.mem (s.reg 2 - BitVec.ofNat 64 o) := by
    intro o ho; rw [hm]; apply read64_congr_on; intro j hj
    exact writeLE_of_not_mem hc (not_mem_of_mem_disj hWd (by simp only [ilS, Region.mem]; rcases ho with rfl | rfl | rfl | rfl <;> bv_omega))
  refine ⟨h1, by rw [h2]; exact c2, by rw [h8]; exact c8, fun q hq a b c d => by rw [hr q hq a b c d]; exact cpr q hq a b c d,
    by rw [hsl 8 (by simp)]; exact s1, by rw [hsl 16 (by simp)]; exact s2, by rw [hsl 24 (by simp)]; exact s3,
    by rw [hsl 32 (by simp)]; exact s4, ?_, by rw [ht]; exact ct⟩
  intro q a b c d
  rcases hR with rfl | rfl
  · rw [hm, writeLE_of_not_mem hc c]; exact cf q a b c d
  · rw [hm, writeLE_of_not_mem hc d]; exact cf q a b c d

/-- `libc.auxv = auxv` (0x11338..0x11340), then the auxv loop to its end (0x1137c). -/
theorem il_aux (s : State) (k : Kern) (e b : Word) (A : List (Word × Word)) (hA : AuxAt s k b A)
    (hlo : 448 ≤ (s.reg 2).toNat) (hsp : aligned (s.reg 2) 16) (hw : ∀ p n, (ilS s).covers p n → k.perm.canWrite p n)
    (hWd : tlW.Disjoint (ilS s)) (hwW : ∀ p n, tlW.covers p n → k.perm.canWrite p n)
    (n : Nat) (hb : e + BitVec.ofNat 64 (8 * (n + 1)) = b) (R : State × Kern → Prop) (u : State)
    (hpc : u.pc = 0x11338#64) (hE : IlEnv s e (n + 1) u)
    (K : ∀ v, v.pc = 0x1137c#64 → IlAuxDone s b A v → PReachK code initLibcD R (v, k)) :
    PReachK code initLibcD R (u, k) := by
  obtain ⟨hC, h9⟩ := hE
  rw [hb] at h9
  have hx := hC.1
  have hfit := hA.fit
  have hL := List.length_pos_iff.mpr hA.ne
  have hdw : (Region.mk 0x141a0#64 8).Disjoint ⟨b, 8⟩ := by
    have := hA.dW; simp only [tlW, Region.Disjoint] at this ⊢; constructor <;> bv_omega
  have hr0 : read64 (writeLE u.mem 0x141a0#64 b.toNat 8) b = A[0].1 := by
    rw [rd_wr hdw]
    have := aux_read s k b A hA u.mem hC.2.2.2.2.2.2.2.2.1 0 (by omega)
    simp only [BitVec.add_zero] at this
    rw [this]; have := hA.ty 0 hL; simpa using this
  have alb : aligned b 8 := hA.al
  have hb0 : (A[0].1 == 0) = false := by simpa using hA.nz 0 hL
  nocompiler_run_n 4 [hx, hpc, h9, show aligned (0x141a0#64 : Word) 8 by decide, alb, hr0] using [hwW]
  refine ⟨by have := hA.rd 0 (by omega) (by omega); simpa using this, ?_⟩
  nocompiler_run_n 1 [hx, hb0] using [hwW]
  iterate 4 nocompiler_wstep [hx]
  have hmeas : ∀ j, j + 1 ≤ A.length → (b + BitVec.ofNat 64 (16 * (j + 1)) - b).toNat / 16 = j + 1 := by
    intro j hj
    rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  refine PReachK.bind (fun _ h => h) ?_ (PReachK.loop (Q := fun y => y.2 = k ∧ y.1.pc = 0x1137c#64 ∧ IlAuxDone s b A y.1)
    (fun x => ∃ j, x.2 = k ∧ x.1.pc = 0x11368#64 ∧ IlAux s b A j x.1)
    (fun x => A.length + 1 - ((x.1.reg 11 - b).toNat / 16)) ?_ (_, k) ⟨0, rfl, by simp only [nocompiler_state], ?_, hL, ?_⟩)
  · rintro ⟨y, ky⟩ ⟨hk, hpy, hy⟩
    simp only at hk hpy hy
    subst hk
    exact K y hpy hy
  · rintro ⟨v, kv⟩ ⟨j, hkv, hpv, hI⟩
    simp only at hkv hpv hI
    subst hkv
    have hj := hI.2.1
    have h11 := hI.2.2.2.1
    refine il_aux_iter s kv b A hA j hlo hsp hw v hpv hI _ (fun w hpw hN => ?_)
    refine PReachK.bind (fun _ h => h) ?_ (il_aux_next s kv b A hA j w hpw hN)
    rintro y (hq | ⟨hk, hpy, hy⟩)
    · exact .done (.inl hq)
    · refine .done (.inr ⟨⟨j + 1, hk, hpy, hy⟩, ?_⟩)
      simp only
      obtain ⟨hj1, h11'⟩ := hy.2.1, hy.2.2.2.1
      rw [h11', h11, hmeas (j + 1) (by omega), hmeas j (by omega)]; omega
  · refine IlCommon_storeW s ilL (.inl rfl) (by have := hWd; simp only [tlW, ilL, Region.Disjoint] at this ⊢; constructor <;> bv_omega)
      u hC 0x141a0#64 b.toNat 8 (by simp only [ilL, Region.covers]; decide) _
      (by simp only [nocompiler_state]; exact hx) (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
      (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) (fun q hq a2 a8 a9 a18 => ?_)
      (by simp only [nocompiler_state]) (by simp only [nocompiler_state])
    have hne : q ≠ 10 ∧ q ≠ 11 ∧ q ≠ 12 ∧ q ≠ 13 := by revert hq; revert q; decide
    simp only [State.setPc_reg, State.setMem_reg, State.reg_setReg_other _ _ _ _ hne.1, State.reg_setReg_other _ _ _ _ hne.2.1,
      State.reg_setReg_other _ _ _ _ hne.2.2.1, State.reg_setReg_other _ _ _ _ hne.2.2.2, State.reg_setReg_other _ _ _ _ a18]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h9]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · have h2 := hC.2.1
      simp (disch := nocompiler_decide_closed) only [nocompiler_state, h2, auxBase]; bv_omega
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h9]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]

end Examples.Libc.Slen

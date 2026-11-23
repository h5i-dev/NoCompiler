import Examples.Libc.InitLibcEntry
import NoCompiler.Linux.RunN
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage

/-- envp's `n` pointers (nonzero) and its NULL in memory `m`, away from what `__init_libc` writes, readable. -/
structure EnvAt (s : State) (k : Kern) (e : Word) (n : Nat) : Prop where
  nz : ∀ i, i < n → read64 s.mem (e + BitVec.ofNat 64 (8 * i)) ≠ 0
  nul : read64 s.mem (e + BitVec.ofNat 64 (8 * n)) = 0
  fit : e.toNat + 8 * (n + 1) < 2 ^ 64
  al : aligned e 8
  rd : ∀ i, i ≤ n → k.perm.canRead (e + BitVec.ofNat 64 (8 * i)) 8
  dS : (Region.mk e (8 * (n + 1))).Disjoint (ilS s)
  dG : (Region.mk e (8 * (n + 1))).Disjoint ilG
  dW : (Region.mk e (8 * (n + 1))).Disjoint tlW

theorem env_read (s : State) (k : Kern) (e : Word) (n : Nat) (hE : EnvAt s k e n) (m : Word → Byte) (hm : IlFrame s m)
    (i : Nat) (hi : i ≤ n) : read64 m (e + BitVec.ofNat 64 (8 * i)) = read64 s.mem (e + BitVec.ofNat 64 (8 * i)) := by
  apply read64_congr_on; intro j hj
  have hin : (Region.mk e (8 * (n + 1))).mem (e + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j) := by
    have := hE.fit; simp only [Region.mem]; bv_omega
  exact hm _ (not_mem_of_mem_disj hE.dS.symm hin) (not_mem_of_mem_disj hE.dG.symm hin)
    (not_ilL_of_tlW (not_mem_of_mem_disj hE.dW.symm hin)) (not_ilP_of_tlW (not_mem_of_mem_disj hE.dW.symm hin))

/-- The envp loop's head (0x1132c) after `i` pointers. -/
def IlEnv (s : State) (e : Word) (i : Nat) (u : State) : Prop :=
  IlCommon s u ∧ u.reg 9 = e + BitVec.ofNat 64 (8 * i)

theorem il_env_loop (s : State) (k : Kern) (e : Word) (n : Nat) (hE : EnvAt s k e n) :
    ∀ x : State × Kern, (∃ i, i ≤ n ∧ x.2 = k ∧ x.1.pc = 0x1132c#64 ∧ IlEnv s e i x.1) →
      PReachK code initLibcD (fun y => y.2 = k ∧ y.1.pc = 0x11338#64 ∧ IlEnv s e (n + 1) y.1) x := by
  refine PReachK.loop _ (fun x => n + 1 - ((x.1.reg 9 - e).toNat / 8)) ?_
  rintro ⟨u, ku⟩ ⟨i, hi, hku, hpc, hC, h9⟩
  simp only at hku hpc hC h9
  subst hku
  have hx := hC.1
  have hr := env_read s _ e n hE u.mem hC.2.2.2.2.2.2.2.2.1 i hi
  have al : aligned (e + BitVec.ofNat 64 (8 * i)) 8 := by have := hE.al; unfold aligned at *; have := hE.fit; bv_omega
  nocompiler_run_n 2 [hx, hpc, h9, al] using [hE.rd]
  have hfit := hE.fit
  have hadd : e + BitVec.ofNat 64 (8 * i) + 8#64 = e + BitVec.ofNat 64 (8 * (i + 1)) := by
    rw [BitVec.add_assoc, show (8#64 : Word) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]; congr 2
  have hmeas : ∀ j, j ≤ n + 1 → (e + BitVec.ofNat 64 (8 * j) - e).toNat / 8 = j := by
    intro j hj
    rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  have hC' : ∀ v : State, v.exit = none → v.reg 2 = u.reg 2 → v.reg 8 = u.reg 8 → v.mem = u.mem → v.trace = u.trace →
      (∀ q ∈ preservedRegs, q ≠ 9 → v.reg q = u.reg q) → IlCommon s v := by
    intro v a1 a2 a3 a4 a5 a6
    obtain ⟨-, c2, c8, cpr, s1, s2, s3, s4, cf, ct⟩ := hC
    refine ⟨a1, by rw [a2]; exact c2, by rw [a3]; exact c8, fun q hq b2 b8 b9 b18 => by rw [a6 q hq b9]; exact cpr q hq b2 b8 b9 b18,
      by rw [a4]; exact s1, by rw [a4]; exact s2, by rw [a4]; exact s3, by rw [a4]; exact s4, by rw [a4]; exact cf,
      by rw [a5]; exact ct⟩
  rcases Nat.lt_or_ge i n with hlt | hge
  · have hb : (read64 s.mem (e + BitVec.ofNat 64 (8 * i)) != 0) = true := by simpa using hE.nz i hlt
    nocompiler_run_n 1 [hx, hr, hb] using [hE.rd]
    refine .done (.inr ⟨⟨i + 1, hlt, rfl, by simp only [nocompiler_state], hC' _ (by simp only [nocompiler_state]; exact hx)
      (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
      (by simp only [nocompiler_state]) (by simp only [nocompiler_state]) (fun q hq h9q => ?_),
      by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact hadd⟩, ?_⟩)
    · have h10 : q ≠ 10 := by revert hq; revert q; decide
      simp only [State.setPc_reg, State.reg_setReg_other _ _ _ _ h10, State.reg_setReg_other _ _ _ _ h9q]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
      rw [hadd, hmeas (i + 1) (by omega), hmeas i (by omega)]; omega
  · have hin : i = n := by omega
    subst hin
    have hb : (read64 s.mem (e + BitVec.ofNat 64 (8 * i)) != 0) = false := by rw [hE.nul]; rfl
    nocompiler_run_n 1 [hx, hr, hb] using [hE.rd]
    refine .done (.inl ⟨rfl, by simp only [nocompiler_state], hC' _ (by simp only [nocompiler_state]; exact hx)
      (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
      (by simp only [nocompiler_state]) (by simp only [nocompiler_state]) (fun q hq h9q => ?_),
      by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact hadd⟩)
    have h10 : q ≠ 10 := by revert hq; revert q; decide
    simp only [State.setPc_reg, State.reg_setReg_other _ _ _ _ h10, State.reg_setReg_other _ _ _ _ h9q]

/-- A store into `.sbss` keeps `IlCommon`: the frame excludes `.sbss`, the slots are off it. -/
theorem IlCommon_storeG (s : State) (hG : ilG.Disjoint (ilS s)) (u : State) (hC : IlCommon s u) (p : Word) (v n : Nat)
    (hc : ilG.covers p n) (w : State) (h1 : w.exit = none) (h2 : w.reg 2 = u.reg 2) (h8 : w.reg 8 = u.reg 8)
    (hr : ∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 8 → q ≠ 9 → q ≠ 18 → w.reg q = u.reg q)
    (hm : w.mem = writeLE u.mem p v n) (ht : w.trace = u.trace) : IlCommon s w := by
  obtain ⟨-, c2, c8, cpr, s1, s2, s3, s4, cf, ct⟩ := hC
  have hsl : ∀ o, o = 8 ∨ o = 16 ∨ o = 24 ∨ o = 32 → read64 w.mem (s.reg 2 - BitVec.ofNat 64 o) = read64 u.mem (s.reg 2 - BitVec.ofNat 64 o) := by
    intro o ho; rw [hm]; apply read64_congr_on; intro j hj
    exact writeLE_of_not_mem hc (not_mem_of_mem_disj hG (by simp only [ilS, Region.mem]; rcases ho with rfl | rfl | rfl | rfl <;> bv_omega))
  refine ⟨h1, by rw [h2]; exact c2, by rw [h8]; exact c8, fun q hq a b c d => by rw [hr q hq a b c d]; exact cpr q hq a b c d,
    by rw [hsl 8 (by simp)]; exact s1, by rw [hsl 16 (by simp)]; exact s2, by rw [hsl 24 (by simp)]; exact s3,
    by rw [hsl 32 (by simp)]; exact s4, ?_, by rw [ht]; exact ct⟩
  intro q a b c d; rw [hm, writeLE_of_not_mem hc b]; exact cf q a b c d

/-- `__environ = envp` (0x11320..0x11328), then the envp loop to its end (0x11338). -/
theorem il_env (s : State) (k : Kern) (e : Word) (n : Nat) (hE : EnvAt s k e n) (hG : ilG.Disjoint (ilS s))
    (hwG : ∀ p n, ilG.covers p n → k.perm.canWrite p n) (R : State × Kern → Prop) (u : State)
    (hpc : u.pc = 0x11320#64) (hC : IlCommon s u) (h9 : u.reg 9 = e)
    (K : ∀ v, v.pc = 0x11338#64 → IlEnv s e (n + 1) v → PReachK code initLibcD R (v, k)) :
    PReachK code initLibcD R (u, k) := by
  have hx := hC.1
  nocompiler_run_n 3 [hx, hpc, h9, show aligned (0x13fd0#64 : Word) 8 by decide] using [hwG]
  refine PReachK.bind (fun _ h => h) ?_ (il_env_loop s k e n hE (_, k) ⟨0, by omega, rfl, by simp only [nocompiler_state], ?_, ?_⟩)
  · rintro ⟨y, ky⟩ ⟨hk, hpy, hy⟩
    simp only at hk hpy hy
    subst hk
    exact K y hpy hy
  · refine IlCommon_storeG s hG u hC 0x13fd0#64 e.toNat 8 (by simp only [ilG, Region.covers]; decide) _ (by simp only [nocompiler_state]; exact hx)
      (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
      (fun q hq a2 a8 a9 a18 => ?_) (by simp only [nocompiler_state]) (by simp only [nocompiler_state])
    have h10 : q ≠ 10 := by revert hq; revert q; decide
    simp only [State.setPc_reg, State.setMem_reg, State.reg_setReg_other _ _ _ _ h10]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h9]; simp

end Examples.Libc.Slen

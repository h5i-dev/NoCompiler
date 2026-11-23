import Examples.Libc.InitTlsEntry
import NoCompiler.Linux.RunN
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage

/-- Memory after the TLS layout stores (0x118d4..0x11908): main_tls.size = 0, .offset = 0, .align = 8,
    libc.tls_align = 8, libc.tls_size = 224. -/
def tl3M (m : Word → Byte) : Word → Byte :=
  writeLE (writeLE (writeLE (writeLE (writeLE m 0x14030#64 0 8) 0x14040#64 0 8) 0x14038#64 8 8) 0x141b8#64 8 8)
    0x141b0#64 224 8

/-- At 0x11938, the built-in TLS area chosen: a1 = libc.tls_size = 224, a2 = libc.tls_align = 8. -/
def TlLay (s : State) (m : Word → Byte) (u : State) : Prop :=
  u.exit = none ∧ u.reg 11 = 224#64 ∧ u.reg 12 = 8#64 ∧ u.reg 9 = 0x14198#64 ∧ u.reg 2 = s.reg 2 - 64#64 ∧
  u.mem = tl3M m ∧ u.trace = s.trace ∧ (∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 8 → q ≠ 9 → u.reg q = s.reg q)

theorem tl_layout (s : State) (k : Kern) (m : Word → Byte) (R : State × Kern → Prop) (u : State)
    (hpc : u.pc = 0x11880#64) (hO : TlOut s m u)
    (h20 : read64 m 0x14020#64 = 0) (h30 : read64 m 0x14030#64 = 0) (h38 : read64 m 0x14038#64 = 0)
    (hw : ∀ a, a = 0x14030#64 ∨ a = 0x14040#64 ∨ a = 0x14038#64 ∨ a = 0x141b8#64 ∨ a = 0x141b0#64 →
      k.perm.canWrite a 8)
    (hr : ∀ a, a = 0x14020#64 ∨ a = 0x14030#64 ∨ a = 0x14038#64 → k.perm.canRead a 8)
    (K : ∀ v : State, v.pc = 0x11938#64 → TlLay s m v → PReachK code initTlsD R (v, k)) :
    PReachK code initTlsD R (u, k) := by
  obtain ⟨hx, h17, h11, h9, h2, hm, htr, hpr⟩ := hO
  nocompiler_run_n 4 [hx, hpc, h17, h11, hm, h38, show aligned (0x14038#64 : Word) 8 by decide, h30, show aligned (0x14030#64 : Word) 8 by decide, h20, show aligned (0x14020#64 : Word) 8 by decide] using [hr, hw]
  iterate 5 nocompiler_wstep [hx]
  nocompiler_run_n 8 [hx, h11, show aligned (0x14030#64 : Word) 8 by decide, show aligned (0x14040#64 : Word) 8 by decide, show aligned (0x14038#64 : Word) 8 by decide, h9, show aligned (0x141b8#64 : Word) 8 by decide] using [hr, hw]
  iterate 5 nocompiler_wstep [hx]
  nocompiler_run_n 2 [hx, h9, show aligned (0x141b0#64 : Word) 8 by decide] using [hr, hw]
  refine K _ (by simp only [nocompiler_state]) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp (disch := nocompiler_decide_closed) only [nocompiler_state, hx, h9, h2, htr]; done)
    | (simp only [nocompiler_state, hm, tl3M]; done)
    | (intro q hq a2 a8 a9
       have hne : q ≠ 10 ∧ q ≠ 11 ∧ q ≠ 12 ∧ q ≠ 13 ∧ q ≠ 14 ∧ q ≠ 15 := by revert hq; revert q; decide
       obtain ⟨n10, n11, n12, n13, n14, n15⟩ := hne
       simp only [State.setPc_reg, State.setMem_reg, State.reg_setReg_other _ _ _ _ n10, State.reg_setReg_other _ _ _ _ n11,
         State.reg_setReg_other _ _ _ _ n12, State.reg_setReg_other _ _ _ _ n13, State.reg_setReg_other _ _ _ _ n14,
         State.reg_setReg_other _ _ _ _ n15]
       exact hpr q hq a2 a8 a9)

theorem rd_wr {m : Word → Byte} {a b : Word} {v n : Nat} (h : (Region.mk b n).Disjoint ⟨a, 8⟩) :
    read64 (writeLE m b v n) a = read64 m a := by
  apply read64_congr_on; intro j hj
  exact writeLE_of_not_mem (r := ⟨b, n⟩) (by simp [Region.covers])
    (not_mem_of_mem_disj h (by simp only [Region.mem]; bv_omega))

theorem tl3M_read (m : Word → Byte) (a : Word) (h1 : (Region.mk 0x14030#64 8).Disjoint ⟨a, 8⟩)
    (h2 : (Region.mk 0x14040#64 8).Disjoint ⟨a, 8⟩) (h3 : (Region.mk 0x14038#64 8).Disjoint ⟨a, 8⟩)
    (h4 : (Region.mk 0x141b8#64 8).Disjoint ⟨a, 8⟩) (h5 : (Region.mk 0x141b0#64 8).Disjoint ⟨a, 8⟩) :
    read64 (tl3M m) a = read64 m a := by
  unfold tl3M; rw [rd_wr h5, rd_wr h4, rd_wr h3, rd_wr h2, rd_wr h1]

/-- Memory when `__set_thread_area` is called: dtv[0] = 0 (0x14120), td->dtv (0x14108), td->self (0x14048). -/
def tl4M (m : Word → Byte) : Word → Byte :=
  writeLE (writeLE (writeLE (tl3M m) 0x14120#64 0 8) 0x14108#64 0x14120 8) 0x14048#64 0x14048 8

/-- At 0x119d0, back from `__set_thread_area`: tp = 0x14110 (td + 200), a0 = 0, s0 = tp, s1 = &libc, s2 = td. -/
def TlTp (s : State) (m : Word → Byte) (u : State) : Prop :=
  u.exit = none ∧ u.reg 4 = 0x14110#64 ∧ u.reg 10 = 0 ∧ u.reg 8 = 0x14110#64 ∧ u.reg 9 = 0x14198#64 ∧
  u.reg 18 = 0x14048#64 ∧ u.reg 2 = s.reg 2 - 64#64 ∧ u.mem = tl4M m ∧ u.trace = s.trace ∧
  (∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 4 → q ≠ 8 → q ≠ 9 → q ≠ 18 → q ≠ 19 → q ≠ 20 → u.reg q = s.reg q)

theorem tl_tp (s : State) (k : Kern) (m : Word → Byte) (R : State × Kern → Prop) (u : State)
    (hpc : u.pc = 0x11938#64) (hL : TlLay s m u)
    (hc0 : read64 m 0x141c0#64 = 0) (ha8 : read64 m 0x141a8#64 = 0)
    (hw : ∀ a, a = 0x14120#64 ∨ a = 0x14108#64 ∨ a = 0x14048#64 → k.perm.canWrite a 8)
    (hr : ∀ a, a = 0x141c0#64 ∨ a = 0x141a8#64 → k.perm.canRead a 8)
    (K : ∀ v : State, v.pc = 0x119d0#64 → TlTp s m v → PReachK code initTlsD R (v, k)) :
    PReachK code initTlsD R (u, k) := by
  obtain ⟨hx, h11, h12, h9, h2, hm, htr, hpr⟩ := hL
  have r1 : read64 (tl3M m) 0x141c0#64 = 0 := by rw [tl3M_read m _ (by unfold Region.Disjoint; decide) (by unfold Region.Disjoint; decide) (by unfold Region.Disjoint; decide) (by unfold Region.Disjoint; decide) (by unfold Region.Disjoint; decide)]; exact hc0
  have r2 : read64 (tl3M m) 0x141a8#64 = 0 := by rw [tl3M_read m _ (by unfold Region.Disjoint; decide) (by unfold Region.Disjoint; decide) (by unfold Region.Disjoint; decide) (by unfold Region.Disjoint; decide) (by unfold Region.Disjoint; decide)]; exact ha8
  nocompiler_run_n 3 [hx, hpc, h9, hm, r1, show aligned (0x141c0#64 : Word) 8 by decide] using [hr, hw]
  iterate 5 nocompiler_wstep [hx, h11]
  nocompiler_run_n 1 [hx, h9, hm, r2, show aligned (0x141a8#64 : Word) 8 by decide] using [hr, hw]
  iterate 5 nocompiler_wstep [hx, h12]
  nocompiler_run_n 3 [hx, show aligned (0x14120#64 : Word) 8 by decide, show aligned (0x14108#64 : Word) 8 by decide, show aligned (0x14048#64 : Word) 8 by decide] using [hr, hw]
  iterate 3 nocompiler_wstep [hx]
  refine __set_thread_area_verified initTlsD (Dom.sub_of_ranges (by decide)) R _ k (by simp only [nocompiler_state])
    (by simp only [nocompiler_state]; exact hx) (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
    (fun y hpcy hxy h4y h10y hsy hmy htry => ?_)
  have hsr : ∀ q : Reg, q.val ≠ 4 → q.val ≠ 10 → y.reg q = _ := fun q a b => hsy q (by simp [a, b])
  refine K y (by rw [hpcy]; simp (disch := nocompiler_decide_closed) only [nocompiler_state]) ⟨hxy, ?_, h10y, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4y]; simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · rw [hsr 8 (by decide) (by decide)]; simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · rw [hsr 9 (by decide) (by decide)]; simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h9
  · rw [hsr 18 (by decide) (by decide)]; simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · rw [hsr 2 (by decide) (by decide)]; simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h2
  · rw [hmy]; simp only [nocompiler_state, hm, tl4M]
  · rw [htry]; simp only [nocompiler_state]; exact htr
  · intro q hq
    have hne : q ≠ 1 ∧ q ≠ 10 ∧ q ≠ 12 ∧ q ≠ 13 ∧ q ≠ 14 ∧ q ≠ 15 := by revert hq; revert q; decide
    intro a2 a4 a8 a9 a18 a19 a20
    obtain ⟨n1, n10, n12, n13, n14, n15⟩ := hne
    rw [hsr q (fun h => a4 (Fin.ext h)) (fun h => n10 (Fin.ext h))]
    simp only [State.setPc_reg, State.setMem_reg, State.reg_setReg_other _ _ _ _ n1, State.reg_setReg_other _ _ _ _ n10,
      State.reg_setReg_other _ _ _ _ n12, State.reg_setReg_other _ _ _ _ n13, State.reg_setReg_other _ _ _ _ n14,
      State.reg_setReg_other _ _ _ _ n15, State.reg_setReg_other _ _ _ _ a8, State.reg_setReg_other _ _ _ _ a18,
      State.reg_setReg_other _ _ _ _ a19, State.reg_setReg_other _ _ _ _ a20]
    exact hpr q hq a2 a8 a9

end Examples.Libc.Slen

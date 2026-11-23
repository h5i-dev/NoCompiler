import Examples.Libc.InitLibcMisc
import NoCompiler.Linux.RunN
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage

theorem read8_eq (m : Word → Byte) (a : Word) : read8 m a = BitVec.ofNat 64 (m a).toNat := by
  simp [read8, readLE]

theorem byte_beq (c : Byte) (n : Nat) (hn : n < 256) : (BitVec.ofNat 64 c.toNat == BitVec.ofNat 64 n) = decide (c.toNat = n) := by
  have := c.isLt
  by_cases h : c.toNat = n
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro he; apply h; have := congrArg BitVec.toNat he; simp only [BitVec.toNat_ofNat] at this; omega

theorem str_byte (s : State) (k : Kern) (P : Word) (S : List Byte) (hS : StrAt s k P S) (m : Word → Byte)
    (hm : IlFrame s m) (i : Nat) (hi : i ≤ S.length) : m (P + BitVec.ofNat 64 i) = (S ++ [0]).getD i 0 := by
  have hin : (Region.mk P (S.length + 1)).mem (P + BitVec.ofNat 64 i) := by
    have := hS.fit; simp only [Region.mem]; bv_omega
  rw [hm _ (not_mem_of_mem_disj hS.dS.symm hin) (not_mem_of_mem_disj hS.dG.symm hin) (not_mem_of_mem_disj hS.dL.symm hin)
    (not_mem_of_mem_disj hS.dP.symm hin)]
  exact Auto.mem_of_readBytes hS.bytes i (by omega)

/-- The program name loop (0x113f8) from byte `i` to its end (0x11404). -/
theorem il_pn (s : State) (k : Kern) (P : Word) (S : List Byte) (hS : StrAt s k P S)
    (hwG : ∀ p n, ilG.covers p n → k.perm.canWrite p n) (hGd : ilG.Disjoint (ilS s)) (hlo : 448 ≤ (s.reg 2).toNat)
    (M0 : Word → Byte) :
    ∀ x : State × Kern, (∃ i, i ≤ S.length ∧ x.2 = k ∧ x.1.pc = 0x113f8#64 ∧ IlPn s P i x.1 ∧ AuxKeep s M0 x.1.mem) →
      PReachK code initLibcD (fun y => y.2 = k ∧ y.1.pc = 0x11404#64 ∧ IlCommon (s.setReg 11 P) y.1 ∧
        y.1.reg 18 = 0x14198#64 ∧ AuxKeep s M0 y.1.mem) x := by
  have hfit := hS.fit
  have hGd' : ilG.Disjoint (ilS (s.setReg 11 P)) := by
    simpa only [ilS, State.reg_setReg_other _ _ _ _ (show (2 : Reg) ≠ 11 by decide)] using hGd
  refine PReachK.loop _ (fun x => S.length + 1 - ((x.1.reg 11 - P).toNat - 1)) ?_
  rintro ⟨u, ku⟩ ⟨i, hi, hku, hpc, ⟨hC, h11, h12, h10, h18⟩, hAK⟩
  simp only at hku hpc hC h11 h12 h10 h18 hAK
  subst hku
  have hx := hC.1
  have hfr : IlFrame s u.mem := by
    have := hC.2.2.2.2.2.2.2.2.1
    intro p a b c d
    have e : ilS (s.setReg 11 P) = ilS s := by simp only [ilS, State.reg_setReg_other _ _ _ _ (show (2 : Reg) ≠ 11 by decide)]
    rw [← e] at a; have := this p a b c d; simpa only [nocompiler_state] using this
  have hby := str_byte s _ P S hS u.mem hfr i hi
  have ea : P + BitVec.ofNat 64 (i + 1) + 18446744073709551615#64 = P + BitVec.ofNat 64 i := by bv_omega
  have hr8 := read8_eq u.mem (P + BitVec.ofNat 64 i)
  rw [hby] at hr8
  have hc0 : i < S.length → (S ++ [0]).getD i 0 ≠ 0 := by
    intro hlt h
    have : (S ++ [0]).getD i 0 = S[i] := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, List.getElem?_eq_getElem hlt, Option.getD_some]
    rw [this] at h; exact hS.nz (h ▸ List.getElem_mem hlt)
  have hcl : i = S.length → (S ++ [0]).getD i 0 = 0 := by intro h; subst h; simp
  generalize (S ++ [0]).getD i 0 = c at hr8 hc0 hcl
  nocompiler_run_n 1 [hx, hpc, h11, ea, hr8, Auto.aligned_one] using [hS.rd, hwG]
  have hmeas : ∀ j, j ≤ S.length → (P + BitVec.ofNat 64 (j + 1) - P).toNat - 1 = j := by
    intro j hj; rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  have hadd : P + BitVec.ofNat 64 (i + 1) + 1#64 = P + BitVec.ofNat 64 (i + 1 + 1) := by
    rw [BitVec.add_assoc, show (1#64 : Word) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  have hpn : ∀ v : State, v.exit = none → v.reg 2 = u.reg 2 → v.reg 8 = u.reg 8 → v.mem = u.mem → v.trace = u.trace →
      (∀ q ∈ preservedRegs, v.reg q = u.reg q) → v.reg 11 = P + BitVec.ofNat 64 (i + 1 + 1) → v.reg 12 = 47#64 →
      v.reg 10 = 0x13fe8#64 → v.reg 18 = 0x14198#64 → IlPn s P (i + 1) v := fun v a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 =>
    ⟨IlCommon_congr _ _ _ hC a1 a2 a3 (fun q hq _ _ _ _ => a6 q hq) a4 a5, a7, a8, a9, a10⟩
  rcases Nat.lt_or_ge i S.length with hlt | hge
  · have hc0 := hc0 hlt
    by_cases hsl : c.toNat = 47
    · have hb : (BitVec.ofNat 64 c.toNat == 47#64) = true := by
        rw [show (47#64 : Word) = BitVec.ofNat 64 47 from rfl, byte_beq _ _ (by omega)]; exact decide_eq_true hsl
      nocompiler_run_n 3 [hx, h12, hb, h10, h11, show aligned (0x13fe8#64 : Word) 8 by decide] using [hS.rd, hwG]
      refine .done (.inr ⟨⟨i + 1, hlt, rfl, by simp only [nocompiler_state], ?_, by
          simp only [nocompiler_state]
          exact auxkeep_write s hlo M0 _ ilG hGd _ _ _ (by simp only [ilG, Region.covers]; decide) hAK⟩, ?_⟩)
      · refine ⟨IlCommon_storeG _ hGd' u hC 0x13fe8#64 (P + BitVec.ofNat 64 (i + 1)).toNat 8
          (by simp only [ilG, Region.covers]; decide) _ (by simp only [nocompiler_state]; exact hx)
          (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
          (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) (fun q hq _ _ _ _ => ?_)
          (by simp only [nocompiler_state, h11]) (by simp only [nocompiler_state]), ?_, ?_, ?_, ?_⟩
        · have hne : q ≠ 11 ∧ q ≠ 13 := by revert hq; revert q; decide
          simp only [State.setPc_reg, State.setMem_reg, State.reg_setReg_other _ _ _ _ hne.1, State.reg_setReg_other _ _ _ _ hne.2]
        · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h11]; exact hadd
        · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12
        · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h10
        · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h18
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h11]
        rw [hadd, hmeas (i + 1) (by omega), hmeas i (by omega)]; omega
    · have hb : (BitVec.ofNat 64 c.toNat == 47#64) = false := by
        rw [show (47#64 : Word) = BitVec.ofNat 64 47 from rfl, byte_beq _ _ (by omega)]; exact decide_eq_false hsl
      have hb2 : (BitVec.ofNat 64 c.toNat != (0 : Word)) = true := by
        have hne : BitVec.ofNat 64 c.toNat ≠ (0 : Word) := by
          intro h; apply hc0; bv_omega
        simpa using hne
      nocompiler_run_n 3 [hx, h12, hb, hb2] using [hS.rd, hwG]
      refine .done (.inr ⟨⟨i + 1, hlt, rfl, by simp only [nocompiler_state], hpn _ (by simp only [nocompiler_state]; exact hx)
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
        (by simp only [nocompiler_state]) (by simp only [nocompiler_state]) (fun q hq => ?_)
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state, h11]; exact hadd)
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12)
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h10)
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h18), by simp only [nocompiler_state]; exact hAK⟩, ?_⟩)
      · have hne : q ≠ 11 ∧ q ≠ 13 := by revert hq; revert q; decide
        simp only [State.setPc_reg, State.reg_setReg_other _ _ _ _ hne.1, State.reg_setReg_other _ _ _ _ hne.2]
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h11]
        rw [hadd, hmeas (i + 1) (by omega), hmeas i (by omega)]; omega
  · have hie : i = S.length := by omega
    have hc := hcl hie
    subst hc
    have hb : ((0#64 : Word) == 47#64) = false := by decide
    have hb2 : ((0#64 : Word) != 0#64) = false := by decide
    nocompiler_run_n 2 [hx, h12, hb, hb2] using [hS.rd, hwG]
    refine .done (.inl ⟨rfl, by simp only [nocompiler_state], IlCommon_congr _ _ _ hC (by simp only [nocompiler_state]; exact hx)
      (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
      (fun q hq _ _ _ _ => ?_) (by simp only [nocompiler_state]) (by simp only [nocompiler_state]),
      by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h18, by simp only [nocompiler_state]; exact hAK⟩)
    have h13 : q ≠ 13 := by revert hq; revert q; decide
    simp only [State.setPc_reg, State.reg_setReg_other _ _ _ _ h13]

end Examples.Libc.Slen

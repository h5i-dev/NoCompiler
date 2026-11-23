import Examples.Libc.Musl.Memcpy3

set_option maxRecDepth 20000
namespace NoCompiler.Libc.Musl.Memcpy
open NoCompiler NoCompiler.Linux NoCompiler.Libc.Musl.MemcpyImg
/-- The entry of the shifted loop for a destination 1 past word alignment (0x12654): 3 byte(s) from the first
    source word, the rest of it carried into the loop. -/

theorem mc_e1 (d src n : Word) (s : State) (k : Kern) (he : Entry dom 0x125dc#64 s)
    (hpre : memcpySpec.pre (d, src, n) s k) (c r : Nat) (hcn : c + r = n.toNat) (hr : 32 ≤ r)
    (had : aligned (d + BitVec.ofNat 64 (c + 3)) 4) (has : aligned (src + BitVec.ofNat 64 c) 4)
    (u : State) (hpc : u.pc = 0x12654#64) (hu : McAt s d src c u) (h12 : u.reg 12 = BitVec.ofNat 64 r) :
    PReachK img dom (McQ d src n s k) (u, k) := by
  have hpre' := hpre
  obtain ⟨-, -, -, hrd, hw, hd⟩ := hpre'
  obtain ⟨hk, h13, h14, hc⟩ := hu
  have hx := hk.1
  have hn := n.isLt
  have hm : ∀ i, decide (i ≤ 3) = true → u.mem (src + BitVec.ofNat 64 (c + i)) = s.mem (src + BitVec.ofNat 64 (c + i)) := by
    intro i h; simp only [decide_eq_true_eq] at h; exact hc.src hd (by omega) (c + i) (by omega)
  have hm0 : u.mem (src + BitVec.ofNat 64 c) = s.mem (src + BitVec.ofNat 64 c) := hc.src hd (by omega) c (by omega)
  have wr : ∀ j, j < 4 → k.perm.canWrite (d + BitVec.ofNat 64 (c + j)) 1 := fun j hj => perm_write_sub hw (c + j) 1 (by omega) (by omega)
  have wr0 : k.perm.canWrite (d + BitVec.ofNat 64 c) 1 := perm_write_sub hw c 1 (by omega) (by omega)
  have hrt : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub : BitVec.ofNat 64 r + 18446744073709551613#64 = BitVec.ofNat 64 (r - 3) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, hrt, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  obtain ⟨wb0, wb1, wb2, wb3⟩ := word_bytes (s.mem (src + BitVec.ofNat 64 c)) (s.mem (src + BitVec.ofNat 64 (c + 1))) (s.mem (src + BitVec.ofNat 64 (c + 2))) (s.mem (src + BitVec.ofNat 64 (c + 3)))
  have hne : ∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] → q ≠ 11 ∧ q ≠ 12 ∧ q ≠ 13 ∧ q ≠ 14 ∧ q ≠ 15 :=
    fun q hq => ⟨fun e => hq (by subst e; simp), fun e => hq (by subst e; simp), fun e => hq (by subst e; simp),
      fun e => hq (by subst e; simp), fun e => hq (by subst e; simp)⟩
  nocompiler_run_n 10 [hx, hpc, h14, BitVec.add_zero, has, ofNat32_se, add_ofNat_assoc, Nat.add_assoc, Nat.reduceAdd, hm, hm0, h13, Auto.aligned_one, h12, hsub] using [perm_read_sub, wr0, wr]
  refine mc_sloop1 d src n s k he hpre _ ⟨c + 3, r - 3, (s.mem (src + BitVec.ofNat 64 c)), (s.mem (src + BitVec.ofNat 64 (c + 1))), (s.mem (src + BitVec.ofNat 64 (c + 2))), rfl, by simp only [nocompiler_state], ?_, ?_, ?_, ?_, ?_,
    by omega, by omega, had, by unfold aligned at *; bv_omega, ?_, ?_⟩
  · refine hk.step (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state])
    obtain ⟨a11, a12, a13, a14, a15⟩ := hne q hq
    repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ a11] | rw [State.reg_setReg_other _ _ _ _ a12] | rw [State.reg_setReg_other _ _ _ _ a13] | rw [State.reg_setReg_other _ _ _ _ a14] | rw [State.reg_setReg_other _ _ _ _ a15])
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp only [nocompiler_state]; exact (((hc.byte (by omega) _ wb0).byte (by omega) _ wb1).byte (by omega) _ wb2)
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]

/-- The entry of the shifted loop for a destination 2 past word alignment (0x12878): 2 byte(s) from the first
    source word, the rest of it carried into the loop. -/
theorem mc_e2 (d src n : Word) (s : State) (k : Kern) (he : Entry dom 0x125dc#64 s)
    (hpre : memcpySpec.pre (d, src, n) s k) (c r : Nat) (hcn : c + r = n.toNat) (hr : 32 ≤ r)
    (had : aligned (d + BitVec.ofNat 64 (c + 2)) 4) (has : aligned (src + BitVec.ofNat 64 c) 4)
    (u : State) (hpc : u.pc = 0x12878#64) (hu : McAt s d src c u) (h12 : u.reg 12 = BitVec.ofNat 64 r) :
    PReachK img dom (McQ d src n s k) (u, k) := by
  have hpre' := hpre
  obtain ⟨-, -, -, hrd, hw, hd⟩ := hpre'
  obtain ⟨hk, h13, h14, hc⟩ := hu
  have hx := hk.1
  have hn := n.isLt
  have hm : ∀ i, decide (i ≤ 3) = true → u.mem (src + BitVec.ofNat 64 (c + i)) = s.mem (src + BitVec.ofNat 64 (c + i)) := by
    intro i h; simp only [decide_eq_true_eq] at h; exact hc.src hd (by omega) (c + i) (by omega)
  have hm0 : u.mem (src + BitVec.ofNat 64 c) = s.mem (src + BitVec.ofNat 64 c) := hc.src hd (by omega) c (by omega)
  have wr : ∀ j, j < 4 → k.perm.canWrite (d + BitVec.ofNat 64 (c + j)) 1 := fun j hj => perm_write_sub hw (c + j) 1 (by omega) (by omega)
  have wr0 : k.perm.canWrite (d + BitVec.ofNat 64 c) 1 := perm_write_sub hw c 1 (by omega) (by omega)
  have hrt : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub : BitVec.ofNat 64 r + 18446744073709551614#64 = BitVec.ofNat 64 (r - 2) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, hrt, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  obtain ⟨wb0, wb1, wb2, wb3⟩ := word_bytes (s.mem (src + BitVec.ofNat 64 c)) (s.mem (src + BitVec.ofNat 64 (c + 1))) (s.mem (src + BitVec.ofNat 64 (c + 2))) (s.mem (src + BitVec.ofNat 64 (c + 3)))
  have hne : ∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] → q ≠ 11 ∧ q ≠ 12 ∧ q ≠ 13 ∧ q ≠ 14 ∧ q ≠ 15 :=
    fun q hq => ⟨fun e => hq (by subst e; simp), fun e => hq (by subst e; simp), fun e => hq (by subst e; simp),
      fun e => hq (by subst e; simp), fun e => hq (by subst e; simp)⟩
  nocompiler_run_n 8 [hx, hpc, h14, BitVec.add_zero, has, ofNat32_se, add_ofNat_assoc, Nat.add_assoc, Nat.reduceAdd, hm, hm0, h13, Auto.aligned_one, h12, hsub] using [perm_read_sub, wr0, wr]
  refine mc_sloop2 d src n s k he hpre _ ⟨c + 2, r - 2, (s.mem (src + BitVec.ofNat 64 c)), (s.mem (src + BitVec.ofNat 64 (c + 1))), rfl, by simp only [nocompiler_state], ?_, ?_, ?_, ?_, ?_,
    by omega, by omega, had, by unfold aligned at *; bv_omega, ?_, ?_⟩
  · refine hk.step (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state])
    obtain ⟨a11, a12, a13, a14, a15⟩ := hne q hq
    repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ a11] | rw [State.reg_setReg_other _ _ _ _ a12] | rw [State.reg_setReg_other _ _ _ _ a13] | rw [State.reg_setReg_other _ _ _ _ a14] | rw [State.reg_setReg_other _ _ _ _ a15])
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp only [nocompiler_state]; exact ((hc.byte (by omega) _ wb0).byte (by omega) _ wb1)
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]

/-- The entry of the shifted loop for a destination 3 past word alignment (0x12774): 1 byte(s) from the first
    source word, the rest of it carried into the loop. -/
theorem mc_e3 (d src n : Word) (s : State) (k : Kern) (he : Entry dom 0x125dc#64 s)
    (hpre : memcpySpec.pre (d, src, n) s k) (c r : Nat) (hcn : c + r = n.toNat) (hr : 32 ≤ r)
    (had : aligned (d + BitVec.ofNat 64 (c + 1)) 4) (has : aligned (src + BitVec.ofNat 64 c) 4)
    (u : State) (hpc : u.pc = 0x12774#64) (hu : McAt s d src c u) (h12 : u.reg 12 = BitVec.ofNat 64 r) :
    PReachK img dom (McQ d src n s k) (u, k) := by
  have hpre' := hpre
  obtain ⟨-, -, -, hrd, hw, hd⟩ := hpre'
  obtain ⟨hk, h13, h14, hc⟩ := hu
  have hx := hk.1
  have hn := n.isLt
  have hm : ∀ i, decide (i ≤ 3) = true → u.mem (src + BitVec.ofNat 64 (c + i)) = s.mem (src + BitVec.ofNat 64 (c + i)) := by
    intro i h; simp only [decide_eq_true_eq] at h; exact hc.src hd (by omega) (c + i) (by omega)
  have hm0 : u.mem (src + BitVec.ofNat 64 c) = s.mem (src + BitVec.ofNat 64 c) := hc.src hd (by omega) c (by omega)
  have wr : ∀ j, j < 4 → k.perm.canWrite (d + BitVec.ofNat 64 (c + j)) 1 := fun j hj => perm_write_sub hw (c + j) 1 (by omega) (by omega)
  have wr0 : k.perm.canWrite (d + BitVec.ofNat 64 c) 1 := perm_write_sub hw c 1 (by omega) (by omega)
  have hrt : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub : BitVec.ofNat 64 r + 18446744073709551615#64 = BitVec.ofNat 64 (r - 1) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, hrt, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  obtain ⟨wb0, wb1, wb2, wb3⟩ := word_bytes (s.mem (src + BitVec.ofNat 64 c)) (s.mem (src + BitVec.ofNat 64 (c + 1))) (s.mem (src + BitVec.ofNat 64 (c + 2))) (s.mem (src + BitVec.ofNat 64 (c + 3)))
  have hne : ∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] → q ≠ 11 ∧ q ≠ 12 ∧ q ≠ 13 ∧ q ≠ 14 ∧ q ≠ 15 :=
    fun q hq => ⟨fun e => hq (by subst e; simp), fun e => hq (by subst e; simp), fun e => hq (by subst e; simp),
      fun e => hq (by subst e; simp), fun e => hq (by subst e; simp)⟩
  nocompiler_run_n 6 [hx, hpc, h14, BitVec.add_zero, has, ofNat32_se, add_ofNat_assoc, Nat.add_assoc, Nat.reduceAdd, hm, hm0, h13, Auto.aligned_one, h12, hsub] using [perm_read_sub, wr0]
  refine mc_sloop3 d src n s k he hpre _ ⟨c + 1, r - 1, (s.mem (src + BitVec.ofNat 64 c)), rfl, by simp only [nocompiler_state], ?_, ?_, ?_, ?_, ?_,
    by omega, by omega, had, by unfold aligned at *; bv_omega, ?_, ?_⟩
  · refine hk.step (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state])
    obtain ⟨a11, a12, a13, a14, a15⟩ := hne q hq
    repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ a11] | rw [State.reg_setReg_other _ _ _ _ a12] | rw [State.reg_setReg_other _ _ _ _ a13] | rw [State.reg_setReg_other _ _ _ _ a14] | rw [State.reg_setReg_other _ _ _ _ a15])
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp only [nocompiler_state]; exact (hc.byte (by omega) _ wb0)
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]

/-- The dispatch of a misaligned destination (0x12634, source aligned): bytes if fewer than 32, else the
    shifted loop for the destination's offset. -/
theorem mc_disp (d src n : Word) (s : State) (k : Kern) (he : Entry dom 0x125dc#64 s)
    (hpre : memcpySpec.pre (d, src, n) s k) (c r : Nat) (hcn : c + r = n.toNat)
    (has' : 0 < r → aligned (src + BitVec.ofNat 64 c) 4) (hnz : (d + BitVec.ofNat 64 c).toNat % 4 ≠ 0)
    (u : State) (hpc : u.pc = 0x12634#64) (hu : McAt s d src c u) (h12 : u.reg 12 = BitVec.ofNat 64 r)
    (h11 : u.reg 11 = (d + BitVec.ofNat 64 c) &&& 3#64) :
    PReachK img dom (McQ d src n s k) (u, k) := by
  have hu' := hu
  obtain ⟨hk, h13, h14, hc⟩ := hu'
  have hx := hk.1
  have hn := n.isLt
  have hrt : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hat : ∀ v : State, v.exit = none → (∀ q : Reg, q ≠ 15 → v.reg q = u.reg q) → v.trace = u.trace → v.mem = u.mem →
      McAt s d src c v := fun v a b c' e =>
    McAt.mk hk v a (fun q hq => b q (fun h => hq (by subst h; simp))) c' (by rw [b 13 (by decide)]; exact h13)
      (by rw [b 14 (by decide)]; exact h14) (by rw [e]; exact hc)
  have hregs : ∀ (v : State) (a : Word) (q : Reg), q ≠ 15 → ((v.setReg 15 a).setPc 0).reg q = v.reg q := by
    intro v a q h; simp only [State.setPc_reg]; exact State.reg_setReg_other _ _ _ _ h
  have hmod : (d + BitVec.ofNat 64 c).toNat % 4 < 4 := Nat.mod_lt _ (by omega)
  nocompiler_run_n 1 [hx, hpc] using []
  by_cases hlt : r < 32
  · have hb : BitVec.ult (BitVec.ofNat 64 r) 32#64 = true := by simp only [BitVec.ult, hrt, decide_eq_true_eq]; exact hlt
    nocompiler_run_n 1 [hx, h12, hb] using []
    refine mc_t16 d src n s k he hpre c r (by omega) (by omega) _ ?_ ?_ ?_
    · simp only [nocompiler_state]
    · refine hat _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state]) (by simp only [nocompiler_state])
      simp only [State.setPc_reg]; exact State.reg_setReg_other _ _ _ _ hq
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12
  have hb : BitVec.ult (BitVec.ofNat 64 r) 32#64 = false := by simp only [BitVec.ult, hrt, decide_eq_false_iff_not]; exact hlt
  have has := has' (by omega)
  nocompiler_run_n 2 [hx, h12, hb] using []
  have b3 := and3_beq (d + BitVec.ofNat 64 c) 3 (by omega)
  have b2 := and3_beq (d + BitVec.ofNat 64 c) 2 (by omega)
  have b1 := and3_beq (d + BitVec.ofNat 64 c) 1 (by omega)
  by_cases h3 : (d + BitVec.ofNat 64 c).toNat % 4 = 3
  · nocompiler_wstep [hx, h11, b3, h3]
    refine mc_e3 d src n s k he hpre c r hcn (by omega) (al_of_mod d c 1 (by omega)) has _ ?_ ?_ ?_
    · simp only [nocompiler_state]
    · refine hat _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state]) (by simp only [nocompiler_state])
      repeat (first | rw [State.setPc_reg] | rw [State.reg_setReg_other _ _ _ _ hq])
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12
  nocompiler_run_n 2 [hx, h11, b3, h3] using []
  by_cases h2 : (d + BitVec.ofNat 64 c).toNat % 4 = 2
  · nocompiler_wstep [hx, h11, b2, h2]
    refine mc_e2 d src n s k he hpre c r hcn (by omega) (al_of_mod d c 2 (by omega)) has _ ?_ ?_ ?_
    · simp only [nocompiler_state]
    · refine hat _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state]) (by simp only [nocompiler_state])
      repeat (first | rw [State.setPc_reg] | rw [State.reg_setReg_other _ _ _ _ hq])
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12
  have h1 : (d + BitVec.ofNat 64 c).toNat % 4 = 1 := by omega
  have hb1 : (((d + BitVec.ofNat 64 c) &&& 3#64) != 1#64) = false := by simp only [bne, b1, h1, decide_true]; rfl
  nocompiler_run_n 3 [hx, h11, b2, h2, hb1] using []
  refine mc_e1 d src n s k he hpre c r hcn (by omega) (al_of_mod d c 3 (by omega)) has _ ?_ ?_ ?_
  · simp only [nocompiler_state]
  · refine hat _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state]) (by simp only [nocompiler_state])
    repeat (first | rw [State.setPc_reg] | rw [State.reg_setReg_other _ _ _ _ hq])
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12

/-- After the head (0x1262c, `c` bytes copied, the source aligned unless none are left): the aligned path or the
    dispatch on the destination's offset. -/
theorem mc_j (d src n : Word) (s : State) (k : Kern) (he : Entry dom 0x125dc#64 s)
    (hpre : memcpySpec.pre (d, src, n) s k) (c r : Nat) (hcn : c + r = n.toNat)
    (has' : 0 < r → aligned (src + BitVec.ofNat 64 c) 4)
    (u : State) (hpc : u.pc = 0x1262c#64 ∨ u.pc = 0x126f4#64) (hu : McAt s d src c u) (h12 : u.reg 12 = BitVec.ofNat 64 r) :
    PReachK img dom (McQ d src n s k) (u, k) := by
  have hu' := hu
  obtain ⟨hk, h13, h14, hc⟩ := hu'
  have hx := hk.1
  have hat : ∀ v : State, v.exit = none → (∀ q : Reg, q ≠ 11 → v.reg q = u.reg q) → v.trace = u.trace → v.mem = u.mem →
      McAt s d src c v := fun v a b c' e =>
    McAt.mk hk v a (fun q hq => b q (fun h => hq (by subst h; simp))) c' (by rw [b 13 (by decide)]; exact h13)
      (by rw [b 14 (by decide)]; exact h14) (by rw [e]; exact hc)
  have b0 := and3_eq0 (d + BitVec.ofNat 64 c)
  have bn0 : ((d + BitVec.ofNat 64 c) &&& 3#64 != 0) = !decide ((d + BitVec.ofNat 64 c).toNat % 4 = 0) := by
    simp only [bne, b0]
  rcases hpc with hpc | hpc
  all_goals (
    nocompiler_run_n 1 [hx, hpc, h13] using []
    by_cases ha : (d + BitVec.ofNat 64 c).toNat % 4 = 0
    · nocompiler_wstep [hx, b0, bn0, ha]
      refine mc_al d src n s k he hpre c r hcn (fun _ => by unfold aligned; exact ha) has' _ ?_ ?_ ?_
      · simp only [nocompiler_state]
      · refine hat _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state]) (by simp only [nocompiler_state])
        repeat (first | rw [State.setPc_reg] | rw [State.reg_setReg_other _ _ _ _ hq])
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12
    · have hb : ((d + BitVec.ofNat 64 c) &&& 3#64 == 0) = false := by rw [b0]; simpa using ha
      first
        | (nocompiler_wstep [hx, hb]
           refine mc_disp d src n s k he hpre c r hcn has' ha _ ?_ ?_ ?_ ?_
           · simp only [nocompiler_state]
           · refine hat _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state]) (by simp only [nocompiler_state])
             repeat (first | rw [State.setPc_reg] | rw [State.reg_setReg_other _ _ _ _ hq])
           · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12
           · simp (disch := nocompiler_decide_closed) only [nocompiler_state])
        | (have hb' : ((d + BitVec.ofNat 64 c) &&& 3#64 != 0) = true := by simpa using hb
           nocompiler_run_n 1 [hx, hb'] using []
           refine mc_disp d src n s k he hpre c r hcn has' ha _ ?_ ?_ ?_ ?_
           · simp only [nocompiler_state]
           · refine hat _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state]) (by simp only [nocompiler_state])
             repeat (first | rw [State.setPc_reg] | rw [State.reg_setReg_other _ _ _ _ hq])
           · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12
           · simp (disch := nocompiler_decide_closed) only [nocompiler_state]))

theorem Copied.zero (m0 : Word → Byte) (d src : Word) : Copied m0 d src 0 m0 := by
  intro p; simp

/-- The head loop (0x125f8): byte by byte until the source is word-aligned or nothing is left. -/
theorem mc_hloop (d src n : Word) (s : State) (k : Kern) (he : Entry dom 0x125dc#64 s)
    (hpre : memcpySpec.pre (d, src, n) s k) :
    ∀ x : State × Kern, (∃ c, x.2 = k ∧ x.1.pc = 0x125f8#64 ∧ McKeep s d x.1 ∧ x.1.reg 11 = src + BitVec.ofNat 64 c ∧
      x.1.reg 16 = d + BitVec.ofNat 64 c ∧ x.1.reg 15 = src + BitVec.ofNat 64 (c + 1) ∧
      x.1.reg 12 = BitVec.ofNat 64 (n.toNat - c) ∧ c < n.toNat ∧ Copied s.mem d src c x.1.mem) →
      PReachK img dom (McQ d src n s k) x := by
  refine PReachK.loop _ (fun x => (x.1.reg 12).toNat) ?_
  rintro ⟨u, ku⟩ ⟨c, hku, hpc, hk, h11, h16, h15, h12, hcn, hc⟩
  simp only at hku hpc hk h11 h16 h15 h12 hc
  rw [hku]
  have hpre' := hpre
  obtain ⟨-, -, -, hrd, hw, hd⟩ := hpre'
  have hx := hk.1
  have hn := n.isLt
  have hsv := hc.src hd (by omega) c hcn
  have hrt : (BitVec.ofNat 64 (n.toNat - c)).toNat = n.toNat - c := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hs1 : BitVec.ofNat 64 (n.toNat - c) + 18446744073709551615#64 = BitVec.ofNat 64 (n.toNat - (c + 1)) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, hrt, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hr1 : (BitVec.ofNat 64 (n.toNat - (c + 1))).toNat = n.toNat - (c + 1) := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne : ∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] →
      q ≠ 11 ∧ q ≠ 12 ∧ q ≠ 13 ∧ q ≠ 14 ∧ q ≠ 15 ∧ q ≠ 16 ∧ q ≠ 17 :=
    fun q hq => ⟨fun e => hq (by subst e; simp), fun e => hq (by subst e; simp), fun e => hq (by subst e; simp),
      fun e => hq (by subst e; simp), fun e => hq (by subst e; simp), fun e => hq (by subst e; simp), fun e => hq (by subst e; simp)⟩
  nocompiler_run_n 12 [hx, hpc, h11, BitVec.add_zero, Auto.aligned_one, readLE_one, add_ofNat_assoc, h16, h12, hs1, h15] using [perm_read_sub, perm_write_sub]
  have hcp := hc.byte (by omega) _ (byteval_eq' hsv)
  by_cases hcont : (src + BitVec.ofNat 64 (c + 1)).toNat % 4 ≠ 0 ∧ n.toNat - (c + 1) ≠ 0
  · have hb : (bool64 (BitVec.ult (0 : Word) ((src + BitVec.ofNat 64 (c + 1)) &&& 3#64)) &&&
        bool64 (BitVec.ult (0 : Word) (BitVec.ofNat 64 (n.toNat - (c + 1)))) != 0) = true := by
      rw [bool64_and_ne, ult_zero_and3, ult_zero', hr1, decide_eq_true hcont.1, decide_eq_true hcont.2]; rfl
    nocompiler_run_n 1 [hx, hb] using [perm_read_sub, perm_write_sub]
    refine .done (.inr ⟨⟨c + 1, rfl, by simp only [nocompiler_state], ?_, ?_, ?_, ?_, ?_, by omega, ?_⟩, ?_⟩)
    · refine hk.step (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state])
      obtain ⟨a11, a12, a13, a14, a15, a16, a17⟩ := hne q hq
      repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ a11] | rw [State.reg_setReg_other _ _ _ _ a12] | rw [State.reg_setReg_other _ _ _ _ a13] | rw [State.reg_setReg_other _ _ _ _ a14] | rw [State.reg_setReg_other _ _ _ _ a15] | rw [State.reg_setReg_other _ _ _ _ a16] | rw [State.reg_setReg_other _ _ _ _ a17])
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · simp only [nocompiler_state]; exact hcp
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; rw [hr1, hrt]; omega
  · have hb : (bool64 (BitVec.ult (0 : Word) ((src + BitVec.ofNat 64 (c + 1)) &&& 3#64)) &&&
        bool64 (BitVec.ult (0 : Word) (BitVec.ofNat 64 (n.toNat - (c + 1)))) != 0) = false := by
      rw [bool64_and_ne, ult_zero_and3, ult_zero', hr1]
      by_cases h1 : (src + BitVec.ofNat 64 (c + 1)).toNat % 4 = 0
      · rw [decide_eq_false (not_not_intro h1)]; rfl
      · have h2 : n.toNat - (c + 1) = 0 := by
          by_cases h2 : n.toNat - (c + 1) = 0
          · exact h2
          · exact absurd ⟨h1, h2⟩ hcont
        rw [decide_eq_false (not_not_intro h2), Bool.and_false]
    nocompiler_run_n 1 [hx, hb] using [perm_read_sub, perm_write_sub]
    refine PReachK.bind (Dom.sub_of_ranges (by decide)) (fun y hy => .done (.inl hy))
      (mc_j d src n s k he hpre (c + 1) (n.toNat - (c + 1)) (by omega) (fun h => ?_) _ (.inl (by simp only [nocompiler_state])) ?_ ?_)
    · unfold aligned; omega
    · refine McAt.mk hk _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state])
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) (by simp only [nocompiler_state]; exact hcp)
      obtain ⟨a11, a12, a13, a14, a15, a16, a17⟩ := hne q hq
      repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ a11] | rw [State.reg_setReg_other _ _ _ _ a12] | rw [State.reg_setReg_other _ _ _ _ a13] | rw [State.reg_setReg_other _ _ _ _ a14] | rw [State.reg_setReg_other _ _ _ _ a15] | rw [State.reg_setReg_other _ _ _ _ a16] | rw [State.reg_setReg_other _ _ _ _ a17])
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]

/-- `memcpy(d, src, n)` (musl src/string/memcpy.c, the C version with its word loop and the three shifted loops
    for a misaligned destination) at the process level: `memcpySpec`. -/
theorem memcpy_verified : VerifiedProc img dom 0x125dc#64 memcpySpec := by
  rintro ⟨d, src, n⟩ s k he hpre
  have hpre' := hpre
  obtain ⟨ha0, ha1, ha2, hrd, hw, hd⟩ := hpre'
  have hpc := he.pc
  have hx := he.live
  have hn := n.isLt
  have hk0 : McKeep s d s := ⟨hx, ha0, rfl, fun _ _ => rfl, rfl⟩
  nocompiler_run_n 4 [hx, hpc, ha1, ha2] using []
  have hne : ∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] → q ≠ 13 ∧ q ≠ 14 ∧ q ≠ 15 ∧ q ≠ 16 :=
    fun q hq => ⟨fun e => hq (by subst e; simp), fun e => hq (by subst e; simp), fun e => hq (by subst e; simp),
      fun e => hq (by subst e; simp)⟩
  by_cases hskip : src.toNat % 4 = 0 ∨ n.toNat = 0
  · have hb : (bool64 (BitVec.ult (src &&& 3#64) 1#64) ||| bool64 (BitVec.ult n 1#64) != 0) = true := by
      rw [bool64_or_ne, ult_and3_one, ult_one]; rcases hskip with h | h <;> simp [h]
    nocompiler_run_n 3 [hx, hb, ha0, ha1] using []
    refine mc_j d src n s k he hpre 0 n.toNat (by omega) (fun h => ?_) _ (.inr (by simp only [nocompiler_state])) ?_ ?_
    · rcases hskip with h' | h'
      · simp only [BitVec.add_zero]; unfold aligned; exact h'
      · omega
    · refine McAt.mk hk0 _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state])
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state, BitVec.add_zero, ha0])
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state, BitVec.add_zero, ha1])
        (by simp only [nocompiler_state]; exact Copied.zero _ _ _)
      obtain ⟨a13, a14, a15, a16⟩ := hne q hq
      repeat (first | rw [State.setPc_reg] | rw [State.reg_setReg_other _ _ _ _ a13] | rw [State.reg_setReg_other _ _ _ _ a14])
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; rw [ha2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · have hb : (bool64 (BitVec.ult (src &&& 3#64) 1#64) ||| bool64 (BitVec.ult n 1#64) != 0) = false := by
      rw [bool64_or_ne, ult_and3_one, ult_one]
      have h1 : ¬ src.toNat % 4 = 0 := fun h => hskip (.inl h)
      have h2 : ¬ n.toNat = 0 := fun h => hskip (.inr h)
      simp [h1, h2]
    nocompiler_run_n 3 [hx, hb, ha1, ha0] using []
    refine mc_hloop d src n s k he hpre _ ⟨0, rfl, by simp only [nocompiler_state], ?_, ?_, ?_, ?_, ?_, by omega, ?_⟩
    · refine hk0.step (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state])
      obtain ⟨a13, a14, a15, a16⟩ := hne q hq
      repeat (first | rw [State.setPc_reg] | rw [State.reg_setReg_other _ _ _ _ a13] | rw [State.reg_setReg_other _ _ _ _ a14] | rw [State.reg_setReg_other _ _ _ _ a15] | rw [State.reg_setReg_other _ _ _ _ a16])
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, BitVec.add_zero]; exact ha1
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, BitVec.add_zero]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Nat.zero_add]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; rw [ha2, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · simp only [nocompiler_state]; exact Copied.zero _ _ _


end NoCompiler.Libc.Musl.Memcpy

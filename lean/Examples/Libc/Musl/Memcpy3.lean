import Examples.Libc.Musl.Memcpy2

set_option maxRecDepth 20000
namespace NoCompiler.Libc.Musl.Memcpy
open NoCompiler NoCompiler.Linux NoCompiler.Libc.Musl.MemcpyImg

theorem mc_d16a (d src n : Word) (s : State) (k : Kern) (he : Entry dom 0x125dc#64 s)
    (hpre : memcpySpec.pre (d, src, n) s k) (c r : Nat) (hr : r < 2 ^ 64) (hcn : c + r % 32 = n.toNat)
    (u : State) (hpc : u.pc = 0x126e0#64) (hu : McAt s d src c u) (h12 : u.reg 12 = BitVec.ofNat 64 r) :
    PReachK img dom (McQ d src n s k) (u, k) := by
  obtain ⟨hk, h13, h14, hc⟩ := hu
  have hx := hk.1
  have hrt : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  have hat2 : ∀ v : State, v.exit = none → (∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] → v.reg q = u.reg q) →
      v.trace = u.trace → v.reg 13 = d + BitVec.ofNat 64 c → v.reg 14 = src + BitVec.ofNat 64 c → v.mem = u.mem →
      McAt s d src c v := fun v a b c' e f g => McAt.mk hk v a b c' e f (by rw [g]; exact hc)
  by_cases hb : r / 16 % 2 = 0
  · have hz : BitVec.ofNat 64 r &&& 16#64 = 0 := (and_bit16 _).2 (by rw [hrt]; exact hb)
    nocompiler_run_n 2 [hx, hpc, h12, beq_of_nbit hz] using []
    refine mc_t8 d src n s k he hpre c r hr (by omega) _ ?_ ?_ ?_
    · simp only [nocompiler_state]
    · refine hat2 _ ?_ ?_ ?_ ?_ ?_ ?_
      · simp only [nocompiler_state]; exact hx
      · intro q hq; simp only [State.setPc_reg]; exact State.reg_setReg_other _ _ _ _ (fun e => hq (by subst e; simp))
      · simp only [nocompiler_state]
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h13
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h14
      · simp only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12
  · have hz : BitVec.ofNat 64 r &&& 16#64 ≠ 0 := fun e => hb (by have := (and_bit16 _).1 e; rwa [hrt] at this)
    nocompiler_run_n 3 [hx, hpc, h12, beq_of_bit hz] using []
    refine mc_b16 d src n s k he hpre c r hr (by omega) _ ?_ ?_ ?_
    · simp only [nocompiler_state]
    · refine hat2 _ ?_ ?_ ?_ ?_ ?_ ?_
      · simp only [nocompiler_state]; exact hx
      · intro q hq; simp only [State.setPc_reg]; exact State.reg_setReg_other _ _ _ _ (fun e => hq (by subst e; simp))
      · simp only [nocompiler_state]
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h13
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h14
      · simp only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12

/-- The shifted loop for a destination 1 past word alignment (0x1267c): 16 bytes a round from source words
    merged with 8-bit shifts, while more than 16 are left. -/
theorem mc_sloop1 (d src n : Word) (s : State) (k : Kern) (he : Entry dom 0x125dc#64 s)
    (hpre : memcpySpec.pre (d, src, n) s k) :
    ∀ x : State × Kern, (∃ c r, ∃ w0 w1 w2 : Byte, x.2 = k ∧ x.1.pc = 0x1267c#64 ∧ McKeep s d x.1 ∧
      x.1.reg 13 = d + BitVec.ofNat 64 c ∧ x.1.reg 11 = src + BitVec.ofNat 64 (c + 13) ∧ x.1.reg 14 = 16#64 ∧
      x.1.reg 12 = BitVec.ofNat 64 r ∧ c + r = n.toNat ∧ 16 < r ∧ aligned (d + BitVec.ofNat 64 c) 4 ∧
      aligned (src + BitVec.ofNat 64 (c + 1)) 4 ∧ Copied s.mem d src c x.1.mem ∧
      x.1.reg 15 = ((s.mem (src + BitVec.ofNat 64 c)) ++ w2 ++ w1 ++ w0).signExtend 64) →
      PReachK img dom (McQ d src n s k) x := by
  refine PReachK.loop _ (fun x => (x.1.reg 12).toNat) ?_
  rintro ⟨u, ku⟩ ⟨c, r, w0, w1, w2, hku, hpc, hk, h13, h11, h14, h12, hcn, hr, had, has, hc, h15⟩
  simp only at hku hpc hk h13 h11 h14 h12 hc h15
  rw [hku]
  have hpre' := hpre
  obtain ⟨-, -, -, hrd, hw, hd⟩ := hpre'
  have hx := hk.1
  have hn := n.isLt
  have hm : ∀ i, decide (i ≤ 16) = true → u.mem (src + BitVec.ofNat 64 (c + i)) = s.mem (src + BitVec.ofNat 64 (c + i)) := by
    intro i h; simp only [decide_eq_true_eq] at h; exact hc.src hd (by omega) (c + i) (by omega)
  have sw : ∀ (j i : Nat), decide (j ≤ 12 ∧ i ≤ 16) = true → ∀ (m : Word → Byte) (v : Nat),
      writeLE m (d + BitVec.ofNat 64 (c + j)) v 4 (src + BitVec.ofNat 64 (c + i)) = m (src + BitVec.ofNat 64 (c + i)) := by
    intro j i h m v; simp only [decide_eq_true_eq] at h; exact srcw4 hd (c + j) (c + i) (by omega) (by omega) m v
  have sw0 : ∀ (i : Nat), decide (i ≤ 16) = true → ∀ (m : Word → Byte) (v : Nat),
      writeLE m (d + BitVec.ofNat 64 c) v 4 (src + BitVec.ofNat 64 (c + i)) = m (src + BitVec.ofNat 64 (c + i)) := by
    intro i h m v; simp only [decide_eq_true_eq] at h; exact srcw4 hd c (c + i) (by omega) (by omega) m v
  have as : ∀ j, j % 4 = 1 → aligned (src + BitVec.ofNat 64 (c + j)) 4 := fun j hj => by unfold aligned at *; bv_omega
  have ad : ∀ j, j % 4 = 0 → aligned (d + BitVec.ofNat 64 (c + j)) 4 := fun j hj => by unfold aligned at *; bv_omega
  have rw4 : ∀ j, j + 4 ≤ 17 → k.perm.canRead (src + BitVec.ofNat 64 (c + j)) 4 :=
    fun j hj => perm_read_sub hrd (c + j) 4 (by omega) (by omega)
  have ww0 : k.perm.canWrite (d + BitVec.ofNat 64 c) 4 := perm_write_sub hw c 4 (by omega) (by omega)
  have hrt : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hs16 : BitVec.ofNat 64 r + 18446744073709551600#64 = BitVec.ofNat 64 (r - 16) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, hrt, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have ww4 : ∀ j, j + 4 ≤ 16 → k.perm.canWrite (d + BitVec.ofNat 64 (c + j)) 4 := fun j hj => perm_write_sub hw (c + j) 4 (by omega) (by omega)
  have e12 : src + BitVec.ofNat 64 (c + 13) + 18446744073709551604#64 = src + BitVec.ofNat 64 (c + 1) := by bv_omega
  have e8 : src + BitVec.ofNat 64 (c + 13) + 18446744073709551608#64 = src + BitVec.ofNat 64 (c + 5) := by bv_omega
  have e4 : src + BitVec.ofNat 64 (c + 13) + 18446744073709551612#64 = src + BitVec.ofNat 64 (c + 9) := by bv_omega
  nocompiler_run_n 23 [hx, hpc, h11, e12, has, ofNat32_se, add_ofNat_assoc, Nat.add_assoc, Nat.reduceAdd, sw, sw0, hm, h15, e8, as 5 (by omega), h13, BitVec.add_zero, had, e4, as 9 (by omega), ad 4 (by omega), as 13 (by omega), ad 8 (by omega), ad 12 (by omega), h12, hs16] using [rw4, ww0, ww4]
  have hr16 : (BitVec.ofNat 64 (r - 16)).toNat = r - 16 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne : ∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] →
      q ≠ 11 ∧ q ≠ 12 ∧ q ≠ 13 ∧ q ≠ 15 ∧ q ≠ 16 ∧ q ≠ 17 ∧ q ≠ 5 :=
    fun q hq => ⟨fun e => hq (by subst e; simp), fun e => hq (by subst e; simp), fun e => hq (by subst e; simp),
      fun e => hq (by subst e; simp), fun e => hq (by subst e; simp), fun e => hq (by subst e; simp), fun e => hq (by subst e; simp)⟩
  obtain ⟨m10, m11, m12, m13⟩ := merge8 w0 w1 w2 (s.mem (src + BitVec.ofNat 64 c)) (s.mem (src + BitVec.ofNat 64 (c + 1)))
    (s.mem (src + BitVec.ofNat 64 (c + 2))) (s.mem (src + BitVec.ofNat 64 (c + 3))) (s.mem (src + BitVec.ofNat 64 (c + 4)))
  obtain ⟨m20, m21, m22, m23⟩ := merge8 (s.mem (src + BitVec.ofNat 64 (c + 1))) (s.mem (src + BitVec.ofNat 64 (c + 2)))
    (s.mem (src + BitVec.ofNat 64 (c + 3))) (s.mem (src + BitVec.ofNat 64 (c + 4))) (s.mem (src + BitVec.ofNat 64 (c + 5)))
    (s.mem (src + BitVec.ofNat 64 (c + 6))) (s.mem (src + BitVec.ofNat 64 (c + 7))) (s.mem (src + BitVec.ofNat 64 (c + 8)))
  obtain ⟨m30, m31, m32, m33⟩ := merge8 (s.mem (src + BitVec.ofNat 64 (c + 5))) (s.mem (src + BitVec.ofNat 64 (c + 6)))
    (s.mem (src + BitVec.ofNat 64 (c + 7))) (s.mem (src + BitVec.ofNat 64 (c + 8))) (s.mem (src + BitVec.ofNat 64 (c + 9)))
    (s.mem (src + BitVec.ofNat 64 (c + 10))) (s.mem (src + BitVec.ofNat 64 (c + 11))) (s.mem (src + BitVec.ofNat 64 (c + 12)))
  obtain ⟨m40, m41, m42, m43⟩ := merge8 (s.mem (src + BitVec.ofNat 64 (c + 9))) (s.mem (src + BitVec.ofNat 64 (c + 10)))
    (s.mem (src + BitVec.ofNat 64 (c + 11))) (s.mem (src + BitVec.ofNat 64 (c + 12))) (s.mem (src + BitVec.ofNat 64 (c + 13)))
    (s.mem (src + BitVec.ofNat 64 (c + 14))) (s.mem (src + BitVec.ofNat 64 (c + 15))) (s.mem (src + BitVec.ofNat 64 (c + 16)))
  have hcp := (((hc.store4 (by omega) _ m10 m11 m12 m13).store4 (by omega) _ m20 m21 m22 m23).store4 (by omega) _ m30 m31 m32 m33).store4
    (by omega) _ m40 m41 m42 m43
  have hregs : ∀ (v : State), (∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] → v.reg q = u.reg q) → True := fun _ _ => trivial
  by_cases hlp : 16 < r - 16
  · have hb : BitVec.ult 16#64 (BitVec.ofNat 64 (r - 16)) = true := by
      simp only [BitVec.ult, hr16, decide_eq_true_eq]; exact hlp
    nocompiler_run_n 1 [hx, h14, hb] using [rw4, ww0, ww4]
    refine .done (.inr ⟨⟨c + 16, r - 16, s.mem (src + BitVec.ofNat 64 (c + 13)), s.mem (src + BitVec.ofNat 64 (c + 14)),
      s.mem (src + BitVec.ofNat 64 (c + 15)), rfl, by simp only [nocompiler_state], ?_, ?_, ?_, ?_, ?_, by omega, hlp,
      ad 16 (by omega), as 17 (by omega), ?_, ?_⟩, ?_⟩)
    · refine hk.step (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state])
      obtain ⟨a11, a12, a13, a15, a16, a17, a5⟩ := hne q hq
      repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ a11] | rw [State.reg_setReg_other _ _ _ _ a12] | rw [State.reg_setReg_other _ _ _ _ a13] | rw [State.reg_setReg_other _ _ _ _ a15] | rw [State.reg_setReg_other _ _ _ _ a16] | rw [State.reg_setReg_other _ _ _ _ a17] | rw [State.reg_setReg_other _ _ _ _ a5])
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h14
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · simp only [nocompiler_state]; exact hcp
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; rw [hr16, hrt]; omega
  · have hb : BitVec.ult 16#64 (BitVec.ofNat 64 (r - 16)) = false := by
      simp only [BitVec.ult, hr16, decide_eq_false_iff_not]; exact hlp
    have e13 := sub_back13 src c
    nocompiler_run_n 2 [hx, h14, hb, e13] using [rw4, ww0, ww4]
    refine PReachK.bind (Dom.sub_of_ranges (by decide)) (fun y hy => .done (.inl hy))
      (mc_d16a d src n s k he hpre (c + 16) (r - 16) (by omega) (by omega) _ ?_ ?_ ?_)
    · simp only [nocompiler_state]
    · refine McAt.mk hk _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state])
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) (by simp only [nocompiler_state]; exact hcp)
      obtain ⟨a11, a12, a13, a15, a16, a17, a5⟩ := hne q hq
      have a14 : q ≠ 14 := fun e => hq (by subst e; simp)
      repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ a11] | rw [State.reg_setReg_other _ _ _ _ a12] | rw [State.reg_setReg_other _ _ _ _ a13] | rw [State.reg_setReg_other _ _ _ _ a14] | rw [State.reg_setReg_other _ _ _ _ a15] | rw [State.reg_setReg_other _ _ _ _ a16] | rw [State.reg_setReg_other _ _ _ _ a17] | rw [State.reg_setReg_other _ _ _ _ a5])
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]

theorem mc_d16b (d src n : Word) (s : State) (k : Kern) (he : Entry dom 0x125dc#64 s)
    (hpre : memcpySpec.pre (d, src, n) s k) (c r : Nat) (hr : r < 2 ^ 64) (hcn : c + r % 32 = n.toNat)
    (u : State) (hpc : u.pc = 0x128fc#64) (hu : McAt s d src c u) (h12 : u.reg 12 = BitVec.ofNat 64 r) :
    PReachK img dom (McQ d src n s k) (u, k) := by
  obtain ⟨hk, h13, h14, hc⟩ := hu
  have hx := hk.1
  have hrt : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  have hat2 : ∀ v : State, v.exit = none → (∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] → v.reg q = u.reg q) →
      v.trace = u.trace → v.reg 13 = d + BitVec.ofNat 64 c → v.reg 14 = src + BitVec.ofNat 64 c → v.mem = u.mem →
      McAt s d src c v := fun v a b c' e f g => McAt.mk hk v a b c' e f (by rw [g]; exact hc)
  by_cases hb : r / 16 % 2 = 0
  · have hz : BitVec.ofNat 64 r &&& 16#64 = 0 := (and_bit16 _).2 (by rw [hrt]; exact hb)
    nocompiler_run_n 2 [hx, hpc, h12, beq_of_nbit hz] using []
    refine mc_t8 d src n s k he hpre c r hr (by omega) _ ?_ ?_ ?_
    · simp only [nocompiler_state]
    · refine hat2 _ ?_ ?_ ?_ ?_ ?_ ?_
      · simp only [nocompiler_state]; exact hx
      · intro q hq; simp only [State.setPc_reg]; exact State.reg_setReg_other _ _ _ _ (fun e => hq (by subst e; simp))
      · simp only [nocompiler_state]
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h13
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h14
      · simp only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12
  · have hz : BitVec.ofNat 64 r &&& 16#64 ≠ 0 := fun e => hb (by have := (and_bit16 _).1 e; rwa [hrt] at this)
    nocompiler_run_n 2 [hx, hpc, h12, beq_of_bit hz] using []
    refine mc_b16 d src n s k he hpre c r hr (by omega) _ ?_ ?_ ?_
    · simp only [nocompiler_state]
    · refine hat2 _ ?_ ?_ ?_ ?_ ?_ ?_
      · simp only [nocompiler_state]; exact hx
      · intro q hq; simp only [State.setPc_reg]; exact State.reg_setReg_other _ _ _ _ (fun e => hq (by subst e; simp))
      · simp only [nocompiler_state]
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h13
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h14
      · simp only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12

/-- The shifted loop for a destination 2 past word alignment (0x12898): 16 bytes a round from source words
    merged with 16-bit shifts, while more than 17 are left. -/
theorem mc_sloop2 (d src n : Word) (s : State) (k : Kern) (he : Entry dom 0x125dc#64 s)
    (hpre : memcpySpec.pre (d, src, n) s k) :
    ∀ x : State × Kern, (∃ c r, ∃ w0 w1 : Byte, x.2 = k ∧ x.1.pc = 0x12898#64 ∧ McKeep s d x.1 ∧
      x.1.reg 13 = d + BitVec.ofNat 64 c ∧ x.1.reg 11 = src + BitVec.ofNat 64 (c + 14) ∧ x.1.reg 14 = 17#64 ∧
      x.1.reg 12 = BitVec.ofNat 64 r ∧ c + r = n.toNat ∧ 17 < r ∧ aligned (d + BitVec.ofNat 64 c) 4 ∧
      aligned (src + BitVec.ofNat 64 (c + 2)) 4 ∧ Copied s.mem d src c x.1.mem ∧
      x.1.reg 15 = ((s.mem (src + BitVec.ofNat 64 (c + 1))) ++ (s.mem (src + BitVec.ofNat 64 c)) ++ w1 ++ w0).signExtend 64) →
      PReachK img dom (McQ d src n s k) x := by
  refine PReachK.loop _ (fun x => (x.1.reg 12).toNat) ?_
  rintro ⟨u, ku⟩ ⟨c, r, w0, w1, hku, hpc, hk, h13, h11, h14, h12, hcn, hr, had, has, hc, h15⟩
  simp only at hku hpc hk h13 h11 h14 h12 hc h15
  rw [hku]
  have hpre' := hpre
  obtain ⟨-, -, -, hrd, hw, hd⟩ := hpre'
  have hx := hk.1
  have hn := n.isLt
  have hm : ∀ i, decide (i ≤ 17) = true → u.mem (src + BitVec.ofNat 64 (c + i)) = s.mem (src + BitVec.ofNat 64 (c + i)) := by
    intro i h; simp only [decide_eq_true_eq] at h; exact hc.src hd (by omega) (c + i) (by omega)
  have sw : ∀ (j i : Nat), decide (j ≤ 12 ∧ i ≤ 17) = true → ∀ (m : Word → Byte) (v : Nat),
      writeLE m (d + BitVec.ofNat 64 (c + j)) v 4 (src + BitVec.ofNat 64 (c + i)) = m (src + BitVec.ofNat 64 (c + i)) := by
    intro j i h m v; simp only [decide_eq_true_eq] at h; exact srcw4 hd (c + j) (c + i) (by omega) (by omega) m v
  have sw0 : ∀ (i : Nat), decide (i ≤ 17) = true → ∀ (m : Word → Byte) (v : Nat),
      writeLE m (d + BitVec.ofNat 64 c) v 4 (src + BitVec.ofNat 64 (c + i)) = m (src + BitVec.ofNat 64 (c + i)) := by
    intro i h m v; simp only [decide_eq_true_eq] at h; exact srcw4 hd c (c + i) (by omega) (by omega) m v
  have as : ∀ j, j % 4 = 2 → aligned (src + BitVec.ofNat 64 (c + j)) 4 := fun j hj => by unfold aligned at *; bv_omega
  have ad : ∀ j, j % 4 = 0 → aligned (d + BitVec.ofNat 64 (c + j)) 4 := fun j hj => by unfold aligned at *; bv_omega
  have rw4 : ∀ j, j + 4 ≤ 18 → k.perm.canRead (src + BitVec.ofNat 64 (c + j)) 4 :=
    fun j hj => perm_read_sub hrd (c + j) 4 (by omega) (by omega)
  have ww0 : k.perm.canWrite (d + BitVec.ofNat 64 c) 4 := perm_write_sub hw c 4 (by omega) (by omega)
  have hrt : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hs16 : BitVec.ofNat 64 r + 18446744073709551600#64 = BitVec.ofNat 64 (r - 16) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, hrt, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have ww4 : ∀ j, j + 4 ≤ 16 → k.perm.canWrite (d + BitVec.ofNat 64 (c + j)) 4 := fun j hj => perm_write_sub hw (c + j) 4 (by omega) (by omega)
  have e12 : src + BitVec.ofNat 64 (c + 14) + 18446744073709551604#64 = src + BitVec.ofNat 64 (c + 2) := by bv_omega
  have e8 : src + BitVec.ofNat 64 (c + 14) + 18446744073709551608#64 = src + BitVec.ofNat 64 (c + 6) := by bv_omega
  have e4 : src + BitVec.ofNat 64 (c + 14) + 18446744073709551612#64 = src + BitVec.ofNat 64 (c + 10) := by bv_omega
  nocompiler_run_n 1 [hx, hpc, h11, e12, has, ofNat32_se, add_ofNat_assoc, Nat.add_assoc, Nat.reduceAdd, sw, sw0, hm] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx, h15] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx, h11, e8, as 6 (by omega), ofNat32_se, add_ofNat_assoc, Nat.add_assoc, Nat.reduceAdd, sw, sw0, hm] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx, h13, BitVec.add_zero, had] using [rw4, ww0, ww4]
  nocompiler_run_n 2 [hx] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx, h11, e4, as 10 (by omega), ofNat32_se, add_ofNat_assoc, Nat.add_assoc, Nat.reduceAdd, sw, sw0, hm] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx, h13, add_ofNat_assoc, ad 4 (by omega)] using [rw4, ww0, ww4]
  nocompiler_run_n 2 [hx] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx, h11, BitVec.add_zero, as 14 (by omega), ofNat32_se, add_ofNat_assoc, Nat.add_assoc, Nat.reduceAdd, sw, sw0, hm] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx, h13, add_ofNat_assoc, ad 8 (by omega)] using [rw4, ww0, ww4]
  nocompiler_run_n 3 [hx] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx, h13, add_ofNat_assoc, ad 12 (by omega)] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx, h13, add_ofNat_assoc] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx, h12, hs16] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx, h11, add_ofNat_assoc, Nat.add_assoc, Nat.reduceAdd] using [rw4, ww0, ww4]
  have hr16 : (BitVec.ofNat 64 (r - 16)).toNat = r - 16 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne : ∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] →
      q ≠ 11 ∧ q ≠ 12 ∧ q ≠ 13 ∧ q ≠ 15 ∧ q ≠ 16 ∧ q ≠ 17 ∧ q ≠ 5 :=
    fun q hq => ⟨fun e => hq (by subst e; simp), fun e => hq (by subst e; simp), fun e => hq (by subst e; simp),
      fun e => hq (by subst e; simp), fun e => hq (by subst e; simp), fun e => hq (by subst e; simp), fun e => hq (by subst e; simp)⟩
  obtain ⟨m10, m11, m12, m13⟩ := merge16 w0 w1 (s.mem (src + BitVec.ofNat 64 c)) (s.mem (src + BitVec.ofNat 64 (c + 1))) (s.mem (src + BitVec.ofNat 64 (c + 2))) (s.mem (src + BitVec.ofNat 64 (c + 3))) (s.mem (src + BitVec.ofNat 64 (c + 4))) (s.mem (src + BitVec.ofNat 64 (c + 5)))
  obtain ⟨m20, m21, m22, m23⟩ := merge16 (s.mem (src + BitVec.ofNat 64 (c + 2))) (s.mem (src + BitVec.ofNat 64 (c + 3))) (s.mem (src + BitVec.ofNat 64 (c + 4))) (s.mem (src + BitVec.ofNat 64 (c + 5))) (s.mem (src + BitVec.ofNat 64 (c + 6))) (s.mem (src + BitVec.ofNat 64 (c + 7))) (s.mem (src + BitVec.ofNat 64 (c + 8))) (s.mem (src + BitVec.ofNat 64 (c + 9)))
  obtain ⟨m30, m31, m32, m33⟩ := merge16 (s.mem (src + BitVec.ofNat 64 (c + 6))) (s.mem (src + BitVec.ofNat 64 (c + 7))) (s.mem (src + BitVec.ofNat 64 (c + 8))) (s.mem (src + BitVec.ofNat 64 (c + 9))) (s.mem (src + BitVec.ofNat 64 (c + 10))) (s.mem (src + BitVec.ofNat 64 (c + 11))) (s.mem (src + BitVec.ofNat 64 (c + 12))) (s.mem (src + BitVec.ofNat 64 (c + 13)))
  obtain ⟨m40, m41, m42, m43⟩ := merge16 (s.mem (src + BitVec.ofNat 64 (c + 10))) (s.mem (src + BitVec.ofNat 64 (c + 11))) (s.mem (src + BitVec.ofNat 64 (c + 12))) (s.mem (src + BitVec.ofNat 64 (c + 13))) (s.mem (src + BitVec.ofNat 64 (c + 14))) (s.mem (src + BitVec.ofNat 64 (c + 15))) (s.mem (src + BitVec.ofNat 64 (c + 16))) (s.mem (src + BitVec.ofNat 64 (c + 17)))
  have hcp := (((hc.store4 (by omega) _ m10 m11 m12 m13).store4 (by omega) _ m20 m21 m22 m23).store4 (by omega) _ m30 m31 m32 m33).store4
    (by omega) _ m40 m41 m42 m43
  by_cases hlp : 17 < r - 16
  · have hb : BitVec.ult 17#64 (BitVec.ofNat 64 (r - 16)) = true := by
      simp only [BitVec.ult, hr16, decide_eq_true_eq]; exact hlp
    nocompiler_run_n 1 [hx, h14, hb] using [rw4, ww0, ww4]
    refine .done (.inr ⟨⟨c + 16, r - 16, (s.mem (src + BitVec.ofNat 64 (c + 14))), (s.mem (src + BitVec.ofNat 64 (c + 15))), rfl, by simp only [nocompiler_state], ?_, ?_, ?_, ?_, ?_, by omega, hlp,
      ad 16 (by omega), as 18 (by omega), ?_, ?_⟩, ?_⟩)
    · refine hk.step (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state])
      obtain ⟨a11, a12, a13, a15, a16, a17, a5⟩ := hne q hq
      repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ a11] | rw [State.reg_setReg_other _ _ _ _ a12] | rw [State.reg_setReg_other _ _ _ _ a13] | rw [State.reg_setReg_other _ _ _ _ a15] | rw [State.reg_setReg_other _ _ _ _ a16] | rw [State.reg_setReg_other _ _ _ _ a17] | rw [State.reg_setReg_other _ _ _ _ a5])
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h14
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · simp only [nocompiler_state]; exact hcp
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; rw [hr16, hrt]; omega
  · have hb : BitVec.ult 17#64 (BitVec.ofNat 64 (r - 16)) = false := by
      simp only [BitVec.ult, hr16, decide_eq_false_iff_not]; exact hlp
    have e13 := sub_back14 src c
    nocompiler_run_n 1 [hx, h14, hb] using [rw4, ww0, ww4]
    nocompiler_run_n 1 [hx, e13] using [rw4, ww0, ww4]
    refine PReachK.bind (Dom.sub_of_ranges (by decide)) (fun y hy => .done (.inl hy))
      (mc_d16b d src n s k he hpre (c + 16) (r - 16) (by omega) (by omega) _ ?_ ?_ ?_)
    · simp only [nocompiler_state]
    · refine McAt.mk hk _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state])
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) (by simp only [nocompiler_state]; exact hcp)
      obtain ⟨a11, a12, a13, a15, a16, a17, a5⟩ := hne q hq
      have a14 : q ≠ 14 := fun e => hq (by subst e; simp)
      repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ a11] | rw [State.reg_setReg_other _ _ _ _ a12] | rw [State.reg_setReg_other _ _ _ _ a13] | rw [State.reg_setReg_other _ _ _ _ a14] | rw [State.reg_setReg_other _ _ _ _ a15] | rw [State.reg_setReg_other _ _ _ _ a16] | rw [State.reg_setReg_other _ _ _ _ a17] | rw [State.reg_setReg_other _ _ _ _ a5])
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]

/-- The shifted loop for a destination 3 past word alignment (0x1278c): 16 bytes a round from source words
    merged with 24-bit shifts, while more than 18 are left. -/
theorem mc_sloop3 (d src n : Word) (s : State) (k : Kern) (he : Entry dom 0x125dc#64 s)
    (hpre : memcpySpec.pre (d, src, n) s k) :
    ∀ x : State × Kern, (∃ c r, ∃ w0 : Byte, x.2 = k ∧ x.1.pc = 0x1278c#64 ∧ McKeep s d x.1 ∧
      x.1.reg 13 = d + BitVec.ofNat 64 c ∧ x.1.reg 11 = src + BitVec.ofNat 64 (c + 15) ∧ x.1.reg 14 = 18#64 ∧
      x.1.reg 12 = BitVec.ofNat 64 r ∧ c + r = n.toNat ∧ 18 < r ∧ aligned (d + BitVec.ofNat 64 c) 4 ∧
      aligned (src + BitVec.ofNat 64 (c + 3)) 4 ∧ Copied s.mem d src c x.1.mem ∧
      x.1.reg 15 = ((s.mem (src + BitVec.ofNat 64 (c + 2))) ++ (s.mem (src + BitVec.ofNat 64 (c + 1))) ++ (s.mem (src + BitVec.ofNat 64 c)) ++ w0).signExtend 64) →
      PReachK img dom (McQ d src n s k) x := by
  refine PReachK.loop _ (fun x => (x.1.reg 12).toNat) ?_
  rintro ⟨u, ku⟩ ⟨c, r, w0, hku, hpc, hk, h13, h11, h14, h12, hcn, hr, had, has, hc, h15⟩
  simp only at hku hpc hk h13 h11 h14 h12 hc h15
  rw [hku]
  have hpre' := hpre
  obtain ⟨-, -, -, hrd, hw, hd⟩ := hpre'
  have hx := hk.1
  have hn := n.isLt
  have hm : ∀ i, decide (i ≤ 18) = true → u.mem (src + BitVec.ofNat 64 (c + i)) = s.mem (src + BitVec.ofNat 64 (c + i)) := by
    intro i h; simp only [decide_eq_true_eq] at h; exact hc.src hd (by omega) (c + i) (by omega)
  have sw : ∀ (j i : Nat), decide (j ≤ 12 ∧ i ≤ 18) = true → ∀ (m : Word → Byte) (v : Nat),
      writeLE m (d + BitVec.ofNat 64 (c + j)) v 4 (src + BitVec.ofNat 64 (c + i)) = m (src + BitVec.ofNat 64 (c + i)) := by
    intro j i h m v; simp only [decide_eq_true_eq] at h; exact srcw4 hd (c + j) (c + i) (by omega) (by omega) m v
  have sw0 : ∀ (i : Nat), decide (i ≤ 18) = true → ∀ (m : Word → Byte) (v : Nat),
      writeLE m (d + BitVec.ofNat 64 c) v 4 (src + BitVec.ofNat 64 (c + i)) = m (src + BitVec.ofNat 64 (c + i)) := by
    intro i h m v; simp only [decide_eq_true_eq] at h; exact srcw4 hd c (c + i) (by omega) (by omega) m v
  have as : ∀ j, j % 4 = 3 → aligned (src + BitVec.ofNat 64 (c + j)) 4 := fun j hj => by unfold aligned at *; bv_omega
  have ad : ∀ j, j % 4 = 0 → aligned (d + BitVec.ofNat 64 (c + j)) 4 := fun j hj => by unfold aligned at *; bv_omega
  have rw4 : ∀ j, j + 4 ≤ 19 → k.perm.canRead (src + BitVec.ofNat 64 (c + j)) 4 :=
    fun j hj => perm_read_sub hrd (c + j) 4 (by omega) (by omega)
  have ww0 : k.perm.canWrite (d + BitVec.ofNat 64 c) 4 := perm_write_sub hw c 4 (by omega) (by omega)
  have hrt : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hs16 : BitVec.ofNat 64 r + 18446744073709551600#64 = BitVec.ofNat 64 (r - 16) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, hrt, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have ww4 : ∀ j, j + 4 ≤ 16 → k.perm.canWrite (d + BitVec.ofNat 64 (c + j)) 4 := fun j hj => perm_write_sub hw (c + j) 4 (by omega) (by omega)
  have e12 : src + BitVec.ofNat 64 (c + 15) + 18446744073709551604#64 = src + BitVec.ofNat 64 (c + 3) := by bv_omega
  have e8 : src + BitVec.ofNat 64 (c + 15) + 18446744073709551608#64 = src + BitVec.ofNat 64 (c + 7) := by bv_omega
  have e4 : src + BitVec.ofNat 64 (c + 15) + 18446744073709551612#64 = src + BitVec.ofNat 64 (c + 11) := by bv_omega
  nocompiler_run_n 1 [hx, hpc, h11, e12, has, ofNat32_se, add_ofNat_assoc, Nat.add_assoc, Nat.reduceAdd, sw, sw0, hm] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx, h15] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx, h11, e8, as 7 (by omega), ofNat32_se, add_ofNat_assoc, Nat.add_assoc, Nat.reduceAdd, sw, sw0, hm] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx, h13, BitVec.add_zero, had] using [rw4, ww0, ww4]
  nocompiler_run_n 2 [hx] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx, h11, e4, as 11 (by omega), ofNat32_se, add_ofNat_assoc, Nat.add_assoc, Nat.reduceAdd, sw, sw0, hm] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx, h13, add_ofNat_assoc, ad 4 (by omega)] using [rw4, ww0, ww4]
  nocompiler_run_n 2 [hx] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx, h11, BitVec.add_zero, as 15 (by omega), ofNat32_se, add_ofNat_assoc, Nat.add_assoc, Nat.reduceAdd, sw, sw0, hm] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx, h13, add_ofNat_assoc, ad 8 (by omega)] using [rw4, ww0, ww4]
  nocompiler_run_n 3 [hx] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx, h13, add_ofNat_assoc, ad 12 (by omega)] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx, h13, add_ofNat_assoc] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx, h12, hs16] using [rw4, ww0, ww4]
  nocompiler_run_n 1 [hx, h11, add_ofNat_assoc, Nat.add_assoc, Nat.reduceAdd] using [rw4, ww0, ww4]
  have hr16 : (BitVec.ofNat 64 (r - 16)).toNat = r - 16 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne : ∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] →
      q ≠ 11 ∧ q ≠ 12 ∧ q ≠ 13 ∧ q ≠ 15 ∧ q ≠ 16 ∧ q ≠ 17 ∧ q ≠ 5 :=
    fun q hq => ⟨fun e => hq (by subst e; simp), fun e => hq (by subst e; simp), fun e => hq (by subst e; simp),
      fun e => hq (by subst e; simp), fun e => hq (by subst e; simp), fun e => hq (by subst e; simp), fun e => hq (by subst e; simp)⟩
  obtain ⟨m10, m11, m12, m13⟩ := merge24 w0 (s.mem (src + BitVec.ofNat 64 c)) (s.mem (src + BitVec.ofNat 64 (c + 1))) (s.mem (src + BitVec.ofNat 64 (c + 2))) (s.mem (src + BitVec.ofNat 64 (c + 3))) (s.mem (src + BitVec.ofNat 64 (c + 4))) (s.mem (src + BitVec.ofNat 64 (c + 5))) (s.mem (src + BitVec.ofNat 64 (c + 6)))
  obtain ⟨m20, m21, m22, m23⟩ := merge24 (s.mem (src + BitVec.ofNat 64 (c + 3))) (s.mem (src + BitVec.ofNat 64 (c + 4))) (s.mem (src + BitVec.ofNat 64 (c + 5))) (s.mem (src + BitVec.ofNat 64 (c + 6))) (s.mem (src + BitVec.ofNat 64 (c + 7))) (s.mem (src + BitVec.ofNat 64 (c + 8))) (s.mem (src + BitVec.ofNat 64 (c + 9))) (s.mem (src + BitVec.ofNat 64 (c + 10)))
  obtain ⟨m30, m31, m32, m33⟩ := merge24 (s.mem (src + BitVec.ofNat 64 (c + 7))) (s.mem (src + BitVec.ofNat 64 (c + 8))) (s.mem (src + BitVec.ofNat 64 (c + 9))) (s.mem (src + BitVec.ofNat 64 (c + 10))) (s.mem (src + BitVec.ofNat 64 (c + 11))) (s.mem (src + BitVec.ofNat 64 (c + 12))) (s.mem (src + BitVec.ofNat 64 (c + 13))) (s.mem (src + BitVec.ofNat 64 (c + 14)))
  obtain ⟨m40, m41, m42, m43⟩ := merge24 (s.mem (src + BitVec.ofNat 64 (c + 11))) (s.mem (src + BitVec.ofNat 64 (c + 12))) (s.mem (src + BitVec.ofNat 64 (c + 13))) (s.mem (src + BitVec.ofNat 64 (c + 14))) (s.mem (src + BitVec.ofNat 64 (c + 15))) (s.mem (src + BitVec.ofNat 64 (c + 16))) (s.mem (src + BitVec.ofNat 64 (c + 17))) (s.mem (src + BitVec.ofNat 64 (c + 18)))
  have hcp := (((hc.store4 (by omega) _ m10 m11 m12 m13).store4 (by omega) _ m20 m21 m22 m23).store4 (by omega) _ m30 m31 m32 m33).store4
    (by omega) _ m40 m41 m42 m43
  by_cases hlp : 18 < r - 16
  · have hb : BitVec.ult 18#64 (BitVec.ofNat 64 (r - 16)) = true := by
      simp only [BitVec.ult, hr16, decide_eq_true_eq]; exact hlp
    nocompiler_run_n 1 [hx, h14, hb] using [rw4, ww0, ww4]
    refine .done (.inr ⟨⟨c + 16, r - 16, (s.mem (src + BitVec.ofNat 64 (c + 15))), rfl, by simp only [nocompiler_state], ?_, ?_, ?_, ?_, ?_, by omega, hlp,
      ad 16 (by omega), as 19 (by omega), ?_, ?_⟩, ?_⟩)
    · refine hk.step (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state])
      obtain ⟨a11, a12, a13, a15, a16, a17, a5⟩ := hne q hq
      repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ a11] | rw [State.reg_setReg_other _ _ _ _ a12] | rw [State.reg_setReg_other _ _ _ _ a13] | rw [State.reg_setReg_other _ _ _ _ a15] | rw [State.reg_setReg_other _ _ _ _ a16] | rw [State.reg_setReg_other _ _ _ _ a17] | rw [State.reg_setReg_other _ _ _ _ a5])
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h14
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · simp only [nocompiler_state]; exact hcp
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; rw [hr16, hrt]; omega
  · have hb : BitVec.ult 18#64 (BitVec.ofNat 64 (r - 16)) = false := by
      simp only [BitVec.ult, hr16, decide_eq_false_iff_not]; exact hlp
    have e13 := sub_back15 src c
    nocompiler_run_n 1 [hx, h14, hb] using [rw4, ww0, ww4]
    nocompiler_run_n 1 [hx, e13] using [rw4, ww0, ww4]
    refine PReachK.bind (Dom.sub_of_ranges (by decide)) (fun y hy => .done (.inl hy))
      (mc_t16 d src n s k he hpre (c + 16) (r - 16) (by omega) (by omega) _ ?_ ?_ ?_)
    · simp only [nocompiler_state]
    · refine McAt.mk hk _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state])
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) (by simp only [nocompiler_state]; exact hcp)
      obtain ⟨a11, a12, a13, a15, a16, a17, a5⟩ := hne q hq
      have a14 : q ≠ 14 := fun e => hq (by subst e; simp)
      repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ a11] | rw [State.reg_setReg_other _ _ _ _ a12] | rw [State.reg_setReg_other _ _ _ _ a13] | rw [State.reg_setReg_other _ _ _ _ a14] | rw [State.reg_setReg_other _ _ _ _ a15] | rw [State.reg_setReg_other _ _ _ _ a16] | rw [State.reg_setReg_other _ _ _ _ a17] | rw [State.reg_setReg_other _ _ _ _ a5])
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]

end NoCompiler.Libc.Musl.Memcpy

import Examples.Libc.Musl.Memcpy1

set_option maxRecDepth 20000
namespace NoCompiler.Libc.Musl.Memcpy
open NoCompiler NoCompiler.Linux NoCompiler.Libc.Musl.MemcpyImg

theorem mc_b16 (d src n : Word) (s : State) (k : Kern) (he : Entry dom 0x125dc#64 s)
    (hpre : memcpySpec.pre (d, src, n) s k) (c r : Nat) (hr : r < 2 ^ 64) (hcn : c + 16 + r % 16 = n.toNat)
    (u : State) (hpc : u.pc = 0x12904#64) (hu : McAt s d src c u) (h12 : u.reg 12 = BitVec.ofNat 64 r) :
    PReachK img dom (McQ d src n s k) (u, k) := by
  have hpre' := hpre
  obtain ⟨-, -, -, hrd, hw, hd⟩ := hpre'
  obtain ⟨hk, h13, h14, hc⟩ := hu
  have hx := hk.1
  have hn := n.isLt
  have sw : ∀ (j i : Nat), decide (j < 16 ∧ i < 16) = true → ∀ (m : Word → Byte) (v : Nat),
      writeLE m (d + BitVec.ofNat 64 (c + j)) v 1 (src + BitVec.ofNat 64 (c + i)) = m (src + BitVec.ofNat 64 (c + i)) := by
    intro j i h m v; simp only [decide_eq_true_eq] at h; exact srcw hd (c + j) (c + i) (by omega) (by omega) m v
  have sw0 : ∀ (i : Nat), decide (i < 16) = true → ∀ (m : Word → Byte) (v : Nat),
      writeLE m (d + BitVec.ofNat 64 c) v 1 (src + BitVec.ofNat 64 (c + i)) = m (src + BitVec.ofNat 64 (c + i)) := by
    intro i h m v; simp only [decide_eq_true_eq] at h; exact srcw hd c (c + i) (by omega) (by omega) m v
  have sv : ∀ i, i < 16 → u.mem (src + BitVec.ofNat 64 (c + i)) = s.mem (src + BitVec.ofNat 64 (c + i)) :=
    fun i hi => hc.src hd (by omega) (c + i) (by omega)
  have sv0 : u.mem (src + BitVec.ofNat 64 c) = s.mem (src + BitVec.ofNat 64 c) := hc.src hd (by omega) c (by omega)
  have rd : ∀ j, j < 16 → k.perm.canRead (src + BitVec.ofNat 64 (c + j)) 1 := fun j hj => perm_read_sub hrd (c + j) 1 (by omega) (by omega)
  have wr : ∀ j, j < 16 → k.perm.canWrite (d + BitVec.ofNat 64 (c + j)) 1 := fun j hj => perm_write_sub hw (c + j) 1 (by omega) (by omega)
  have rd0 : k.perm.canRead (src + BitVec.ofNat 64 c) 1 := perm_read_sub hrd c 1 (by omega) (by omega)
  have wr0 : k.perm.canWrite (d + BitVec.ofNat 64 c) 1 := perm_write_sub hw c 1 (by omega) (by omega)
  have hne : ∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] → q ≠ 11 ∧ q ≠ 13 ∧ q ≠ 14 ∧ q ≠ 15 ∧ q ≠ 16 :=
    fun q hq => ⟨fun e => hq (by subst e; simp), fun e => hq (by subst e; simp), fun e => hq (by subst e; simp),
      fun e => hq (by subst e; simp), fun e => hq (by subst e; simp)⟩
  have hcp : Copied s.mem d src (c + 16) (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE u.mem (d + BitVec.ofNat 64 c) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 c))))).toNat 1) (d + BitVec.ofNat 64 (c + 1)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 1)))))).toNat 1) (d + BitVec.ofNat 64 (c + 2)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 2)))))).toNat 1) (d + BitVec.ofNat 64 (c + 3)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 3)))))).toNat 1) (d + BitVec.ofNat 64 (c + 4)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 4)))))).toNat 1) (d + BitVec.ofNat 64 (c + 5)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 5)))))).toNat 1) (d + BitVec.ofNat 64 (c + 6)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 6)))))).toNat 1) (d + BitVec.ofNat 64 (c + 7)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 7)))))).toNat 1) (d + BitVec.ofNat 64 (c + 8)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 8)))))).toNat 1) (d + BitVec.ofNat 64 (c + 9)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 9)))))).toNat 1) (d + BitVec.ofNat 64 (c + 10)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 10)))))).toNat 1) (d + BitVec.ofNat 64 (c + 11)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 11)))))).toNat 1) (d + BitVec.ofNat 64 (c + 12)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 12)))))).toNat 1) (d + BitVec.ofNat 64 (c + 13)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 13)))))).toNat 1) (d + BitVec.ofNat 64 (c + 14)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 14)))))).toNat 1) (d + BitVec.ofNat 64 (c + 15)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 15)))))).toNat 1) := ((((((((((((((((hc.byte (by omega) _ (byteval_eq' sv0)).byte (by omega) _ (byteval_eq' (sv 1 (by omega)))).byte (by omega) _ (byteval_eq' (sv 2 (by omega)))).byte (by omega) _ (byteval_eq' (sv 3 (by omega)))).byte (by omega) _ (byteval_eq' (sv 4 (by omega)))).byte (by omega) _ (byteval_eq' (sv 5 (by omega)))).byte (by omega) _ (byteval_eq' (sv 6 (by omega)))).byte (by omega) _ (byteval_eq' (sv 7 (by omega)))).byte (by omega) _ (byteval_eq' (sv 8 (by omega)))).byte (by omega) _ (byteval_eq' (sv 9 (by omega)))).byte (by omega) _ (byteval_eq' (sv 10 (by omega)))).byte (by omega) _ (byteval_eq' (sv 11 (by omega)))).byte (by omega) _ (byteval_eq' (sv 12 (by omega)))).byte (by omega) _ (byteval_eq' (sv 13 (by omega)))).byte (by omega) _ (byteval_eq' (sv 14 (by omega)))).byte (by omega) _ (byteval_eq' (sv 15 (by omega))))
  have hat : ∀ v : State, v.exit = none → (∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] → v.reg q = u.reg q) →
      v.trace = u.trace → v.reg 13 = d + BitVec.ofNat 64 (c + 16) → v.reg 14 = src + BitVec.ofNat 64 (c + 16) →
      v.mem = (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE u.mem (d + BitVec.ofNat 64 c) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 c))))).toNat 1) (d + BitVec.ofNat 64 (c + 1)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 1)))))).toNat 1) (d + BitVec.ofNat 64 (c + 2)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 2)))))).toNat 1) (d + BitVec.ofNat 64 (c + 3)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 3)))))).toNat 1) (d + BitVec.ofNat 64 (c + 4)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 4)))))).toNat 1) (d + BitVec.ofNat 64 (c + 5)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 5)))))).toNat 1) (d + BitVec.ofNat 64 (c + 6)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 6)))))).toNat 1) (d + BitVec.ofNat 64 (c + 7)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 7)))))).toNat 1) (d + BitVec.ofNat 64 (c + 8)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 8)))))).toNat 1) (d + BitVec.ofNat 64 (c + 9)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 9)))))).toNat 1) (d + BitVec.ofNat 64 (c + 10)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 10)))))).toNat 1) (d + BitVec.ofNat 64 (c + 11)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 11)))))).toNat 1) (d + BitVec.ofNat 64 (c + 12)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 12)))))).toNat 1) (d + BitVec.ofNat 64 (c + 13)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 13)))))).toNat 1) (d + BitVec.ofNat 64 (c + 14)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 14)))))).toNat 1) (d + BitVec.ofNat 64 (c + 15)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat (u.mem (src + BitVec.ofNat 64 (c + 15)))))).toNat 1) → McAt s d src (c + 16) v :=
    fun v a b c' e f g => McAt.mk hk v a b c' e f (by rw [g]; exact hcp)
  nocompiler_run_n 35 [hx, hpc, h14, BitVec.add_zero, Auto.aligned_one, readLE_one, sw, sw0, add_ofNat_assoc, h13] using [rd0, rd, wr0, wr]
  refine mc_d8 d src n s k he hpre (c + 16) r hr (by omega) _ (by simp only [nocompiler_state]) ?_
    (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12)
  refine hat _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state])
    (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
    (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) (by simp only [nocompiler_state])
  obtain ⟨a11, a13, a14, a15, a16⟩ := hne q hq
  repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ a11] | rw [State.reg_setReg_other _ _ _ _ a13] | rw [State.reg_setReg_other _ _ _ _ a14] | rw [State.reg_setReg_other _ _ _ _ a15] | rw [State.reg_setReg_other _ _ _ _ a16])

theorem mc_t16 (d src n : Word) (s : State) (k : Kern) (he : Entry dom 0x125dc#64 s)
    (hpre : memcpySpec.pre (d, src, n) s k) (c r : Nat) (hr : r < 2 ^ 64) (hcn : c + r % 32 = n.toNat)
    (u : State) (hpc : u.pc = 0x127f0#64) (hu : McAt s d src c u) (h12 : u.reg 12 = BitVec.ofNat 64 r) :
    PReachK img dom (McQ d src n s k) (u, k) := by
  obtain ⟨hk, h13, h14, hc⟩ := hu
  have hx := hk.1
  have hrt : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  have hat2 : ∀ v : State, v.exit = none → (∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] → v.reg q = u.reg q) →
      v.trace = u.trace → v.reg 13 = d + BitVec.ofNat 64 c → v.reg 14 = src + BitVec.ofNat 64 c → v.mem = u.mem →
      McAt s d src c v := fun v a b c' e f g => McAt.mk hk v a b c' e f (by rw [g]; exact hc)
  by_cases hb : r / 16 % 2 = 0
  · have hz : BitVec.ofNat 64 r &&& 16#64 = 0 := (and_bit16 _).2 (by rw [hrt]; exact hb)
    nocompiler_run_n 2 [hx, hpc, h12, bne_of_nbit hz] using []
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
    nocompiler_run_n 2 [hx, hpc, h12, bne_of_bit hz] using []
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

/-- One word stored at `d + c`: the word loaded from `src + c` (in a memory with the entry's source bytes). -/
theorem Copied.word {m0 : Word → Byte} {d src : Word} {c : Nat} {m : Word → Byte} (h : Copied m0 d src c m)
    (hc : c + 4 < 2 ^ 64) (m1 : Word → Byte)
    (hm1 : ∀ i, i < 4 → m1 (src + BitVec.ofNat 64 (c + i)) = m0 (src + BitVec.ofNat 64 (c + i))) :
    Copied m0 d src (c + 4) (writeLE m (d + BitVec.ofNat 64 c)
      ((BitVec.ofNat 32 (readLE m1 (src + BitVec.ofNat 64 c) 4)).signExtend 64 : Word).toNat 4) := by
  refine h.store 4 _ (by omega) hc (fun i hi => ?_)
  rw [byte_of_word, ofNat32_readLE]
  have e : ∀ j, src + BitVec.ofNat 64 c + BitVec.ofNat 64 j = src + BitVec.ofNat 64 (c + j) := fun j => add_ofNat_assoc _ _ _
  obtain ⟨w0, w1, w2, w3⟩ := word_bytes (m1 (src + BitVec.ofNat 64 c)) (m1 (src + BitVec.ofNat 64 c + 1#64))
    (m1 (src + BitVec.ofNat 64 c + 2#64)) (m1 (src + BitVec.ofNat 64 c + 3#64))
  have hm0 := hm1 0 (by omega); simp only [Nat.add_zero] at hm0
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · simp only [Nat.mul_zero, BitVec.ushiftRight_zero, Nat.add_zero]; rw [w0, hm0]
  · simp only [Nat.mul_one]; rw [w1, e 1, hm1 1 (by omega)]
  · rw [show 8 * 2 = 16 from rfl, w2, e 2, hm1 2 (by omega)]
  · rw [show 8 * 3 = 24 from rfl, w3, e 3, hm1 3 (by omega)]

theorem mc_w4 (d src n : Word) (s : State) (k : Kern) (he : Entry dom 0x125dc#64 s)
    (hpre : memcpySpec.pre (d, src, n) s k) (c r : Nat) (hr : r < 2 ^ 64) (hcn : c + r % 8 = n.toNat)
    (had' : 0 < r → aligned (d + BitVec.ofNat 64 c) 4) (has' : 0 < r → aligned (src + BitVec.ofNat 64 c) 4)
    (u : State) (hpc : u.pc = 0x12758#64) (hu : McAt s d src c u) (h12 : u.reg 12 = BitVec.ofNat 64 r) :
    PReachK img dom (McQ d src n s k) (u, k) := by
  have hpre' := hpre
  obtain ⟨-, -, -, hrd, hw, hd⟩ := hpre'
  obtain ⟨hk, h13, h14, hc⟩ := hu
  have hx := hk.1
  have hn := n.isLt
  have hrt : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  have hne : ∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] → q ≠ 11 ∧ q ≠ 13 ∧ q ≠ 14 ∧ q ≠ 15 :=
    fun q hq => ⟨fun e => hq (by subst e; simp), fun e => hq (by subst e; simp), fun e => hq (by subst e; simp),
      fun e => hq (by subst e; simp)⟩
  by_cases hb : r / 4 % 2 = 0
  · have hz : BitVec.ofNat 64 r &&& 4#64 = 0 := (and_bit4 _).2 (by rw [hrt]; exact hb)
    nocompiler_run_n 2 [hx, hpc, h12, beq_of_nbit hz] using [rw0, ww0]
    refine mc_t2 d src n s k he hpre c r hr (by omega) _ ?_ ?_ ?_
    · simp only [nocompiler_state]
    · refine McAt.mk hk _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state])
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h13)
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h14) (by simp only [nocompiler_state]; exact hc)
      simp only [State.setPc_reg]; exact State.reg_setReg_other _ _ _ _ (fun e => hq (by subst e; simp))
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12
  · have hz : BitVec.ofNat 64 r &&& 4#64 ≠ 0 := fun e => hb (by have := (and_bit4 _).1 e; rwa [hrt] at this)
    nocompiler_run_n 2 [hx, hpc, h12, beq_of_bit hz] using [rw0, ww0]
    have hK : c + 4 ≤ n.toNat := by omega
    have had := had' (by omega); have has := has' (by omega)
    have hm : ∀ j i, j + i < 4 → u.mem (src + BitVec.ofNat 64 (c + j + i)) = s.mem (src + BitVec.ofNat 64 (c + j + i)) :=
      fun j i h => hc.src hd (by omega) (c + j + i) (by omega)
    have hm0 : ∀ i, i < 4 → u.mem (src + BitVec.ofNat 64 (c + i)) = s.mem (src + BitVec.ofNat 64 (c + i)) :=
      fun i h => hc.src hd (by omega) (c + i) (by omega)
    have as : ∀ j, j % 4 = 0 → aligned (src + BitVec.ofNat 64 (c + j)) 4 := fun j hj => by unfold aligned at *; bv_omega
    have ad : ∀ j, j % 4 = 0 → aligned (d + BitVec.ofNat 64 (c + j)) 4 := fun j hj => by unfold aligned at *; bv_omega
    have as0 : aligned (src + BitVec.ofNat 64 c) 4 := has
    have ad0 : aligned (d + BitVec.ofNat 64 c) 4 := had
    have rw4 : ∀ j, j + 4 ≤ 4 → k.perm.canRead (src + BitVec.ofNat 64 (c + j)) 4 := fun j hj => perm_read_sub hrd (c + j) 4 (by omega) (by omega)
    have ww4 : ∀ j, j + 4 ≤ 4 → k.perm.canWrite (d + BitVec.ofNat 64 (c + j)) 4 := fun j hj => perm_write_sub hw (c + j) 4 (by omega) (by omega)
    have rw0 : k.perm.canRead (src + BitVec.ofNat 64 c) 4 := perm_read_sub hrd c 4 (by omega) (by omega)
    have ww0 : k.perm.canWrite (d + BitVec.ofNat 64 c) 4 := perm_write_sub hw c 4 (by omega) (by omega)

    nocompiler_run_n 5 [hx, h14, BitVec.add_zero, as0, h13, ad0, h12, add_ofNat_assoc] using [rw0, ww0]
    refine mc_t2 d src n s k he hpre (c + 4) r hr (by omega) _ ?_ ?_ ?_
    · simp only [nocompiler_state]
    · refine McAt.mk hk _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state])
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) ?_
      · obtain ⟨a11, a13, a14, a15⟩ := hne q hq
        repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ a11] | rw [State.reg_setReg_other _ _ _ _ a13] | rw [State.reg_setReg_other _ _ _ _ a14] | rw [State.reg_setReg_other _ _ _ _ a15])
      · simp only [nocompiler_state]; exact (hc.word (by omega) u.mem hm0)
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12

theorem mc_w8 (d src n : Word) (s : State) (k : Kern) (he : Entry dom 0x125dc#64 s)
    (hpre : memcpySpec.pre (d, src, n) s k) (c r : Nat) (hr : r < 2 ^ 64) (hcn : c + r % 16 = n.toNat)
    (had' : 0 < r → aligned (d + BitVec.ofNat 64 c) 4) (has' : 0 < r → aligned (src + BitVec.ofNat 64 c) 4)
    (u : State) (hpc : u.pc = 0x12738#64) (hu : McAt s d src c u) (h12 : u.reg 12 = BitVec.ofNat 64 r) :
    PReachK img dom (McQ d src n s k) (u, k) := by
  have hpre' := hpre
  obtain ⟨-, -, -, hrd, hw, hd⟩ := hpre'
  obtain ⟨hk, h13, h14, hc⟩ := hu
  have hx := hk.1
  have hn := n.isLt
  have hrt : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  have hne : ∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] → q ≠ 11 ∧ q ≠ 13 ∧ q ≠ 14 ∧ q ≠ 15 :=
    fun q hq => ⟨fun e => hq (by subst e; simp), fun e => hq (by subst e; simp), fun e => hq (by subst e; simp),
      fun e => hq (by subst e; simp)⟩
  by_cases hb : r / 8 % 2 = 0
  · have hz : BitVec.ofNat 64 r &&& 8#64 = 0 := (and_bit8 _).2 (by rw [hrt]; exact hb)
    nocompiler_run_n 2 [hx, hpc, h12, beq_of_nbit hz] using [rw0, rw4, ww0, ww4]
    refine mc_w4 d src n s k he hpre c r hr (by omega) had' has' _ ?_ ?_ ?_
    · simp only [nocompiler_state]
    · refine McAt.mk hk _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state])
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h13)
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h14) (by simp only [nocompiler_state]; exact hc)
      simp only [State.setPc_reg]; exact State.reg_setReg_other _ _ _ _ (fun e => hq (by subst e; simp))
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12
  · have hz : BitVec.ofNat 64 r &&& 8#64 ≠ 0 := fun e => hb (by have := (and_bit8 _).1 e; rwa [hrt] at this)
    nocompiler_run_n 2 [hx, hpc, h12, beq_of_bit hz] using [rw0, rw4, ww0, ww4]
    have hK : c + 8 ≤ n.toNat := by omega
    have had := had' (by omega); have has := has' (by omega)
    have hm : ∀ j i, j + i < 8 → u.mem (src + BitVec.ofNat 64 (c + j + i)) = s.mem (src + BitVec.ofNat 64 (c + j + i)) :=
      fun j i h => hc.src hd (by omega) (c + j + i) (by omega)
    have hm0 : ∀ i, i < 4 → u.mem (src + BitVec.ofNat 64 (c + i)) = s.mem (src + BitVec.ofNat 64 (c + i)) :=
      fun i h => hc.src hd (by omega) (c + i) (by omega)
    have as : ∀ j, j % 4 = 0 → aligned (src + BitVec.ofNat 64 (c + j)) 4 := fun j hj => by unfold aligned at *; bv_omega
    have ad : ∀ j, j % 4 = 0 → aligned (d + BitVec.ofNat 64 (c + j)) 4 := fun j hj => by unfold aligned at *; bv_omega
    have as0 : aligned (src + BitVec.ofNat 64 c) 4 := has
    have ad0 : aligned (d + BitVec.ofNat 64 c) 4 := had
    have rw4 : ∀ j, j + 4 ≤ 8 → k.perm.canRead (src + BitVec.ofNat 64 (c + j)) 4 := fun j hj => perm_read_sub hrd (c + j) 4 (by omega) (by omega)
    have ww4 : ∀ j, j + 4 ≤ 8 → k.perm.canWrite (d + BitVec.ofNat 64 (c + j)) 4 := fun j hj => perm_write_sub hw (c + j) 4 (by omega) (by omega)
    have rw0 : k.perm.canRead (src + BitVec.ofNat 64 c) 4 := perm_read_sub hrd c 4 (by omega) (by omega)
    have ww0 : k.perm.canWrite (d + BitVec.ofNat 64 c) 4 := perm_write_sub hw c 4 (by omega) (by omega)

    nocompiler_run_n 6 [hx, h14, BitVec.add_zero, as0, add_ofNat_assoc, as 4 (by omega), h13, ad0, ad 4 (by omega), h12] using [rw0, rw4, ww0, ww4]

    refine mc_w4 d src n s k he hpre (c + 8) r hr (by omega) (fun _ => ad 8 (by omega)) (fun _ => as 8 (by omega)) _ ?_ ?_ ?_
    · simp only [nocompiler_state]
    · refine McAt.mk hk _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state])
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) ?_
      · obtain ⟨a11, a13, a14, a15⟩ := hne q hq
        repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ a11] | rw [State.reg_setReg_other _ _ _ _ a13] | rw [State.reg_setReg_other _ _ _ _ a14] | rw [State.reg_setReg_other _ _ _ _ a15])
      · simp only [nocompiler_state]; exact ((hc.word (by omega) u.mem hm0).word (by omega) u.mem (fun i hi => hm 4 i (by omega)))
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12

/-- The aligned word loop (0x12708, 16 bytes a round while more than 15 are left), by the count left. -/
theorem mc_wloop (d src n : Word) (s : State) (k : Kern) (he : Entry dom 0x125dc#64 s)
    (hpre : memcpySpec.pre (d, src, n) s k) :
    ∀ x : State × Kern, (∃ c r, x.2 = k ∧ x.1.pc = 0x12708#64 ∧ McAt s d src c x.1 ∧ x.1.reg 12 = BitVec.ofNat 64 r ∧
      x.1.reg 11 = 15#64 ∧ c + r = n.toNat ∧ 15 < r ∧ aligned (d + BitVec.ofNat 64 c) 4 ∧ aligned (src + BitVec.ofNat 64 c) 4) →
      PReachK img dom (McQ d src n s k) x := by
  refine PReachK.loop _ (fun x => (x.1.reg 12).toNat) ?_
  rintro ⟨u, ku⟩ ⟨c, r, hku, hpc, hu, h12, h11, hcn, hr15, had, has⟩
  simp only at hku hpc hu h12 h11
  rw [hku]
  have hpre' := hpre
  obtain ⟨-, -, -, hrd, hw, hd⟩ := hpre'
  obtain ⟨hk, h13, h14, hc⟩ := hu
  have hx := hk.1
  have hn := n.isLt
  have hK : c + 16 ≤ n.toNat := by omega
  have hrt : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hm : ∀ j i, j + i < 16 → u.mem (src + BitVec.ofNat 64 (c + j + i)) = s.mem (src + BitVec.ofNat 64 (c + j + i)) :=
    fun j i h => hc.src hd (by omega) (c + j + i) (by omega)
  have hm0 : ∀ i, i < 4 → u.mem (src + BitVec.ofNat 64 (c + i)) = s.mem (src + BitVec.ofNat 64 (c + i)) :=
    fun i h => hc.src hd (by omega) (c + i) (by omega)
  have as : ∀ j, j % 4 = 0 → aligned (src + BitVec.ofNat 64 (c + j)) 4 := fun j hj => by unfold aligned at *; bv_omega
  have ad : ∀ j, j % 4 = 0 → aligned (d + BitVec.ofNat 64 (c + j)) 4 := fun j hj => by unfold aligned at *; bv_omega
  have as0 : aligned (src + BitVec.ofNat 64 c) 4 := has
  have ad0 : aligned (d + BitVec.ofNat 64 c) 4 := had
  have rw4 : ∀ j, j + 4 ≤ 16 → k.perm.canRead (src + BitVec.ofNat 64 (c + j)) 4 := fun j hj => perm_read_sub hrd (c + j) 4 (by omega) (by omega)
  have ww4 : ∀ j, j + 4 ≤ 16 → k.perm.canWrite (d + BitVec.ofNat 64 (c + j)) 4 := fun j hj => perm_write_sub hw (c + j) 4 (by omega) (by omega)
  have rw0 : k.perm.canRead (src + BitVec.ofNat 64 c) 4 := perm_read_sub hrd c 4 (by omega) (by omega)
  have ww0 : k.perm.canWrite (d + BitVec.ofNat 64 c) 4 := perm_write_sub hw c 4 (by omega) (by omega)
  have hs16 : BitVec.ofNat 64 r + 18446744073709551600#64 = BitVec.ofNat 64 (r - 16) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, hrt, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hne : ∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] →
      q ≠ 12 ∧ q ≠ 13 ∧ q ≠ 14 ∧ q ≠ 15 ∧ q ≠ 16 ∧ q ≠ 17 ∧ q ≠ 5 :=
    fun q hq => ⟨fun e => hq (by subst e; simp), fun e => hq (by subst e; simp), fun e => hq (by subst e; simp),
      fun e => hq (by subst e; simp), fun e => hq (by subst e; simp), fun e => hq (by subst e; simp), fun e => hq (by subst e; simp)⟩
  nocompiler_run_n 11 [hx, hpc, h14, BitVec.add_zero, as0, add_ofNat_assoc, as 4 (by omega), as 8 (by omega), as 12 (by omega), h13, ad0, ad 4 (by omega), ad 8 (by omega), ad 12 (by omega), h12] using [rw0, rw4, ww0, ww4]
  have hat : ∀ v : State, v.exit = none → (∀ q : Reg, q ∉ [(11 : Reg), 12, 13, 14, 15, 16, 17, 5] → v.reg q = u.reg q) →
      v.trace = u.trace → v.reg 13 = d + BitVec.ofNat 64 (c + 16) → v.reg 14 = src + BitVec.ofNat 64 (c + 16) →
      v.mem = _ → McAt s d src (c + 16) v :=
    fun v a b c' e f g => McAt.mk hk v a b c' e f (by rw [g]; exact ((((hc.word (by omega) u.mem hm0).word (by omega) u.mem (fun i hi => hm 4 i (by omega))).word (by omega) u.mem (fun i hi => hm 8 i (by omega))).word (by omega) u.mem (fun i hi => hm 12 i (by omega))))
  have hregs : ∀ (v : State), v.reg 13 = d + BitVec.ofNat 64 (c + 16) → True := fun _ _ => trivial
  have hr16 : (BitVec.ofNat 64 (r - 16)).toNat = r - 16 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hlp : 15 < r - 16
  · have hb : BitVec.ult 15#64 (BitVec.ofNat 64 (r - 16)) = true := by
      simp only [BitVec.ult, hr16, decide_eq_true_eq]; exact hlp
    nocompiler_run_n 1 [hx, h11, h12, hs16, hb] using [rw0, rw4, ww0, ww4]
    refine .done (.inr ⟨⟨c + 16, r - 16, rfl, by simp only [nocompiler_state], ?_, ?_, ?_, by omega, hlp, ad 16 (by omega),
      as 16 (by omega)⟩, ?_⟩)
    · refine hat _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state])
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) (by simp only [nocompiler_state])
      obtain ⟨a12, a13, a14, a15, a16, a17, a5⟩ := hne q hq
      repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ a12] | rw [State.reg_setReg_other _ _ _ _ a13] | rw [State.reg_setReg_other _ _ _ _ a14] | rw [State.reg_setReg_other _ _ _ _ a15] | rw [State.reg_setReg_other _ _ _ _ a16] | rw [State.reg_setReg_other _ _ _ _ a17] | rw [State.reg_setReg_other _ _ _ _ a5])
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h12, hs16]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h11
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h12, hs16]; rw [hr16, hrt]; omega
  · have hb : BitVec.ult 15#64 (BitVec.ofNat 64 (r - 16)) = false := by
      simp only [BitVec.ult, hr16, decide_eq_false_iff_not]; exact hlp
    nocompiler_run_n 1 [hx, h11, h12, hs16, hb] using [rw0, rw4, ww0, ww4]
    refine PReachK.bind (Dom.sub_of_ranges (by decide)) (fun y hy => .done (.inl hy))
      (mc_w8 d src n s k he hpre (c + 16) (r - 16) (by omega) (by omega) (fun _ => ad 16 (by omega)) (fun _ => as 16 (by omega)) _ ?_ ?_ ?_)
    · simp only [nocompiler_state]
    · refine hat _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state])
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) (by simp only [nocompiler_state])
      obtain ⟨a12, a13, a14, a15, a16, a17, a5⟩ := hne q hq
      repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ a12] | rw [State.reg_setReg_other _ _ _ _ a13] | rw [State.reg_setReg_other _ _ _ _ a14] | rw [State.reg_setReg_other _ _ _ _ a15] | rw [State.reg_setReg_other _ _ _ _ a16] | rw [State.reg_setReg_other _ _ _ _ a17] | rw [State.reg_setReg_other _ _ _ _ a5])
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h12, hs16]

/-- The aligned path (0x126fc): the word loop if 16 or more are left, then the word tails. -/
theorem mc_al (d src n : Word) (s : State) (k : Kern) (he : Entry dom 0x125dc#64 s)
    (hpre : memcpySpec.pre (d, src, n) s k) (c r : Nat) (hcn : c + r = n.toNat)
    (had' : 0 < r → aligned (d + BitVec.ofNat 64 c) 4) (has' : 0 < r → aligned (src + BitVec.ofNat 64 c) 4)
    (u : State) (hpc : u.pc = 0x126fc#64) (hu : McAt s d src c u) (h12 : u.reg 12 = BitVec.ofNat 64 r) :
    PReachK img dom (McQ d src n s k) (u, k) := by
  have hu' := hu
  obtain ⟨hk, h13, h14, hc⟩ := hu'
  have hx := hk.1
  have hn := n.isLt
  have hrt : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hat : ∀ (val : Word) (v : State), v.exit = none → (∀ q : Reg, q ≠ 11 → v.reg q = u.reg q) → v.trace = u.trace →
      v.mem = u.mem → McAt s d src c v := by
    intro val v a b c' e
    exact McAt.mk hk v a (fun q hq => b q (fun h => hq (by subst h; simp))) c'
      (by rw [b 13 (by decide)]; exact h13) (by rw [b 14 (by decide)]; exact h14) (by rw [e]; exact hc)
  nocompiler_run_n 1 [hx, hpc] using []
  by_cases hlt : r < 16
  · have hb : BitVec.ult (BitVec.ofNat 64 r) 16#64 = true := by simp only [BitVec.ult, hrt, decide_eq_true_eq]; exact hlt
    nocompiler_run_n 1 [hx, h12, hb] using []
    refine mc_w8 d src n s k he hpre c r (by omega) (by omega) had' has' _ ?_ ?_ ?_
    · simp only [nocompiler_state]
    · refine hat 0 _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state]) (by simp only [nocompiler_state])
      simp only [State.setPc_reg]; exact State.reg_setReg_other _ _ _ _ hq
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12
  · have hb : BitVec.ult (BitVec.ofNat 64 r) 16#64 = false := by simp only [BitVec.ult, hrt, decide_eq_false_iff_not]; exact hlt
    nocompiler_run_n 2 [hx, h12, hb] using []
    refine mc_wloop d src n s k he hpre _ ⟨c, r, rfl, by simp only [nocompiler_state], ?_, ?_, ?_, hcn, by omega, had' (by omega), has' (by omega)⟩
    · refine hat 0 _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (by simp only [nocompiler_state]) (by simp only [nocompiler_state])
      simp only [State.setPc_reg]; rw [State.reg_setReg_other _ _ _ _ hq, State.setPc_reg, State.reg_setReg_other _ _ _ _ hq]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h12
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]

/-- A 4-byte store at `d + c` of a value whose bytes are the next 4 of `src`. -/
theorem Copied.store4 {m0 : Word → Byte} {d src : Word} {c : Nat} {m : Word → Byte} (h : Copied m0 d src c m)
    (hc : c + 4 < 2 ^ 64) (V : Word)
    (h0 : V.setWidth 8 = m0 (src + BitVec.ofNat 64 c)) (h1 : (V >>> 8).setWidth 8 = m0 (src + BitVec.ofNat 64 (c + 1)))
    (h2 : (V >>> 16).setWidth 8 = m0 (src + BitVec.ofNat 64 (c + 2))) (h3 : (V >>> 24).setWidth 8 = m0 (src + BitVec.ofNat 64 (c + 3))) :
    Copied m0 d src (c + 4) (writeLE m (d + BitVec.ofNat 64 c) V.toNat 4) := by
  refine h.store 4 _ (by omega) hc (fun i hi => ?_)
  rw [byte_of_word]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · simpa using h0
  · simpa using h1
  · exact h2
  · exact h3

/-- A 4-byte store into the destination leaves a source byte. -/
theorem srcw4 {d src : Word} {n : Nat} (hd : (Region.mk d n).Disjoint ⟨src, n⟩) (j i : Nat) (hj : j + 4 ≤ n) (hi : i < n)
    (m : Word → Byte) (v : Nat) : writeLE m (d + BitVec.ofNat 64 j) v 4 (src + BitVec.ofNat 64 i) = m (src + BitVec.ofNat 64 i) := by
  apply writeLE_of_not_mem (r := ⟨d, n⟩) (by simp only [Region.covers]; bv_omega)
  exact Auto.not_mem_of_disjoint hd hi

theorem sub_back13 (a : Word) (c : Nat) : a + BitVec.ofNat 64 (c + 29) + 18446744073709551603#64 = a + BitVec.ofNat 64 (c + 16) := by
  bv_omega
theorem sub_back14 (a : Word) (c : Nat) : a + BitVec.ofNat 64 (c + 30) + 18446744073709551602#64 = a + BitVec.ofNat 64 (c + 16) := by
  bv_omega
theorem sub_back15 (a : Word) (c : Nat) : a + BitVec.ofNat 64 (c + 31) + 18446744073709551601#64 = a + BitVec.ofNat 64 (c + 16) := by
  bv_omega

end NoCompiler.Libc.Musl.Memcpy

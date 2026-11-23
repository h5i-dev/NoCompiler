import LPS.Bridge.Sim

/-!
# Bridge, step 3: every register-only NoCompiler instruction is one LPS `exec`

The stdpp operations LPS computes with (over `Int`, as `Z`) as the `BitVec` operations NoCompiler
computes with, then one simulation theorem per value-computing pattern.
-/

namespace LPS.Bridge
open NoCompiler

/-! ## stdpp's `Z`-level operations on naturals -/

theorem Z.land_nat (m k : Nat) : Z.land (m : Int) (k : Int) = ((m &&& k : Nat) : Int) := rfl
theorem Z.lor_nat (m k : Nat) : Z.lor (m : Int) (k : Int) = ((m ||| k : Nat) : Int) := rfl
theorem Z.lxor_nat (m k : Nat) : Z.lxor (m : Int) (k : Int) = ((m ^^^ k : Nat) : Int) := rfl

theorem Z.shiftlZ_nat (z : Int) (k : Nat) : Z.shiftlZ z (k : Int) = z * ((2 ^ k : Nat) : Int) := rfl

theorem Z.shiftrZ_nat (z : Int) (k : Nat) : Z.shiftrZ z (k : Int) = z >>> k := by
  cases k with
  | zero => simp [Z.shiftrZ, Z.shiftlZ]
  | succ j => rfl

theorem ofNat_eq_of_lt {n m : Nat} (x : BitVec n) (h : m = x.toNat) : BitVec.ofNat n m = x := by
  subst h; simp

/-! ## stdpp's bitvector operations as `BitVec` operations -/

theorem bv_and_eq {n : Nat} (a b : bv n) : bv_and a b = a &&& b := by
  unfold bv_and bv_unsigned Z_to_bv
  rw [Z.land_nat, BitVec.ofInt_natCast]
  exact ofNat_eq_of_lt _ (by simp)

theorem bv_or_eq {n : Nat} (a b : bv n) : bv_or a b = a ||| b := by
  unfold bv_or bv_unsigned Z_to_bv
  rw [Z.lor_nat, BitVec.ofInt_natCast]
  exact ofNat_eq_of_lt _ (by simp)

theorem bv_xor_eq {n : Nat} (a b : bv n) : bv_xor a b = a ^^^ b := by
  unfold bv_xor bv_unsigned Z_to_bv
  rw [Z.lxor_nat, BitVec.ofInt_natCast]
  exact ofNat_eq_of_lt _ (by simp)

theorem bv_shiftl_eq {n : Nat} (a b : bv n) : bv_shiftl a b = a <<< b.toNat := by
  unfold bv_shiftl bv_unsigned Z_to_bv
  rw [Z.shiftlZ_nat, ← Int.natCast_mul, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftLeft_eq]

theorem bv_shiftr_eq {n : Nat} (a b : bv n) : bv_shiftr a b = a >>> b.toNat := by
  unfold bv_shiftr bv_unsigned Z_to_bv
  rw [Z.shiftrZ_nat, ← Int.natCast_shiftRight, BitVec.ofInt_natCast]
  exact ofNat_eq_of_lt _ (by simp)

theorem bv_ashiftr_eq {n : Nat} (a b : bv n) : bv_ashiftr a b = a.sshiftRight b.toNat := by
  unfold bv_ashiftr bv_unsigned bv_signed Z_to_bv
  rw [Z.shiftrZ_nat]; rfl

theorem bv_lts_eq {n : Nat} (a b : bv n) : bv_lts a b = a.slt b := by
  unfold bv_lts bv_signed; simp [BitVec.slt]

theorem bv_ltu_eq {n : Nat} (a b : bv n) : bv_ltu a b = a.ult b := by
  unfold bv_ltu bv_unsigned; simp [BitVec.ult]

theorem bv_eqb_eq {n : Nat} (a b : bv n) : bv_eqb a b = (a == b) := by
  unfold bv_eqb bv_unsigned
  rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq, Int.ofNat_inj, ← BitVec.toNat_eq]

theorem zext_eq {n : Nat} (m : Nat) (b : bv n) : zext m b = b.setWidth m := by
  unfold zext bv_zero_extend bv_unsigned Z_to_bv
  rw [BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq; simp

theorem low32_eq (v : word) : low32 v = v.setWidth 32 := by
  unfold low32 bv_extract
  apply BitVec.eq_of_toNat_eq; simp

theorem bv_not_w1 : bv_not w1 = ~~~(1 : BitVec 64) := by decide

theorem mask63 (b : word) : (bv_and b (Z_to_bv 64 63)).toNat = b.toNat % 64 := by
  rw [bv_and_eq, BitVec.toNat_and, show (Z_to_bv 64 63).toNat = 2 ^ 6 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem mask31 (b : bv 32) : (bv_and b (Z_to_bv 32 31)).toNat = b.toNat % 32 := by
  rw [bv_and_eq, BitVec.toNat_and, show (Z_to_bv 32 31).toNat = 2 ^ 5 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

/-! ## The M extension -/

theorem div0_iff {n : Nat} (b : bv n) : (bv_unsigned b == 0) = true ↔ b = 0 := by
  unfold bv_unsigned
  rw [beq_iff_eq, Int.natCast_eq_zero]
  exact ⟨fun h => BitVec.eq_of_toNat_eq (by simp [h]), fun h => by simp [h]⟩

theorem Z_to_bv_neg_one (n : Nat) : Z_to_bv n (-1) = BitVec.allOnes n := by
  unfold Z_to_bv; rw [← BitVec.neg_one_eq_allOnes, show (-1 : Int) = -((1 : Nat) : Int) from rfl,
    BitVec.ofInt_neg, BitVec.ofInt_natCast]

theorem bv_quots_eq {n : Nat} (a b : bv n) : bv_quots a b = a.sdiv b := by
  unfold bv_quots bv_signed Z_to_bv Z.quot
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_ofInt, BitVec.toInt_sdiv]

theorem bv_rems_eq {n : Nat} (a b : bv n) : bv_rems a b = a.srem b := by
  unfold bv_rems bv_signed Z_to_bv Z.rem
  rw [← BitVec.toInt_srem, BitVec.ofInt_toInt]

theorem bv_divu_eq {n : Nat} (a b : bv n) : bv_divu a b = a / b := by
  unfold bv_divu bv_unsigned Z_to_bv Z.div
  rw [← Int.ofNat_fdiv, BitVec.ofInt_natCast]
  exact ofNat_eq_of_lt _ (by simp [BitVec.toNat_udiv])

theorem bv_modu_eq {n : Nat} (a b : bv n) : bv_modu a b = a % b := by
  unfold bv_modu bv_unsigned Z_to_bv Z.modulo
  rw [Int.fmod_eq_emod_of_nonneg _ (Int.natCast_nonneg _), ← Int.natCast_emod, BitVec.ofInt_natCast]
  exact ofNat_eq_of_lt _ (by simp [BitVec.toNat_umod])

theorem mul_div_div {n : Nat} (a b : bv n) : mul_div .M_DIV a b = rvDiv a b := by
  unfold mul_div rvDiv
  by_cases hb : b = 0
  · subst hb; simp [bv_unsigned, Z_to_bv_neg_one]
  · simp only [show (bv_unsigned b == 0) = false from Bool.eq_false_iff.2 (fun e => hb ((div0_iff b).1 e)),
      hb, Bool.false_eq_true, ite_false, bv_quots_eq]

theorem mul_div_divu {n : Nat} (a b : bv n) : mul_div .M_DIVU a b = rvDivu a b := by
  unfold mul_div rvDivu
  by_cases hb : b = 0
  · subst hb; simp [bv_unsigned, Z_to_bv_neg_one]
  · simp only [show (bv_unsigned b == 0) = false from Bool.eq_false_iff.2 (fun e => hb ((div0_iff b).1 e)),
      hb, Bool.false_eq_true, ite_false, bv_divu_eq]

theorem mul_div_rem {n : Nat} (a b : bv n) : mul_div .M_REM a b = rvRem a b := by
  unfold mul_div rvRem
  by_cases hb : b = 0
  · subst hb; simp [bv_unsigned]
  · simp only [show (bv_unsigned b == 0) = false from Bool.eq_false_iff.2 (fun e => hb ((div0_iff b).1 e)),
      hb, Bool.false_eq_true, ite_false, bv_rems_eq]

theorem mul_div_remu {n : Nat} (a b : bv n) : mul_div .M_REMU a b = rvRemu a b := by
  unfold mul_div rvRemu
  by_cases hb : b = 0
  · subst hb; simp [bv_unsigned]
  · simp only [show (bv_unsigned b == 0) = false from Bool.eq_false_iff.2 (fun e => hb ((div0_iff b).1 e)),
      hb, Bool.false_eq_true, ite_false, bv_modu_eq]

/-- The high half of a 128-bit product, from `Int`s `x`, `y` standing for the 64-bit operands
    extended to 128 bits (`x ≡ X`, `y ≡ Y` modulo `2^128`). -/
theorem high_half (X Y : Int) :
    ((X * Y % 2 ^ 128) / 2 ^ 64) % 2 ^ 64 = ((X * Y) / 2 ^ 64) % 2 ^ 64 := by
  omega

theorem mulh_core (X Y : Int) (A B : BitVec 128) (hA : (A.toNat : Int) = X % 2 ^ 128)
    (hB : (B.toNat : Int) = Y % 2 ^ 128) :
    ((A * B) >>> 64).setWidth 64 = (Z_to_bv 64 (Z.shiftr (X * Y) 64) : BitVec 64) := by
  apply BitVec.eq_of_toNat_eq
  unfold Z_to_bv Z.shiftr
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_ofInt,
    Int.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  apply Int.ofNat_inj.1
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))]
  rw [Int.natCast_emod, Int.natCast_ediv, Int.natCast_emod, Int.natCast_mul, hA, hB]
  simp only [Int.natCast_pow, Int.cast_ofNat_Int]
  rw [← Int.mul_emod]
  exact high_half X Y

theorem toNat_signExtend128 (a : BitVec 64) : ((a.signExtend 128).toNat : Int) = a.toInt % 2 ^ 128 := by
  unfold BitVec.signExtend
  rw [BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))]; rfl

theorem toNat_setWidth128 (a : BitVec 64) : ((a.setWidth 128).toNat : Int) = (a.toNat : Int) % 2 ^ 128 := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), Int.emod_eq_of_lt (by omega) (by omega)]

theorem mul_div_mulh (a b : word) : mul_div .M_MULH a b = mulhSS a b :=
  (mulh_core _ _ _ _ (toNat_signExtend128 a) (toNat_signExtend128 b)).symm

theorem mul_div_mulhsu (a b : word) : mul_div .M_MULHSU a b = mulhSU a b :=
  (mulh_core _ _ _ _ (toNat_signExtend128 a) (toNat_setWidth128 b)).symm

theorem mul_div_mulhu (a b : word) : mul_div .M_MULHU a b = mulhUU a b :=
  (mulh_core _ _ _ _ (toNat_setWidth128 a) (toNat_setWidth128 b)).symm

/-! ## Immediates, widths, shift amounts -/

theorem sext_eq {n : Nat} (m : Nat) (b : bv n) : sext m b = b.signExtend m := rfl

theorem Z_to_bv64_one : Z_to_bv 64 1 = 1 := rfl
theorem Z_to_bv64_zero : Z_to_bv 64 0 = 0 := rfl
theorem Z_to_bv32_one : Z_to_bv 32 1 = 1 := rfl
theorem Z_to_bv32_zero : Z_to_bv 32 0 = 0 := rfl

theorem mask63' (b : word) : (b &&& Z_to_bv 64 63).toNat = b.toNat % 64 := by
  rw [← bv_and_eq]; exact mask63 b

theorem mask31' (b : bv 32) : (b &&& Z_to_bv 32 31).toNat = b.toNat % 32 := by
  rw [← bv_and_eq]; exact mask31 b

theorem shamt6 (sh : BitVec 6) : (sh.setWidth 64).toNat % 64 = sh.toNat := by
  rw [BitVec.toNat_setWidth]; have := sh.isLt; simp only [Nat.reducePow] at this ⊢; omega

theorem shamt5 (sh : BitVec 5) : (sh.setWidth 32).toNat % 32 = sh.toNat := by
  rw [BitVec.toNat_setWidth]; have := sh.isLt; simp only [Nat.reducePow] at this ⊢; omega

theorem setWidth_signExtend32 (imm : BitVec 12) : (imm.signExtend 64).setWidth 32 = imm.signExtend 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.signExtend, BitVec.toNat_ofInt]
  apply Int.ofNat_inj.1
  rw [Int.natCast_emod, Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)),
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))]
  simp only [Int.natCast_pow, Int.cast_ofNat_Int]
  omega

theorem lui_imm (imm : BitVec 20) :
    sext 64 (bv_concat 32 imm (Z_to_bv 12 0)) = (imm.setWidth 32 <<< 12).signExtend 64 := by
  rw [sext_eq]
  congr 1
  unfold bv_concat Z.shiftl
  rw [show bv_unsigned (Z_to_bv 12 0) = ((0 : Nat) : Int) from rfl, bv_unsigned, ← Int.natCast_mul,
    Z.lor_nat, Z_to_bv, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  have := imm.isLt
  simp only [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq,
    Nat.or_zero, Nat.reducePow] at this ⊢
  omega

/-! ## The step shapes -/

/-- A register write and a fall-through on both sides. -/
theorem RelC.next {s : State} {c : core} (h : RelC s c) (rd : Reg) (v : Word) :
    RelC ((s.setReg rd v).setPc (s.pc + 4)) (rset (r rd) v (with_pc (c.c_pc + 4) c)) := by
  rw [h.2, setReg_setPc]; exact (h.setPc _).setReg rd v

theorem jumpTo_some {s s' : State} {t : Word} (hs : jumpTo s t = some s') : s' = s.setPc t := by
  unfold jumpTo at hs; split at hs
  · exact (Option.some.inj hs).symm
  · exact absurd hs (by simp)

/-! ## The simulation theorems -/

theorem sim_lui {s s' : State} {c : core} (h : RelC s c) (rd : Reg) (imm : BitVec 20)
    (hs : NoCompiler.exec (Instr.lui rd imm) s = some s') :
    ∃ c', LPS.exec 4 (.Lui (r rd) imm) c = .EDone c' ∧ RelC s' c' := by
  simp only [NoCompiler.exec, Option.some.injEq] at hs
  subst hs
  refine ⟨_, rfl, ?_⟩
  rw [lui_imm]; exact h.next rd _

theorem sim_auipc {s s' : State} {c : core} (h : RelC s c) (rd : Reg) (imm : BitVec 20)
    (hs : NoCompiler.exec (Instr.auipc rd imm) s = some s') :
    ∃ c', LPS.exec 4 (.Auipc (r rd) imm) c = .EDone c' ∧ RelC s' c' := by
  simp only [NoCompiler.exec, Option.some.injEq] at hs
  subst hs
  refine ⟨_, rfl, ?_⟩
  rw [lui_imm]
  have := h.next rd (s.pc + (imm.setWidth 32 <<< 12).signExtend 64)
  rw [← h.2] at this ⊢; exact this

theorem sim_jal {s s' : State} {c : core} (h : RelC s c) (rd : Reg) (off : BitVec 21)
    (hs : NoCompiler.exec (Instr.jal rd off) s = some s') :
    ∃ c', LPS.exec 4 (.Jal (r rd) off) c = .EDone c' ∧ RelC s' c' := by
  simp only [NoCompiler.exec] at hs
  have hs := jumpTo_some hs
  subst hs
  refine ⟨_, rfl, ?_⟩
  rw [sext_eq, h.2, setReg_setPc]
  exact (h.setPc _).setReg rd _

theorem sim_jalr {s s' : State} {c : core} (h : RelC s c) (rd rs1 : Reg) (off : BitVec 12)
    (hs : NoCompiler.exec (Instr.jalr rd rs1 off) s = some s') :
    ∃ c', LPS.exec 4 (.Jalr (r rd) (r rs1) off) c = .EDone c' ∧ RelC s' c' := by
  simp only [NoCompiler.exec] at hs
  have hs := jumpTo_some hs
  subst hs
  refine ⟨_, rfl, ?_⟩
  rw [sext_eq, h.2, bv_and_eq, bv_not_w1, h.1 rs1, setReg_setPc]
  exact (h.setPc _).setReg rd _

theorem branch_taken_eq (op : BrOp) (a b : word) : branch_taken (brOp op) a b = evalBr op a b := by
  cases op <;> simp only [brOp, branch_taken, evalBr, bv_eqb_eq, bv_lts_eq, bv_ltu_eq, bne]

theorem sim_branch {s s' : State} {c : core} (h : RelC s c) (op : BrOp) (rs1 rs2 : Reg) (off : BitVec 13)
    (hs : NoCompiler.exec (Instr.branch op rs1 rs2 off) s = some s') :
    ∃ c', LPS.exec 4 (.Branch (brOp op) (r rs1) (r rs2) off) c = .EDone c' ∧ RelC s' c' := by
  simp only [NoCompiler.exec] at hs
  refine ⟨_, rfl, ?_⟩
  rw [branch_taken_eq, h.1 rs1, h.1 rs2, sext_eq, h.2]
  split at hs
  · rename_i ht
    rw [jumpTo_some hs]; simp only [ht, ↓reduceIte]; exact h.setPc _
  · rename_i ht
    rw [← Option.some.inj hs]; simp only [ht, Bool.false_eq_true, ↓reduceIte]; exact h.setPc _

theorem alu64_iop (op : IOp) (x y : word) : alu64 (iOp op) x y = evalI op x y := by
  cases op <;> simp only [iOp, alu64, alu, evalI, bv_lts_eq, bv_ltu_eq, bv_xor_eq, bv_or_eq, bv_and_eq,
    bool64, Z_to_bv64_one, Z_to_bv64_zero]

theorem sim_iop {s s' : State} {c : core} (h : RelC s c) (op : IOp) (rd rs1 : Reg) (imm : BitVec 12)
    (hs : NoCompiler.exec (Instr.iop op rd rs1 imm) s = some s') :
    ∃ c', LPS.exec 4 (.OpImm (iOp op) (r rd) (r rs1) imm) c = .EDone c' ∧ RelC s' c' := by
  simp only [NoCompiler.exec, Option.some.injEq] at hs
  subst hs
  refine ⟨_, rfl, ?_⟩
  rw [alu64_iop, h.1 rs1, sext_eq]; exact h.next rd _

theorem sim_addiw {s s' : State} {c : core} (h : RelC s c) (rd rs1 : Reg) (imm : BitVec 12)
    (hs : NoCompiler.exec (Instr.addiw rd rs1 imm) s = some s') :
    ∃ c', LPS.exec 4 (.OpImm32 (r rd) (r rs1) imm) c = .EDone c' ∧ RelC s' c' := by
  simp only [NoCompiler.exec, Option.some.injEq] at hs
  subst hs
  refine ⟨_, rfl, ?_⟩
  have e : sext 64 (alu32 .ALU_ADD (low32 (rget c (r rs1))) (sext 32 imm))
      = sext32 (s.reg rs1 + imm.signExtend 64) := by
    rw [sext32, BitVec.setWidth_add _ _ (by decide), setWidth_signExtend32, alu32, alu, low32_eq,
      h.1 rs1, sext_eq, sext_eq]
  rw [e]; exact h.next rd _

/-- `slli`, `srli`, `srai` (`rori`, `slliuw` are Zbb/Zba: `toLPS` is `none`). -/
theorem sim_shift {s s' : State} {c : core} {j : LPS.instr} (h : RelC s c) (op : ShOp) (rd rs1 : Reg)
    (sh : BitVec 6) (hj : toLPS (.shift op rd rs1 sh) = some j)
    (hs : NoCompiler.exec (Instr.shift op rd rs1 sh) s = some s') :
    ∃ c', LPS.exec 4 j c = .EDone c' ∧ RelC s' c' := by
  simp only [NoCompiler.exec, Option.some.injEq] at hs
  subst hs
  cases op <;> simp only [toLPS, Option.some.injEq, reduceCtorEq] at hj <;> subst hj <;>
    refine ⟨_, rfl, ?_⟩ <;>
    simp only [alu64, alu, zext_eq, bv_shiftl_eq, bv_shiftr_eq, bv_ashiftr_eq, bv_and_eq, mask63', shamt6,
      h.1 rs1] <;>
    exact h.next rd _

/-- `slliw`, `srliw`, `sraiw` (`roriw` is Zbb: `toLPS` is `none`). -/
theorem sim_shiftw {s s' : State} {c : core} {j : LPS.instr} (h : RelC s c) (op : ShWOp) (rd rs1 : Reg)
    (sh : BitVec 5) (hj : toLPS (.shiftw op rd rs1 sh) = some j)
    (hs : NoCompiler.exec (Instr.shiftw op rd rs1 sh) s = some s') :
    ∃ c', LPS.exec 4 j c = .EDone c' ∧ RelC s' c' := by
  simp only [NoCompiler.exec, Option.some.injEq] at hs
  subst hs
  cases op <;> simp only [toLPS, Option.some.injEq, reduceCtorEq] at hj <;> subst hj <;>
    refine ⟨_, rfl, ?_⟩ <;>
    simp only [alu32, alu, sext_eq, low32_eq, zext_eq, bv_shiftl_eq, bv_shiftr_eq, bv_ashiftr_eq, bv_and_eq,
      mask31', shamt5, h.1 rs1] <;>
    exact h.next rd _

end LPS.Bridge

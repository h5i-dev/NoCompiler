import LPS.Bridge.Decode
import LPS.Riscv.Sem2
import NoCompiler.Machine

/-!
# Bridge, step 2 (probe): one NoCompiler instruction step is one LPS `exec`

`RelC s c`: the NoCompiler state `s` and the LPS core `c` agree on every integer register and on the
pc. `sim_addi`: from related states, NoCompiler's `addi` and LPS's `exec 4 (OpImm ALU_ADD ..)` end in
related states. The pattern for the other instructions (and the memory side, through `interp_eff`) is the
same; this module establishes the register-file lemmas they all use.
-/

namespace LPS.Bridge
open NoCompiler

theorem tget_tset_other {A : Type} (p q : Pos) (x : A) (t : tree A) (h : p ≠ q) :
    tget q (tset p x t) = tget q t := by
  induction p generalizing q t with
  | xH =>
    cases q with
    | xH => exact absurd rfl h
    | xO q => cases t <;> simp [tset, tget] <;> cases q <;> rfl
    | xI q => cases t <;> simp [tset, tget] <;> cases q <;> rfl
  | xO p ih =>
    cases q with
    | xH => cases t <;> simp [tset, tget]
    | xO q =>
      have hpq : p ≠ q := fun e => h (e ▸ rfl)
      cases t with
      | TEmpty => simp only [tset, tget]; rw [ih q _ hpq]; cases q <;> rfl
      | TNode l v r => simp only [tset, tget]; exact ih q _ hpq
    | xI q => cases t <;> simp [tset, tget] <;> cases q <;> rfl
  | xI p ih =>
    cases q with
    | xH => cases t <;> simp [tset, tget]
    | xO q => cases t <;> simp [tset, tget] <;> cases q <;> rfl
    | xI q =>
      have hpq : p ≠ q := fun e => h (e ▸ rfl)
      cases t with
      | TEmpty => simp only [tset, tget]; rw [ih q _ hpq]; cases q <;> rfl
      | TNode l v r => simp only [tset, tget]; exact ih q _ hpq

theorem Pos.toNat_ofNat : ∀ n, 1 ≤ n → (Pos.ofNat n).toNat = n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    match n, hn with
    | 1, _ => rw [Pos.ofNat]; rfl
    | k + 2, _ =>
      rw [Pos.ofNat]
      have h2 : (k + 2) / 2 < k + 2 := by omega
      have h1 : 1 ≤ (k + 2) / 2 := by omega
      split
      · simp only [Pos.toNat]; rw [ih _ h2 h1]; omega
      · simp only [Pos.toNat]; rw [ih _ h2 h1]; omega

theorem bv_key_inj {n : Nat} (a b : bv n) (h : bv_key a = bv_key b) : a = b := by
  unfold bv_key Z.to_pos bv_unsigned at h
  have := congrArg Pos.toNat h
  rw [Pos.toNat_ofNat _ (by omega), Pos.toNat_ofNat _ (by omega)] at this
  exact BitVec.eq_of_toNat_eq (by omega)

theorem reg_get_set (rm : bvmap 5 word) (rd x : reg) (v : word) :
    reg_get (bvmap_set rd v rm) x = if x = rd then v else reg_get rm x := by
  by_cases hx : x = rd
  · subst hx
    have e : tget (bv_key x) (tset (bv_key x) v rm) = some v := tget_tset_same _ _ _
    simp only [reg_get, bvmap_get, bvmap_set, ite_true]
    rw [e]
  · have e : tget (bv_key x) (tset (bv_key rd) v rm) = tget (bv_key x) rm :=
      tget_tset_other _ _ _ _ (fun e => hx (bv_key_inj _ _ e).symm)
    simp only [reg_get, bvmap_get, bvmap_set, hx, ite_false]
    rw [e]

theorem is_x0_iff (x : reg) : is_x0 x = true ↔ x = 0 := by
  unfold is_x0 bv_unsigned
  simp only [beq_iff_eq, Int.natCast_eq_zero]
  exact ⟨fun h => BitVec.eq_of_toNat_eq h, fun h => h ▸ rfl⟩

theorem rget_rset (rd x : reg) (v : word) (c : core) :
    rget (rset rd v c) x = if x = rd ∧ rd ≠ 0 then v else rget c x := by
  by_cases h0 : rd = 0
  · subst h0
    have : is_x0 (0 : reg) = true := (is_x0_iff 0).2 rfl
    simp only [rset, this, if_true, ne_eq, not_true_eq_false, and_false, if_false]
  · have hf : is_x0 rd = false := by
      cases h : is_x0 rd
      · rfl
      · exact absurd ((is_x0_iff rd).1 h) h0
    by_cases hx : x = rd
    · subst hx
      simp only [rget, rset, hf, Bool.false_eq_true, ite_false, with_regs, reg_get_set, ite_true, ne_eq, h0,
        not_false_eq_true, and_self]
    · simp only [rget, rset, hf, Bool.false_eq_true, ite_false, with_regs, reg_get_set, hx, false_and]

/-- The NoCompiler state and the LPS core agree on the integer registers and the pc. -/
def RelC (s : State) (c : core) : Prop := (∀ x : Reg, rget c (r x) = s.reg x) ∧ c.c_pc = s.pc

theorem r_inj {x y : Reg} : r x = r y ↔ x = y := by
  unfold r; exact ⟨fun h => by simpa using congrArg BitVec.toFin h, fun h => h ▸ rfl⟩

theorem r_zero_iff (x : Reg) : r x = 0 ↔ x = 0 := by
  rw [show (0 : reg) = r 0 from rfl, r_inj]

theorem RelC.setReg {s : State} {c : core} (h : RelC s c) (rd : Reg) (v : Word) :
    RelC (s.setReg rd v) (rset (r rd) v c) := by
  refine ⟨fun x => ?_, ?_⟩
  · rw [rget_rset]
    unfold State.setReg State.reg State.upd
    by_cases hd : rd = 0
    · have : ¬(r x = r rd ∧ r rd ≠ 0) := fun ⟨_, h2⟩ => h2 ((r_zero_iff rd).2 hd)
      rw [if_neg this, h.1 x]; simp [hd, State.reg]
    · by_cases hx : x = rd
      · subst hx; simp [hd]; intro h0; exact absurd ((r_zero_iff x).1 h0) hd
      · have : ¬(r x = r rd ∧ r rd ≠ 0) := fun ⟨h1, _⟩ => hx (r_inj.1 h1)
        rw [if_neg this, h.1 x]; simp [hd, hx, State.reg]
  · unfold rset; split <;> simp [with_regs, h.2, State.setReg] <;> split <;> rfl

theorem sext_signExtend (imm : BitVec 12) : sext 64 imm = imm.signExtend 64 := by
  rfl

theorem RelC.setPc {s : State} {c : core} (h : RelC s c) (p : Word) : RelC (s.setPc p) (with_pc p c) :=
  ⟨fun x => by simpa [rget, with_pc, State.setPc, State.reg] using h.1 x, rfl⟩

theorem setReg_setPc (s : State) (rd : Reg) (v p : Word) : (s.setReg rd v).setPc p = (s.setPc p).setReg rd v := by
  unfold State.setReg State.setPc; split <;> rfl

/-- `addi`: NoCompiler's step and LPS's `exec` from related states end in related states. -/
theorem sim_addi {s s' : State} {c : core} (h : RelC s c) (rd rs1 : Reg) (imm : BitVec 12)
    (hs : NoCompiler.exec (Instr.iop .addi rd rs1 imm) s = some s') :
    ∃ c', LPS.exec 4 (.OpImm .ALU_ADD (r rd) (r rs1) imm) c = .EDone c' ∧ RelC s' c' := by
  simp only [NoCompiler.exec, Option.some.injEq] at hs
  subst hs
  refine ⟨_, rfl, ?_⟩
  have e : alu64 .ALU_ADD (rget c (r rs1)) (sext 64 imm) = evalI .addi (s.reg rs1) (imm.signExtend 64) := by
    simp only [alu64, alu, sext_signExtend, h.1 rs1, evalI]
  have hc : (c.c_pc + 4) = s.pc + 4 := by rw [h.2]
  simp only [hc]
  rw [e, setReg_setPc]
  exact ((h.setPc (s.pc + 4)).setReg rd _)

end LPS.Bridge

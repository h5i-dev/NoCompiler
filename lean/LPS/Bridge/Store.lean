import LPS.Bridge.Load

/-!
# Bridge, step 2 (stores): NoCompiler's stores are LPS's

`sim_store`: from related states (`RelC`, `RelM`) and NoCompiler's permission for the store, LPS's
`interp_eff_accesses` of `exec 4 (Store ..)` succeeds with the one access `(a, width)`, ending in a related
core and a related memory: LPS's overlay after `write_to_mem` holds, at each stored byte, NoCompiler's
byte after `writeLE`.
-/

namespace LPS.Bridge
open NoCompiler LPS.RiscvSemantics

/-- `store_ok` holds when every byte of the range is in LPS's writable view. -/
theorem store_ok_of (segs : List Segment) (m : word → Option byte) :
    ∀ (n : Nat) (a : word), (∀ k, k < n → (wview segs m (a + BitVec.ofNat 64 k)).isSome) →
      store_ok segs m a n = true := by
  intro n
  induction n with
  | zero => intro a _; rfl
  | succ n ih =>
    intro a h
    have h0 := h 0 (by omega)
    simp only [BitVec.add_zero] at h0
    have hr := ih (a + 1) (fun k hk => by
      have := h (k + 1) (by omega)
      rwa [show a + BitVec.ofNat 64 (k + 1) = a + 1 + BitVec.ofNat 64 k by
        rw [BitVec.add_assoc]; congr 1; bv_omega] at this)
    simp only [store_ok]
    cases hw : wview segs m a with
    | none => rw [hw] at h0; cases h0
    | some _ => exact hr

theorem store_ok_rel {segs : List Segment} {P : Perm} {s : State} {m : word → Option byte} (hm : RelM segs P s m)
    {a : Word} {n : Nat} (hw : P.canWrite a n) : store_ok segs m a n = true :=
  store_ok_of segs m n a fun k hk => hm.2 _ (NoCompiler.Libc.perm_write_sub hw k 1 (by omega) (by omega))

theorem shiftr_natCast (z k : Nat) : Z.shiftr (z : Int) k = ((z >>> k : Nat) : Int) := by
  simp only [Z.shiftr]; rfl

/-- LPS's write of the `n` little-endian bytes of a natural `z`, pointwise. -/
theorem write_to_mem_le_bytes (p : word) :
    ∀ (n : Nat) (a : word) (z : Nat) (m : word → Option byte), n < 2 ^ 64 →
      write_to_mem m a (Z_to_le_bytes n (z : Int)) p =
        if (p - a).toNat < n then some (BitVec.ofNat 8 (z >>> (8 * (p - a).toNat))) else m p := by
  intro n
  induction n with
  | zero => intro a z m _; simp [Z_to_le_bytes, write_to_mem]
  | succ n ih =>
    intro a z m hn
    simp only [Z_to_le_bytes, write_to_mem]
    rw [shiftr_natCast, ih _ _ _ (by omega)]
    by_cases hpa : p = a
    · subst hpa
      have e : (p - (p + 1)).toNat = 2 ^ 64 - 1 := by
        rw [show p - (p + 1) = -1 by bv_omega]; rfl
      rw [e, if_neg (by omega)]
      simp [bv_eqb, Z_to_bv]
    · have e : (p - (a + 1)).toNat = (p - a).toNat - 1 := sub_succ_toNat p a hpa
      have h0 : (p - a).toNat ≠ 0 := by
        intro h; apply hpa; have := BitVec.eq_of_toNat_eq (by simpa using h : (p - a).toNat = (0#64).toNat); bv_omega
      have hne : bv_eqb p a = false := by
        simp only [bv_eqb, bv_unsigned, decide_eq_false_iff_not, Int.natCast_inj]
        exact fun h => hpa (BitVec.eq_of_toNat_eq h)
      rw [e]
      by_cases hlt : (p - a).toNat - 1 < n
      · rw [if_pos hlt, if_pos (show (p - a).toNat < n + 1 by omega)]
        congr 2
        rw [← Nat.shiftRight_add]
        congr 1
        omega
      · rw [if_neg hlt, if_neg (show ¬(p - a).toNat < n + 1 by omega)]
        simp [hne]

/-- Byte `k < w` of `x` truncated to `w` bytes is byte `k` of `x`. -/
theorem byte_mod (x w k : Nat) (hk : k < w) :
    BitVec.ofNat 8 ((x % 2 ^ (8 * w)) >>> (8 * k)) = BitVec.ofNat 8 (x >>> (8 * k)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hi : i < 8
  · simp only [hi, decide_true, Bool.true_and]
    have : 8 * k + i < 8 * w := by omega
    simp [this]
  · simp [hi]

/-- The memory after the store, pointwise, when LPS stores the low `w` bytes of `x`. -/
theorem write_eq (m : word → Option byte) (a : word) (x w : Nat) (p : word) (hw : w < 2 ^ 64) :
    write_to_mem m a (Z_to_le_bytes w ((x % 2 ^ (8 * w) : Nat) : Int)) p =
      if (p - a).toNat < w then some (BitVec.ofNat 8 (x >>> (8 * (p - a).toNat))) else m p := by
  rw [write_to_mem_le_bytes p w a _ m hw]
  split
  · rename_i h; rw [byte_mod _ _ _ h]
  · rfl

theorem rget_inval_resv (a : word) (c : core) (x : reg) : rget (inval_resv a c) x = rget c x := by
  unfold inval_resv; split
  · split <;> rfl
  · rfl

theorem pc_inval_resv (a : word) (c : core) : (inval_resv a c).c_pc = c.c_pc := by
  unfold inval_resv; split
  · split <;> rfl
  · rfl

/-- After the store: LPS's memory written with NoCompiler's `writeLE` bytes is related to NoCompiler's. -/
theorem RelM.store {segs : List Segment} {P : Perm} {s : State} {m m' : word → Option byte}
    (hm : RelM segs P s m) (a : Word) (v w : Nat) (hw : w < 2 ^ 64)
    (hm' : ∀ p, m' p = if (p - a).toNat < w then some (BitVec.ofNat 8 (v >>> (8 * (p - a).toNat))) else m p) :
    RelM segs P (s.setMem (writeLE s.mem a v w)) m' := by
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · simp only [State.setMem, NoCompiler.Libc.writeLE_apply _ _ _ _ _ hw]
    have h := hm.1 p hp
    by_cases hin : (p - a).toNat < w
    · simp only [ovByte, hm' p, hin, ite_true]
    · simp only [ovByte, hm' p, hin, ite_false] at h ⊢; exact h
  · have h := hm.2 p hp
    by_cases hin : (p - a).toNat < w
    · simp only [wview, hm' p, hin, ite_true, Option.isSome_some]
    · simp only [wview, hm' p, hin, ite_false] at h ⊢; exact h

theorem toNat_extract (v : word) (n : Nat) :
    (bv_extract 0 n v).toNat = v.toNat % 2 ^ n := by
  simp only [bv_extract, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]

/-- Stores: NoCompiler's `store op rs1 rs2 off` and LPS's interpretation of `exec 4 (Store ..)` end in
    related states, with the one access `(ea, width)`. -/
theorem sim_store {segs : List Segment} {P : Perm} {s s' : State} {c : core} {m : word → Option byte}
    (hc : RelC s c) (hm : RelM segs P s m) (op : StOp) (rs1 rs2 : Reg) (off : BitVec 12)
    (hok : P.canWrite (ea s rs1 off) op.width) (hs : NoCompiler.exec (Instr.store op rs1 rs2 off) s = some s') :
    ∃ c' m' acc, interp_eff_accesses segs (LPS.exec 4 (.Store (stOp op) (r rs1) (r rs2) off) c) m =
      .MachineOk (mkAccessReport (c', m') acc) ∧ RelC s' c' ∧ RelM segs P s' m' := by
  simp only [NoCompiler.exec] at hs
  split at hs
  · rename_i hal
    simp only [Option.some.injEq] at hs
    subst hs
    have ha : rget c (r rs1) + sext 64 off = ea s rs1 off := by rw [hc.1 rs1, sext_signExtend]; rfl
    have hv : rget c (r rs2) = s.reg rs2 := hc.1 rs2
    have hpc : c.c_pc + 4 = s.pc + 4 := by rw [hc.2]
    have fin : RelC ((s.setMem (writeLE s.mem (ea s rs1 off) (s.reg rs2).toNat op.width)).setPc (s.pc + 4))
        (inval_resv (ea s rs1 off) (with_pc (c.c_pc + 4) c)) := by
      refine ⟨fun x => ?_, ?_⟩
      · rw [rget_inval_resv]; exact (hc.setPc _).1 x
      · rw [pc_inval_resv]; exact hpc
    have hst := store_ok_rel hm hok
    have hrel : ∀ (w : Nat) (y : Nat), w = op.width → y = (s.reg rs2).toNat % 2 ^ (8 * w) →
        RelM segs P ((s.setMem (writeLE s.mem (ea s rs1 off) (s.reg rs2).toNat op.width)).setPc (s.pc + 4))
          (write_to_mem m (ea s rs1 off) (Z_to_le_bytes w (y : Int))) := by
      intro w y hw hy; subst hw hy
      have hlt : op.width < 2 ^ 64 := by cases op <;> decide
      exact hm.store _ _ _ hlt (fun p => write_eq m _ _ _ p hlt)
    cases op
    all_goals
      simp only [StOp.width] at hst hrel
      simp only [LPS.exec, stOp, store_val, ha, hv, interp_eff_accesses, width_bytes, hst, ite_true]
      refine ⟨_, _, _, rfl, fin, ?_⟩
    · exact hrel 1 _ rfl (toNat_extract _ 8)
    · exact hrel 2 _ rfl (toNat_extract _ 16)
    · exact hrel 4 _ rfl (toNat_extract _ 32)
    · exact hrel 8 _ rfl (Nat.mod_eq_of_lt (s.reg rs2).isLt).symm
  · cases hs

#print axioms sim_store

end LPS.Bridge

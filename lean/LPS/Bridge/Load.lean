import LPS.Bridge.Mem
import NoCompiler.Libc.Mem

/-!
# Bridge, step 2 (loads): NoCompiler's loads are LPS's

`sim_load`: from related states (`RelC`, `RelM`) and NoCompiler's permission for the load, LPS's
`interp_eff_accesses` of `exec 4 (Load ..)` succeeds with the related core, memory unchanged, and the one
access `(a, width)`.
-/

namespace LPS.Bridge
open NoCompiler LPS.RiscvSemantics

theorem read_rel {segs : List Segment} {P : Perm} {s : State} {m : word → Option byte} (hm : RelM segs P s m)
    {a : Word} {w : Nat} (hw : P.canRead a w) : ov_read_bytes segs m a w = some (readBytes s.mem a w) :=
  ov_read_bytes_of segs m s.mem w a fun k hk => hm.1 _ (NoCompiler.Libc.perm_read_sub hw k 1 (by omega) (by omega))

theorem readLE_lt (mem : Word → Byte) : ∀ (n : Nat) (a : Word), readLE mem a n < 256 ^ n := by
  intro n; induction n with
  | zero => intro a; simp [readLE]
  | succ n ih =>
    intro a; simp only [readLE, Nat.pow_succ]
    have h1 : (mem a).toNat < 256 := (mem a).isLt
    have h2 := ih (a + 1)
    omega

theorem extract_le (n R : Nat) (hn : n ≤ 64) : bv_extract 0 n (Z_to_bv 64 (R : Int)) = BitVec.ofNat n R := by
  apply BitVec.eq_of_toNat_eq
  simp only [bv_extract, Z_to_bv, BitVec.ofInt_natCast, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hn)

theorem zext_ofNat (k R : Nat) (hR : R < 2 ^ k) : zext 64 (BitVec.ofNat k R) = BitVec.ofNat 64 R := by
  apply BitVec.eq_of_toNat_eq
  simp only [zext, bv_zero_extend, Z_to_bv, bv_unsigned, BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hR]

theorem le_word_readBytes (mem : Word → Byte) (a : Word) (n k : Nat) (hk : k ≤ 64) :
    bv_extract 0 k (le_bytes_to_word (readBytes mem a n)) = BitVec.ofNat k (readLE mem a n) := by
  unfold le_bytes_to_word; rw [bytes_le_to_Z_readBytes]; exact extract_le _ _ hk

/-- Loads: NoCompiler's `load op rd rs1 off` and LPS's interpretation of `exec 4 (Load ..)` end in related
    states, LPS's memory unchanged. -/
theorem sim_load {segs : List Segment} {P : Perm} {s s' : State} {c : core} {m : word → Option byte}
    (hc : RelC s c) (hm : RelM segs P s m) (op : LdOp) (rd rs1 : Reg) (off : BitVec 12)
    (hok : P.canRead (ea s rs1 off) op.width) (hs : NoCompiler.exec (Instr.load op rd rs1 off) s = some s') :
    ∃ c' acc, interp_eff_accesses segs (LPS.exec 4 (.Load (ldOp op).1 (ldOp op).2 (r rd) (r rs1) off) c) m =
      .MachineOk (mkAccessReport (c', m) acc) ∧ RelC s' c' := by
  simp only [NoCompiler.exec] at hs
  split at hs
  · rename_i hal
    simp only [Option.some.injEq] at hs
    subst hs
    have ha : rget c (r rs1) + sext 64 off = ea s rs1 off := by rw [hc.1 rs1, sext_signExtend]; rfl
    have hpc : c.c_pc + 4 = s.pc + 4 := by rw [hc.2]
    -- the related core after writing `v` to rd: what every case ends in
    have fin : RelC ((s.setReg rd (loadVal op s.mem (ea s rs1 off))).setPc (s.pc + 4))
        (rset (r rd) (loadVal op s.mem (ea s rs1 off)) (with_pc (c.c_pc + 4) c)) := by
      rw [hpc, setReg_setPc]; exact (hc.setPc _).setReg rd _
    cases op
    all_goals
      have hr := read_rel hm hok
      simp only [LdOp.width] at hr
      simp only [LPS.exec, ldOp, load_val, ha, interp_eff_accesses, width_bytes, hr, ite_true, ite_false,
        Bool.false_eq_true]
      refine ⟨_, _, rfl, ?_⟩
    · rw [le_word_readBytes _ _ _ _ (by omega)]; exact fin
    · rw [le_word_readBytes _ _ _ _ (by omega)]; exact fin
    · rw [le_word_readBytes _ _ _ _ (by omega)]; exact fin
    · rw [le_word_readBytes _ _ _ _ (by omega)]; exact fin
    · rw [le_word_readBytes _ _ _ _ (by omega), zext_ofNat _ _ (readLE_lt _ 1 _)]; exact fin
    · rw [le_word_readBytes _ _ _ _ (by omega), zext_ofNat _ _ (by have := readLE_lt s.mem 2 (ea s rs1 off); omega)]; exact fin
    · rw [le_word_readBytes _ _ _ _ (by omega), zext_ofNat _ _ (by have := readLE_lt s.mem 4 (ea s rs1 off); omega)]; exact fin
  · cases hs

end LPS.Bridge

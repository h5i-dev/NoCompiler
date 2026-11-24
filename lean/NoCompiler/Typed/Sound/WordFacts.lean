import NoCompiler.Typed.Sem

/-
Facts about words that do not mention the checker (no Check/CheckBase import): literals,
low words, products modulo 2^32, bit counts, disjoint bits.
-/
namespace NoCompiler.Typed

/-- A register typed by a constant holds exactly that constant (mod 2^64). -/
theorem eq_ofInt_of_hasInt {ι : Val} {w : Word} {c : Int} (h : HasInt ι w (.mk c [])) :
    w = BitVec.ofInt 64 c := by
  unfold HasInt at h
  simp only [IExpr.eval, List.map_nil, List.sum_nil, Int.add_zero] at h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt]
  have hw := w.isLt
  have : ((w.toNat : Int) % 2 ^ 64) = (w.toNat : Int) := Int.emod_eq_of_lt (by omega) (by omega)
  rw [this] at h
  omega

theorem bool64_toNat (b : Bool) : ((bool64 b).toNat : Int) = if b = true then 1 else 0 := by
  cases b <;> simp [bool64]

theorem hasInt_toInt (ι : Val) (w : Word) (x : Var) (h : ι x = w.toInt) : HasInt ι w (.var x) := by
  unfold HasInt
  simp only [IExpr.eval_var, h]
  have hc := BitVec.toInt_eq_toNat_cond w
  have := w.isLt
  split at hc <;> omega

theorem zext32_toNat (w : Word) : (zext32 w).toNat = w.toNat % 2 ^ 32 := by
  unfold zext32
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))

theorem zexth_toNat (w : Word) : ((w.setWidth 16).setWidth 64).toNat = w.toNat % 2 ^ 16 := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))

/-- A register typed by the literal `c` holds `c mod 2^64`. -/
theorem toNat_of_lit {ι : Val} {w : Word} {c : Int} (h : HasInt ι w (.mk c [])) :
    (w.toNat : Int) = c % 2 ^ 64 := by
  have := eq_ofInt_of_hasInt h
  subst this
  rw [BitVec.toNat_ofInt]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))

/-- Products agree modulo 2^32 when the factors do. -/
theorem mod32_mul {A B a b : Int} (hA : (A - a) % 2 ^ 32 = 0) (hB : (B - b) % 2 ^ 32 = 0) :
    (A * B - a * b) % 2 ^ 32 = 0 := by
  have hA' := Int.dvd_of_emod_eq_zero hA
  have hB' := Int.dvd_of_emod_eq_zero hB
  have : A * B - a * b = A * (B - b) + (A - a) * b := by
    rw [Int.mul_sub, Int.sub_mul]; omega
  rw [this]
  exact Int.emod_eq_zero_of_dvd (Int.dvd_add (Int.dvd_trans hB' (Int.dvd_mul_left _ _))
    (Int.dvd_trans hA' (Int.dvd_mul_right _ _)))

theorem w32_mul_mod {x y : Word} {E1 E2 : Int} (hx : (x.toNat : Int) % 2 ^ 64 = E1 % 2 ^ 64)
    (hy : (y.toNat : Int) % 2 ^ 64 = E2 % 2 ^ 64) :
    (((x.setWidth 32 * y.setWidth 32).toNat : Int) - E1 * E2) % 2 ^ 32 = 0 := by
  rw [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  generalize hP : x.toNat % 2 ^ 32 * (y.toNat % 2 ^ 32) = P
  have hPc : ((P : Nat) : Int) = ((x.toNat % 2 ^ 32 : Nat) : Int) * ((y.toNat % 2 ^ 32 : Nat) : Int) := by
    rw [← hP, Int.natCast_mul]
  have k := mod32_mul (A := ((x.toNat % 2 ^ 32 : Nat) : Int)) (a := E1)
    (B := ((y.toNat % 2 ^ 32 : Nat) : Int)) (b := E2) (by omega) (by omega)
  rw [← hPc] at k
  generalize E1 * E2 = Q at k ⊢
  omega

theorem w32_shl_mod {x : Word} {E : Int} (n : Nat) (hx : (x.toNat : Int) % 2 ^ 64 = E % 2 ^ 64) :
    ((((x.setWidth 32) <<< n).toNat : Int) - ((2 ^ n : Nat) : Int) * E) % 2 ^ 32 = 0 := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]
  generalize hP : x.toNat % 2 ^ 32 * 2 ^ n = P
  generalize hN : 2 ^ n = N at hP ⊢
  have hPc : ((P : Nat) : Int) = ((x.toNat % 2 ^ 32 : Nat) : Int) * ((N : Nat) : Int) := by
    rw [← hP, Int.natCast_mul]
  have k := mod32_mul (A := ((x.toNat % 2 ^ 32 : Nat) : Int)) (a := E) (B := ((N : Nat) : Int))
    (b := ((N : Nat) : Int)) (by omega) (by simp)
  rw [← hPc] at k
  rw [Int.mul_comm ((N : Nat) : Int) E]
  generalize E * ((N : Nat) : Int) = Q at k ⊢
  omega

theorem bitcount_le (x : Word) :
    (evalU .clz x).toNat ≤ 64 ∧ (evalU .ctz x).toNat ≤ 64 ∧ (evalU .cpop x).toNat ≤ 64 ∧
    (evalU .clzw x).toNat ≤ 32 ∧ (evalU .ctzw x).toNat ≤ 32 ∧ (evalU .cpopw x).toNat ≤ 32 := by
  have c64 : ∀ y : BitVec 64, y.clz.toNat ≤ 64 := fun y => by
    have := BitVec.le_def.1 (BitVec.clz_le (x := y)); simpa using this
  have c32 : ∀ y : BitVec 32, y.clz.toNat ≤ 32 := fun y => by
    have := BitVec.le_def.1 (BitVec.clz_le (x := y)); simpa using this
  have p64 : ∀ y : BitVec 64, y.cpop.toNat ≤ 64 := fun y => by
    unfold BitVec.cpop; rw [BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le _ _) (BitVec.cpopNatRec_zero_le y 64)
  have p32 : ∀ y : BitVec 32, y.cpop.toNat ≤ 32 := fun y => by
    unfold BitVec.cpop; rw [BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le _ _) (BitVec.cpopNatRec_zero_le y 32)
  simp only [evalU, BitVec.ctz, BitVec.toNat_setWidth]
  refine ⟨c64 _, c64 _, p64 _, ?_, ?_, ?_⟩ <;>
    exact Nat.le_trans (Nat.mod_le _ _) (by first | exact c32 _ | exact p32 _)

theorem nat_and_eq_zero {a b j : Nat} (ha : a < 2 ^ j) (hb : b % 2 ^ j = 0) : a &&& b = 0 := by
  have h1 : a = a &&& (2 ^ j - 1) := (Nat.and_two_pow_sub_one_of_lt_two_pow ha).symm
  rw [h1, Nat.and_assoc, Nat.and_comm (2 ^ j - 1) b, Nat.and_two_pow_sub_one_eq_mod, hb, Nat.and_zero]

theorem bv_disjoint {w c : Word} (h : w &&& c = 0#64) : w ||| c = w + c ∧ w ^^^ c = w + c := by
  have ho := (BitVec.add_eq_or_of_and_eq_zero w c h).symm
  refine ⟨ho, ?_⟩
  rw [← ho]
  ext i hi
  have := congrArg (fun z => z.getLsbD i) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at this
  simp only [BitVec.getElem_xor, BitVec.getElem_or]
  rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem]
  cases hw : w.getLsbD i <;> cases hc : c.getLsbD i <;> simp_all

/-- The low `k` bits of `x xor y` are zero exactly when `x` and `y` agree modulo `2^k`. -/
theorem xor_low_zero_iff (x y : Word) (k : Nat) :
    (x ^^^ y).toNat % 2 ^ k = 0 ↔ x.toNat % 2 ^ k = y.toNat % 2 ^ k := by
  rw [BitVec.toNat_xor, Nat.xor_mod_two_pow]
  constructor
  · intro h
    have := congrArg (· ^^^ (y.toNat % 2 ^ k)) h
    simpa [Nat.xor_assoc] using this
  · intro h; rw [h]; simp

/-- For words standing for `a` and `b` (mod 2^64) and `k ≤ 64`: `2^k ∣ x xor y ⇔ 2^k ∣ a − b`
    (the xor-then-mask idiom, I23). -/
theorem xor_dvd_iff {x y : Word} {a b : Int} (hx : (x.toNat : Int) % 2 ^ 64 = a % 2 ^ 64)
    (hy : (y.toNat : Int) % 2 ^ 64 = b % 2 ^ 64) {k : Nat} (hk : k ≤ 64) :
    ((x ^^^ y).toNat : Int) % 2 ^ k = 0 ↔ (a - b) % 2 ^ k = 0 := by
  have hdk : ((2 : Int) ^ k) ∣ 2 ^ 64 := by
    have := Int.natCast_dvd_natCast.2 (Nat.pow_dvd_pow 2 hk); exact_mod_cast this
  have ha : (x.toNat : Int) % 2 ^ k = a % 2 ^ k := by
    rw [← Int.emod_emod_of_dvd (x.toNat : Int) hdk, hx, Int.emod_emod_of_dvd a hdk]
  have hb : (y.toNat : Int) % 2 ^ k = b % 2 ^ k := by
    rw [← Int.emod_emod_of_dvd (y.toNat : Int) hdk, hy, Int.emod_emod_of_dvd b hdk]
  rw [← Int.emod_eq_emod_iff_emod_sub_eq_zero, ← ha, ← hb]
  have h := xor_low_zero_iff x y k
  constructor
  · intro h1
    have h2 : (x ^^^ y).toNat % 2 ^ k = 0 := by exact_mod_cast h1
    have h3 := h.1 h2
    exact_mod_cast h3
  · intro h1
    have h3 : x.toNat % 2 ^ k = y.toNat % 2 ^ k := by exact_mod_cast h1
    have h2 := h.2 h3
    exact_mod_cast h2

end NoCompiler.Typed

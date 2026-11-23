import NoCompiler.Typed.Sem
import NoCompiler.Mem
import NoCompiler.Lemmas

/-
Address and memory facts that do not mention the checker (no Check/CheckBase import), so
that adding a rule does not rebuild them: 64-bit wrap-around arithmetic on addresses,
region and stack membership, byte reads, and the meaning of capabilities in memory.
-/
namespace NoCompiler.Typed

/-- `x` lies in `[B, B + n)` exactly when `x − B < n` (no wrap-around: `B + n ≤ 2^64`). -/
theorem sub_lt_iff (x B : Word) (n : Nat) (hB : B.toNat + n ≤ 2 ^ 64) :
    (x - B).toNat < n ↔ B.toNat ≤ x.toNat ∧ x.toNat < B.toNat + n := by
  rw [BitVec.toNat_sub]
  have := x.isLt; have := B.isLt
  by_cases hx : B.toNat ≤ x.toNat
  · have e : (2 ^ 64 - B.toNat + x.toNat) % 2 ^ 64 = x.toNat - B.toNat := by omega
    rw [e]; omega
  · have e : (2 ^ 64 - B.toNat + x.toNat) % 2 ^ 64 = 2 ^ 64 - B.toNat + x.toNat := by omega
    rw [e]; omega

theorem toNat_ofInt_of {a : Int} (h0 : 0 ≤ a) (h1 : a < 2 ^ 64) :
    ((BitVec.ofInt 64 a).toNat : Int) = a := by
  rw [BitVec.toNat_ofInt]; omega

theorem toNat_add_ofNat {A : Word} {i : Nat} (h : A.toNat + i < 2 ^ 64) :
    (A + BitVec.ofNat 64 i).toNat = A.toNat + i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- Words below the entry `sp`: `sp0 − d + o` for `d ≤ sp0`, `o` small. -/
theorem below_sp_toNat (sp : Word) (d o : Nat) (h1 : d ≤ sp.toNat) (h2 : sp.toNat - d + o < 2 ^ 64) :
    (sp - BitVec.ofNat 64 d + BitVec.ofNat 64 o).toNat = sp.toNat - d + o := by
  have := sp.isLt
  rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (a := o) (by omega)]
  omega

theorem diff_toNat (x y : Word) (h : y.toNat ≤ x.toNat) : (x - y).toNat = x.toNat - y.toNat := by
  rw [BitVec.toNat_sub]; have := x.isLt; have := y.isLt; omega

/-- `sp0 − d` as a number. -/
theorem sp_sub_toNat (sp : Word) (d : Nat) (h : d ≤ sp.toNat) :
    (sp - BitVec.ofNat 64 d).toNat = sp.toNat - d := by
  have := below_sp_toNat sp d 0 h (by have := sp.isLt; omega)
  simpa using this

/-- Membership in a capability's region, for a region inside the address space. -/
theorem region_mem_iff {ι : Val} {b : BytesCap} (h0 : 0 ≤ b.base.eval ι) (h1 : 0 ≤ b.len.eval ι)
    (h2 : b.base.eval ι + b.len.eval ι ≤ 2 ^ 64) (x : Word) :
    (b.region ι).mem x ↔ b.base.eval ι ≤ x.toNat ∧ (x.toNat : Int) < b.base.eval ι + b.len.eval ι := by
  unfold BytesCap.region Region.mem
  simp only
  by_cases hl : b.len.eval ι = 0
  · rw [hl]; simp only [Int.toNat_zero, Nat.not_lt_zero, false_iff]; omega
  have hb := toNat_ofInt_of h0 (by omega)
  rw [sub_lt_iff _ _ _ (by omega)]
  omega

/-- The stack region below the entry `sp`, by numbers. -/
theorem stack_mem_iff (s0 : State) (K : Nat) (hK : K ≤ (s0.reg Reg.sp).toNat) (x : Word) :
    (Spec.stackRegion s0 K).mem x ↔
      (s0.reg Reg.sp).toNat - K ≤ x.toNat ∧ x.toNat < (s0.reg Reg.sp).toNat := by
  have hB := sp_sub_toNat (s0.reg Reg.sp) K hK
  unfold Spec.stackRegion Region.mem
  simp only
  rw [sub_lt_iff _ _ _ (by have := (s0.reg Reg.sp).isLt; omega), hB]
  omega

theorem readLE_lt (m : Word → Byte) (a : Word) : ∀ n, readLE m a n < 256 ^ n
  | 0 => by simp [readLE]
  | n + 1 => by
    simp only [readLE]
    have h1 := (m a).isLt
    have h2 := readLE_lt m (a + 1) n
    rw [Nat.pow_succ]
    have : 256 * readLE m (a + 1) n ≤ 256 * (256 ^ n - 1) := Nat.mul_le_mul_left _ (by omega)
    have : 256 * (256 ^ n - 1) = 256 ^ n * 256 - 256 := by
      rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm]
    have : 256 ≤ 256 ^ n * 256 := by have := Nat.one_le_two_pow (n := 8 * n); simp [Nat.pow_mul] at this; omega
    simp only [BitVec.toNat] at h1
    omega

/-- Equal bytes give equal words (instead of `unfold read64; congr 1`, which is slow). -/
theorem read64_congr {m m' : Word → Byte} {a : Word}
    (h : ∀ k, k < 8 → m (a + BitVec.ofNat 64 k) = m' (a + BitVec.ofNat 64 k)) :
    read64 m a = read64 m' a := by
  unfold read64; rw [readLE_congr h]

/-- `a + j + i = a + (j + i)` for small offsets. -/
theorem add_ofNat_add (a : Word) (j i : Nat) :
    a + BitVec.ofNat 64 j + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (j + i) := by
  rw [BitVec.add_assoc]; exact congrArg (a + ·) (BitVec.eq_of_toNat_eq (by simp))

/-- A field's bytes are in the region, so it depends on memory only there. -/
theorem field_congr {ι : Val} {b : BytesCap} {fd : Field} {m m' : Word → Byte}
    (h0 : 0 ≤ b.base.eval ι) (h1 : 0 ≤ b.len.eval ι) (h2 : b.base.eval ι + b.len.eval ι ≤ 2 ^ 64)
    (hf : Cap.Field.holds ι m b fd) (hm : ∀ x, (b.region ι).mem x → m x = m' x) :
    Cap.Field.holds ι m' b fd := by
  obtain ⟨k1, k2, k3⟩ := hf
  refine ⟨k1, k2, ?_⟩
  have hA := toNat_ofInt_of (a := b.base.eval ι + fd.off) (by omega) (by omega)
  have : read64 m' (BitVec.ofInt 64 (b.base.eval ι + fd.off)) =
      read64 m (BitVec.ofInt 64 (b.base.eval ι + fd.off)) := by
    refine (read64_congr fun j hj => ?_).symm
    apply hm
    rw [region_mem_iff h0 h1 h2]
    have := toNat_add_ofNat (A := BitVec.ofInt 64 (b.base.eval ι + fd.off)) (i := j) (by omega)
    omega
  rw [this]; exact k3

/-- Validity depends on memory only in the footprint. -/
theorem Cap.valid_congr {T : TokEnv} {ι : Val} {F : TokFp} {c : Cap} {m m' : Word → Byte}
    (hv : c.valid T ι F m) (hm : ∀ x, c.fp ι F x → m x = m' x) : c.valid T ι F m' := by
  unfold Cap.valid at *
  intro hg
  have hv := hv hg
  have hg' : c.guard.eval ι = true := hg
  split at hv
  · rename_i b hk
    obtain ⟨h0, h1, h2, hf⟩ := hv
    refine ⟨h0, h1, h2, fun fd hfd => field_congr h0 h1 h2 (hf fd hfd) (fun x hx => hm x ?_)⟩
    unfold Cap.fp Cap.regions; rw [if_pos hg', hk]; exact ⟨_, List.mem_singleton_self _, hx⟩
  · rename_i t hk
    refine (T t).local_ _ _ _ (fun x hx => hm x ?_) hv
    unfold Cap.fp Cap.regions; rw [if_pos hg', hk]; exact hx

/-- The integer a loaded word stands for: signed for the sign-extending loads. -/
def ldInt (op : LdOp) (v : Word) : Int :=
  match op with
  | .lb | .lh | .lw => v.toInt
  | _ => v.toNat

theorem ldInt_hasInt (ι : Val) (op : LdOp) (v : Word) (x : Var) (hx : ι x = ldInt op v) :
    HasInt ι v (.var x) := by
  unfold HasInt
  simp only [IExpr.eval_var, hx]
  have := BitVec.toInt_eq_toNat_cond v
  cases op <;> simp only [ldInt] <;> (try split at this) <;> omega

end NoCompiler.Typed

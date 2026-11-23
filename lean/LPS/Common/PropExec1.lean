import LPS.Common.PlacementSearch
import LPS.LinuxProcessSem.Run2

/-!
# LPS `theories/Common/PropExec.v` (f1006fe8), part 1: stdpp facts, state shape, value shapes

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/PropExec.v` at f1006fe8: the propositional symbolic-execution engine (image
INDEPENDENT proof infrastructure: `mkst`/`getr`/`regupd`, value shapes `v_addi`/`v_mul`/..., conditions
`c_lts`/`c_eq`, per-instruction `step_*` lemmas, and the stack layout/read lemmas). PropExec.v is
2803 lines; the port is `PropExec1` .. `PropExec5`:

- PropExec1 (this file): the stdpp `bv` facts the proofs need (below), `FPState`/`mkst`, register
  helpers, the Z-level range/bit helpers, the value-shape definitions (PropExec.v:1-290);
- PropExec2: memory read mirrors (`seg_rom`, `rdn`), little-endian bridges, range views, `bv_swrap`
  lemmas (PropExec.v:290-505);
- PropExec3: the value bridges (exec-produced `bv` expressions = `v_*` forms) (PropExec.v:505-1031);
- PropExec4: the step lemmas (PropExec.v:1033-2003);
- PropExec5: value/comparison simplification, register-file helpers, LE decoding, stack reads, the
  stack-layout decomposition and the wrapper bridge (PropExec.v:2004-2803).

What changed and why (all files):
- `Class FPState` is a Lean `class` with constructor `mkFP`; Rocq's `Context {fx : FPState}` sections
  (`WithFP1/2/3`) are an instance argument `[FPState]` of each lemma, as Rocq's section discharge makes
  it (resolved by instance search in both).
- stdpp's `bv_modulus`, `bv_half_modulus`, `bv_swrap` are not in `LPS/Stdpp.lean`; they are defined
  here with stdpp's meaning (`2^n`, `2^n / 2`, `bv_wrap n (z + h) - h`). The stdpp lemmas the Rocq
  proofs cite (`bv_eq`, `Z_to_bv_unsigned`, `bv_wrap_small`, `bv_add_unsigned`, ...) are proved here
  under their stdpp names, for `LPS/Stdpp.lean`'s `BitVec` encoding (`bv_signed b = bv_swrap n
  (bv_unsigned b)` is `bv_signed_swrap`).
- Rocq `Z.shiftl`/`Z.shiftr` with a `Z` amount are `Z.shiftlZ`/`Z.shiftrZ` (LPS/Riscv/StdppExtra.lean);
  with a literal or `nat` amount they are `Z.shiftl`/`Z.shiftr` (LPS/Stdpp.lean); `mod`, `/` are
  `Z.modulo`, `Z.div`; `Z.eqb` is `==` and `Z.ltb`/`Z.leb` are `decide`, as in `LPS/Riscv/Sem.lean`.
  A Rocq `2 ^ e` with a `Z` variable exponent is `Z.pow 2 e`; with a `nat`-valued exponent
  (`8 * Z.of_nat k`) it is `2 ^ (8 * k)`.
- The Ltacs `step_pipeline` and `split_value_ifs` are not ported (proof scripts with no statement;
  the step lemmas are proved directly in Lean). Everything else is ported under its Rocq name.
-/

namespace LPS
open RiscvSemantics

/-! ## stdpp vocabulary and facts (not in `LPS/Stdpp.lean`) -/

/-- stdpp `bv_modulus n = 2 ^ n`. -/
def bv_modulus (n : Nat) : Int := ((2 ^ n : Nat) : Int)
/-- stdpp `bv_half_modulus n = bv_modulus n `div` 2`. -/
def bv_half_modulus (n : Nat) : Int := Z.div (bv_modulus n) 2
/-- stdpp `bv_swrap n z`: `z` into the signed range `[-2^(n-1), 2^(n-1))`. -/
def bv_swrap (n : Nat) (z : Int) : Int := bv_wrap n (z + bv_half_modulus n) - bv_half_modulus n

theorem bv_modulus_pos (n : Nat) : 0 < bv_modulus n := by
  unfold bv_modulus; exact_mod_cast Nat.two_pow_pos n

theorem bv_half_modulus_0 : bv_half_modulus 0 = 0 := by decide

theorem bv_half_modulus_twice (n : Nat) (h : n ≠ 0) : bv_modulus n = 2 * bv_half_modulus n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  unfold bv_half_modulus bv_modulus Z.div
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide), Nat.pow_succ, Int.natCast_mul]
  omega

theorem bv_wrap_eq (n : Nat) (z : Int) : bv_wrap n z = z % bv_modulus n := rfl

theorem bv_eq {n : Nat} (a b : bv n) (h : bv_unsigned a = bv_unsigned b) : a = b := by
  unfold bv_unsigned at h; exact BitVec.eq_of_toNat_eq (by omega)

theorem Z_to_bv_unsigned (n : Nat) (z : Int) : bv_unsigned (Z_to_bv n z) = bv_wrap n z := by
  unfold bv_unsigned Z_to_bv bv_wrap
  rw [BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by have := Nat.two_pow_pos n; omega))]

theorem bv_wrap_in_range (n : Nat) (z : Int) : 0 ≤ bv_wrap n z ∧ bv_wrap n z < bv_modulus n := by
  have h := bv_modulus_pos n
  unfold bv_modulus at h; unfold bv_wrap bv_modulus
  exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ h⟩

theorem bv_wrap_small (n : Nat) (z : Int) (h0 : 0 ≤ z) (h1 : z < bv_modulus n) : bv_wrap n z = z :=
  Int.emod_eq_of_lt h0 h1

theorem bv_unsigned_range {n : Nat} (b : bv n) : 0 ≤ bv_unsigned b ∧ bv_unsigned b < bv_modulus n :=
  bv_unsigned_in_range b

theorem bv_wrap_bv_unsigned {n : Nat} (b : bv n) : bv_wrap n (bv_unsigned b) = bv_unsigned b :=
  bv_wrap_small n _ (bv_unsigned_range b).1 (bv_unsigned_range b).2

theorem Z_to_bv_bv_unsigned {n : Nat} (b : bv n) : Z_to_bv n (bv_unsigned b) = b :=
  bv_eq _ _ (by rw [Z_to_bv_unsigned, bv_wrap_bv_unsigned])

theorem Z_to_bv_small (n : Nat) (z : Int) (h0 : 0 ≤ z) (h1 : z < bv_modulus n) :
    bv_unsigned (Z_to_bv n z) = z := by
  rw [Z_to_bv_unsigned, bv_wrap_small n z h0 h1]

theorem bv_wrap_wrap (n : Nat) (z : Int) : bv_wrap n (bv_wrap n z) = bv_wrap n z := Int.emod_emod _ _

theorem bv_wrap_add_idemp_l (n : Nat) (x y : Int) : bv_wrap n (bv_wrap n x + y) = bv_wrap n (x + y) :=
  Int.emod_add_emod _ _ _

theorem bv_wrap_add_idemp_r (n : Nat) (x y : Int) : bv_wrap n (x + bv_wrap n y) = bv_wrap n (x + y) :=
  Int.add_emod_emod _ _ _

theorem Z_to_bv_wrap (n : Nat) (z : Int) : Z_to_bv n (bv_wrap n z) = Z_to_bv n z :=
  bv_eq _ _ (by rw [Z_to_bv_unsigned, Z_to_bv_unsigned, bv_wrap_wrap])

theorem bv_add_unsigned {n : Nat} (a b : bv n) :
    bv_unsigned (a + b) = bv_wrap n (bv_unsigned a + bv_unsigned b) := by
  unfold bv_unsigned bv_wrap; rw [BitVec.toNat_add]; push_cast; rfl

theorem bv_mul_unsigned {n : Nat} (a b : bv n) :
    bv_unsigned (a * b) = bv_wrap n (bv_unsigned a * bv_unsigned b) := by
  unfold bv_unsigned bv_wrap; rw [BitVec.toNat_mul]; push_cast; rfl

theorem bv_sub_unsigned {n : Nat} (a b : bv n) :
    bv_unsigned (a - b) = bv_wrap n (bv_unsigned a - bv_unsigned b) := by
  have hb := b.isLt
  unfold bv_unsigned bv_wrap; rw [BitVec.toNat_sub, Int.natCast_emod, Int.natCast_add, Int.natCast_sub (by omega)]
  rw [show ((2 ^ n : Nat) : Int) - (b.toNat : Int) + (a.toNat : Int)
      = ((a.toNat : Int) - (b.toNat : Int)) + ((2 ^ n : Nat) : Int) * 1 by omega, Int.add_mul_emod_self_left]

/-- `bv_wrap` against `bv_modulus`, the form the `bv_swrap` proofs use. -/
theorem bv_wrap_mod_eq (n : Nat) (x y : Int) : bv_wrap n x = bv_wrap n y ↔ x % bv_modulus n = y % bv_modulus n :=
  Iff.rfl

theorem bv_swrap_wrap (n : Nat) (z : Int) : bv_swrap n (bv_wrap n z) = bv_swrap n z := by
  unfold bv_swrap; rw [bv_wrap_add_idemp_l]

/-- `bv_swrap` only depends on the argument mod `2^n` (PropExec.v:477, here because the signed-view
    lemmas below use it). -/
theorem bv_swrap_congr (n : Nat) (x y : Int) (H : bv_wrap n x = bv_wrap n y) : bv_swrap n x = bv_swrap n y := by
  unfold bv_swrap
  rw [← bv_wrap_add_idemp_l n x, H, bv_wrap_add_idemp_l]

theorem bv_swrap_small (n : Nat) (z : Int) (h0 : -bv_half_modulus n ≤ z) (h1 : z < bv_half_modulus n) :
    bv_swrap n z = z := by
  by_cases hn : n = 0
  · subst hn; rw [bv_half_modulus_0] at h0 h1; omega
  · have := bv_half_modulus_twice n hn
    unfold bv_swrap; rw [bv_wrap_small n _ (by omega) (by omega)]; omega

theorem bv_swrap_range (n : Nat) (z : Int) (hn : n ≠ 0) :
    -bv_half_modulus n ≤ bv_swrap n z ∧ bv_swrap n z < bv_half_modulus n := by
  have := bv_half_modulus_twice n hn
  have := bv_wrap_in_range n (z + bv_half_modulus n)
  unfold bv_swrap; omega

/-- stdpp `bv_swrap` is `Int.bmod` (Lean's balanced mod), which `BitVec.toInt` is stated with. -/
theorem bv_swrap_bmod (n : Nat) (z : Int) : bv_swrap n z = z.bmod (2 ^ n) := by
  rw [Int.bmod_def]
  have hM := bv_modulus_pos n
  change bv_swrap n z = if z % bv_modulus n < (bv_modulus n + 1) / 2 then z % bv_modulus n
    else z % bv_modulus n - bv_modulus n
  have hr := bv_wrap_in_range n z
  rw [bv_wrap_eq] at hr
  unfold bv_swrap
  rw [← bv_wrap_add_idemp_l, bv_wrap_eq, bv_wrap_eq]
  by_cases hn : n = 0
  · subst hn
    have h1 : bv_modulus 0 = 1 := rfl
    rw [bv_half_modulus_0, h1]; simp
  · have htw := bv_half_modulus_twice n hn
    have hh : (bv_modulus n + 1) / 2 = bv_half_modulus n := by omega
    rw [hh]
    split
    · rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
    · rw [show z % bv_modulus n + bv_half_modulus n
          = (z % bv_modulus n + bv_half_modulus n - bv_modulus n) + bv_modulus n * 1 by omega,
        Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
      omega

/-- stdpp `Z_to_bv_signed`. -/
theorem bv_signed_Z_to_bv (n : Nat) (z : Int) : bv_signed (Z_to_bv n z) = bv_swrap n z := by
  unfold bv_signed Z_to_bv; rw [BitVec.toInt_ofInt, bv_swrap_bmod]

/-- stdpp's definition of `bv_signed`. -/
theorem bv_signed_swrap {n : Nat} (b : bv n) : bv_signed b = bv_swrap n (bv_unsigned b) := by
  conv => lhs; rw [← Z_to_bv_bv_unsigned b]
  exact bv_signed_Z_to_bv n _

theorem bv_signed_range {n : Nat} (b : bv n) (hn : n ≠ 0) :
    -bv_half_modulus n ≤ bv_signed b ∧ bv_signed b < bv_half_modulus n := by
  rw [bv_signed_swrap]; exact bv_swrap_range n _ hn

theorem bv_extract0_unsigned {n : Nat} (len : Nat) (b : bv n) :
    bv_unsigned (bv_extract 0 len b) = bv_wrap len (bv_unsigned b) := by
  unfold bv_unsigned bv_extract bv_wrap
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Int.natCast_emod]

theorem bv_extract_unsigned {n : Nat} (lo len : Nat) (b : bv n) :
    bv_unsigned (bv_extract lo len b) = bv_wrap len (Z.shiftr (bv_unsigned b) lo) := by
  unfold bv_unsigned bv_extract bv_wrap Z.shiftr
  rw [BitVec.extractLsb'_toNat, Int.natCast_emod, Int.natCast_shiftRight]

theorem bv_extract0_signed {n : Nat} (len : Nat) (b : bv n) :
    bv_signed (bv_extract 0 len b) = bv_swrap len (bv_unsigned b) := by
  rw [bv_signed_swrap, bv_extract0_unsigned, bv_swrap_wrap]

theorem bv_sign_extend_unsigned {n : Nat} (m : Nat) (b : bv n) :
    bv_unsigned (bv_sign_extend m b) = bv_wrap m (bv_signed b) := Z_to_bv_unsigned _ _

theorem bv_zero_extend_unsigned {n : Nat} (m : Nat) (b : bv n) (h : n ≤ m) :
    bv_unsigned (bv_zero_extend m b) = bv_unsigned b := by
  unfold bv_zero_extend
  have := bv_unsigned_range b
  have : bv_modulus n ≤ bv_modulus m := by
    unfold bv_modulus; exact_mod_cast Nat.pow_le_pow_right (by decide) h
  exact Z_to_bv_small _ _ (by omega) (by omega)

theorem bv_half_modulus_mono (n m : Nat) (h : n ≤ m) : bv_half_modulus n ≤ bv_half_modulus m := by
  unfold bv_half_modulus Z.div
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide), Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  have : bv_modulus n ≤ bv_modulus m := by
    unfold bv_modulus; exact_mod_cast Nat.pow_le_pow_right (by decide) h
  omega

theorem bv_sign_extend_signed {n : Nat} (m : Nat) (b : bv n) (hn : n ≠ 0) (h : n ≤ m) :
    bv_signed (bv_sign_extend m b) = bv_signed b := by
  unfold bv_sign_extend
  rw [bv_signed_Z_to_bv]
  have := bv_signed_range b hn
  have := bv_half_modulus_mono n m h
  exact bv_swrap_small _ _ (by omega) (by omega)

/-! ### `Z.land`/`Z.lor`/`Z.lxor` on naturals -/

theorem Z.lor_natCast (m k : Nat) : Z.lor (m : Int) (k : Int) = ((m ||| k : Nat) : Int) := rfl
theorem Z.land_natCast (m k : Nat) : Z.land (m : Int) (k : Int) = ((m &&& k : Nat) : Int) := rfl
theorem Z.lxor_natCast (m k : Nat) : Z.lxor (m : Int) (k : Int) = ((m ^^^ k : Nat) : Int) := rfl

theorem Z.lor_0_r (z : Int) : Z.lor z 0 = z := by
  cases z with
  | ofNat m => show ((m ||| 0 : Nat) : Int) = _; rw [Nat.or_zero]; rfl
  | negSucc m => show Int.negSucc (m ^^^ (m &&& 0)) = _; rw [Nat.and_zero, Nat.xor_zero]

theorem Z.lor_comm (a b : Int) : Z.lor a b = Z.lor b a := by
  cases a <;> cases b <;> simp only [Z.lor, Nat.or_comm, Nat.and_comm]

theorem Z.shiftl_natCast (j k : Nat) : Z.shiftl (j : Int) k = ((j * 2 ^ k : Nat) : Int) := by
  unfold Z.shiftl; push_cast; rfl

theorem Z.shiftl_0_l (k : Nat) : Z.shiftl 0 k = 0 := by unfold Z.shiftl; simp

/-- The disjoint `lor` of a low part and a shifted high part is their sum. -/
theorem lor_shiftl_add (x y : Int) (k : Nat) (hx0 : 0 ≤ x) (hx1 : x < (2 ^ k : Nat)) (hy : 0 ≤ y) :
    Z.lor x (Z.shiftl y k) = x + y * (2 ^ k : Nat) := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hx0
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hy
  rw [Z.shiftl_natCast, Z.lor_natCast, Nat.or_comm, Nat.mul_comm,
    ← Nat.two_pow_add_eq_or_of_lt (by omega) j]
  push_cast; rw [Int.mul_comm]; omega

/-! ## State constructors and register helpers (PropExec.v:24-65) -/

/-- PropExec.v:43. The FP register file and fcsr, which integer instructions preserve. -/
class FPState where
  mkFP ::
  fp_regs : bvmap 5 word
  fp_csr : bv 32

export FPState (fp_regs fp_csr)

/-- PropExec.v:44. The FP state at process entry. -/
@[instance_reducible] def fx0 : FPState := FPState.mkFP bvmap_empty (Z_to_bv 32 0)

/-- PropExec.v:46. The state shape every per-instruction step lemma is stated at: no pending syscall,
    no reservation, the ambient FP state. -/
def mkst [FPState] (regs : bvmap 5 word) (pc : word) (mem rom : word → Option byte) : machine_state :=
  { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := none, ms_resv := none,
    ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom }

/-- PropExec.v:59. Mirrors `Sem.rget` (x0 reads 0, missing keys 0). -/
def getr (regs : bvmap 5 word) (r : reg) : word :=
  if bv_eqb r 0 then Z_to_bv 64 0 else reg_get regs r
/-- PropExec.v:61. -/
def regupd (regs : bvmap 5 word) (r : reg) (v : word) : bvmap 5 word :=
  bvmap_set r v regs

/-! ## Small conversion helpers (PropExec.v:64-100) -/

theorem bv_eqb0_is_x0 (r : reg) : bv_eqb r 0 = is_x0 r := by
  unfold bv_eqb is_x0; rw [show bv_unsigned (0 : reg) = 0 from rfl]
  cases h : bv_unsigned r == 0 <;> simp_all

theorem is_x0_0 : is_x0 0 = true := rfl

theorem bv_wrap64_mod (z : Int) : bv_wrap 64 z = z % 2 ^ 64 := rfl

theorem bv_wrap32_mod (z : Int) : bv_wrap 32 z = z % 2 ^ 32 := rfl

theorem bv_eqb_refl {n : Nat} (a : bv n) : bv_eqb a a = true := by
  unfold bv_eqb; simp

theorem bv_eqb_neq {n : Nat} (a b : bv n) (Hne : a ≠ b) : bv_eqb a b = false := by
  unfold bv_eqb; simp only [decide_eq_false_iff_not]
  exact fun h => Hne (bv_eq a b h)

/-- PropExec.v:95. The argument registers of the raw ecall record, as `reg` indices. -/
theorem arg_reg_0 : Z_to_bv 5 (10 + ((0 : Nat) : Int)) = (10 : reg) := by decide
theorem arg_reg_1 : Z_to_bv 5 (10 + ((1 : Nat) : Int)) = (11 : reg) := by decide
theorem arg_reg_2 : Z_to_bv 5 (10 + ((2 : Nat) : Int)) = (12 : reg) := by decide

/-! ## Z-level range/bit helpers (PropExec.v:102-180) -/

theorem Z_testbit_high (n a k : Int) (Hn : 0 ≤ n) (Ha : 0 ≤ a ∧ a < Z.pow 2 n) (Hk : n ≤ k) :
    Z.testbit a k = false := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le Ha.1
  obtain ⟨n', rfl⟩ := Int.eq_ofNat_of_zero_le Hn
  have hlt : m < 2 ^ n' := by
    have := Ha.2
    simp only [Z.pow, show ¬ ((n' : Int) < 0) by omega, ↓reduceIte, Int.toNat_natCast] at this
    exact_mod_cast this
  unfold Z.testbit
  simp only [show ¬ (k < 0) by omega, ↓reduceIte]
  show m.testBit k.toNat = false
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega)))

theorem Z_bounded_by_bits (n a : Int) (Hn : 0 ≤ n) (Ha : 0 ≤ a)
    (Hb : ∀ k, n ≤ k → Z.testbit a k = false) : a < Z.pow 2 n := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le Ha
  obtain ⟨n', rfl⟩ := Int.eq_ofNat_of_zero_le Hn
  have : m < 2 ^ n' := Nat.lt_pow_two_of_testBit m fun i hi => by
    have := Hb (i : Int) (by omega)
    unfold Z.testbit at this; simp only [show ¬ ((i : Int) < 0) by omega, ↓reduceIte] at this
    exact this
  simp only [Z.pow, show ¬ ((n' : Int) < 0) by omega, ↓reduceIte, Int.toNat_natCast]
  exact_mod_cast this

theorem Z_land_range (a b : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 64) (Hb : 0 ≤ b) :
    0 ≤ Z.land a b ∧ Z.land a b < 2 ^ 64 := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le Ha.1
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le Hb
  rw [Z.land_natCast, Nat.and_comm]
  have : m < 2 ^ 64 := by have := Ha.2; omega
  have := Nat.and_lt_two_pow j this
  omega

theorem Z_lor_range (a b : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 64) (Hb : 0 ≤ b ∧ b < 2 ^ 64) :
    0 ≤ Z.lor a b ∧ Z.lor a b < 2 ^ 64 := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le Ha.1
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le Hb.1
  rw [Z.lor_natCast]
  have := @Nat.or_lt_two_pow m j 64 (by have := Ha.2; omega) (by have := Hb.2; omega)
  omega

theorem Z_lxor_range (a b : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 64) (Hb : 0 ≤ b ∧ b < 2 ^ 64) :
    0 ≤ Z.lxor a b ∧ Z.lxor a b < 2 ^ 64 := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le Ha.1
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le Hb.1
  rw [Z.lxor_natCast]
  have := @Nat.xor_lt_two_pow m j 64 (by have := Ha.2; omega) (by have := Hb.2; omega)
  omega

theorem Z_shiftr_range (a k : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 64) (Hk : 0 ≤ k) :
    0 ≤ Z.shiftrZ a k ∧ Z.shiftrZ a k < 2 ^ 64 := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le Ha.1
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le Hk
  unfold Z.shiftrZ
  cases j with
  | zero => simp [Z.shiftlZ]; omega
  | succ j =>
    rw [show -((j + 1 : Nat) : Int) = Int.negSucc j by rfl]
    simp only [Z.shiftlZ]
    rw [Int.shiftRight_eq_div_pow]
    have := @Int.ediv_le_self (m : Int) (((2 ^ (j + 1) : Nat) : Int)) (Int.natCast_nonneg m)
    have := Int.ediv_nonneg (Int.natCast_nonneg m) (Int.natCast_nonneg (2 ^ (j + 1)))
    omega

/-- `bv_swrap` absorbs an inner `bv_wrap` on either summand. -/
theorem bv_swrap_add_idemp_l (n : Nat) (x y : Int) : bv_swrap n (bv_wrap n x + y) = bv_swrap n (x + y) :=
  bv_swrap_congr _ _ _ (bv_wrap_add_idemp_l _ _ _)

theorem bv_swrap_add_idemp_r (n : Nat) (x y : Int) : bv_swrap n (x + bv_wrap n y) = bv_swrap n (x + y) :=
  bv_swrap_congr _ _ _ (bv_wrap_add_idemp_r _ _ _)

theorem bv_swrap_wrap' (n : Nat) (z : Int) : bv_swrap n (bv_wrap n z) = bv_swrap n z := bv_swrap_wrap n z

/-! ## Value shapes (PropExec.v:180-290): `Z` normal forms over `bv_unsigned`/`bv_signed` -/

/-- Signed view of a register value. -/
def zsig (x : word) : Int := bv_signed x

def v_addi (x : word) (imm : Int) : word := Z_to_bv 64 (bv_unsigned x + imm)
def v_add (x y : word) : word := Z_to_bv 64 (bv_unsigned x + bv_unsigned y)
def v_sub (x y : word) : word := Z_to_bv 64 (bv_unsigned x - bv_unsigned y)
def v_mul (x y : word) : word := Z_to_bv 64 (bv_unsigned x * bv_unsigned y)
def v_andi (x : word) (imm : Int) : word := Z_to_bv 64 (Z.land (bv_unsigned x) (bv_wrap 64 imm))
def v_ori (x : word) (imm : Int) : word := Z_to_bv 64 (Z.lor (bv_unsigned x) (bv_wrap 64 imm))
def v_xori (x : word) (imm : Int) : word := Z_to_bv 64 (Z.lxor (bv_unsigned x) (bv_wrap 64 imm))
def v_and (x y : word) : word := Z_to_bv 64 (Z.land (bv_unsigned x) (bv_unsigned y))
def v_or (x y : word) : word := Z_to_bv 64 (Z.lor (bv_unsigned x) (bv_unsigned y))
def v_xor (x y : word) : word := Z_to_bv 64 (Z.lxor (bv_unsigned x) (bv_unsigned y))

def c_eq (x y : word) : Bool := bv_eqb x y
def c_lts (x y : word) : Bool := bv_lts x y
def c_ltu (x y : word) : Bool := bv_ltu x y

def btgt (pc : word) (imm : Int) : word := v_addi pc imm

/-! comparisons: 0/1 results -/
def v_slti (x : word) (imm : Int) : word :=
  if decide (zsig x < imm) then Z_to_bv 64 1 else Z_to_bv 64 0
def v_sltiu (x : word) (imm : Int) : word :=
  if decide (bv_unsigned x < bv_wrap 64 imm) then Z_to_bv 64 1 else Z_to_bv 64 0
def v_slt (x y : word) : word := if c_lts x y then Z_to_bv 64 1 else Z_to_bv 64 0
def v_sltu (x y : word) : word := if c_ltu x y then Z_to_bv 64 1 else Z_to_bv 64 0

/-! immediate shifts (the shift amount is the 6-bit shamt, as `Z`) -/
def v_slli (x : word) (sh : Int) : word := Z_to_bv 64 (Z.shiftlZ (bv_unsigned x) sh)
def v_srli (x : word) (sh : Int) : word := Z_to_bv 64 (Z.shiftrZ (bv_unsigned x) sh)
def v_srai (x : word) (sh : Int) : word := Z_to_bv 64 (Z.shiftrZ (bv_signed x) sh)

/-! register shifts (the shift amount is the rs2 value mod 64) -/
def v_sll (x y : word) : word := Z_to_bv 64 (Z.shiftlZ (bv_unsigned x) (Z.modulo (bv_unsigned y) 64))
def v_srl (x y : word) : word := Z_to_bv 64 (Z.shiftrZ (bv_unsigned x) (Z.modulo (bv_unsigned y) 64))
def v_sra (x y : word) : word := Z_to_bv 64 (Z.shiftrZ (bv_signed x) (Z.modulo (bv_unsigned y) 64))

/-! upper immediates: `imm` is the ALREADY-SHIFTED signed U-immediate -/
def v_lui (imm : Int) : word := Z_to_bv 64 imm
def v_auipc (pc : word) (imm : Int) : word := Z_to_bv 64 (imm + bv_unsigned pc)

/-! RV64 word ops: compute in 32 bits, sign-extend to 64 -/
def v_addiw (x : word) (imm : Int) : word := Z_to_bv 64 (bv_swrap 32 (bv_unsigned x + imm))
def v_slliw (x : word) (sh : Int) : word := Z_to_bv 64 (bv_swrap 32 (Z.shiftlZ (bv_unsigned x) sh))
def v_srliw (x : word) (sh : Int) : word :=
  Z_to_bv 64 (bv_swrap 32 (Z.shiftrZ (bv_wrap 32 (bv_unsigned x)) sh))
def v_sraiw (x : word) (sh : Int) : word :=
  Z_to_bv 64 (bv_swrap 32 (Z.shiftrZ (bv_swrap 32 (bv_unsigned x)) sh))
def v_addw (x y : word) : word := Z_to_bv 64 (bv_swrap 32 (bv_unsigned x + bv_unsigned y))
def v_subw (x y : word) : word := Z_to_bv 64 (bv_swrap 32 (bv_unsigned x - bv_unsigned y))
def v_sllw (x y : word) : word :=
  Z_to_bv 64 (bv_swrap 32 (Z.shiftlZ (bv_unsigned x) (Z.modulo (bv_unsigned y) 32)))
def v_srlw (x y : word) : word :=
  Z_to_bv 64 (bv_swrap 32 (Z.shiftrZ (bv_wrap 32 (bv_unsigned x)) (Z.modulo (bv_unsigned y) 32)))
def v_sraw (x y : word) : word :=
  Z_to_bv 64 (bv_swrap 32 (Z.shiftrZ (bv_swrap 32 (bv_unsigned x)) (Z.modulo (bv_unsigned y) 32)))

/-! high multiplies -/
def v_mulh (x y : word) : word := Z_to_bv 64 (Z.shiftr (bv_signed x * bv_signed y) 64)
def v_mulhsu (x y : word) : word := Z_to_bv 64 (Z.shiftr (bv_signed x * bv_unsigned y) 64)
def v_mulhu (x y : word) : word := Z_to_bv 64 (Z.shiftr (bv_unsigned x * bv_unsigned y) 64)
def v_mulw (x y : word) : word := Z_to_bv 64 (bv_swrap 32 (bv_unsigned x * bv_unsigned y))

/-! division family: only the divide-by-zero split remains -/
def v_div (x y : word) : word :=
  if bv_unsigned y == 0 then Z_to_bv 64 (-1) else Z_to_bv 64 (Z.quot (zsig x) (zsig y))
def v_rem (x y : word) : word :=
  if bv_unsigned y == 0 then x else Z_to_bv 64 (Z.rem (zsig x) (zsig y))
def v_divw (x y : word) : word :=
  if bv_wrap 32 (bv_unsigned y) == 0 then Z_to_bv 64 (-1)
  else Z_to_bv 64 (bv_swrap 32 (Z.quot (bv_swrap 32 (bv_unsigned x)) (bv_swrap 32 (bv_unsigned y))))
def v_remw (x y : word) : word :=
  if bv_wrap 32 (bv_unsigned y) == 0 then Z_to_bv 64 (bv_swrap 32 (bv_unsigned x))
  else Z_to_bv 64 (bv_swrap 32 (Z.rem (bv_swrap 32 (bv_unsigned x)) (bv_swrap 32 (bv_unsigned y))))
def v_divuw (x y : word) : word :=
  if bv_wrap 32 (bv_unsigned y) == 0 then Z_to_bv 64 (-1)
  else Z_to_bv 64 (bv_swrap 32 (Z.div (bv_wrap 32 (bv_unsigned x)) (bv_wrap 32 (bv_unsigned y))))
def v_remuw (x y : word) : word :=
  if bv_wrap 32 (bv_unsigned y) == 0 then Z_to_bv 64 (bv_swrap 32 (bv_unsigned x))
  else Z_to_bv 64 (bv_swrap 32 (Z.modulo (bv_wrap 32 (bv_unsigned x)) (bv_wrap 32 (bv_unsigned y))))

/-! signed-load register results -/
def v_lb (b : byte) : word := Z_to_bv 64 (bv_signed b)
def v_lh (v : word) : word := Z_to_bv 64 (bv_swrap 16 (bv_unsigned v))
def v_lw (v : word) : word := Z_to_bv 64 (bv_swrap 32 (bv_unsigned v))

/-! jalr target: (rs1 + imm) with bit 0 cleared -/
def jalr_tgtZ (x : word) (imm : Int) : Int := Z.land (bv_unsigned x + imm) (-2)
def jalr_tgt (x : word) (imm : Int) : word := Z_to_bv 64 (jalr_tgtZ x imm)

end LPS

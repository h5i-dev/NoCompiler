import Examples.Libc.Musl.MemsetImg
import NoCompiler.Libc.Place
import NoCompiler.Auto
import NoCompiler.Libc.Mem
import NoCompiler.Libc.Word
import NoCompiler.Lib.Rw

/-!
# `memset` (musl src/string/memset.c), at the state level, by `nocompiler_auto`
-/
namespace NoCompiler.Libc.Musl.Memset
open NoCompiler NoCompiler.Libc.Musl.MemsetImg

/-- `memset(d, c, n)` for `n ≥ 32`: returns `d` and writes nothing outside `[d, d + n)` (the bytes it
    writes there are not stated: no proof on the path reads them yet). On slen's path its one caller is
    `__init_libc`, zeroing `aux[AUX_CNT]`: 38 words, 304 bytes. The mask lemmas below are proved by
    arithmetic (NoCompiler.Lib), not `bv_decide`. -/
def memsetSpec : Spec (Word × Nat) where
  pre := fun ⟨d, n⟩ s => s.reg Reg.a0 = d ∧ s.reg Reg.a2 = BitVec.ofNat 64 n ∧ 32 ≤ n ∧ n < 2 ^ 63 ∧
    d.toNat + n < 2 ^ 64
  post := fun ⟨d, _⟩ _ s' => s'.reg Reg.a0 = d
  writes := fun ⟨d, n⟩ _ => [⟨d, n⟩]


theorem toNat_and3 (x : Word) : (x &&& 3#64).toNat = x.toNat % 4 := by
  rw [BitVec.toNat_and]
  have : (3#64).toNat = 2 ^ 2 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

/-- memset's alignment step: `(0 - d) & 3` (in 32 bits, sign-extended) is what rounds `d` up to 4. -/
theorem subw0_and3 (d : Word) : evalRW RWOp.subw 0#64 d &&& 3#64 = (0#64 - d) &&& 3#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_and3, toNat_and3]
  simp only [evalRW, w32]
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_sub,
    BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have := d.isLt
  split <;> simp <;> omega

theorem toNat_r (d : Word) : (evalRW RWOp.subw 0#64 d &&& 3#64).toNat = (4 - d.toNat % 4) % 4 := by
  rw [subw0_and3, toNat_and3, BitVec.toNat_sub]; simp; omega

theorem toNat_andneg4 (y : Word) : (y &&& 18446744073709551612#64).toNat = y.toNat - y.toNat % 4 := by
  have e : (18446744073709551612#64 : Word) = ~~~BitVec.ofNat 64 (2 ^ 2 - 1) := by decide
  rw [e, Lib.toNat_and_not_mask y (by decide)]

/-- memset's step to an 8-byte boundary: `(x & 4) | 24` is 24 or 28. -/
theorem toNat_and4_or24 (x : Word) : ((x &&& 4#64) ||| 24#64).toNat = x.toNat % 8 - x.toNat % 4 + 24 := by
  rw [BitVec.toNat_or, BitVec.toNat_and]
  show (x.toNat &&& 4) ||| 24 = _
  have e : x.toNat &&& 4 = (x.toNat &&& (2 ^ 3 - 1)) &&& 4 := by rw [Nat.and_assoc]; rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod, show x.toNat % 4 = x.toNat % 8 % 4 from
    (Nat.mod_mod_of_dvd _ (by decide)).symm]
  have hr : x.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize x.toNat % 8 = r at *
  revert r; decide

theorem memset_perm {s : State} {d a : Word} {n w : Nat} (h : (a - d).toNat + w ≤ n) :
    (memsetSpec.perm (d, n) s).canWrite a w :=
  .inr ⟨⟨d, n⟩, by simp [Spec.perm, memsetSpec], h⟩

theorem memset_verified : VerifiedImg img dom base memsetSpec := by
  rintro ⟨d, n⟩ s he ⟨ha0, ha2, h32, hn, hd⟩
  nocompiler_auto memset_func s he
    loop_inv $l1 (fun u => ∃ k, u.reg 13 = d + BitVec.ofNat 64 k ∧ k + (u.reg 12).toNat ≤ n ∧
        32 ≤ (u.reg 12).toNat ∧ (u.reg 13).toNat % 8 = 0 ∧ u.reg 10 = d ∧ u.reg 14 = 31#64)
      measure (fun u => (u.reg 12).toNat)
  all_goals (try (
    apply memset_perm
    simp only [BitVec.ult, decide_eq_false_iff_not, decide_eq_true_eq, Bool.not_eq_true, Reg.a0, Reg.a2,
      Bool.false_eq_true, not_false_eq_true, beq_eq_false_iff_ne, bne_iff_ne, ne_eq, beq_iff_eq] at *
    subst ha0
    rw [ha2] at *
    have hr := toNat_r (s.reg 10)
    have hL := toNat_andneg4 (BitVec.ofNat 64 n - (evalRW RWOp.subw 0#64 (s.reg 10) &&& 3#64))
    simp only [aligned] at *
    bv_omega))
  all_goals (try (
    simp only [BitVec.ult, decide_eq_false_iff_not, decide_eq_true_eq, Bool.not_eq_true, Reg.a0, Reg.a2,
      Bool.false_eq_true, not_false_eq_true, beq_eq_false_iff_ne, bne_iff_ne, ne_eq, beq_iff_eq] at *
    subst ha0
    rw [ha2] at *
    have hr := toNat_r (s.reg 10)
    have hL := toNat_andneg4 (BitVec.ofNat 64 n - (evalRW RWOp.subw 0#64 (s.reg 10) &&& 3#64))
    simp only [aligned] at *
    bv_omega))
  case entry_to_l1 =>
    have hr : (w32 (fun x1 x2 => x1 - x2) (0#64) d &&& 3#64).toNat = (4 - d.toNat % 4) % 4 := toNat_r d
    have hm := toNat_and4_or24 (d + (w32 (fun x1 x2 => x1 - x2) (0#64) d &&& 3#64))
    have hL := toNat_andneg4 (BitVec.ofNat 64 n - (w32 (fun x1 x2 => x1 - x2) (0#64) d &&& 3#64))
    simp only [BitVec.ult, decide_eq_false_iff_not, Bool.not_eq_true] at hb_12ab4 hb_12a80
    refine ⟨(w32 (fun x1 x2 => x1 - x2) (0#64) d &&& 3#64).toNat +
      ((d + (w32 (fun x1 x2 => x1 - x2) (0#64) d &&& 3#64) &&& 4#64 ||| 24#64)).toNat, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try rfl) <;> bv_omega

end NoCompiler.Libc.Musl.Memset

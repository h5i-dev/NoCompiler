import NoCompiler.Lib.LE

/-!
# Library: loop counters as words

The steps of a counting loop over a 64-bit counter: below its bound (`ult i n`) an increment does
not wrap; leaving the loop (`¬ ult i n`) with the counter never past the bound means it reached
the bound; a non-zero counter decrements without wrap and a count-down loop ends at zero; and a
pointer stepped by `w` per iteration is `base + w * count`. Namespace `NoCompiler.Lib`. Round 7,
B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

/-- Below the bound, `i + 1` does not wrap. -/
theorem toNat_succ_of_ult {i n : Word} (h : BitVec.ult i n = true) : (i + 1).toNat = i.toNat + 1 := by
  rw [ult_iff, decide_eq_true_eq] at h
  have := n.isLt
  rw [BitVec.toNat_add]; simp; omega

/-- Leaving the loop with the counter never past the bound: the counter is the bound. -/
theorem eq_of_not_ult_of_le {i n : Word} (h : BitVec.ult i n = false) (hle : i.toNat ≤ n.toNat) :
    i = n := by
  rw [ult_iff] at h
  simp at h
  exact BitVec.eq_of_toNat_eq (by omega)

/-- A loop exit by `i = n` (`beq`/`bne` on the counter). -/
theorem toNat_eq_of_eq {i n : Word} (h : i = n) : i.toNat = n.toNat := h ▸ rfl

/-- A non-zero counter decrements without wrap. -/
theorem toNat_pred_of_ne {i : Word} (h : i ≠ 0) : (i - 1).toNat = i.toNat - 1 := by
  have h0 : i.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
  exact toNat_sub_of_le (by simp; omega)

/-- A counter that was `k` steps from `n` is one step closer after an increment. -/
theorem sub_succ_of_ult {i n : Word} (h : BitVec.ult i n = true) :
    n.toNat - (i + 1).toNat = n.toNat - i.toNat - 1 := by
  rw [toNat_succ_of_ult h]; omega

/-- A pointer stepped by `w` bytes per iteration, after `k` iterations. -/
theorem ptr_step (base : Word) (w k : Nat) :
    base + BitVec.ofNat 64 (w * k) + BitVec.ofNat 64 w = base + BitVec.ofNat 64 (w * (k + 1)) := by
  rw [add_ofNat_add_ofNat, Nat.mul_succ]

/-- A pointer stepped by one byte, after `k` iterations. -/
theorem ptr_step_one (base : Word) (k : Nat) :
    base + BitVec.ofNat 64 k + 1 = base + BitVec.ofNat 64 (k + 1) := by
  apply BitVec.eq_of_toNat_eq; simp; omega

/-- The counter as the number of iterations: `i = ofNat k` with `k < 2^64` has value `k`. -/
theorem toNat_counter {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k).toNat = k :=
  toNat_ofNat_of_lt h

/-- Incrementing the counter `ofNat k`. -/
theorem counter_succ (k : Nat) : BitVec.ofNat 64 k + 1 = BitVec.ofNat 64 (k + 1) := by
  apply BitVec.eq_of_toNat_eq; simp

end NoCompiler.Lib

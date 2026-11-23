import NoCompiler.Lib.CopyLoop

/-!
# Library: the strlen loop

The pieces of a proof of a loop that walks a pointer `p = s + k` to a string's terminator: the
invariant "no zero byte before offset `k`", its step on a non-zero byte, the `CStr` it gives at the
zero byte, the length as `p - s`, and the measure `n - k` that the loop decreases on a string of
length `n`. Namespace `NoCompiler.Lib`. Round 7, B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

/-- The scan's invariant: no zero byte before offset `k`. -/
def NoZeroBefore (m : Word → Byte) (s : Word) (k : Nat) : Prop :=
  ∀ i, i < k → m (s + BitVec.ofNat 64 i) ≠ 0

theorem noZeroBefore_zero (m : Word → Byte) (s : Word) : NoZeroBefore m s 0 :=
  fun _ h => absurd h (Nat.not_lt_zero _)

/-- The step: a non-zero byte at `k` extends the invariant to `k + 1`. -/
theorem NoZeroBefore.step {m : Word → Byte} {s : Word} {k : Nat} (h : NoZeroBefore m s k)
    (hk : m (s + BitVec.ofNat 64 k) ≠ 0) : NoZeroBefore m s (k + 1) :=
  forall_lt_succ.2 ⟨h, hk⟩

/-- The end: a zero byte at `k` makes a string of length `k`. -/
theorem NoZeroBefore.cstr {m : Word → Byte} {s : Word} {k : Nat} (h : NoZeroBefore m s k)
    (hk : m (s + BitVec.ofNat 64 k) = 0) : CStr m s k := ⟨h, hk⟩

/-- On a string of length `n`, the invariant holds only up to `n`. -/
theorem NoZeroBefore.le {m : Word → Byte} {s : Word} {k n : Nat} (h : NoZeroBefore m s k)
    (hs : CStr m s n) : k ≤ n := by
  rcases Nat.lt_or_ge n k with hl | hl
  · exact absurd hs.nul (h n hl)
  · exact hl

/-- A string's own bytes give the invariant up to its length. -/
theorem CStr.noZeroBefore {m : Word → Byte} {s : Word} {n : Nat} (hs : CStr m s n) :
    NoZeroBefore m s n := hs.1

/-- The length the loop returns: the end pointer minus the start. -/
theorem ptr_sub_start (s : Word) {k : Nat} (h : k < 2 ^ 64) :
    (s + BitVec.ofNat 64 k - s).toNat = k := by
  rw [add_ofNat_sub_self, toNat_ofNat_of_lt h]

/-- The loop's measure decreases: on a string of length `n`, a non-zero byte at `k` means `k < n`. -/
theorem lt_len_of_ne_zero {m : Word → Byte} {s : Word} {k n : Nat} (hs : CStr m s n)
    (hinv : NoZeroBefore m s k) (hk : m (s + BitVec.ofNat 64 k) ≠ 0) : k < n := by
  have hle := hinv.le hs
  rcases Nat.lt_or_ge k n with h | h
  · exact h
  · exact absurd (by rw [show k = n by omega]; exact hs.nul) hk

/-- A zero byte found at `k` on a string of length `n`: `k = n`. -/
theorem eq_len_of_zero {m : Word → Byte} {s : Word} {k n : Nat} (hs : CStr m s n)
    (hinv : NoZeroBefore m s k) (hk : m (s + BitVec.ofNat 64 k) = 0) : k = n :=
  (hinv.cstr hk).unique hs

end NoCompiler.Lib

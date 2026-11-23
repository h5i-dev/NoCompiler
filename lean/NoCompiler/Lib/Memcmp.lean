import NoCompiler.Lib.Strlen

/-!
# Library: comparing byte ranges

`FirstDiff m a b k`: the ranges at `a` and `b` agree below offset `k` and differ at `k`. The
facts a `memcmp`/`strcmp` proof needs: the first difference is unique, equal ranges have none
below their length, the compare loop's invariant (equal so far) and its two exits (equal one
further, or a first difference found), and the result's sign as the comparison of the two
differing bytes. Namespace `NoCompiler.Lib`. Round 7, B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

/-- The ranges agree below `k`. -/
def EqBefore (m : Word → Byte) (a b : Word) (k : Nat) : Prop :=
  ∀ i, i < k → m (a + BitVec.ofNat 64 i) = m (b + BitVec.ofNat 64 i)

/-- The ranges agree below `k` and differ at `k`. -/
def FirstDiff (m : Word → Byte) (a b : Word) (k : Nat) : Prop :=
  EqBefore m a b k ∧ m (a + BitVec.ofNat 64 k) ≠ m (b + BitVec.ofNat 64 k)

theorem eqBefore_zero (m : Word → Byte) (a b : Word) : EqBefore m a b 0 :=
  fun _ h => absurd h (Nat.not_lt_zero _)

/-- The compare loop's step on equal bytes. -/
theorem EqBefore.step {m : Word → Byte} {a b : Word} {k : Nat} (h : EqBefore m a b k)
    (hk : m (a + BitVec.ofNat 64 k) = m (b + BitVec.ofNat 64 k)) : EqBefore m a b (k + 1) :=
  forall_lt_succ.2 ⟨h, hk⟩

/-- The compare loop's other exit: differing bytes at `k` are the first difference. -/
theorem EqBefore.firstDiff {m : Word → Byte} {a b : Word} {k : Nat} (h : EqBefore m a b k)
    (hk : m (a + BitVec.ofNat 64 k) ≠ m (b + BitVec.ofNat 64 k)) : FirstDiff m a b k := ⟨h, hk⟩

/-- Agreement below `n` is equality of the bytes read. -/
theorem eqBefore_iff_readBytes (m : Word → Byte) (a b : Word) (n : Nat) :
    EqBefore m a b n ↔ readBytes m a n = readBytes m b n :=
  (readBytes_eq_iff m m a b n).symm

/-- The first difference is unique. -/
theorem FirstDiff.unique {m : Word → Byte} {a b : Word} {k k' : Nat} (h : FirstDiff m a b k)
    (h' : FirstDiff m a b k') : k = k' := by
  rcases Nat.lt_trichotomy k k' with hl | he | hl
  · exact absurd (h'.1 k hl) h.2
  · exact he
  · exact absurd (h.1 k' hl) h'.2

/-- Equal ranges have no difference below their length. -/
theorem not_firstDiff_of_eq {m : Word → Byte} {a b : Word} {n k : Nat}
    (h : readBytes m a n = readBytes m b n) (hk : k < n) : ¬ FirstDiff m a b k :=
  fun hd => hd.2 ((eqBefore_iff_readBytes m a b n).2 h k hk)

/-- A first difference below `n`: the ranges differ. -/
theorem FirstDiff.readBytes_ne {m : Word → Byte} {a b : Word} {k n : Nat} (h : FirstDiff m a b k)
    (hk : k < n) : readBytes m a n ≠ readBytes m b n :=
  fun he => not_firstDiff_of_eq he hk h

/-- The sign of `memcmp`: the differing bytes compare as unsigned numbers, and they are unequal. -/
theorem FirstDiff.lt_or_gt {m : Word → Byte} {a b : Word} {k : Nat} (h : FirstDiff m a b k) :
    (m (a + BitVec.ofNat 64 k)).toNat < (m (b + BitVec.ofNat 64 k)).toNat ∨
      (m (b + BitVec.ofNat 64 k)).toNat < (m (a + BitVec.ofNat 64 k)).toNat := by
  have hne : (m (a + BitVec.ofNat 64 k)).toNat ≠ (m (b + BitVec.ofNat 64 k)).toNat :=
    fun e => h.2 (BitVec.eq_of_toNat_eq e)
  omega

end NoCompiler.Lib

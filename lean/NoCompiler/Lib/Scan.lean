import NoCompiler.Lib.Bits

/-!
# Library: loops that scan bytes

The invariant steps of a loop that walks one or two byte ranges (`memcmp`, `memchr`, `strcmp`, a
search for a byte): the first `k + 1` bytes are the first `k` and one more, a property of every
byte so far extends by one, two ranges equal so far stay equal while the next bytes agree, and
the first difference decides. Namespace `NoCompiler.Lib`. Round 7, B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

/-- The first `k + 1` bytes: the first `k`, then the byte at offset `k`. -/
theorem readBytes_snoc (m : Word → Byte) (a : Word) (k : Nat) :
    readBytes m a (k + 1) = readBytes m a k ++ [m (a + BitVec.ofNat 64 k)] := by
  rw [← readBytes_append m a k 1]; simp

/-- A property of every byte so far, extended by the next. -/
theorem forall_lt_succ {p : Nat → Prop} {k : Nat} :
    (∀ i, i < k + 1 → p i) ↔ (∀ i, i < k → p i) ∧ p k :=
  ⟨fun h => ⟨fun i hi => h i (by omega), h k (by omega)⟩,
   fun ⟨h, hk⟩ i hi => if e : i = k then e ▸ hk else h i (by omega)⟩

/-- Every byte of a range satisfies `p` exactly when every byte read does. -/
theorem forall_readBytes_iff (m : Word → Byte) (a : Word) (n : Nat) (p : Byte → Prop) :
    (∀ b ∈ readBytes m a n, p b) ↔ ∀ i, i < n → p (m (a + BitVec.ofNat 64 i)) := by
  constructor
  · intro h i hi
    have := h _ (List.getElem_mem (by rw [length_readBytes]; exact hi) : (readBytes m a n)[i]'(by rw [length_readBytes]; exact hi) ∈ _)
    rwa [readBytes_getElem m a hi] at this
  · intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have hi' : i < n := by simpa [length_readBytes] using hi
    rw [readBytes_getElem m a hi']; exact h i hi'

/-- Two ranges read the same exactly when they agree byte by byte. -/
theorem readBytes_eq_iff (m m' : Word → Byte) (a b : Word) (n : Nat) :
    readBytes m a n = readBytes m' b n ↔
      ∀ i, i < n → m (a + BitVec.ofNat 64 i) = m' (b + BitVec.ofNat 64 i) := by
  constructor
  · intro h i hi
    have := congrArg (fun l => l[i]?) h
    rw [List.getElem?_eq_getElem (by rw [length_readBytes]; exact hi),
      List.getElem?_eq_getElem (by rw [length_readBytes]; exact hi), Option.some.injEq,
      readBytes_getElem _ _ hi, readBytes_getElem _ _ hi] at this
    exact this
  · intro h
    apply List.ext_getElem (by simp [length_readBytes])
    intro i h1 _
    rw [length_readBytes] at h1
    rw [readBytes_getElem _ _ h1, readBytes_getElem _ _ h1]; exact h i h1

/-- Equal so far, and the next bytes agree: equal one further (the loop step of `memcmp`). -/
theorem readBytes_eq_succ {m m' : Word → Byte} {a b : Word} {k : Nat}
    (h : readBytes m a k = readBytes m' b k)
    (hk : m (a + BitVec.ofNat 64 k) = m' (b + BitVec.ofNat 64 k)) :
    readBytes m a (k + 1) = readBytes m' b (k + 1) := by
  rw [readBytes_snoc, readBytes_snoc, h, hk]

/-- Equal so far, and the next bytes differ: the ranges differ (from `k + 1` bytes on). -/
theorem readBytes_ne_of_first_diff {m m' : Word → Byte} {a b : Word} {k n : Nat} (hkn : k < n)
    (hk : m (a + BitVec.ofNat 64 k) ≠ m' (b + BitVec.ofNat 64 k)) :
    readBytes m a n ≠ readBytes m' b n :=
  fun h => hk ((readBytes_eq_iff m m' a b n).1 h k hkn)

/-- A search for byte `c`: no byte so far is `c`, and the next is not either. -/
theorem not_found_succ {m : Word → Byte} {a : Word} {c : Byte} {k : Nat}
    (h : ∀ i, i < k → m (a + BitVec.ofNat 64 i) ≠ c) (hk : m (a + BitVec.ofNat 64 k) ≠ c) :
    ∀ i, i < k + 1 → m (a + BitVec.ofNat 64 i) ≠ c :=
  forall_lt_succ.2 ⟨h, hk⟩

/-- A search for byte `c`: where no byte so far is `c`, any position of `c` is at or after `k`
    (so a `c` found at `k` is the first). -/
theorem le_of_not_found {m : Word → Byte} {a : Word} {c : Byte} {k : Nat}
    (h : ∀ i, i < k → m (a + BitVec.ofNat 64 i) ≠ c) :
    ∀ k', m (a + BitVec.ofNat 64 k') = c → k ≤ k' := by
  intro k' hk'
  rcases Nat.lt_or_ge k' k with hl | hl
  · exact absurd hk' (h k' hl)
  · exact hl

end NoCompiler.Lib

import NoCompiler.Typed.Track

/-!
# Writes from both ends (memset)

Compiled `memset` stores from the start and from the end of `d[0, n)` at once. `Written2` says
the prefix `d[0, c)` and the suffix `d[n − c2, n)` hold the pattern `G`, the rest of memory the
entry's; the two ranges may overlap (both say `G` there). A store extends either end, and once
`c + c2 ≥ n` the whole range is written (`Written2.full`).
-/
namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed.Bytes

/-- `d[0, c)` and `d[n − c2, n)` hold the pattern, the rest is the entry memory. -/
def Written2 (m0 m : Word → Byte) (d : Word) (G : Nat → Byte) (c c2 n : Nat) : Prop :=
  ∀ p, m p = if (p - d).toNat < c ∨ (n - c2 ≤ (p - d).toNat ∧ (p - d).toNat < n)
    then G (p - d).toNat else m0 p

theorem Written2.zero (m0 : Word → Byte) (d : Word) (G : Nat → Byte) (n : Nat) :
    Written2 m0 m0 d G 0 0 n := by
  intro p
  rw [if_neg (by omega)]

/-- A store of `k ≤ 8` pattern bytes at `d + c` extends the prefix. -/
theorem Written2.store_front {m0 m : Word → Byte} {d : Word} {G : Nat → Byte} {c c2 n : Nat}
    (h : Written2 m0 m d G c c2 n) (w : Word) {k : Nat} (hk : k ≤ 8) (hck : c + k < 2 ^ 64)
    (hw : ∀ i < k, byte w i = G (c + i)) :
    Written2 m0 (writeLE m (d + BitVec.ofNat 64 c) w.toNat k) d G (c + k) c2 n := by
  intro p
  rw [writeLE_apply _ _ _ (by omega), h p]
  have hc : c < 2 ^ 64 := by omega
  by_cases h1 : (p - (d + BitVec.ofNat 64 c)).toNat < k
  · rw [if_pos h1]
    have e : (p - d).toNat = c + (p - (d + BitVec.ofNat 64 c)).toNat := by bv_omega
    rw [if_pos (Or.inl (by omega))]
    have hb := hw _ h1
    rw [byte_eq] at hb
    have e2 : (2 : Nat) ^ (8 * (p - (d + BitVec.ofNat 64 c)).toNat) =
        256 ^ (p - (d + BitVec.ofNat 64 c)).toNat := by rw [Nat.pow_mul]
    rw [e2] at hb
    rw [hb, e]
  · rw [if_neg h1]
    have hout : ¬ (p - d).toNat < c + k ∨ (p - d).toNat < c := by bv_omega
    by_cases h2 : (p - d).toNat < c ∨ (n - c2 ≤ (p - d).toNat ∧ (p - d).toNat < n)
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by omega)]

/-- A store of `k ≤ 8` pattern bytes at `d + (n − c2 − k)` extends the suffix. -/
theorem Written2.store_back {m0 m : Word → Byte} {d : Word} {G : Nat → Byte} {c c2 n : Nat}
    (h : Written2 m0 m d G c c2 n) (w : Word) {k : Nat} (hk : k ≤ 8) (hkn : c2 + k ≤ n)
    (hn : n < 2 ^ 64) (hw : ∀ i < k, byte w i = G (n - c2 - k + i)) :
    Written2 m0 (writeLE m (d + BitVec.ofNat 64 (n - c2 - k)) w.toNat k) d G c (c2 + k) n := by
  intro p
  rw [writeLE_apply _ _ _ (by omega), h p]
  by_cases h1 : (p - (d + BitVec.ofNat 64 (n - c2 - k))).toNat < k
  · rw [if_pos h1]
    have e : (p - d).toNat = (n - c2 - k) + (p - (d + BitVec.ofNat 64 (n - c2 - k))).toNat := by
      bv_omega
    rw [if_pos (Or.inr ⟨by omega, by omega⟩)]
    have hb := hw _ h1
    rw [byte_eq] at hb
    have e2 : (2 : Nat) ^ (8 * (p - (d + BitVec.ofNat 64 (n - c2 - k))).toNat) =
        256 ^ (p - (d + BitVec.ofNat 64 (n - c2 - k))).toNat := by rw [Nat.pow_mul]
    rw [e2] at hb
    rw [hb, e]
  · rw [if_neg h1]
    have hout : ¬ (n - c2 - k ≤ (p - d).toNat ∧ (p - d).toNat < n - c2) := by bv_omega
    by_cases h2 : (p - d).toNat < c ∨ (n - c2 ≤ (p - d).toNat ∧ (p - d).toNat < n)
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by omega)]

/-- Both ends together cover the range: everything is written. -/
theorem Written2.full {m0 m : Word → Byte} {d : Word} {G : Nat → Byte} {c c2 n : Nat}
    (h : Written2 m0 m d G c c2 n) (hcov : n ≤ c + c2) (hc : c ≤ n) : Written m0 m d G n := by
  intro p
  rw [h p]
  by_cases h1 : (p - d).toNat < n
  · rw [if_pos (by omega), if_pos h1]
  · rw [if_neg (by omega), if_neg h1]

/-- A prefix alone is a two-ended write with an empty suffix. -/
theorem Written.two {m0 m : Word → Byte} {d : Word} {G : Nat → Byte} {c : Nat}
    (h : Written m0 m d G c) (n : Nat) : Written2 m0 m d G c 0 n := by
  intro p
  rw [h p]
  by_cases h1 : (p - d).toNat < c
  · rw [if_pos h1, if_pos (Or.inl h1)]
  · rw [if_neg h1, if_neg (by omega)]

/-- A store of `k ≤ 8` pattern bytes at `d + q` that meets or overlaps the prefix (`q ≤ c`) extends
    it to `max c (q + k)` (a fill's overlapping stores write the same bytes again). -/
theorem Written2.store_front_ov {m0 m : Word → Byte} {d : Word} {G : Nat → Byte} {c c2 n q : Nat}
    (h : Written2 m0 m d G c c2 n) (w : Word) {k : Nat} (hk : k ≤ 8) (hq : q ≤ c)
    (hqk : q + k < 2 ^ 64) (hw : ∀ i < k, byte w i = G (q + i)) :
    Written2 m0 (writeLE m (d + BitVec.ofNat 64 q) w.toNat k) d G (max c (q + k)) c2 n := by
  intro p
  rw [writeLE_apply _ _ _ (by omega), h p]
  by_cases h1 : (p - (d + BitVec.ofNat 64 q)).toNat < k
  · rw [if_pos h1]
    have e : (p - d).toNat = q + (p - (d + BitVec.ofNat 64 q)).toNat := by bv_omega
    rw [if_pos (Or.inl (by omega))]
    have hb := hw _ h1
    rw [byte_eq] at hb
    have e2 : (2 : Nat) ^ (8 * (p - (d + BitVec.ofNat 64 q)).toNat) =
        256 ^ (p - (d + BitVec.ofNat 64 q)).toNat := by rw [Nat.pow_mul]
    rw [e2] at hb
    rw [hb, e]
  · rw [if_neg h1]
    have hout : ¬ ((p - d).toNat < q + k ∧ q ≤ (p - d).toNat) := by bv_omega
    by_cases h2 : (p - d).toNat < c ∨ (n - c2 ≤ (p - d).toNat ∧ (p - d).toNat < n)
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by omega)]

/-- A store of `k ≤ 8` pattern bytes at `d + q` that meets or overlaps the suffix
    (`n − c2 ≤ q + k ≤ n`) extends it down to `min (n − c2) q`. -/
theorem Written2.store_back_ov {m0 m : Word → Byte} {d : Word} {G : Nat → Byte} {c c2 n q : Nat}
    (h : Written2 m0 m d G c c2 n) (w : Word) {k : Nat} (hk : k ≤ 8) (hc2 : c2 ≤ n)
    (hlo : n - c2 ≤ q + k) (hhi : q + k ≤ n) (hn : n < 2 ^ 64)
    (hw : ∀ i < k, byte w i = G (q + i)) :
    Written2 m0 (writeLE m (d + BitVec.ofNat 64 q) w.toNat k) d G c (n - min (n - c2) q) n := by
  intro p
  rw [writeLE_apply _ _ _ (by omega), h p]
  by_cases h1 : (p - (d + BitVec.ofNat 64 q)).toNat < k
  · rw [if_pos h1]
    have e : (p - d).toNat = q + (p - (d + BitVec.ofNat 64 q)).toNat := by bv_omega
    rw [if_pos (Or.inr ⟨by omega, by omega⟩)]
    have hb := hw _ h1
    rw [byte_eq] at hb
    have e2 : (2 : Nat) ^ (8 * (p - (d + BitVec.ofNat 64 q)).toNat) =
        256 ^ (p - (d + BitVec.ofNat 64 q)).toNat := by rw [Nat.pow_mul]
    rw [e2] at hb
    rw [hb, e]
  · rw [if_neg h1]
    have hout : ¬ ((p - d).toNat < q + k ∧ q ≤ (p - d).toNat) := by bv_omega
    by_cases h2 : (p - d).toNat < c ∨ (n - c2 ≤ (p - d).toNat ∧ (p - d).toNat < n)
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by omega)]

end NoCompiler.Typed.Track

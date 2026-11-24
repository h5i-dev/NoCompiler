import NoCompiler.Typed.Bytes

/-
The copy relation for value invariants (docs/typed/value-tracker.md): memory is the entry memory
with a prefix of one range copied to another, and a store of the next bytes extends it.
-/
namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed.Bytes

/-- Memory `m` is the entry memory `m0` with the first `c` bytes of `src` copied to `d`. -/
def Copied (m0 m : Word → Byte) (d src : Word) (c : Nat) : Prop :=
  ∀ p, m p = if (p - d).toNat < c then m0 (src + (p - d)) else m0 p

theorem Copied.zero (m0 : Word → Byte) (d src : Word) : Copied m0 m0 d src 0 := by
  intro p; simp

/-- A store of `k ≤ 8` bytes of `w` at `d + c`, whose bytes are the next `k` source bytes,
    extends the copied prefix to `c + k`. -/
theorem Copied.store {m0 m : Word → Byte} {d src : Word} {c : Nat} (h : Copied m0 m d src c)
    (w : Word) {k : Nat} (hk : k ≤ 8) (hck : c + k < 2 ^ 64)
    (hw : ∀ i < k, byte w i = m0 (src + BitVec.ofNat 64 (c + i))) :
    Copied m0 (writeLE m (d + BitVec.ofNat 64 c) w.toNat k) d src (c + k) := by
  intro p
  rw [writeLE_apply _ _ _ (by omega), h p]
  have hc : c < 2 ^ 64 := by omega
  by_cases h1 : (p - (d + BitVec.ofNat 64 c)).toNat < k
  · rw [if_pos h1]
    have e : (p - d).toNat = c + (p - (d + BitVec.ofNat 64 c)).toNat := by bv_omega
    rw [if_pos (by omega)]
    have hb := hw _ h1
    rw [byte_eq] at hb
    have e2 : (2 : Nat) ^ (8 * (p - (d + BitVec.ofNat 64 c)).toNat) = 256 ^ (p - (d + BitVec.ofNat 64 c)).toNat := by
      rw [Nat.pow_mul]
    rw [e2] at hb
    rw [hb]
    congr 1
    bv_omega
  · rw [if_neg h1]
    by_cases h2 : (p - d).toNat < c
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by bv_omega)]

/-- Everything copied gives the copy's bytes. -/
theorem Copied.bytes {m0 m : Word → Byte} {d src : Word} {n : Nat} (h : Copied m0 m d src n)
    (hn : n < 2 ^ 64) : ∀ j < n, m (d + BitVec.ofNat 64 j) = m0 (src + BitVec.ofNat 64 j) := by
  intro j hj
  rw [h]
  have e : (d + BitVec.ofNat 64 j - d) = BitVec.ofNat 64 j := by bv_omega
  rw [e, if_pos (by simp [BitVec.toNat_ofNat]; omega)]

end NoCompiler.Typed.Track

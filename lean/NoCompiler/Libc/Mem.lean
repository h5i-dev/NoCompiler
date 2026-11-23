import NoCompiler.Auto

/-!
# Libc library: memory, permissions, regions

Generic lemmas about `readLE`/`writeLE`/`writeBytes`, `Perm` and `Region` used by the libc proofs
(Examples/Libc). Moved from A's files (QUEUE-D P1, lead 2026-11-22T12:16:41Z); no slen address in them.
A's files see them through `export NoCompiler.Libc (...)` in Examples/Libc/Slen.lean.
-/

namespace NoCompiler.Libc
open NoCompiler

-- from Examples/Libc/SlenProc.lean
theorem readLE_writeLE_disj {R : Region} {a : Word} {n : Nat} (hd : R.Disjoint ⟨a, n⟩)
    (m : Word → Byte) (p : Word) (v w : Nat) (hc : R.covers p w) :
    readLE (writeLE m p v w) a n = readLE m a n :=
  readLE_congr fun j hj => Auto.writeLE_apply_of_disjoint hd m p v w hc j hj

-- from Examples/Libc/SlenProc.lean
theorem readLE_writeBytes_above {m : Word → Byte} {a b : Word} {ws : List Byte} {n : Nat}
    (h : ∀ j, j < n → ws.length ≤ (b + BitVec.ofNat 64 j - a).toNat) :
    readLE (writeBytes m a ws) b n = readLE m b n :=
  readLE_congr fun j hj => writeBytes_other m a ws _ (h j hj)

-- from Examples/Libc/StdioWrite.lean
/-- A word read in `R` sees what `m'` holds there if `m'` agrees with `m` on `R`. -/
theorem read64_congr_on {m m' : Word → Byte} {a : Word} (h : ∀ j, j < 8 → m (a + BitVec.ofNat 64 j) = m' (a + BitVec.ofNat 64 j)) :
    read64 m a = read64 m' a := by
  unfold read64; rw [readLE_congr h]

-- from Examples/Libc/StdioWrite.lean
theorem not_mem_of_disj_mem {R : Region} {b p : Word} {n : Nat} (hd : R.Disjoint ⟨b, n⟩)
    (hp : (Region.mk b n).mem p) : ¬ R.mem p := by
  simp only [Region.Disjoint, Region.mem] at *; bv_omega

-- from Examples/Libc/Memcpy.lean
/-- A byte of `writeLE`. -/
theorem writeLE_apply (m : Word → Byte) (a : Word) (v n : Nat) (p : Word) (hn : n < 2 ^ 64) :
    writeLE m a v n p = if (p - a).toNat < n then BitVec.ofNat 8 (v >>> (8 * (p - a).toNat)) else m p := by
  induction n generalizing a v with
  | zero => simp [writeLE]
  | succ n ih =>
    simp only [writeLE]
    by_cases hpa : p = a
    · subst hpa; simp
    · rw [if_neg hpa, ih _ _ (by omega)]
      have e : (p - (a + 1)).toNat = (p - a).toNat - 1 := sub_succ_toNat p a hpa
      have h0 : (p - a).toNat ≠ 0 := by
        intro h; apply hpa; have := BitVec.eq_of_toNat_eq (by simpa using h : (p - a).toNat = (0#64).toNat); bv_omega
      rw [e]
      by_cases hlt : (p - a).toNat - 1 < n
      · rw [if_pos hlt, if_pos (by omega)]
        congr 1
        rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]
        congr 1
        rw [show 8 * (p - a).toNat = 8 + 8 * ((p - a).toNat - 1) by omega, Nat.pow_add]
      · rw [if_neg hlt, if_neg (by omega)]

-- from Examples/Libc/Memcpy.lean
/-- A loaded word as the concatenation of its bytes. -/
theorem ofNat32_readLE (m : Word → Byte) (a : Word) :
    BitVec.ofNat 32 (readLE m a 4) = (m (a + 3#64)) ++ (m (a + 2#64)) ++ (m (a + 1#64)) ++ (m a) := by
  apply BitVec.eq_of_toNat_eq
  have e2 : a + 1 + 1 = a + 2#64 := by bv_omega
  have e3 : a + 2#64 + 1 = a + 3#64 := by bv_omega
  simp only [readLE, BitVec.toNat_append, BitVec.toNat_ofNat, e2, e3]
  have h0 := (m a).isLt; have h1 := (m (a + 1)).isLt; have h2 := (m (a + 2#64)).isLt; have h3 := (m (a + 3#64)).isLt
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
  simp only [Nat.shiftLeft_eq]
  rw [show (1 : Word) = 1#64 from rfl]
  omega

-- from Examples/Libc/Memcpy.lean
theorem perm_read_sub {P : Perm} {a : Word} {n : Nat} (h : P.canRead a n) (j len : Nat) (hj : j + len ≤ n) (hl : 0 < len) :
    P.canRead (a + BitVec.ofNat 64 j) len := by
  rcases h with h | ⟨r, hr, hc⟩
  · omega
  · exact .inr ⟨r, hr, by simp only [Region.covers] at *; bv_omega⟩

-- from Examples/Libc/Memcpy.lean
theorem perm_write_sub {P : Perm} {a : Word} {n : Nat} (h : P.canWrite a n) (j len : Nat) (hj : j + len ≤ n) (hl : 0 < len) :
    P.canWrite (a + BitVec.ofNat 64 j) len := by
  rcases h with h | ⟨r, hr, hc⟩
  · omega
  · exact .inr ⟨r, hr, by simp only [Region.covers] at *; bv_omega⟩

-- from Examples/Libc/Memcpy.lean
theorem ofNat32_se (m : Word → Byte) (a : Word) :
    ((BitVec.ofNat 32 (readLE m a 4)).signExtend 64 : Word) = ((m (a + 3#64)) ++ (m (a + 2#64)) ++ (m (a + 1#64)) ++ (m a)).signExtend 64 := by
  rw [ofNat32_readLE]
end NoCompiler.Libc

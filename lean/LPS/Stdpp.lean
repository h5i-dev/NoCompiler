/-!
# The stdpp bitvector vocabulary LPS uses, over Lean's `BitVec`

LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs, PBC) is
written over stdpp's `bv n`, a `Z` in `[0, 2^n)`. This module gives the names it uses the same meaning
on `BitVec n`, so the port of each LPS file reads like its source:

| stdpp                 | here                                   |
|-----------------------|----------------------------------------|
| `bv n`                | `BitVec n`                             |
| `bv_unsigned b : Z`   | `(b.toNat : Int)`                      |
| `bv_signed b : Z`     | `b.toInt`                              |
| `Z_to_bv n z`         | `BitVec.ofInt n z` (`z mod 2^n`)       |
| `bv_extract lo len b` | bits `lo .. lo + len - 1` of `b`       |
| `bv_concat n hi lo`   | `Z_to_bv n (hi << |lo| ∣ lo)`          |
| `bv_sign_extend m b`  | `Z_to_bv m (bv_signed b)`              |
| `bv_zero_extend m b`  | `Z_to_bv m (bv_unsigned b)`            |
| `bv_wrap n z`         | `z % 2^n`                              |
| `Z.div`, `Z.modulo`   | `Int.fdiv`, `Int.fmod` (floor)          |
| `Z.quot`, `Z.rem`     | `Int.tdiv`, `Int.tmod` (truncate)       |
| `Z.lor/land/lxor`     | two's complement on `Int`              |

`N` is `Nat`, `Z` is `Int`, `positive` is `Pos` below.
-/

namespace LPS

abbrev bv (n : Nat) := BitVec n

/-- Rocq's `Z.lor` (two's complement on negatives: `~x = -x - 1`). -/
def Z.lor : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (m ||| n)
  | .negSucc m, .ofNat n => .negSucc (m ^^^ (m &&& n))
  | .ofNat m, .negSucc n => .negSucc (n ^^^ (n &&& m))
  | .negSucc m, .negSucc n => .negSucc (m &&& n)

/-- Rocq's `Z.shiftl z n` for `n ≥ 0`: `z * 2^n`. -/
def Z.shiftl (z : Int) (n : Nat) : Int := z * (2 ^ n : Nat)

/-- Rocq's `Z.shiftr z n` for `n ≥ 0`: `⌊z / 2^n⌋`. -/
def Z.shiftr (z : Int) (n : Nat) : Int := z >>> n

/-- Rocq's `Z.div` / `Z.modulo` (`/`, `mod` in `Z_scope`): floor division, remainder with the divisor's
    sign. -/
def Z.div (a b : Int) : Int := Int.fdiv a b
def Z.modulo (a b : Int) : Int := Int.fmod a b
/-- Rocq's `Z.quot` / `Z.rem` (`÷`): truncating division, remainder with the dividend's sign. -/
def Z.quot (a b : Int) : Int := Int.tdiv a b
def Z.rem (a b : Int) : Int := Int.tmod a b

/-- Rocq's `Z.land` / `Z.lxor` (two's complement). -/
def Z.land : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (m &&& n)
  | .negSucc m, .ofNat n => .ofNat (n ^^^ (n &&& m))
  | .ofNat m, .negSucc n => .ofNat (m ^^^ (m &&& n))
  | .negSucc m, .negSucc n => .negSucc (m ||| n)
def Z.lxor : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (m ^^^ n)
  | .negSucc m, .ofNat n => .negSucc (m ^^^ n)
  | .ofNat m, .negSucc n => .negSucc (m ^^^ n)
  | .negSucc m, .negSucc n => .ofNat (m ^^^ n)
-- `Z.ones`, `Z.lnot`, `Z.ldiff` and stdpp's `bv_and/or/xor/not`: LPS/Riscv/StdppExtra.lean.

/-- Rocq's `Z.testbit z i` for `i ≥ 0` (two's complement; `false` for negative `i` in Rocq). -/
def Z.testbit (z : Int) (i : Int) : Bool :=
  if i < 0 then false else
  match z with
  | .ofNat m => m.testBit i.toNat
  | .negSucc m => !(m.testBit i.toNat)

def bv_unsigned {n : Nat} (b : bv n) : Int := (b.toNat : Int)
def bv_signed {n : Nat} (b : bv n) : Int := b.toInt
def Z_to_bv (n : Nat) (z : Int) : bv n := BitVec.ofInt n z
def bv_wrap (n : Nat) (z : Int) : Int := z % (2 ^ n : Nat)
def bv_extract {n : Nat} (lo len : Nat) (b : bv n) : bv len := b.extractLsb' lo len
def bv_concat {n1 n2 : Nat} (n : Nat) (hi : bv n1) (lo : bv n2) : bv n :=
  Z_to_bv n (Z.lor (Z.shiftl (bv_unsigned hi) n2) (bv_unsigned lo))
/-- stdpp `bv_add`, `bv_sub`, `bv_mul`: modular. -/
def bv_add {n : Nat} (a b : bv n) : bv n := a + b
def bv_sub {n : Nat} (a b : bv n) : bv n := a - b
def bv_mul {n : Nat} (a b : bv n) : bv n := a * b
def bv_sign_extend {n : Nat} (m : Nat) (b : bv n) : bv m := Z_to_bv m (bv_signed b)
def bv_zero_extend {n : Nat} (m : Nat) (b : bv n) : bv m := Z_to_bv m (bv_unsigned b)

theorem bv_unsigned_in_range {n : Nat} (b : bv n) : 0 ≤ bv_unsigned b ∧ bv_unsigned b < (2 ^ n : Nat) := by
  unfold bv_unsigned; exact ⟨Int.natCast_nonneg _, by exact_mod_cast b.isLt⟩

/-- Rocq's `positive`: binary, most significant bit `xH`. -/
inductive Pos where
  | xH
  | xO (p : Pos)
  | xI (p : Pos)
  deriving DecidableEq, Repr

/-- `Pos.ofNat n` for `n ≥ 1` (`xH` for 0, as Rocq's `Z.to_pos` sends non-positives to 1). -/
def Pos.ofNat : Nat → Pos
  | 0 => .xH
  | 1 => .xH
  | n + 2 =>
    have : (n + 2) / 2 < n + 2 := Nat.div_lt_self (by omega) (by omega)
    if (n + 2) % 2 = 0 then .xO (Pos.ofNat ((n + 2) / 2)) else .xI (Pos.ofNat ((n + 2) / 2))

def Pos.toNat : Pos → Nat
  | .xH => 1
  | .xO p => 2 * p.toNat
  | .xI p => 2 * p.toNat + 1

/-- Rocq's `Z.to_pos`: `z` for `z > 0`, `1` otherwise. -/
def Z.to_pos (z : Int) : Pos := Pos.ofNat z.toNat

end LPS

import LPS.Riscv.Prelude

/-!
# LPS `theories/LinuxProcessSem/BvBase.v` (f1006fe8): bitvector helpers of the spec layer

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/BvBase.v` at f1006fe8 (TRUST BOUNDARY there: part of the trusted
specification). Machine quantities are `word`, bytes `byte`; range arithmetic in `Z` (`Int`) over
`bv_unsigned`, no wrap-around.
-/

namespace LPS

abbrev byte := bv 8

/-- BvBase.v:26. -/
def bv_leu {n : Nat} (a b : bv n) : Bool := decide (bv_unsigned a ≤ bv_unsigned b)

/-- BvBase.v:31. -/
def len_word {A : Type} (l : List A) : word := Z_to_bv 64 (l.length : Int)

/-- BvBase.v:35-36. -/
def word_to_nat (w : word) : Nat := (bv_unsigned w).toNat
def nat_to_word (n : Nat) : word := Z_to_bv 64 (n : Int)

/-- BvBase.v:44. -/
def word_to_nat_bounded (w : word) (bound : Nat) : Nat :=
  if bv_unsigned w ≤ (bound : Int) then word_to_nat w else bound

theorem word_to_nat_bounded_eq_min (w : word) (bound : Nat) :
    word_to_nat_bounded w bound = Nat.min (word_to_nat w) bound := by
  unfold word_to_nat_bounded word_to_nat bv_unsigned
  simp only [Int.toNat_natCast, Nat.min_def]
  split <;> split <;> omega

/-- BvBase.v:68: the 8 little-endian bytes of a word. -/
def word_le8 (v : word) : List byte :=
  [bv_extract 0 8 v, bv_extract 8 8 v, bv_extract 16 8 v, bv_extract 24 8 v,
   bv_extract 32 8 v, bv_extract 40 8 v, bv_extract 48 8 v, bv_extract 56 8 v]

/-- BvBase.v:75-79 (`bv_concat` puts its first argument in the high bits). -/
def le2 (b1 b0 : byte) : bv 16 := bv_concat 16 b1 b0
def le4 (b3 b2 b1 b0 : byte) : bv 32 := bv_concat 32 (le2 b3 b2) (le2 b1 b0)
def le8 (b7 b6 b5 b4 b3 b2 b1 b0 : byte) : word := bv_concat 64 (le4 b7 b6 b5 b4) (le4 b3 b2 b1 b0)

/-- BvBase.v:88: the exact value of a little-endian byte list. -/
def bytes_le_to_Z : List byte → Int
  | [] => 0
  | b :: rest => Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z rest) 8)

/-- BvBase.v:96. -/
def le_bytes_to_word (bs : List byte) : word := Z_to_bv 64 (bytes_le_to_Z bs)

/-- BvBase.v:105: the `n` little-endian bytes of `z`. -/
def Z_to_le_bytes : Nat → Int → List byte
  | 0, _ => []
  | n + 1, z => Z_to_bv 8 z :: Z_to_le_bytes n (Z.shiftr z 8)

theorem length_Z_to_le_bytes (n : Nat) (z : Int) : (Z_to_le_bytes n z).length = n := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp [Z_to_le_bytes, ih]

-- `bv_wrap8_mod`, `bytes_le_to_Z_of_le_bytes` (BvBase.v:117-150): ported when a proof needs them.

/-- BvBase.v:154: an `int` as `put_user` stores it. -/
def word_le4 (v : word) : List byte := [bv_extract 0 8 v, bv_extract 8 8 v, bv_extract 16 8 v, bv_extract 24 8 v]

/-- BvBase.v:161: a `short`. -/
def word_le2 (v : word) : List byte := [bv_extract 0 8 v, bv_extract 8 8 v]

end LPS

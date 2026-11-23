import LPS.Stdpp
import LPS.Riscv.StdppExtra

/-!
# LPS `theories/Riscv/Prelude.v` (f1006fe8): bitvector helpers and a radix-tree map

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), file `theories/Riscv/Prelude.v` at commit f1006fe8178338a499b5e5c41be83006c4edd058, lines 1-150
(the whole file). Names and structure kept; stdpp's `bv` is `LPS.bv` (LPS/Stdpp.lean).
-/

namespace LPS

abbrev word := bv 64
abbrev reg := bv 5

/-- Prelude.v:17. -/
def bits {n : Nat} (lo len : Nat) (w : bv n) : bv len := bv_extract lo len w

/-- Prelude.v:19-20. -/
def sext {n : Nat} (m : Nat) (b : bv n) : bv m := bv_sign_extend m b
def zext {n : Nat} (m : Nat) (b : bv n) : bv m := bv_zero_extend m b

/-- Untyped bit test, for decoding (Prelude.v:23). -/
def bit {n : Nat} (i : Nat) (w : bv n) : Bool := (bv_unsigned w).toNat.testBit i

/-! Signedness-explicit wrappers (Prelude.v:26-50). -/

def bv_lts {n : Nat} (a b : bv n) : Bool := decide (bv_signed a < bv_signed b)
def bv_ltu {n : Nat} (a b : bv n) : Bool := decide (bv_unsigned a < bv_unsigned b)
def bv_eqb {n : Nat} (a b : bv n) : Bool := decide (bv_unsigned a = bv_unsigned b)

/-- High `n` bits of the exact product, signed × signed (Prelude.v:44); `Z.shiftr` is floor division
    by `2^n`, Lean's `Int.shiftRight` likewise. -/
def bv_mulhss {n : Nat} (a b : bv n) : bv n := Z_to_bv n (Z.shiftr (bv_signed a * bv_signed b) n)
def bv_mulhsu {n : Nat} (a b : bv n) : bv n := Z_to_bv n (Z.shiftr (bv_signed a * bv_unsigned b) n)
def bv_mulhuu {n : Nat} (a b : bv n) : bv n := Z_to_bv n (Z.shiftr (bv_unsigned a * bv_unsigned b) n)

/-! Radix-tree map keyed by `positive` (Prelude.v:52-150). -/

inductive tree (A : Type) : Type where
  | TEmpty
  | TNode (l : tree A) (v : Option A) (r : tree A)

open tree

def tget {A : Type} (p : Pos) (t : tree A) : Option A :=
  match t with
  | TEmpty => none
  | TNode l v r =>
    match p with
    | .xH => v
    | .xO p => tget p l
    | .xI p => tget p r

def tset {A : Type} (p : Pos) (x : A) (t : tree A) : tree A :=
  match t with
  | TEmpty =>
    match p with
    | .xH => TNode TEmpty (some x) TEmpty
    | .xO p => TNode (tset p x TEmpty) none TEmpty
    | .xI p => TNode TEmpty none (tset p x TEmpty)
  | TNode l v r =>
    match p with
    | .xH => TNode l (some x) r
    | .xO p => TNode (tset p x l) v r
    | .xI p => TNode l v (tset p x r)

theorem tget_tset_same {A : Type} (p : Pos) (x : A) (t : tree A) : tget p (tset p x t) = some x := by
  induction p generalizing t with
  | xH => cases t <;> rfl
  | xO p ih => cases t <;> simp [tset, tget, ih]
  | xI p ih => cases t <;> simp [tset, tget, ih]

-- `tget_tset_other`, `bv_key_inj`, `bvmap_get_set_other` (Prelude.v:93-150): ported when a proof needs them.

/-- Map bitvector keys into `positive` (Prelude.v:121). -/
def bv_key {n : Nat} (b : bv n) : Pos := Z.to_pos (bv_unsigned b + 1)

def bvmap (_n : Nat) (A : Type) := tree A
def bvmap_get {n : Nat} {A : Type} (k : bv n) (m : bvmap n A) : Option A := tget (bv_key k) m
def bvmap_set {n : Nat} {A : Type} (k : bv n) (x : A) (m : bvmap n A) : bvmap n A := tset (bv_key k) x m
def bvmap_empty {n : Nat} {A : Type} : bvmap n A := TEmpty

theorem bvmap_get_set_same {n : Nat} {A : Type} (k : bv n) (x : A) (m : bvmap n A) :
    bvmap_get k (bvmap_set k x m) = some x := tget_tset_same _ _ _

end LPS

import LPS.Stdpp

/-!
# Further Stdlib/stdpp primitives the Riscv port needs

Companion of `LPS/Stdpp.lean` (kept separate so the two branches do not conflict). Each name has the
exact meaning of the Rocq primitive it is named after, on `Int`/`Nat`/`Pos`/`bv`:

| Rocq                       | here                                                       |
|----------------------------|------------------------------------------------------------|
| `Z.shiftl z n` (n : Z)     | `Z.shiftlZ z n`: `z * 2^n` for `n ≥ 0`, `⌊z / 2^-n⌋` else  |
| `Z.shiftr z n` (n : Z)     | `Z.shiftrZ z n := Z.shiftlZ z (-n)`                        |
| `Z.ones n`                 | `Z.shiftlZ 1 n - 1`                                        |
| `Z.lnot z`                 | `-z - 1`                                                   |
| `Z.log2 z`                 | `Nat.log2 z.toNat` (0 for `z ≤ 0`)                         |
| `Z.even z`                 | `Z.modulo z 2 == 0`                                        |
| `Z.div2 z`                 | `Z.div z 2` (floor)                                        |
| `Z.div_eucl a b`           | `(Z.div a b, Z.modulo a b)` (floor, as Rocq)               |
| `Z.sqrtrem z`              | `(s, z - s*s)`, `s = ⌊√z⌋` for `z > 0`, `(0, 0)` otherwise |
| `Z.pow a b`                | `a ^ b` for `b ≥ 0`, `0` for `b < 0`                       |
| `Z.compare`, `comparison`  | `compare`, `Ordering` (`Eq/Lt/Gt` = `.eq/.lt/.gt`)         |
| `CompOpp`                  | `Ordering.swap`                                            |
| `Zpos p`                   | `Z.pos p := (p.toNat : Int)`                               |
| `match z with Z0/Zpos/Zneg`| `match Z.view z with ...` (`Zv`)                           |
| `Pos.succ/add/mul/size/iter/compare_cont/sub` | structural definitions on `Pos`         |
| stdpp `bv_and/or/xor/not`  | `Z_to_bv n (Z.land/lor/lxor/lnot ...)` of `bv_unsigned`    |
| stdpp `≪`, `≫`, `bv_ashiftr` | `Z_to_bv n (Z.shiftl/shiftr (bv_unsigned or bv_signed a) (bv_unsigned b))` |
| stdpp `bv_quots/rems`      | `Z_to_bv n (Z.quot/Z.rem (bv_signed a) (bv_signed b))`     |
| stdpp `bv_divu/modu`       | `Z_to_bv n (Z.div/Z.modulo (bv_unsigned a) (bv_unsigned b))` |
| `Uint63.int`, `char63`     | `Nat` below `2^63`; `Uint63.of_Z z = z mod 2^63`; `sub` wraps; `ltb/leb/eqb` unsigned |
| `PrimString.length s`      | `s.utf8ByteSize` (`PrimString.string` is a byte string; MemImageType ports it as `String`) |
| `PrimString.get s i`       | the `i`-th UTF-8 byte of `s`, `0` out of bounds              |

stdpp's `bv_add/sub/mul` (`+ - *` on `bv n`, i.e. `Z_to_bv n` of the `Z` result) are Lean's `BitVec`
`+ - *`, which also reduce modulo `2^n`.
-/

namespace LPS

/-- Rocq's `Z.shiftl` with a `Z` shift amount: a negative amount shifts right (floor). -/
def Z.shiftlZ (z : Int) : Int → Int
  | .ofNat k => z * (2 ^ k : Nat)
  | .negSucc k => z >>> (k + 1)

/-- Rocq's `Z.shiftr` with a `Z` shift amount (`Z.shiftr a n = Z.shiftl a (-n)`). -/
def Z.shiftrZ (z n : Int) : Int := Z.shiftlZ z (-n)

/-- Rocq's `Z.ones n = Z.pred (Z.shiftl 1 n)`. -/
def Z.ones (n : Int) : Int := Z.shiftlZ 1 n - 1

/-- Rocq's `Z.lnot`. -/
def Z.lnot (z : Int) : Int := -z - 1

/-- Rocq's `Z.ldiff a b = a land (lnot b)`. -/
def Z.ldiff (a b : Int) : Int := Z.land a (Z.lnot b)

/-- Rocq's `Z.log2` (0 on non-positive arguments). -/
def Z.log2 (z : Int) : Int := (Nat.log2 z.toNat : Nat)

/-- Rocq's `Z.even`. -/
def Z.even (z : Int) : Bool := Z.modulo z 2 == 0

/-- Rocq's `Z.div2` (floor halving: `Z.div2 (-3) = -2`). -/
def Z.div2 (z : Int) : Int := Z.div z 2

/-- Rocq's `Z.div_eucl` (despite the name, floor division: `Z.div = fst ∘ Z.div_eucl`). -/
def Z.div_eucl (a b : Int) : Int × Int := (Z.div a b, Z.modulo a b)

/-- Rocq's `Z.sqrtrem`: `(⌊√n⌋, n - ⌊√n⌋²)` for `n > 0`, `(0, 0)` otherwise. -/
def Z.sqrtrem (n : Int) : Int × Int :=
  if 0 < n then
    let s : Int := (Nat.sqrt n.toNat : Nat)
    (s, n - s * s)
  else (0, 0)

/-- Rocq's `Z.pow` (`0` for a negative exponent). -/
def Z.pow (a b : Int) : Int := if b < 0 then 0 else a ^ b.toNat

/-- Rocq's `Z.compare`. -/
def Z.compare (a b : Int) : Ordering := Ord.compare a b

/-- Rocq's `CompOpp`. -/
def CompOpp (c : Ordering) : Ordering := c.swap

/-! ## `positive` -/

/-- Rocq's `Zpos`. -/
def Z.pos (p : Pos) : Int := (p.toNat : Int)

/-- Rocq's `Z` constructors, as a view on `Int`, so `match z with Z0 | Zpos p | Zneg p` ports as is. -/
inductive Zv where
  | Z0
  | Zpos (p : Pos)
  | Zneg (p : Pos)

/-- The `Zv` view of an `Int`: `Z.view (Z.pos p) = Zpos p`, `Z.view (-(Z.pos p)) = Zneg p`. -/
def Z.view (z : Int) : Zv :=
  match z with
  | .ofNat 0 => .Z0
  | .ofNat (k + 1) => .Zpos (Pos.ofNat (k + 1))
  | .negSucc k => .Zneg (Pos.ofNat (k + 1))

def Pos.succ : Pos → Pos
  | .xH => .xO .xH
  | .xO p => .xI p
  | .xI p => .xO (Pos.succ p)

mutual
/-- Rocq's `Pos.add`. -/
def Pos.add : Pos → Pos → Pos
  | .xI p, .xI q => .xO (Pos.add_carry p q)
  | .xI p, .xO q => .xI (Pos.add p q)
  | .xI p, .xH => .xO (Pos.succ p)
  | .xO p, .xI q => .xI (Pos.add p q)
  | .xO p, .xO q => .xO (Pos.add p q)
  | .xO p, .xH => .xI p
  | .xH, .xI q => .xO (Pos.succ q)
  | .xH, .xO q => .xI q
  | .xH, .xH => .xO .xH
/-- Rocq's `Pos.add_carry` (`p + q + 1`). -/
def Pos.add_carry : Pos → Pos → Pos
  | .xI p, .xI q => .xI (Pos.add_carry p q)
  | .xI p, .xO q => .xO (Pos.add_carry p q)
  | .xI p, .xH => .xI (Pos.succ p)
  | .xO p, .xI q => .xO (Pos.add_carry p q)
  | .xO p, .xO q => .xI (Pos.add p q)
  | .xO p, .xH => .xO (Pos.succ p)
  | .xH, .xI q => .xI (Pos.succ q)
  | .xH, .xO q => .xO (Pos.succ q)
  | .xH, .xH => .xI .xH
end

/-- Rocq's `Pos.mul`. -/
def Pos.mul : Pos → Pos → Pos
  | .xI p, y => Pos.add y (.xO (Pos.mul p y))
  | .xO p, y => .xO (Pos.mul p y)
  | .xH, y => y

/-- Rocq's `Pos.size` (number of binary digits). -/
def Pos.size : Pos → Pos
  | .xH => .xH
  | .xO p => Pos.succ (Pos.size p)
  | .xI p => Pos.succ (Pos.size p)

/-- Rocq's `Pos.iter f x n`: `f` applied `n` times to `x`. -/
def Pos.iter {A : Type} (f : A → A) (x : A) : Pos → A
  | .xH => f x
  | .xO n => Pos.iter f (Pos.iter f x n) n
  | .xI n => f (Pos.iter f (Pos.iter f x n) n)

/-- Rocq's `Pos.compare_cont`. -/
def Pos.compare_cont (r : Ordering) : Pos → Pos → Ordering
  | .xI p, .xI q => Pos.compare_cont r p q
  | .xI p, .xO q => Pos.compare_cont .gt p q
  | .xI _, .xH => .gt
  | .xO p, .xI q => Pos.compare_cont .lt p q
  | .xO p, .xO q => Pos.compare_cont r p q
  | .xO _, .xH => .gt
  | .xH, .xI _ => .lt
  | .xH, .xO _ => .lt
  | .xH, .xH => r

/-- Rocq's `Pos.sub p q`: `p - q` if `q < p`, else `1`. -/
def Pos.sub (p q : Pos) : Pos := Pos.ofNat (p.toNat - q.toNat)

/-! ## stdpp bitvector operations (`bitvector/definitions.v`) -/

def bv_and {n : Nat} (a b : bv n) : bv n := Z_to_bv n (Z.land (bv_unsigned a) (bv_unsigned b))
def bv_or {n : Nat} (a b : bv n) : bv n := Z_to_bv n (Z.lor (bv_unsigned a) (bv_unsigned b))
def bv_xor {n : Nat} (a b : bv n) : bv n := Z_to_bv n (Z.lxor (bv_unsigned a) (bv_unsigned b))
def bv_not {n : Nat} (a : bv n) : bv n := Z_to_bv n (Z.lnot (bv_unsigned a))
/-- stdpp `bv_shiftl` (`≪`). -/
def bv_shiftl {n : Nat} (a b : bv n) : bv n := Z_to_bv n (Z.shiftlZ (bv_unsigned a) (bv_unsigned b))
/-- stdpp `bv_shiftr` (`≫`). -/
def bv_shiftr {n : Nat} (a b : bv n) : bv n := Z_to_bv n (Z.shiftrZ (bv_unsigned a) (bv_unsigned b))
def bv_ashiftr {n : Nat} (a b : bv n) : bv n := Z_to_bv n (Z.shiftrZ (bv_signed a) (bv_unsigned b))
def bv_quots {n : Nat} (a b : bv n) : bv n := Z_to_bv n (Z.quot (bv_signed a) (bv_signed b))
def bv_rems {n : Nat} (a b : bv n) : bv n := Z_to_bv n (Z.rem (bv_signed a) (bv_signed b))
def bv_divu {n : Nat} (a b : bv n) : bv n := Z_to_bv n (Z.div (bv_unsigned a) (bv_unsigned b))
def bv_modu {n : Nat} (a b : bv n) : bv n := Z_to_bv n (Z.modulo (bv_unsigned a) (bv_unsigned b))

/-! ## Primitive integers and strings (`Stdlib.PrimInt63`, `Uint63`, `PrimString`) -/

/-- `2^63`, the modulus of `Uint63.int`. -/
def Uint63.wB : Nat := 2 ^ 63
/-- `Uint63.of_Z`: reduction modulo `2^63`. -/
def Uint63.of_Z (z : Int) : Nat := (Z.modulo z (Uint63.wB : Int)).toNat
def Uint63.to_Z (c : Nat) : Int := (c : Int)
def Uint63.ltb (a b : Nat) : Bool := decide (a < b)
def Uint63.leb (a b : Nat) : Bool := decide (a ≤ b)
def Uint63.eqb (a b : Nat) : Bool := a == b
/-- `Uint63.sub`: subtraction modulo `2^63`. -/
def Uint63.sub (a b : Nat) : Nat := Uint63.of_Z ((a : Int) - (b : Int))

/-- `PrimString.length`: the number of bytes. -/
def PrimString.length (s : String) : Nat := s.utf8ByteSize
/-- `PrimString.get s i`: the byte at `i` (as a `char63`), `0` when `i` is out of bounds. -/
def PrimString.get (s : String) (i : Nat) : Nat := ((s.toUTF8[i]?).getD 0).toNat

end LPS

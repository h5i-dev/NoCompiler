import LPS.Riscv.StdppExtra

/-!
# The part of Rocq's `SpecFloat` and Flocq's `BinarySingleNaN` that LPS `Fpu.v` uses

`theories/Riscv/Fpu.v` (LPS f1006fe8) imports `Stdlib SpecFloat` (Rocq 9.2: `Corelib.Floats.SpecFloat`,
LGPL-2.1, The Rocq Development Team) and `Flocq.IEEE754.BinarySingleNaN` (Flocq ≥ 4.2, LGPL-3,
S. Boldo, G. Melquiond et al.). It calls, from them: `spec_float`, `location`, `shr_record`, `shr`,
`shr_fexp`, `shr_record_of_loc`, `loc_of_shr_record`, `Zdigits2`, `digits2_pos`, `fexp`, `shl_align`,
`new_location`, `SFdiv_core_binary`, `SFsqrt_core_binary`, `SFcompare` (SpecFloat), and `mode`,
`choice_mode`, `binary_overflow`, `binary_round_aux` (Flocq). This module transcribes exactly those
definitions and what they call, nothing else (no `SFadd`, `SFmul`, ..., which Fpu does not use).
This file is therefore under those licences, LGPL-2.1 (SpecFloat) and LGPL-3.0 (Flocq), not MIT; see NOTICE.

Section variables `prec emax` become explicit leading arguments, in that order, exactly on the
definitions whose bodies use them (as Rocq's section discharge does): `emin`, `fexp`, `shr_fexp`,
`SFdiv_core_binary`, `SFsqrt_core_binary`, `binary_overflow`, `binary_fit_aux`, `binary_round_aux`.
Flocq's section also has the hypotheses `Prec_gt_0 prec`, `Prec_lt_emax prec emax`, which none of
these bodies uses, so they are not arguments (Fpu.v calls them without proofs).

Rocq's `comparison` (`Eq | Lt | Gt`) is Lean's `Ordering` (`.eq | .lt | .gt`).
Sources read: rocq-prover/rocq `theories/Corelib/Floats/SpecFloat.v` at V9.2.0; flocq master
`src/IEEE754/BinarySingleNaN.v` (lines 1129-1277), `src/Calc/Round.v` (`cond_incr`, `round_sign_DN`,
`round_sign_UP`, `round_N`).
-/

namespace LPS

/-- SpecFloat.v `spec_float`: IEEE datum with no NaN payload. -/
inductive spec_float where
  | S754_zero (s : Bool)
  | S754_infinity (s : Bool)
  | S754_nan
  | S754_finite (s : Bool) (m : Pos) (e : Int)
  deriving DecidableEq, Repr

open spec_float

/-- SpecFloat `emin`. -/
def emin (prec emax : Int) : Int := 3 - emax - prec
/-- SpecFloat `fexp`. -/
def fexp (prec emax : Int) (e : Int) : Int := max (e - prec) (emin prec emax)

/-- SpecFloat `digits2_pos`. -/
def digits2_pos : Pos → Pos
  | .xH => .xH
  | .xO p => Pos.succ (digits2_pos p)
  | .xI p => Pos.succ (digits2_pos p)

/-- SpecFloat `Zdigits2`. -/
def Zdigits2 (n : Int) : Int :=
  match Z.view n with
  | .Z0 => n
  | .Zpos p => Z.pos (digits2_pos p)
  | .Zneg p => Z.pos (digits2_pos p)

/-- SpecFloat `iter_pos` (note the order: `xI` applies `f` first, unlike `Pos.iter`). -/
def iter_pos {A : Type} (f : A → A) : Pos → A → A
  | .xI n', x => iter_pos f n' (iter_pos f n' (f x))
  | .xO n', x => iter_pos f n' (iter_pos f n' x)
  | .xH, x => f x

/-- SpecFloat `location`. -/
inductive location where
  | loc_Exact
  | loc_Inexact (c : Ordering)
  deriving DecidableEq, Repr

open location

/-- SpecFloat `shr_record`. -/
structure shr_record where
  Build_shr_record ::
  shr_m : Int
  shr_r : Bool
  shr_s : Bool
  deriving DecidableEq, Repr

open shr_record

/-- SpecFloat `shr_1`. -/
def shr_1 (mrs : shr_record) : shr_record :=
  let ⟨m, r, s⟩ := mrs
  let s := r || s
  match Z.view m with
  | .Z0 => Build_shr_record 0 false s
  | .Zpos .xH => Build_shr_record 0 true s
  | .Zpos (.xO p) => Build_shr_record (Z.pos p) false s
  | .Zpos (.xI p) => Build_shr_record (Z.pos p) true s
  | .Zneg .xH => Build_shr_record 0 true s
  | .Zneg (.xO p) => Build_shr_record (-(Z.pos p)) false s
  | .Zneg (.xI p) => Build_shr_record (-(Z.pos p)) true s

/-- SpecFloat `loc_of_shr_record`. -/
def loc_of_shr_record (mrs : shr_record) : location :=
  match mrs with
  | ⟨_, false, false⟩ => loc_Exact
  | ⟨_, false, true⟩ => loc_Inexact .lt
  | ⟨_, true, false⟩ => loc_Inexact .eq
  | ⟨_, true, true⟩ => loc_Inexact .gt

/-- SpecFloat `shr_record_of_loc`. -/
def shr_record_of_loc (m : Int) (l : location) : shr_record :=
  match l with
  | loc_Exact => Build_shr_record m false false
  | loc_Inexact .lt => Build_shr_record m false true
  | loc_Inexact .eq => Build_shr_record m true false
  | loc_Inexact .gt => Build_shr_record m true true

/-- SpecFloat `shr`. -/
def shr (mrs : shr_record) (e n : Int) : shr_record × Int :=
  match Z.view n with
  | .Zpos p => (iter_pos shr_1 p mrs, e + n)
  | _ => (mrs, e)

/-- SpecFloat `shr_fexp`. -/
def shr_fexp (prec emax : Int) (m e : Int) (l : location) : shr_record × Int :=
  shr (shr_record_of_loc m l) e (fexp prec emax (Zdigits2 m + e) - e)

/-- SpecFloat `shl_align`. -/
def shl_align (mx : Pos) (ex ex' : Int) : Pos × Int :=
  match Z.view (ex' - ex) with
  | .Zneg d => (Pos.iter .xO mx d, ex')
  | _ => (mx, ex)

/-- SpecFloat `SFcompare`. -/
def SFcompare (f1 f2 : spec_float) : Option Ordering :=
  match f1, f2 with
  | S754_nan, _ | _, S754_nan => none
  | S754_infinity s1, S754_infinity s2 =>
    some (match s1, s2 with
      | true, true => .eq
      | false, false => .eq
      | true, false => .lt
      | false, true => .gt)
  | S754_infinity s, _ => some (if s then .lt else .gt)
  | _, S754_infinity s => some (if s then .gt else .lt)
  | S754_finite s _ _, S754_zero _ => some (if s then .lt else .gt)
  | S754_zero _, S754_finite s _ _ => some (if s then .gt else .lt)
  | S754_zero _, S754_zero _ => some .eq
  | S754_finite s1 m1 e1, S754_finite s2 m2 e2 =>
    some (match s1, s2 with
      | true, false => .lt
      | false, true => .gt
      | false, false =>
        match Z.compare e1 e2 with
        | .lt => .lt
        | .gt => .gt
        | .eq => Pos.compare_cont .eq m1 m2
      | true, true =>
        match Z.compare e1 e2 with
        | .lt => .gt
        | .gt => .lt
        | .eq => CompOpp (Pos.compare_cont .eq m1 m2))

/-- SpecFloat `new_location_even`. -/
def new_location_even (nb_steps k : Int) : location :=
  if k == 0 then loc_Exact
  else loc_Inexact (Z.compare (2 * k) nb_steps)

/-- SpecFloat `new_location_odd`. -/
def new_location_odd (nb_steps k : Int) : location :=
  if k == 0 then loc_Exact
  else
    loc_Inexact
      (match Z.compare (2 * k + 1) nb_steps with
       | .lt => .lt
       | .eq => .lt
       | .gt => .gt)

/-- SpecFloat `new_location`. -/
def new_location (nb_steps : Int) : Int → location :=
  if Z.even nb_steps then new_location_even nb_steps else new_location_odd nb_steps

/-- SpecFloat `SFdiv_core_binary`. -/
def SFdiv_core_binary (prec emax : Int) (m1 e1 m2 e2 : Int) : Int × Int × location :=
  let d1 := Zdigits2 m1
  let d2 := Zdigits2 m2
  let e' := min (fexp prec emax ((d1 + e1) - (d2 + e2))) (e1 - e2)
  let s := (e1 - e2) - e'
  let m' :=
    match Z.view s with
    | .Zpos _ => Z.shiftlZ m1 s
    | .Z0 => m1
    | .Zneg _ => 0
  let (q, r) := Z.div_eucl m' m2
  (q, e', new_location m2 r)

/-- SpecFloat `SFsqrt_core_binary`. -/
def SFsqrt_core_binary (prec emax : Int) (m e : Int) : Int × Int × location :=
  let d := Zdigits2 m
  let e' := min (fexp prec emax (Z.div2 ((d + e) + 1))) (Z.div2 e)
  let s := e - 2 * e'
  let m' :=
    match Z.view s with
    | .Zpos _ => Z.shiftlZ m s
    | .Z0 => m
    | .Zneg _ => 0
  let (q, r) := Z.sqrtrem m'
  let l :=
    if r == 0 then loc_Exact
    else loc_Inexact (if decide (r ≤ q) then .lt else .gt)
  (q, e', l)

/-! ## Flocq `Calc/Round.v` and `IEEE754/BinarySingleNaN.v` -/

/-- Round.v `cond_incr`. -/
def cond_incr (b : Bool) (m : Int) : Int := if b then m + 1 else m

/-- Round.v `round_sign_DN`. -/
def round_sign_DN (s : Bool) (l : location) : Bool :=
  match l with
  | loc_Exact => false
  | _ => s

/-- Round.v `round_sign_UP`. -/
def round_sign_UP (s : Bool) (l : location) : Bool :=
  match l with
  | loc_Exact => false
  | _ => !s

/-- Round.v `round_N`. -/
def round_N (p : Bool) (l : location) : Bool :=
  match l with
  | loc_Exact => false
  | loc_Inexact .lt => false
  | loc_Inexact .eq => p
  | loc_Inexact .gt => true

namespace BinarySingleNaN

/-- BinarySingleNaN.v:1129 `mode`. -/
inductive mode where
  | mode_NE | mode_ZR | mode_DN | mode_UP | mode_NA
  deriving DecidableEq, Repr

open mode

/-- BinarySingleNaN.v:1140 `choice_mode`. -/
def choice_mode (m : mode) (sx : Bool) (mx : Int) (lx : location) : Int :=
  match m with
  | mode_NE => cond_incr (round_N (!(Z.even mx)) lx) mx
  | mode_ZR => mx
  | mode_DN => cond_incr (round_sign_DN sx lx) mx
  | mode_UP => cond_incr (round_sign_UP sx lx) mx
  | mode_NA => cond_incr (round_N true lx) mx

/-- BinarySingleNaN.v:1173 `overflow_to_inf`. -/
def overflow_to_inf (m : mode) (s : Bool) : Bool :=
  match m with
  | mode_NE => true
  | mode_NA => true
  | mode_ZR => false
  | mode_UP => !s
  | mode_DN => s

/-- BinarySingleNaN.v:1182 `binary_overflow` (`Zpower 2 prec` is `Z.pow 2 prec`). -/
def binary_overflow (prec emax : Int) (m : mode) (s : Bool) : spec_float :=
  if overflow_to_inf m s then S754_infinity s
  else S754_finite s (Z.to_pos (Z.pow 2 prec - 1)) (emax - prec)

/-- BinarySingleNaN.v:1229 `binary_fit_aux`. -/
def binary_fit_aux (prec emax : Int) (mode : mode) (sx : Bool) (mx : Pos) (ex : Int) : spec_float :=
  if decide (ex ≤ emax - prec) then S754_finite sx mx ex
  else binary_overflow prec emax mode sx

/-- BinarySingleNaN.v:1270 `binary_round_aux`. -/
def binary_round_aux (prec emax : Int) (mode : mode) (sx : Bool) (mx ex : Int) (lx : location) :
    spec_float :=
  let (mrs', e') := shr_fexp prec emax mx ex lx
  let (mrs'', e'') :=
    shr_fexp prec emax (choice_mode mode sx (shr_m mrs') (loc_of_shr_record mrs')) e' loc_Exact
  match Z.view (shr_m mrs'') with
  | .Z0 => S754_zero sx
  | .Zpos m => binary_fit_aux prec emax mode sx m e''
  | _ => S754_nan

end BinarySingleNaN

end LPS

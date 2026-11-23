import LPS.Riscv.SpecFloat

/-!
# LPS `theories/Riscv/Fpu.v` (f1006fe8): IEEE-754 binary arithmetic with RISC-V exception flags

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Riscv/Fpu.v` at f1006fe8 (TRUST BOUNDARY there). Every definition of the file, same
names, argument order and case structure. Everything is a computation over `Int` on raw bit patterns
of the format's width (32 or 64); the value half is Flocq's rounding kernel, transcribed with the
SpecFloat/Flocq definitions it uses in `LPS/Riscv/SpecFloat.lean` (Lean's `Float` is not used).

What changed and why:
- `match z with Zpos p => .. | _ => ..` on a `Z` is `match Z.view z with ..` (`LPS/Riscv/StdppExtra`);
  `Z.pos p` is `Zpos p`.
- `Z.shiftl`/`Z.shiftr` with a `Z` shift amount are `Z.shiftlZ`/`Z.shiftrZ` (same meaning: a negative
  amount shifts the other way); `Z.eqb/ltb/leb` are `==`/`decide (<)`/`decide (≤)`.
- `comparison` is `Ordering`; `Bool.eqb a b` is `a == b`; `xorb` is `Bool.xor`.
- `let '(a, b) := e in ..` is `let (a, b) := e; ..`.
-/

namespace LPS

open spec_float location

/-! ## Formats (Fpu.v:82-99) -/

/-- Fpu.v:92. -/
structure format where
  Fmt ::
  fp_prec : Int
  fp_emax : Int
  deriving DecidableEq, Repr

open format

/-- Fpu.v:94. -/
def fmt_single : format := Fmt 24 128
/-- Fpu.v:95. -/
def fmt_double : format := Fmt 53 1024

/-- Fpu.v:97 (mantissa field). -/
def fp_mw (f : format) : Int := fp_prec f - 1
/-- Fpu.v:98 (exponent field). -/
def fp_ew (f : format) : Int := Z.log2 (fp_emax f) + 1
/-- Fpu.v:99. -/
def fp_emin (f : format) : Int := 3 - fp_emax f - fp_prec f

/-! ## Exception flags (Fpu.v:101-124) -/

/-- Fpu.v:108. -/
structure fflags where
  Fflags ::
  fl_nv : Bool
  fl_dz : Bool
  fl_of : Bool
  fl_uf : Bool
  fl_nx : Bool
  deriving DecidableEq, Repr

open fflags

/-- Fpu.v:116. -/
def no_flags : fflags := Fflags false false false false false
/-- Fpu.v:117. -/
def nv_flag : fflags := Fflags true false false false false
/-- Fpu.v:118. -/
def dz_flag : fflags := Fflags false true false false false
/-- Fpu.v:119. -/
def nx_flag : fflags := Fflags false false false false true

/-- Fpu.v:121. -/
def fflags_bits (fl : fflags) : Int :=
  let b (p : Bool) (i : Int) : Int := if p then Z.shiftlZ 1 i else 0
  b (fl_nx fl) 0 + b (fl_uf fl) 1 + b (fl_of fl) 2
  + b (fl_dz fl) 3 + b (fl_nv fl) 4

/-! ## Rounding modes (Fpu.v:126-158) -/

/-- Fpu.v:137. -/
inductive rmode where
  | RNE | RTZ | RDN | RUP | RMM
  deriving DecidableEq, Repr

open rmode

/-- Fpu.v:139. -/
def rmode_of_Z (z : Int) : Option rmode :=
  if z == 0 then some RNE
  else if z == 1 then some RTZ
  else if z == 2 then some RDN
  else if z == 3 then some RUP
  else if z == 4 then some RMM
  else none

/-- Fpu.v:148. `rm` is the instruction field, `frm` the fcsr rounding mode. -/
def rmode_of_field (rm frm : Int) : Option rmode :=
  if rm == 7 then rmode_of_Z frm else rmode_of_Z rm

/-- Fpu.v:151. -/
def flocq_mode (m : rmode) : BinarySingleNaN.mode :=
  match m with
  | RNE => .mode_NE
  | RTZ => .mode_ZR
  | RDN => .mode_DN
  | RUP => .mode_UP
  | RMM => .mode_NA

/-! ## Bit patterns (Fpu.v:160-229) -/

/-- Fpu.v:170. -/
def fp_sign_bit (f : format) (x : Int) : Bool :=
  Z.testbit x (fp_mw f + fp_ew f)
/-- Fpu.v:172. -/
def fp_exp_field (f : format) (x : Int) : Int :=
  Z.land (Z.shiftrZ x (fp_mw f)) (Z.ones (fp_ew f))
/-- Fpu.v:174. -/
def fp_man_field (f : format) (x : Int) : Int :=
  Z.land x (Z.ones (fp_mw f))

/-- Fpu.v:177. -/
def fp_decode (f : format) (x : Int) : spec_float :=
  let s := fp_sign_bit f x
  let e := fp_exp_field f x
  let m := fp_man_field f x
  if e == 0 then
    match Z.view m with
    | .Zpos p => S754_finite s p (fp_emin f)
    | _ => S754_zero s
  else if e == Z.ones (fp_ew f) then
    (if m == 0 then S754_infinity s else S754_nan)
  else
    match Z.view (Z.shiftlZ 1 (fp_mw f) + m) with
    | .Zpos p => S754_finite s p (e + fp_emin f - 1)
    | _ => S754_nan   -- unreachable: the implicit bit makes this positive

/-- Fpu.v:195. The one NaN this semantics ever produces. -/
def fp_canonical_nan (f : format) : Int :=
  Z.shiftlZ (Z.ones (fp_ew f)) (fp_mw f) + Z.shiftlZ 1 (fp_mw f - 1)

/-- Fpu.v:198. -/
def fp_encode (f : format) (x : spec_float) : Int :=
  let sb (s : Bool) : Int := if s then Z.shiftlZ 1 (fp_mw f + fp_ew f) else 0
  match x with
  | S754_nan => fp_canonical_nan f
  | S754_zero s => sb s
  | S754_infinity s => sb s + Z.shiftlZ (Z.ones (fp_ew f)) (fp_mw f)
  | S754_finite s m e =>
    if decide (Z.pos (Pos.size m) < fp_prec f)
    then sb s + Z.pos m                                   -- subnormal
    else sb s + Z.shiftlZ (e - fp_emin f + 1) (fp_mw f)
         + (Z.pos m - Z.shiftlZ 1 (fp_mw f))

/-- Fpu.v:214. A signalling NaN is a NaN whose leading mantissa bit is clear. -/
def fp_is_snan (f : format) (x : Int) : Bool :=
  (fp_exp_field f x == Z.ones (fp_ew f)) &&
    (!(fp_man_field f x == 0) && !(Z.testbit x (fp_mw f - 1)))

/-- Fpu.v:219. -/
def fp_is_nan (f : format) (x : Int) : Bool :=
  (fp_exp_field f x == Z.ones (fp_ew f)) && !(fp_man_field f x == 0)

/-- Fpu.v:228. Flip the sign bit. -/
def fp_neg (f : format) (x : Int) : Int :=
  Z.lxor x (Z.shiftlZ 1 (fp_mw f + fp_ew f))

/-! ## The rounding kernel, with flags (Fpu.v:231-320) -/

/-- Fpu.v:245. -/
def mk_round_flags (of_ uf nx : Bool) : fflags :=
  Fflags false false of_ uf nx

/-- Fpu.v:262. Tininess detected after rounding (unbounded exponent range). -/
def round_tiny (f : format) (md : rmode) (sx : Bool) (mx ex : Int) (lx : location) : Bool :=
  let (mrs, e') := shr (shr_record_of_loc mx lx) ex (Zdigits2 mx - fp_prec f)
  let m' := BinarySingleNaN.choice_mode (flocq_mode md) sx (shr_record.shr_m mrs)
              (loc_of_shr_record mrs)
  decide (Zdigits2 m' + e' ≤ fp_emin f + fp_prec f - 1)

/-- Fpu.v:269. -/
def round_aux (f : format) (md : rmode) (sx : Bool) (mx ex : Int) (lx : location) :
    spec_float × fflags :=
  let p := fp_prec f
  let em := fp_emax f
  let (mrs1, e1) := shr_fexp p em mx ex lx
  let l1 := loc_of_shr_record mrs1
  let nx := match l1 with | loc_Exact => false | _ => true
  let (mrs2, e2) :=
    shr_fexp p em (BinarySingleNaN.choice_mode (flocq_mode md) sx (shr_record.shr_m mrs1) l1)
             e1 loc_Exact
  match Z.view (shr_record.shr_m mrs2) with
  | .Z0 => (S754_zero sx, mk_round_flags false nx nx)
  | .Zpos mz =>
    if decide (e2 ≤ em - p)
    then (S754_finite sx mz e2,
          mk_round_flags false (nx && round_tiny f md sx mx ex lx) nx)
    else (BinarySingleNaN.binary_overflow p em (flocq_mode md) sx,
          mk_round_flags true false true)
  | .Zneg _ => (S754_nan, no_flags)   -- unreachable: mantissas are non-negative

/-- Fpu.v:301. Left-align an exact operand to the canonical exponent, then round. -/
def round_exact (f : format) (md : rmode) (sx : Bool) (mx : Pos) (ex : Int) :
    spec_float × fflags :=
  let (mz, ez) :=
    shl_align mx ex (fexp (fp_prec f) (fp_emax f) (Z.pos (digits2_pos mx) + ex))
  round_aux f md sx (Z.pos mz) ez loc_Exact

/-- Fpu.v:308. -/
theorem round_aux_value (f : format) (md : rmode) (sx : Bool) (mx ex : Int) (lx : location) :
    (round_aux f md sx mx ex lx).1
    = BinarySingleNaN.binary_round_aux (fp_prec f) (fp_emax f) (flocq_mode md) sx mx ex lx := by
  unfold round_aux BinarySingleNaN.binary_round_aux BinarySingleNaN.binary_fit_aux
  dsimp only
  split <;> rename_i h <;> simp only [h] <;> split <;> rfl

/-! ## Exact operands as scaled integers (Fpu.v:322-370) -/

/-- Fpu.v:333. -/
def sf_scaled (x : spec_float) : Int × Int :=
  match x with
  | S754_finite s m e => ((if s then -(Z.pos m) else Z.pos m), e)
  | _ => (0, 0)

/-- Fpu.v:339. -/
def scaled_add (a b : Int × Int) : Int × Int :=
  let (ma, ea) := a
  let (mb, eb) := b
  let e := min ea eb
  (Z.shiftlZ ma (ea - e) + Z.shiftlZ mb (eb - e), e)

/-- Fpu.v:345. -/
def sf_sign (x : spec_float) : Bool :=
  match x with
  | S754_zero s | S754_infinity s | S754_finite s _ _ => s
  | S754_nan => false

/-- Fpu.v:356. The sign of an exactly zero sum. -/
def zero_sign (md : rmode) (sa sb : Bool) : Bool :=
  if sa == sb then sa
  else match md with | RDN => true | _ => false

/-- Fpu.v:363. -/
def round_scaled (f : format) (md : rmode) (szero : Bool) (v : Int × Int) :
    spec_float × fflags :=
  let (m, e) := v
  match Z.view m with
  | .Z0 => (S754_zero szero, no_flags)
  | .Zpos p => round_exact f md false p e
  | .Zneg p => round_exact f md true p e

/-! ## NaN pre-pass (Fpu.v:372-400) -/

/-- Fpu.v:380. -/
def nan_pass1 (f : format) (a : Int) : Option (Int × fflags) :=
  if fp_is_nan f a
  then some (fp_canonical_nan f, if fp_is_snan f a then nv_flag else no_flags)
  else none

/-- Fpu.v:386. -/
def nan_pass2 (f : format) (a b : Int) : Option (Int × fflags) :=
  if fp_is_nan f a || fp_is_nan f b
  then some (fp_canonical_nan f,
             if fp_is_snan f a || fp_is_snan f b then nv_flag else no_flags)
  else none

/-- Fpu.v:392. -/
def nan_pass3 (f : format) (a b c : Int) : Option (Int × fflags) :=
  if fp_is_nan f a || (fp_is_nan f b || fp_is_nan f c)
  then some (fp_canonical_nan f,
             if fp_is_snan f a || (fp_is_snan f b || fp_is_snan f c)
             then nv_flag else no_flags)
  else none

/-- Fpu.v:399. -/
def enc (f : format) (r : spec_float × fflags) : Int × fflags :=
  (fp_encode f r.1, r.2)

/-! ## Addition, subtraction, multiplication, division, square root (Fpu.v:402-483) -/

/-- Fpu.v:404. -/
def fp_add (f : format) (md : rmode) (a b : Int) : Int × fflags :=
  match nan_pass2 f a b with
  | some r => r
  | none =>
    let x := fp_decode f a
    let y := fp_decode f b
    match x, y with
    | S754_infinity sa, S754_infinity sb =>
      if sa == sb
      then (fp_encode f (S754_infinity sa), no_flags)
      else (fp_canonical_nan f, nv_flag)   -- inf - inf
    | S754_infinity sa, _ => (fp_encode f (S754_infinity sa), no_flags)
    | _, S754_infinity sb => (fp_encode f (S754_infinity sb), no_flags)
    | _, _ =>
      enc f (round_scaled f md (zero_sign md (sf_sign x) (sf_sign y))
                          (scaled_add (sf_scaled x) (sf_scaled y)))

/-- Fpu.v:427. Subtraction is addition of the sign-flipped operand. -/
def fp_sub (f : format) (md : rmode) (a b : Int) : Int × fflags :=
  fp_add f md a (fp_neg f b)

/-- Fpu.v:430. -/
def fp_mul (f : format) (md : rmode) (a b : Int) : Int × fflags :=
  match nan_pass2 f a b with
  | some r => r
  | none =>
    match fp_decode f a, fp_decode f b with
    | S754_infinity _, S754_zero _ | S754_zero _, S754_infinity _ =>
      (fp_canonical_nan f, nv_flag)        -- 0 × inf
    | S754_infinity sa, y => (fp_encode f (S754_infinity (Bool.xor sa (sf_sign y))), no_flags)
    | x, S754_infinity sb => (fp_encode f (S754_infinity (Bool.xor (sf_sign x) sb)), no_flags)
    | S754_zero sa, y => (fp_encode f (S754_zero (Bool.xor sa (sf_sign y))), no_flags)
    | x, S754_zero sb => (fp_encode f (S754_zero (Bool.xor (sf_sign x) sb)), no_flags)
    | S754_finite sa ma ea, S754_finite sb mb eb =>
      enc f (round_exact f md (Bool.xor sa sb) (Pos.mul ma mb) (ea + eb))
    | _, _ => (fp_canonical_nan f, no_flags)  -- unreachable: NaNs handled above

/-- Fpu.v:447. -/
def fp_div (f : format) (md : rmode) (a b : Int) : Int × fflags :=
  match nan_pass2 f a b with
  | some r => r
  | none =>
    match fp_decode f a, fp_decode f b with
    | S754_infinity _, S754_infinity _ => (fp_canonical_nan f, nv_flag)
    | S754_zero _, S754_zero _ => (fp_canonical_nan f, nv_flag)
    | S754_infinity sa, y => (fp_encode f (S754_infinity (Bool.xor sa (sf_sign y))), no_flags)
    | x, S754_infinity sb => (fp_encode f (S754_zero (Bool.xor (sf_sign x) sb)), no_flags)
    | S754_zero sa, y => (fp_encode f (S754_zero (Bool.xor sa (sf_sign y))), no_flags)
    -- finite nonzero / zero: the only divide-by-zero there is
    | x, S754_zero sb => (fp_encode f (S754_infinity (Bool.xor (sf_sign x) sb)), dz_flag)
    | S754_finite sa ma ea, S754_finite sb mb eb =>
      let (mz, ez, lz) :=
        SFdiv_core_binary (fp_prec f) (fp_emax f) (Z.pos ma) ea (Z.pos mb) eb
      enc f (round_aux f md (Bool.xor sa sb) mz ez lz)
    | _, _ => (fp_canonical_nan f, no_flags)  -- unreachable

/-- Fpu.v:469. sqrt(-0) is -0. -/
def fp_sqrt (f : format) (md : rmode) (a : Int) : Int × fflags :=
  match nan_pass1 f a with
  | some r => r
  | none =>
    match fp_decode f a with
    | S754_zero s => (fp_encode f (S754_zero s), no_flags)
    | S754_infinity false => (fp_encode f (S754_infinity false), no_flags)
    | S754_infinity true => (fp_canonical_nan f, nv_flag)
    | S754_finite true _ _ => (fp_canonical_nan f, nv_flag)
    | S754_finite false m e =>
      let (mz, ez, lz) := SFsqrt_core_binary (fp_prec f) (fp_emax f) (Z.pos m) e
      enc f (round_aux f md false mz ez lz)
    | S754_nan => (fp_canonical_nan f, no_flags)  -- unreachable

/-! ## Fused multiply-add (Fpu.v:485-544) -/

/-- Fpu.v:497. -/
def fp_fma (f : format) (md : rmode) (a b c : Int) : Int × fflags :=
  let x := fp_decode f a
  let y := fp_decode f b
  let prod_invalid :=
    match x, y with
    | S754_infinity _, S754_zero _ | S754_zero _, S754_infinity _ => true
    | _, _ => false
  if prod_invalid && !(fp_is_nan f a || fp_is_nan f b)
  then (fp_canonical_nan f, nv_flag)
  else
  match nan_pass3 f a b c with
  | some r => r
  | none =>
    let z := fp_decode f c
    let sp := Bool.xor (sf_sign x) (sf_sign y)
    match x, y with
    -- An infinite product: the addend can only make it invalid.
    | S754_infinity _, _ | _, S754_infinity _ =>
      match z with
      | S754_infinity sz =>
        if sp == sz
        then (fp_encode f (S754_infinity sp), no_flags)
        else (fp_canonical_nan f, nv_flag)
      | _ => (fp_encode f (S754_infinity sp), no_flags)
    | S754_finite _ ma ea, S754_finite _ mb eb =>
      match z with
      | S754_infinity sz => (fp_encode f (S754_infinity sz), no_flags)
      | _ =>
        let prod := ((if sp then -(Z.pos (Pos.mul ma mb))
                            else Z.pos (Pos.mul ma mb)), ea + eb)
        enc f (round_scaled f md (zero_sign md sp (sf_sign z))
                            (scaled_add prod (sf_scaled z)))
    -- A zero product: the sum is the addend, but the zero sign still follows the product's sign.
    | _, _ =>
      match z with
      | S754_infinity sz => (fp_encode f (S754_infinity sz), no_flags)
      | _ => enc f (round_scaled f md (zero_sign md sp (sf_sign z))
                                 (sf_scaled z))

/-! ## Comparisons, min/max, classification (Fpu.v:546-598) -/

/-- Fpu.v:549. `none` is "unordered". -/
def fp_compare (f : format) (a b : Int) : Option Ordering :=
  SFcompare (fp_decode f a) (fp_decode f b)

/-- Fpu.v:555. feq is quiet. -/
def fp_eq (f : format) (a b : Int) : Bool × fflags :=
  ((match fp_compare f a b with | some .eq => true | _ => false),
   if fp_is_snan f a || fp_is_snan f b then nv_flag else no_flags)

/-- Fpu.v:559. flt is signalling. -/
def fp_lt (f : format) (a b : Int) : Bool × fflags :=
  ((match fp_compare f a b with | some .lt => true | _ => false),
   if fp_is_nan f a || fp_is_nan f b then nv_flag else no_flags)

/-- Fpu.v:563. fle is signalling. -/
def fp_le (f : format) (a b : Int) : Bool × fflags :=
  ((match fp_compare f a b with | some .lt | some .eq => true | _ => false),
   if fp_is_nan f a || fp_is_nan f b then nv_flag else no_flags)

/-- Fpu.v:572. fmin/fmax. -/
def fp_minmax (f : format) (is_max : Bool) (a b : Int) : Int × fflags :=
  let fl := if fp_is_snan f a || fp_is_snan f b then nv_flag else no_flags
  if fp_is_nan f a && fp_is_nan f b then (fp_canonical_nan f, fl)
  else if fp_is_nan f a then (b, fl)
  else if fp_is_nan f b then (a, fl)
  else
    let a_lt_b :=
      match fp_compare f a b with
      | some .lt => true
      | some .eq => fp_sign_bit f a && !(fp_sign_bit f b)
      | _ => false
    ((if Bool.xor is_max a_lt_b then a else b), fl)

/-- Fpu.v:588. The fclass bit mask. -/
def fp_class (f : format) (a : Int) : Int :=
  let s := fp_sign_bit f a
  let e := fp_exp_field f a
  let m := fp_man_field f a
  if e == Z.ones (fp_ew f) then
    (if m == 0 then (if s then 1 else Z.shiftlZ 1 7)
     else if fp_is_snan f a then Z.shiftlZ 1 8 else Z.shiftlZ 1 9)
  else if e == 0 then
    (if m == 0 then (if s then Z.shiftlZ 1 3 else Z.shiftlZ 1 4)
     else if s then Z.shiftlZ 1 2 else Z.shiftlZ 1 5)
  else (if s then Z.shiftlZ 1 1 else Z.shiftlZ 1 6)

/-! ## Conversions (Fpu.v:600-674) -/

/-- Fpu.v:614. -/
def int_lo (signed : Bool) (bits : Int) : Int :=
  if signed then -(Z.shiftlZ 1 (bits - 1)) else 0
/-- Fpu.v:616. -/
def int_hi (signed : Bool) (bits : Int) : Int :=
  if signed then Z.shiftlZ 1 (bits - 1) - 1 else Z.shiftlZ 1 bits - 1

/-- Fpu.v:620. Two's-complement image of `v` in `bits` bits. -/
def int_wrap (bits v : Int) : Int := Z.land v (Z.ones bits)

/-- Fpu.v:622. float → integer, saturating. -/
def fp_to_int (f : format) (md : rmode) (signed : Bool) (bits : Int) (a : Int) : Int × fflags :=
  let sat (v : Int) : Int × fflags := (int_wrap bits v, nv_flag)
  if fp_is_nan f a then sat (int_hi signed bits)
  else
    match fp_decode f a with
    | S754_infinity s => sat (if s then int_lo signed bits else int_hi signed bits)
    | S754_zero _ => (0, no_flags)
    | S754_nan => sat (int_hi signed bits)   -- unreachable
    | S754_finite s m e =>
      let (q, l) :=
        if decide (0 ≤ e) then (Z.shiftlZ (Z.pos m) e, loc_Exact)
        else
          let d := Z.shiftlZ 1 (-e)
          let (q, r) := Z.div_eucl (Z.pos m) d
          (q, new_location d r)
      let q' := BinarySingleNaN.choice_mode (flocq_mode md) s q l
      let v := if s then -q' else q'
      if decide (v < int_lo signed bits) || decide (int_hi signed bits < v)
      then sat (if s then int_lo signed bits else int_hi signed bits)
      else (int_wrap bits v,
            match l with | loc_Exact => no_flags | _ => nx_flag)

/-- Fpu.v:654. integer → float. -/
def fp_of_int (f : format) (md : rmode) (signed : Bool) (bits : Int) (v : Int) : Int × fflags :=
  let u := int_wrap bits v
  let n := if signed && Z.testbit u (bits - 1)
           then u - Z.shiftlZ 1 bits else u
  enc f (round_scaled f md false (n, 0))

/-- Fpu.v:665. float → float. -/
def fp_convert (src dst : format) (md : rmode) (a : Int) : Int × fflags :=
  if fp_is_nan src a
  then (fp_canonical_nan dst, if fp_is_snan src a then nv_flag else no_flags)
  else
    match fp_decode src a with
    | S754_zero s => (fp_encode dst (S754_zero s), no_flags)
    | S754_infinity s => (fp_encode dst (S754_infinity s), no_flags)
    | S754_nan => (fp_canonical_nan dst, no_flags)   -- unreachable
    | S754_finite s m e => enc dst (round_exact dst md s m e)

end LPS

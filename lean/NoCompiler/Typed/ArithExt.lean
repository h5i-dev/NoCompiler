import NoCompiler.Typed.ArithDefs

/-
Arithmetic rules beyond the ones in Check.lean (`Fn.arith`): what `Fn.arith` does for every
register-writing instruction it has no rule of its own for. Proved in
NoCompiler/Typed/Sound/ArithExt.lean (`Fn.arithExt_sound`), which `Fn.arith_sound` uses.

Owned by agent U (docs/typed, STATUS files): the rules the Rust checker has (I20/I23/I29/...).
The default is the note's last row: a fresh word `x` with `0 ≤ x < 2^64`.
-/
namespace NoCompiler.Typed

namespace Fn
variable (f : Fn)

/-- The immediate forms: `xori −1`, `ori`/`xori` with a disjoint constant, `andi` masks, `sltiu`, `slti`. -/
def arith2I (S : STy) (i : Instr) : Option STy :=
  let x := f.freshAt S
  match i with
  | .iop .xori rd rs imm =>
    if imm.toInt = -1 then (S.reg rs).map fun e => S.setReg rd (some ((IExpr.lit (-1)).sub e))
    else (S.reg rs).bind fun e => disjConst S rd e (imm.signExtend 64).toNat
  | .iop .ori rd rs imm =>
    (S.reg rs).bind fun e => disjConst S rd e (imm.signExtend 64).toNat
  -- andi with a mask −2^k: the unsigned representative rounded down to a multiple of 2^k (I23)
  | .iop .andi rd rs imm =>
    match (List.range 12).find? (fun k => imm.signExtend 64 == BitVec.allOnes 64 <<< k) with
    | some k =>
      (S.reg rs).map fun e =>
        let u := Fn.urep S (x + 1) e
        (S.setReg rd (some ((IExpr.var x).smul (2 ^ k)))).addFacts (u.2 ++ quotFacts x u.1 (2 ^ k))
    | none =>
      -- a single bit 2^k (k ≥ 1; reached once `arith` routes it here): 2^k·b, q = ⌊e / 2^k⌋,
      -- b = q mod 2, for `e` of known range (the Rust checker's and_const)
      match (List.range 12).find? (fun k => 1 ≤ k && imm.signExtend 64 == BitVec.twoPow 64 k) with
      | some k =>
        (S.reg rs).bind fun e =>
          if S.ent (.and (.le (.lit 0) e) (.lt e (.lit (2 ^ 64)))) then
            some ((S.setReg rd (some ((IExpr.var x).smul (2 ^ k)))).addFacts
              (quotFacts (x + 1) e (2 ^ k) ++ remFacts x (.var (x + 1)) 2))
          else none
      | none => none
  | .iop .sltiu rd rs imm =>
    (S.reg rs).map fun e =>
      (S.setReg rd (some (.var x))).addFacts
        ((Fn.urep S (x + 1) e).2 ++ [lessFact x (Fn.urep S (x + 1) e).1 (.lit (imm.signExtend 64).toNat)])
  | .iop .slti rd rs imm =>
    (S.reg rs).map fun e =>
      (S.setReg rd (some (.var x))).addFacts
        ((Fn.srep S (x + 1) e).2 ++ [lessFact x (Fn.srep S (x + 1) e).1 (.lit imm.toInt)])
  | _ => none

/-- Comparisons and min/max of two registers (I23). -/
def arith2Cmp (S : STy) (i : Instr) : Option STy :=
  let x := f.freshAt S
  match i with
  | .rop .sltu rd a b =>
    match S.reg a, S.reg b with
    | some e1, some e2 =>
      some ((S.setReg rd (some (.var x))).addFacts
        ((Fn.urep S (x + 1) e1).2 ++ (Fn.urep S (x + 2) e2).2 ++
          [lessFact x (Fn.urep S (x + 1) e1).1 (Fn.urep S (x + 2) e2).1]))
    | _, _ => none
  | .rop .slt rd a b =>
    match S.reg a, S.reg b with
    | some e1, some e2 =>
      some ((S.setReg rd (some (.var x))).addFacts
        ((Fn.srep S (x + 1) e1).2 ++ (Fn.srep S (x + 2) e2).2 ++
          [lessFact x (Fn.srep S (x + 1) e1).1 (Fn.srep S (x + 2) e2).1]))
    | _, _ => none
  | .rop .max rd a b | .rop .min rd a b | .rop .maxu rd a b | .rop .minu rd a b =>
    let uns := match i with | .rop .maxu .. | .rop .minu .. => true | _ => false
    let isMax := match i with | .rop .max .. | .rop .maxu .. => true | _ => false
    match S.reg a, S.reg b with
    | some e1, some e2 =>
      let r1 := if uns then Fn.urep S (x + 1) e1 else Fn.srep S (x + 1) e1
      let r2 := if uns then Fn.urep S (x + 2) e2 else Fn.srep S (x + 2) e2
      some ((S.setReg rd (some (.var x))).addFacts (r1.2 ++ r2.2 ++ [minMaxFact isMax x r1.1 r2.1]))
    | _, _ => none
  | _ => none

/-- Division and remainder (by constants, by positive divisors), the `xor` zero test, and
    `and`/`or` of 0/1 values (I23, I29, I35). -/
def arith2Div (S : STy) (i : Instr) : Option STy :=
  let x := f.freshAt S
  match i with
  -- unsigned division and remainder by a constant `c` (mod 2^64) > 0 (I23)
  | .rop .divu rd a b | .rop .remu rd a b =>
    let isDiv := match i with | .rop .divu .. => true | _ => false
    match S.reg a, S.reg b with
    | some e1, some ⟨c, []⟩ =>
      let cu := c % 2 ^ 64
      if 0 < cu then
        let u := Fn.urep S (x + 1) e1
        if isDiv then
          some ((S.setReg rd (some (.var x))).addFacts (u.2 ++ quotFacts x u.1 cu))
        else
          some ((S.setReg rd (some (.var x))).addFacts (u.2 ++ remFacts x u.1 cu))
      else none
    -- any divisor provably > 0 (its range known): bounds only, as the Rust checker
    | some e1, some e2 =>
      let u1 := Fn.urep S (x + 1) e1
      let u2 := Fn.urep S (x + 2) e2
      if u2.2 = [] ∧ S.ent (.lt (.lit 0) u2.1) = true then
        some ((S.setReg rd (some (.var x))).addFacts (u1.2 ++ divBound isDiv x u1.1 u2.1))
      else none
    | _, _ => none
  -- xor: a fresh word that is 0 exactly when the operands are equal mod 2^64 (I35)
  | .rop .xor rd a b =>
    match S.reg a, S.reg b with
    | some e1, some e2 =>
      some ((S.setReg rd (some (.var x))).addFacts
        [.le (.lit 0) (.var x), .lt (.var x) (.lit (2 ^ 64)),
         .or (.and (.eq (.var x) (.lit 0)) (Constr.eqMod e1 e2))
             (.and (.not (.eq (.var x) (.lit 0))) (.not (Constr.eqMod e1 e2)))])
    | _, _ => none
  -- and/or/xor of two values provably in {0, 1}: exact (I29)
  | .rop .and rd a b | .rop .or rd a b =>
    let g : Nat → Nat → Nat := match i with | .rop .and .. => (· &&& ·) | _ => (· ||| ·)
    match S.reg a, S.reg b with
    | some e1, some e2 =>
      if S.ent (isBit e1) && S.ent (isBit e2) then
        some ((S.setReg rd (some (.var x))).addFacts [bitTable g x e1 e2])
      else none
    | _, _ => none
  | _ => none

/-- The `.uw` forms, `slli.uw`, bit counts, `slliw`, `mulw` by a constant, `zext.h`, `srai`, `srliw`. -/
def arith2Sh (S : STy) (i : Instr) : Option STy :=
  let x := f.freshAt S
  match i with
  -- zero-extension of the low word: `z` with `2^32 ∣ e − z`, `0 ≤ z < 2^32`
  | .rwop .adduw rd a b | .rwop .sh1adduw rd a b | .rwop .sh2adduw rd a b | .rwop .sh3adduw rd a b =>
    let n : Nat := match i with | .rwop .sh1adduw .. => 1 | .rwop .sh2adduw .. => 2 | .rwop .sh3adduw .. => 3 | _ => 0
    match S.reg a, S.reg b with
    | some e1, some e2 =>
      some ((S.setReg rd (some (((IExpr.var x).smul (2 ^ n)).add e2))).addFacts (lowFacts x e1 32))
    | _, _ => none
  | .shift .slliuw rd rs sh =>
    (S.reg rs).map fun e =>
      (S.setReg rd (some ((IExpr.var x).smul (2 ^ sh.toNat)))).addFacts (lowFacts x e 32)
  -- bit counts: at most the width (I23)
  | .uop .clz rd _ | .uop .ctz rd _ | .uop .cpop rd _ =>
    some ((S.setReg rd (some (.var x))).addFacts (boundFacts x 64))
  | .uop .clzw rd _ | .uop .ctzw rd _ | .uop .cpopw rd _ =>
    some ((S.setReg rd (some (.var x))).addFacts (boundFacts x 32))
  -- slliw and mulw by a constant: the sign-extended low word of the product (I23)
  | .shiftw .slliw rd rs sh =>
    (S.reg rs).map fun e => Fn.word32 S rd x (e.smul (2 ^ sh.toNat))
  | .rwop .mulw rd a b =>
    match S.reg a, S.reg b with
    | some e1, some ⟨c, []⟩ => some (Fn.word32 S rd x (e1.smul c))
    | some ⟨c, []⟩, some e2 => some (Fn.word32 S rd x (e2.smul c))
    | _, _ => none
  | .uop .zexth rd rs =>
    (S.reg rs).map fun e => (S.setReg rd (some (.var x))).addFacts (lowFacts x e 16)
  -- arithmetic right shift: the signed representative divided by 2^sh, rounded down
  | .shift .srai rd rs sh =>
    (S.reg rs).map fun e =>
      let r := Fn.srep S (x + 1) e
      (S.setReg rd (some (.var x))).addFacts (r.2 ++ quotFacts x r.1 (2 ^ sh.toNat))
  -- srliw by sh ≥ 1: the low word (zero-extended) divided by 2^sh; below 2^31, so the sign
  -- extension keeps it (I35)
  | .shiftw .srliw rd rs sh =>
    if 1 ≤ sh.toNat then
      (S.reg rs).map fun e =>
        (S.setReg rd (some (.var x))).addFacts
          (lowFacts (x + 1) e 32 ++ quotFacts x (.var (x + 1)) (2 ^ sh.toNat))
    else none
  | _ => none

/-- The rules of decisions.md I23 not in `arith`, by class. `x = f.freshAt S` is the result,
    `x+1`, `x+2` the representatives' variables. -/
def arith2 (S : STy) (i : Instr) : Option STy :=
  match f.arith2I S i with
  | some S' => some S'
  | none =>
    match f.arith2Cmp S i with
    | some S' => some S'
    | none =>
      match f.arith2Div S i with
      | some S' => some S'
      | none => f.arith2Sh S i

/-- `and`/`or`/`xor rd, a, b` with one operand a known constant. -/
def andConst (S : STy) (i : Instr) : Option STy :=
  match i with
  | .rop .and rd a b =>
    match S.reg a, S.reg b with
    | some e1, some ⟨c, []⟩ => andConstOf S rd (f.freshAt S) e1 c
    | some ⟨c, []⟩, some e2 => andConstOf S rd (f.freshAt S) e2 c
    | _, _ => none
  | .rop .or rd a b | .rop .xor rd a b =>
    match S.reg a, S.reg b with
    | some e1, some ⟨c, []⟩ => disjConst S rd e1 (c % 2 ^ 64).toNat
    | some ⟨c, []⟩, some e2 => disjConst S rd e2 (c % 2 ^ 64).toNat
    | _, _ => none
  | _ => none

/-- In order: constant folding, the rules above, the fresh-word default. -/
def arithExt (S : STy) (i : Instr) : Option STy :=
  match Fn.fold S i with
  | some S' => some S'
  | none =>
    match f.andConst S i with
    | some S' => some S'
    | none =>
    match f.arith2 S i with
    | some S' => some S'
    | none =>
      match writesReg i with
      | some rd => some (anyWord S rd (f.freshAt S))
      | none => none

end Fn

end NoCompiler.Typed

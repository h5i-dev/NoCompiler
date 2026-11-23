import NoCompiler.Typed.CheckBase

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

/-! ### More arithmetic (decisions.md I23, I29, I35; tried before `arith`) -/

/-- The value a register-writing instruction (other than `lui`, `auipc` and loads) computes
    from its operand values, exactly as `exec` does. -/
def pureVal : Instr → Word → Word → Option Word
  | .iop op _ _ imm, a, _ => some (evalI op a (imm.signExtend 64))
  | .addiw _ _ imm, a, _ => some (sext32 (a + imm.signExtend 64))
  | .shift op _ _ sh, a, _ => some (evalSh op a sh.toNat)
  | .shiftw op _ _ sh, a, _ => some (evalShW op a sh.toNat)
  | .rop op _ _ _, a, b => some (evalR op a b)
  | .rwop op _ _ _, a, b => some (evalRW op a b)
  | .uop op _ _, a, _ => some (evalU op a)
  | _, _, _ => none

/-- Its source registers (`x0` for an absent second one). -/
def srcRegs : Instr → Reg × Reg
  | .iop _ _ rs _ | .addiw _ rs _ | .shift _ _ rs _ | .shiftw _ _ rs _ | .uop _ _ rs => (rs, 0)
  | .rop _ _ a b | .rwop _ _ a b => (a, b)
  | _ => (0, 0)

/-- Constant folding: when every source is a known constant, the result is computed. -/
def fold (S : STy) (i : Instr) : Option STy :=
  match writesReg i, S.reg (srcRegs i).1, S.reg (srcRegs i).2 with
  | some rd, some ⟨c1, []⟩, some ⟨c2, []⟩ =>
    (pureVal i (BitVec.ofInt 64 c1) (BitVec.ofInt 64 c2)).map fun v =>
      S.setReg rd (some (.lit v.toNat))
  | _, _, _ => none

/-- `x ∈ {0, 1}` and `x = 1 ⇔ a < b`. -/
def lessFact (x : Var) (a b : IExpr) : Constr :=
  .or (.and (.eq (.var x) (.lit 1)) (.lt a b)) (.and (.eq (.var x) (.lit 0)) (.le b a))

/-- `x` is the larger (`isMax`) or the smaller of `a` and `b`, and one of them. -/
def minMaxFact (isMax : Bool) (x : Var) (a b : IExpr) : Constr :=
  let le (p q : IExpr) : Constr := .le p q
  .and (if isMax then le a (.var x) else le (.var x) a)
    (.and (if isMax then le b (.var x) else le (.var x) b)
      (.or (.eq (.var x) a) (.eq (.var x) b)))

/-- `x` is `e` modulo `2^n`: `2^n ∣ e − x`, `0 ≤ x < 2^n`. -/
def lowFacts (x : Var) (e : IExpr) (n : Nat) : List Constr :=
  [.dvd (2 ^ n) (e.sub (.var x)), .le (.lit 0) (.var x), .lt (.var x) (.lit (2 ^ n))]

/-- `x = ⌊u / c⌋`: `0 ≤ u − c·x < c` (no remainder variable, I37). -/
def quotFacts (x : Var) (u : IExpr) (c : Int) : List Constr :=
  [.le (.lit 0) (u.sub ((IExpr.var x).smul c)), .lt (u.sub ((IExpr.var x).smul c)) (.lit c)]

/-- `x = u mod c`: `c ∣ u − x`, `0 ≤ x < c`. -/
def remFacts (x : Var) (u : IExpr) (c : Int) : List Constr :=
  [.dvd c.toNat (u.sub (.var x)), .le (.lit 0) (.var x), .lt (.var x) (.lit c)]

/-- The number of trailing zero bits of `n > 0` (below 64; untrusted: the rule re-checks). -/
def tz (n : Nat) : Nat := ((List.range 64).find? (fun j => n / 2 ^ j % 2 == 1)).getD 0

/-- `or`/`xor` with a constant `cu` whose bits miss those of `e` (I23): `e + cu`. Needs
    `0 ≤ e < 2^64` and either `e < 2^j` with `2^j ∣ cu`, or `2^t ∣ e` with `cu < 2^t`. -/
def disjConst (S : STy) (rd : Reg) (e : IExpr) (cu : Nat) : Option STy :=
  if cu = 0 then some (S.setReg rd (some e))
  else if S.ent (.and (.le (.lit 0) e) (.lt e (.lit (2 ^ 64)))) then
    let j := tz cu
    let t := cu.log2 + 1
    if (cu % 2 ^ j == 0 && S.ent (.lt e (.lit (2 ^ j)))) ||
       (decide (cu < 2 ^ t) && S.ent (.dvd (2 ^ t) e)) then
      some (S.setReg rd (some (e.add (.lit cu))))
    else none
  else none

/-- `divu`/`remu` by a positive divisor: `0 ≤ x < 2^64`, `x ≤ u(a)`, and `x < u(b)` for `remu`. -/
def divBound (isDiv : Bool) (x : Var) (ua ub : IExpr) : List Constr :=
  [.le (.lit 0) (.var x), .lt (.var x) (.lit (2 ^ 64)), .le (.var x) ua] ++
    (if isDiv then [] else [.lt (.var x) ub])

/-- `0 ≤ x ≤ b`. -/
def boundFacts (x : Var) (b : Int) : List Constr := [.le (.lit 0) (.var x), .le (.var x) (.lit b)]

/-- `0 ≤ e ≤ 1`. -/
def isBit (e : IExpr) : Constr := .and (.le (.lit 0) e) (.le e (.lit 1))

/-- The table of a bitwise operation on 0/1 operands `a`, `b`, result `x` (I29). -/
def bitTable (g : Nat → Nat → Nat) (x : Var) (a b : IExpr) : Constr :=
  let row (p q : Nat) : Constr :=
    .and (.eq a (.lit p)) (.and (.eq b (.lit q)) (.eq (.var x) (.lit (g p q))))
  .or (row 0 0) (.or (row 0 1) (.or (row 1 0) (row 1 1)))

/-- The rules of decisions.md I23 not in `arith`. `x = f.freshAt S` is the result, `x+1`,
    `x+2` the representatives' variables. -/
def arith2 (S : STy) (i : Instr) : Option STy :=
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

/-- `and` of `e` with the constant `c` (mod 2^64, I23): a mask `2^k − 1` gives `x = e mod 2^k`; a
    mask `−2^k` gives `2^k·q` with `q` the representative's quotient (as `andi`). -/
def andConstOf (S : STy) (rd : Reg) (x : Var) (e : IExpr) (c : Int) : Option STy :=
  let cu := (c % 2 ^ 64).toNat
  match (List.range 64).find? (fun k => cu == 2 ^ k - 1) with
  | some k => some ((S.setReg rd (some (.var x))).addFacts (lowFacts x e k))
  | none =>
    match (List.range 64).find? (fun k => cu + 2 ^ k == 2 ^ 64) with
    | some k =>
      let u := Fn.urep S (x + 1) e
      some ((S.setReg rd (some ((IExpr.var x).smul (2 ^ k)))).addFacts (u.2 ++ quotFacts x u.1 (2 ^ k)))
    | none => none

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

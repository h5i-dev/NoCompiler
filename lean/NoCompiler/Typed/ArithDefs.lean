import NoCompiler.Typed.CheckBase

/-
The facts and helpers the ArithExt rules (NoCompiler/Typed/ArithExt.lean) use: the value an
instruction computes, constant folding, the fact shapes (comparisons, min/max, low bits,
quotients, remainders, bounds, 0/1 tables), disjoint constants and masks. Owned by agent U.
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

end Fn

end NoCompiler.Typed

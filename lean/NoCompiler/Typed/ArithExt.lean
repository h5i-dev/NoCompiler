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

/-- The rules of decisions.md I23 not in `arith`. `x = f.freshAt S` is the result, `x+1`,
    `x+2` the representatives' variables. -/
def arith2 (S : STy) (i : Instr) : Option STy :=
  let x := f.freshAt S
  match i with
  | .iop .xori rd rs imm =>
    if imm.toInt = -1 then (S.reg rs).map fun e => S.setReg rd (some ((IExpr.lit (-1)).sub e)) else none
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
  | _ => none

/-- In order: constant folding, the rules above, the fresh-word default. -/
def arithExt (S : STy) (i : Instr) : Option STy :=
  match Fn.fold S i with
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

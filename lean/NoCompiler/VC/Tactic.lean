import Lean
import NoCompiler.VC.Explore

/-
`vc_run`: evaluate a segment's symbolic run in a goal, milestone 4c
(docs/design/prior-art-others.md, "Implementation plan").

A cut point's condition (`segVC`) mentions `runSeg D ws S` on closed data.
`vc_run` finds that term, computes its value with compiled code (`evalExpr`),
and rewrites the goal with `runSeg D ws S = v`, by the
proof `Eq.refl v`: the kernel checks it by evaluating `runSeg` itself and
comparing, so the compiled evaluation is only a way to find `v` and is not
trusted. The proof goes into the theorem as it is, unchecked by the elaborator
(building it as an auxiliary theorem first made the elaborator check it).
`Eq.refl` replaced `decide` on the derived `DecidableEq` after measuring both
on the same files (a local run; its log is not in the repository): kernel time with `Eq.refl`
0.56x at 10 instructions per segment to 0.68x at 1000, and 35.4 s against 46 s
on 10^4 instructions (`nocompiler.vc.byDecide` restores `decide`).
-/
namespace NoCompiler.VC.M
open Lean Meta Elab Tactic

deriving instance ToExpr for NoCompiler.IOp
deriving instance ToExpr for NoCompiler.ROp
deriving instance ToExpr for NoCompiler.LdOp
deriving instance ToExpr for NoCompiler.BrOp
deriving instance ToExpr for NoCompiler.ShOp
deriving instance ToExpr for NoCompiler.ShWOp
deriving instance ToExpr for NoCompiler.RWOp
deriving instance ToExpr for NoCompiler.UOp
deriving instance ToExpr for NoCompiler.VC.M.Sym, NoCompiler.VC.M.SMem
deriving instance ToExpr for NoCompiler.VC.M.Ob
deriving instance ToExpr for NoCompiler.VC.M.Term
deriving instance ToExpr for NoCompiler.VC.M.SState
deriving instance ToExpr for NoCompiler.VC.M.Cond
deriving instance ToExpr for NoCompiler.VC.M.PEnd
deriving instance ToExpr for NoCompiler.VC.M.GOb
deriving instance DecidableEq for NoCompiler.VC.M.Sym, NoCompiler.VC.M.SMem
deriving instance DecidableEq for NoCompiler.VC.M.Ob
deriving instance DecidableEq for NoCompiler.VC.M.Term
deriving instance DecidableEq for NoCompiler.VC.M.SState
deriving instance DecidableEq for NoCompiler.VC.M.Cond
deriving instance DecidableEq for NoCompiler.VC.M.PEnd
deriving instance DecidableEq for NoCompiler.VC.M.GOb

/-- The value of a closed `runSeg` term, by compiled evaluation. -/
unsafe def evalRunSegImpl (e : Expr) : MetaM (Option (SState × List Ob × Term)) := do
  evalExpr (Option (SState × List Ob × Term)) (← inferType e) e

@[implemented_by evalRunSegImpl]
opaque evalRunSeg (e : Expr) : MetaM (Option (SState × List Ob × Term))

/-- The value of a closed `exploreR` term, by compiled evaluation. -/
unsafe def evalExploreImpl (e : Expr) : MetaM (Option (List PEnd × List GOb)) := do
  evalExpr (Option (List PEnd × List GOb)) (← inferType e) e

@[implemented_by evalExploreImpl]
opaque evalExplore (e : Expr) : MetaM (Option (List PEnd × List GOb))

register_option nocompiler.vc.byDecide : Bool :=
  { defValue := false, descr := "vc_run: prove the equation by `decide` on the derived DecidableEq \
      instead of `Eq.refl` (measured slower at every size, kept for comparison)" }

/-- Rewrite the first closed `runSeg D ws S` or `exploreR …` in the goal to its
    value, with a kernel-checked equation (`Eq.refl`: the kernel evaluates the
    term while it compares it with the value). -/
elab "vc_run" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let closed (t : Expr) := !t.hasFVar && !t.hasMVar
  let some t := tgt.find? fun t =>
      (t.isAppOfArity ``runSeg 3 || t.isAppOfArity ``exploreR 9) && closed t
    | throwError "vc_run: no closed `runSeg` or `exploreR` term in the goal"
  let v ← if t.isAppOf ``runSeg then pure (toExpr (← evalRunSeg t)) else pure (toExpr (← evalExplore t))
  let eq ← mkEq t v
  let pf ← if !nocompiler.vc.byDecide.get (← getOptions) then
      mkExpectedTypeHint (← mkEqRefl v) eq
    else do
      let inst ← synthInstance (mkApp (mkConst ``Decidable) eq)
      pure <| mkApp3 (mkConst ``of_decide_eq_true) eq inst
        (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
  let r ← g.rewrite tgt pf
  let g' ← g.replaceTargetEq r.eNew r.eqProof
  replaceMainGoal (g' :: r.mvarIds)

/-! ### Denotations in the machine's own terms

`symDen` rewrites `Sym.den ρ μ x` (and `SMem.den ρ μ m`), for closed `x`, to
the expression it denotes, built from the machine's operations: `ρOf u n` is
`u.reg n`, the base memory is `μ`. The step is definitional (`dsimproc`), so the
kernel checks it by unfolding `Sym.den` on a small closed term; `x` is found by
compiled evaluation. -/

unsafe def evalSymImpl (e : Expr) : MetaM Sym := evalExpr Sym (mkConst ``Sym) e
@[implemented_by evalSymImpl] opaque evalSym (e : Expr) : MetaM Sym
unsafe def evalSMemImpl (e : Expr) : MetaM SMem := evalExpr SMem (mkConst ``SMem) e
@[implemented_by evalSMemImpl] opaque evalSMem (e : Expr) : MetaM SMem

/-- The value of variable `n` under `ρ`: `u.reg n` when `ρ` is `ρOf u`. -/
def varE (ρ : Expr) (n : Nat) : MetaM Expr := do
  if ρ.isAppOfArity ``ρOf 1 && n < 32 then
    mkAppM ``State.reg #[ρ.appArg!, ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 32)) n]
  else return mkApp ρ (mkNatLit n)

mutual
partial def symE (ρ μ : Expr) : Sym → MetaM Expr
  | .var n => varE ρ n
  | .const w => return toExpr w
  | .iop op a imm => return mkApp3 (mkConst ``evalI) (toExpr op) (← symE ρ μ a) (toExpr imm)
  | .rop op a b => return mkApp3 (mkConst ``evalR) (toExpr op) (← symE ρ μ a) (← symE ρ μ b)
  | .load op m a => return mkApp3 (mkConst ``loadVal) (toExpr op) (← smemE ρ μ m) (← symE ρ μ a)
  | .addiw a imm => do mkAppM ``sext32 #[← mkAppM ``HAdd.hAdd #[← symE ρ μ a, toExpr imm]]
  | .sh op a n => return mkApp3 (mkConst ``evalSh) (toExpr op) (← symE ρ μ a) (mkNatLit n)
  | .shw op a n => return mkApp3 (mkConst ``evalShW) (toExpr op) (← symE ρ μ a) (mkNatLit n)
  | .rwop op a b => return mkApp3 (mkConst ``evalRW) (toExpr op) (← symE ρ μ a) (← symE ρ μ b)
  | .uop op a => return mkApp2 (mkConst ``evalU) (toExpr op) (← symE ρ μ a)
partial def smemE (ρ μ : Expr) : SMem → MetaM Expr
  | .base => return μ
  | .write m a v w => do
    return mkApp4 (mkConst ``writeLE) (← smemE ρ μ m) (← symE ρ μ a)
      (← mkAppM ``BitVec.toNat #[← symE ρ μ v]) (mkNatLit w)
end

/-! Reading a closed symbolic value structurally. After `vc_run` a value is a
constructor term, or a register or the memory of a literal symbolic state; it is
read off the expression, with no evaluation (each `evalExpr` compiles a definition
first: about 25 ms, measured, per value). Anything else is evaluated as before. -/

/-- Register `r` of the literal state `S` (`SState.reg`), as the constructor term it holds. -/
def regOfLit? (S r : Expr) : MetaM (Option Expr) := do
  let S ← whnfR S
  unless S.isAppOfArity ``SState.mk 3 do return none
  let some ⟨_, v⟩ ← getFinValue? r | return none
  if v.val = 0 then return some (mkApp (mkConst ``Sym.const) (toExpr (0 : Word)))
  let mut l := S.getArg! 0
  for _ in [0:v.val] do
    unless l.isAppOfArity ``List.cons 3 do return some (mkApp (mkConst ``Sym.const) (toExpr (0 : Word)))
    l := l.getArg! 2
  unless l.isAppOfArity ``List.cons 3 do return some (mkApp (mkConst ``Sym.const) (toExpr (0 : Word)))
  return some (l.getArg! 1)

mutual
/-- `symE` on the expression of a closed `Sym`, read structurally; `none` if it is not of that form. -/
partial def symEx? (ρ μ x : Expr) : MetaM (Option Expr) := do
  let x := x.consumeMData
  if x.isAppOfArity ``SState.reg 2 then
    let some y ← regOfLit? (x.getArg! 0) (x.getArg! 1) | return none
    return ← symEx? ρ μ y
  let args := x.getAppArgs
  match x.getAppFn.constName? with
  | some ``Sym.var => do
    let some n ← getNatValue? args[0]! | return none
    return some (← varE ρ n)
  | some ``Sym.const => return some args[0]!
  | some ``Sym.iop => do
    let some a ← symEx? ρ μ args[1]! | return none
    return some (mkApp3 (mkConst ``evalI) args[0]! a args[2]!)
  | some ``Sym.rop => do
    let some a ← symEx? ρ μ args[1]! | return none
    let some b ← symEx? ρ μ args[2]! | return none
    return some (mkApp3 (mkConst ``evalR) args[0]! a b)
  | some ``Sym.load => do
    let some m ← smemEx? ρ μ args[1]! | return none
    let some a ← symEx? ρ μ args[2]! | return none
    return some (mkApp3 (mkConst ``loadVal) args[0]! m a)
  | some ``Sym.addiw => do
    let some a ← symEx? ρ μ args[0]! | return none
    return some (← mkAppM ``sext32 #[← mkAppM ``HAdd.hAdd #[a, args[1]!]])
  | some ``Sym.sh => do
    let some a ← symEx? ρ μ args[1]! | return none
    return some (mkApp3 (mkConst ``evalSh) args[0]! a args[2]!)
  | some ``Sym.shw => do
    let some a ← symEx? ρ μ args[1]! | return none
    return some (mkApp3 (mkConst ``evalShW) args[0]! a args[2]!)
  | some ``Sym.rwop => do
    let some a ← symEx? ρ μ args[1]! | return none
    let some b ← symEx? ρ μ args[2]! | return none
    return some (mkApp3 (mkConst ``evalRW) args[0]! a b)
  | some ``Sym.uop => do
    let some a ← symEx? ρ μ args[1]! | return none
    return some (mkApp2 (mkConst ``evalU) args[0]! a)
  | _ => return none

/-- `smemE` on the expression of a closed `SMem`, read structurally. -/
partial def smemEx? (ρ μ m : Expr) : MetaM (Option Expr) := do
  let m := m.consumeMData
  if m.isAppOfArity ``SState.mem 1 then
    let S ← whnfR (m.getArg! 0)
    unless S.isAppOfArity ``SState.mk 3 do return none
    return ← smemEx? ρ μ (S.getArg! 1)
  let args := m.getAppArgs
  match m.getAppFn.constName? with
  | some ``SMem.base => return some μ
  | some ``SMem.write => do
    let some m' ← smemEx? ρ μ args[0]! | return none
    let some a ← symEx? ρ μ args[1]! | return none
    let some v ← symEx? ρ μ args[2]! | return none
    return some (mkApp4 (mkConst ``writeLE) m' a (← mkAppM ``BitVec.toNat #[v]) args[3]!)
  | _ => return none
end

dsimproc symDen (Sym.den _ _ _) := fun e => do
  let_expr Sym.den ρ μ x := e | return .continue
  if x.hasFVar || x.hasMVar then return .continue
  if let some r ← symEx? ρ μ x then return .done r
  return .done (← symE ρ μ (← evalSym x))

dsimproc smemDen (SMem.den _ _ _) := fun e => do
  let_expr SMem.den ρ μ m := e | return .continue
  if m.hasFVar || m.hasMVar then return .continue
  if let some r ← smemEx? ρ μ m then return .done r
  return .done (← smemE ρ μ (← evalSMem m))

set_option hygiene false in
/-- The goals of one cut point, after `Reach.of_exploreAt`: run `explore`
    (`vc_run`), split the residual obligations and the ends into one goal each,
    and in each end introduce the end state `s'` with its path conditions `hc`,
    registers `hreg`, memory `hmem`, pc `hpc'` and `hx'`, every symbolic value
    rewritten into the machine's terms over the cut point's state. -/
macro "vc_ends" : tactic => `(tactic| (
  unfold exploreVC; vc_run
  simp only [allOb, allNext, GOb.den, Ob.den, symDen, smemDen, evalI, and_true,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, forall_const, true_imp_iff]
  refine ?_
  repeat' apply And.intro
  all_goals try (
    simp only [PEnd.Next]
    intro hc s' ⟨_, hpc', hreg, hmem⟩ hx'
    simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true,
      Cond.den, symDen, smemDen, evalBr, evalI, evalR, loadVal] at hc
    simp only [hreg, hmem, hpc', State.setPc_pc, State.setPc_reg, State.setPc_mem, State.setPc_exit,
      symDen, smemDen, evalI, evalR, loadVal, hx', true_and] )
  all_goals try exact True.intro))

end NoCompiler.VC.M

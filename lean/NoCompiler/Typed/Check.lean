import NoCompiler.Typed.Sem
import NoCompiler.Typed.Search

/-
The type checker for safe functions, run on the decoded code image.

A function is checked against a record of state types, one per instruction (the proof's
D8; the Rust checker exports it, docs/typed/export.md). The record is a hint: every rule
is re-checked here, locally, instruction by instruction and edge by edge (T1), against
the instructions `Code.instr` decodes from the image — never against assembly text.

* Entry (T0): the type built from the signature must be a subtype of the record's type at
  the entry.
* Each instruction: its rule (docs/Tab 1.md, 型付け規則) gives the type after it, with
  fresh variables above every variable of the type before; for each edge the result must
  be a subtype of the record at the target, under an instantiation θ of the target's new
  variables (D7).
* Loops: a backward edge must go to a declared head and come from inside its interval;
  intervals nest; the head's measure is nonnegative and decreases on each backward edge
  (T2). θ never rebinds the variables of a measure of a loop that contains both ends of an
  edge (other than the loop's own backward edge), and never the protected variables (the
  parameters and the entry values of the preserved registers).
* Return: preserved registers as on entry, `out` registers and exit constraint, borrowed
  capabilities back with their exit fields.

Entailments `Ψ ⊢ ψ` go to `Query.decide` (sound by `Query.decide_sound`).

Not yet: calls, frames, syscalls, tokens, `take`/`give` (functions using them are
rejected), `partial`.
-/
namespace NoCompiler.Typed

/-! ## Substitution -/

abbrev Subst := List (Var × IExpr)

namespace IExpr
def substT (θ : Subst) : List (Int × Var) → IExpr
  | [] => lit 0
  | (a, x) :: r =>
    match θ.lookup x with
    | some e => (e.smul a).add (substT θ r)
    | none => (IExpr.mk 0 [(a, x)]).add (substT θ r)

def subst (θ : Subst) (e : IExpr) : IExpr := (lit e.const).add (substT θ e.terms)

/-- The valuation after `θ`: its variables take the values of their images. -/
def upd (ι : Val) (θ : Subst) : Val := fun x =>
  match θ.lookup x with
  | some e => e.eval ι
  | none => ι x

theorem eval_substT (ι : Val) (θ : Subst) (ts : List (Int × Var)) :
    (substT θ ts).eval ι = (ts.map fun t => t.1 * upd ι θ t.2).sum := by
  induction ts with
  | nil => simp [substT]
  | cons t r ih =>
    obtain ⟨a, x⟩ := t
    simp only [substT, List.map_cons, List.sum_cons]
    cases h : θ.lookup x with
    | some e => rw [eval_add, ih]; simp [upd, h]
    | none => rw [eval_add, ih]; simp [eval, upd, h]

@[simp] theorem eval_subst (ι : Val) (θ : Subst) (e : IExpr) :
    (e.subst θ).eval ι = e.eval (upd ι θ) := by
  rw [subst, eval_add, eval_lit, eval_substT]; rfl

/-- `a = b` as linear forms: then equal under every valuation. -/
def same (a b : IExpr) : Bool := (a.sub b).toLin == ⟨0, []⟩

theorem eval_of_same {a b : IExpr} (h : same a b = true) (ι : Val) : a.eval ι = b.eval ι := by
  unfold same at h
  have := congrArg (Lin.eval ι) (eq_of_beq h)
  rw [eval_toLin, eval_sub] at this
  simp [Lin.eval, Lin.evalT] at this
  omega

/-- A bare variable `x`. -/
def asVar (e : IExpr) : Option Var :=
  match e with
  | ⟨0, [(1, x)]⟩ => some x
  | _ => none

def maxVar (e : IExpr) : Nat := e.terms.foldr (fun t m => max t.2 m) 0
end IExpr

namespace Constr
def subst (θ : Subst) : Constr → Constr
  | tt => tt
  | ff => ff
  | le a b => le (a.subst θ) (b.subst θ)
  | eq a b => eq (a.subst θ) (b.subst θ)
  | dvd c e => dvd c (e.subst θ)
  | and p q => and (p.subst θ) (q.subst θ)
  | or p q => or (p.subst θ) (q.subst θ)
  | not p => not (p.subst θ)

@[simp] theorem eval_subst (ι : Val) (θ : Subst) (p : Constr) :
    (p.subst θ).eval ι = p.eval (IExpr.upd ι θ) := by
  induction p <;> simp_all [subst, eval]

def maxVar : Constr → Nat
  | tt | ff => 0
  | le a b | eq a b => max a.maxVar b.maxVar
  | dvd _ e => e.maxVar
  | and p q | or p q => max p.maxVar q.maxVar
  | not p => p.maxVar

def vars : Constr → List Var
  | tt | ff => []
  | le a b | eq a b => a.vars ++ b.vars
  | dvd _ e => e.vars
  | and p q | or p q => p.vars ++ q.vars
  | not p => p.vars

/-- `a ≡ b (mod 2^64)`. -/
def eqMod (a b : IExpr) : Constr := dvd (2 ^ 64) (a.sub b)
/-- `ψ ⇒ φ`. -/
def imp (ψ φ : Constr) : Constr := or (not ψ) φ
end Constr

/-! ## State types -/

/-- A capability the checker holds: an identity (kept along edges, D7's one-to-one
    correspondence), and the `borrow` clause it came from, if any (I12). -/
structure HCap where
  id : Nat
  cap : Cap
  origin : Option Nat := none
  deriving DecidableEq, Repr

/-- The type of a program point: Γ (a register not listed is `int`), Ψ, C. (Φ, the
    frame depth and tokens come with frames and calls.) -/
structure STy where
  regs : List (Reg × IExpr)
  facts : List Constr
  caps : List HCap := []
  deriving DecidableEq, Repr

namespace STy
def reg (S : STy) (r : Reg) : Option IExpr := if r = 0 then some (.lit 0) else S.regs.lookup r

/-- Set (or forget, `none`) the type of `rd`; writes to x0 do nothing. -/
def setReg (S : STy) (rd : Reg) (e : Option IExpr) : STy :=
  if rd = 0 then S else
  { S with regs := match e with
      | some e => (rd, e) :: S.regs.filter (·.1 != rd)
      | none => S.regs.filter (·.1 != rd) }

def addFacts (S : STy) (ps : List Constr) : STy := { S with facts := ps ++ S.facts }

def capMaxVar (c : HCap) : Nat :=
  max c.cap.guard.maxVar <|
    match c.cap.kind with
    | .bytes b => max b.base.maxVar (max b.len.maxVar (b.fields.foldr (fun f m => max f.ty.maxVar m) 0))
    | .token _ => 0

def maxVar (S : STy) : Nat :=
  max (S.regs.foldr (fun p m => max p.2.maxVar m) 0)
    (max (S.facts.foldr (fun p m => max p.maxVar m) 0) (S.caps.foldr (fun c m => max (capMaxVar c) m) 0))

/-- The facts every held capability gives (`0 ≤ b`, `0 ≤ n`, `b + n ≤ 2^64` when its guard
    holds), with the recorded facts: the hypotheses of every query. -/
def hyps (S : STy) : List Constr :=
  S.facts ++ S.caps.filterMap fun c =>
    match c.cap.kind with
    | .bytes b => some (Constr.imp c.cap.guard
        (.and (.le (.lit 0) b.base) (.and (.le (.lit 0) b.len) (.le (b.base.add b.len) (.lit (2 ^ 64))))))
    | .token _ => none

/-- `Ψ ⊢ ψ`. -/
def ent (S : STy) (ψ : Constr) : Bool :=
  match ψ with
  | .tt => true
  | .eq a b => a.same b || (Query.mk S.hyps ψ).decide
  | .dvd _ e => e.same (.lit 0) || (Query.mk S.hyps ψ).decide
  | _ => (Query.mk S.hyps ψ).decide

/-- `a ≡ b (mod 2^64)` under Ψ. -/
def entEqMod (S : STy) (a b : IExpr) : Bool := a.same b || S.ent (Constr.eqMod a b)
end STy

namespace STy
/-- The variables of a type (with repetitions). -/
def vars (S : STy) : List Var :=
  S.regs.flatMap (·.2.vars) ++ S.facts.flatMap Constr.vars ++
    S.caps.flatMap fun c => c.cap.guard.vars ++
      match c.cap.kind with
      | .bytes b => b.base.vars ++ b.len.vars ++ b.fields.flatMap (·.ty.vars)
      | .token _ => []

/-! ### Instantiation (heuristic; any θ is checked) -/

/-- Find `θ y` from a register whose target type is `c + a·y + rest` with `a = ±1` and
    every variable of `rest` already known. -/
def solveFrom (S S' : STy) (y : Var) (known : List Var) : Option IExpr :=
  S'.regs.findSome? fun (r, e') =>
    match S.reg r with
    | none => none
    | some e =>
      match e'.terms.find? (·.2 == y) with
      | none => none
      | some (a, _) =>
        let rest : IExpr := ⟨e'.const, e'.terms.filter (·.2 != y)⟩
        if (a == 1 || a == -1) && (e'.terms.filter (·.2 == y)).length == 1 &&
            rest.vars.all (fun x => known.contains x) then
          some ((e.sub rest).smul a)
        else none

def instantiate (S S' : STy) (newVars : List Var) : Subst :=
  -- passes: each may make more variables known
  let known0 := (S.vars ++ S'.vars).filter (fun x => !newVars.contains x)
  let step (acc : Subst × List Var) : Subst × List Var :=
    newVars.foldl (fun (θ, kn) y =>
      if (θ.lookup y).isSome then (θ, kn) else
      match S.solveFrom S' y kn with
      | some e => ((y, e.subst θ) :: θ, y :: kn)
      | none => (θ, kn)) acc
  (step (step (step ([], known0)))).1

/-! ### Subtyping (D7) -/

def capSub (S : STy) (θ : Subst) (c c' : HCap) : Bool :=
  c.id == c'.id && c.origin == c'.origin &&
  S.ent (Constr.imp (c'.cap.guard.subst θ) c.cap.guard) &&
  match c.cap.kind, c'.cap.kind with
  | .bytes b, .bytes b' =>
    b.mode == b'.mode && b.heap == b'.heap &&
    S.ent (.eq b.base (b'.base.subst θ)) && S.ent (.eq b.len (b'.len.subst θ)) &&
    b'.fields.all fun f' => b.fields.any fun g => g.off == f'.off && S.entEqMod g.ty (f'.ty.subst θ)
  | .token t, .token t' => t == t'
  | _, _ => false

def sub (S : STy) (θ : Subst) (S' : STy) : Bool :=
  S'.facts.all (fun p => S.ent (p.subst θ)) &&
  S'.regs.all (fun (r, e') => match S.reg r with
    | some e => S.entEqMod e (e'.subst θ)
    | none => false) &&
  (S'.caps.map (·.id)).Nodup && (S.caps.map (·.id)).Nodup &&
  S'.caps.all (fun c' => S.caps.any fun c => S.capSub θ c c')

end STy

/-! ## Function context -/

structure Loop where
  /-- Instruction index of the head. -/
  head : Nat
  /-- Index of the last instruction of the loop (its last backward edge). -/
  last : Nat
  /-- Variables the head binds (`inv [m, …]`). -/
  vars : List Var
  /-- `decreases`. -/
  meas : IExpr
  deriving DecidableEq, Repr

/-- What the checker needs about one function. -/
structure Fn where
  sig : Sig
  /-- Entry address and number of instructions. -/
  entry : Word
  size : Nat
  /-- The variable standing for the entry value of each preserved register (ra, sp, gp,
      tp, s0–s11): index 0 is `ra`, then `preservedRegs` order. -/
  regVar : List (Reg × Var)
  loops : List Loop := []
  /-- The record: the type before each instruction, by index. -/
  types : List (Nat × STy)
  /-- Fresh variables are allocated from here up. -/
  fresh : Nat
  deriving Repr

/-- The instructions whose only effect is a register write, and the register. -/
def writesReg : Instr → Option Reg
  | .lui rd _ | .auipc rd _ | .iop _ rd _ _ | .addiw rd _ _ | .shift _ rd _ _
  | .shiftw _ rd _ _ | .rop _ rd _ _ | .rwop _ rd _ _ | .uop _ rd _ => some rd
  | _ => none

/-- The registers the return check compares with their entry values (I7). -/
def keptRegs : List Reg := 1 :: preservedRegs

namespace Fn
variable (f : Fn)

def pcOf (k : Nat) : Word := f.entry + BitVec.ofNat 64 (4 * k)
def tyAt (k : Nat) : Option STy := f.types.lookup k
def loopAt (k : Nat) : Option Loop := f.loops.find? (·.head == k)

/-- Parameters and entry values: never rebound. -/
def protectedVars : List Var := f.sig.params ++ f.regVar.map (·.2)

def inside (L : Loop) (k : Nat) : Bool := L.head ≤ k && k ≤ L.last

/-- The type at the entry, from the signature (T0). -/
def initTy : STy where
  regs := f.sig.inRegs ++ f.regVar.map (fun p => (p.1, .var p.2))
  facts := f.sig.pre ::
    (match f.regVar.lookup 2 with
     | some x => [.le (.lit 0) (.var x), .lt (.var x) (.lit (2 ^ 64)), .dvd 16 (.var x),
                  .le (.lit f.sig.stack) (.var x)]
     | none => [])
  caps := (f.sig.borrow.zipIdx.map fun (b, i) => ({ id := i, cap := b.cap, origin := some i } : HCap))

/-! ### Edges -/


/-- Check the edge from instruction `k` (or the entry, `k = none`) to `k'`, the type after
    the instruction being `S`. -/
def edgeOk (k : Option Nat) (S S' : STy) (k' : Nat) (θ : Subst) : Bool :=
  let back := match k with | some k => decide (k' ≤ k) | none => false
  decide (k' < f.size) &&
  -- θ never binds a protected variable, nor a measure variable of a loop containing both
  -- ends of the edge (other than at the loop's own backward edge)
  θ.all (fun p => !f.protectedVars.contains p.1 &&
    f.loops.all fun K =>
      (match k with
       | some k => !(inside K k && inside K k' && !(back && K.head == k'))
       | none => true) || !K.meas.vars.contains p.1) &&
  S.sub θ S' &&
  (if back then
    match f.loopAt k', k with
    | some L, some k => decide (k ≤ L.last) && S.ent (.le (.lit 0) L.meas) &&
        S.ent (.lt (L.meas.subst θ) L.meas)
    | _, _ => false
   else true)

/-- Check the edge from instruction `k` (or the entry, `k = none`) to `k'`, the type after
    the instruction being `S`; the instantiation is found heuristically. -/
def edge (k : Option Nat) (S : STy) (k' : Nat) : Bool :=
  match f.tyAt k' with
  | none => false
  | some S' =>
    let back := match k with | some k => decide (k' ≤ k) | none => false
    let sv := S.vars
    let nv := (if back then ((f.loopAt k').map (·.vars)).getD [] else []) ++
      (S'.vars.filter (fun x => !sv.contains x)).eraseDups
    f.edgeOk k S S' k' (S.instantiate S' nv)

/-! ### The rules -/

/-- Fresh variables for the instruction at a point of type `S`. -/
def freshAt (S : STy) : Var := max f.fresh (S.maxVar + 1)

/-- The unsigned representative of `e` (D's `u(e)`): `e` itself when Ψ puts it in
    `[0, 2^64)`, else a fresh variable `x` with `0 ≤ x < 2^64` and `x ≡ e`. -/
def urep (S : STy) (x : Var) (e : IExpr) : IExpr × List Constr :=
  if S.ent (.and (.le (.lit 0) e) (.lt e (.lit (2 ^ 64)))) then (e, [])
  else (.var x, [.le (.lit 0) (.var x), .lt (.var x) (.lit (2 ^ 64)), Constr.eqMod e (.var x)])

def srep (S : STy) (x : Var) (e : IExpr) : IExpr × List Constr :=
  if S.ent (.and (.le (.lit (-2 ^ 63)) e) (.lt e (.lit (2 ^ 63)))) then (e, [])
  else (.var x, [.le (.lit (-2 ^ 63)) (.var x), .lt (.var x) (.lit (2 ^ 63)), Constr.eqMod e (.var x)])

/-- The default for any register write: a fresh `x`, `0 ≤ x < 2^64`. -/
def anyWord (S : STy) (rd : Reg) (x : Var) : STy :=
  (S.setReg rd (some (.var x))).addFacts [.le (.lit 0) (.var x), .lt (.var x) (.lit (2 ^ 64))]

/-- The type after a register-writing instruction other than a load. -/
def arith (S : STy) (i : Instr) : Option STy :=
  let x := f.freshAt S
  let r := S.reg
  match i with
  | .lui rd imm => some (S.setReg rd (some (.lit (imm.toInt * 4096))))
  | .iop .addi rd rs imm =>
    some (match r rs with
      | some e => S.setReg rd (some (e.add (.lit imm.toInt)))
      | none => anyWord S rd x)
  | .rop .add rd a b =>
    some (match r a, r b with
      | some e1, some e2 => S.setReg rd (some (e1.add e2))
      | _, _ => anyWord S rd x)
  | .rop .sub rd a b =>
    some (match r a, r b with
      | some e1, some e2 => S.setReg rd (some (e1.sub e2))
      | _, _ => anyWord S rd x)
  | .shift .slli rd rs sh =>
    some (match r rs with
      | some e => S.setReg rd (some (e.smul (2 ^ sh.toNat)))
      | none => anyWord S rd x)
  | .rop .sh1add rd a b | .rop .sh2add rd a b | .rop .sh3add rd a b =>
    let n : Nat := match i with | .rop .sh1add .. => 1 | .rop .sh2add .. => 2 | _ => 3
    some (match r a, r b with
      | some e1, some e2 => S.setReg rd (some ((e1.smul (2 ^ n)).add e2))
      | _, _ => anyWord S rd x)
  | .rop .mul rd a b =>
    some (match r a, r b with
      | some e1, some ⟨c, []⟩ => S.setReg rd (some (e1.smul c))
      | some ⟨c, []⟩, some e2 => S.setReg rd (some (e2.smul c))
      | _, _ => anyWord S rd x)
  | .iop .andi rd _ imm =>
    if 0 ≤ imm.toInt then
      some ((S.setReg rd (some (.var x))).addFacts [.le (.lit 0) (.var x), .le (.var x) (.lit imm.toInt)])
    else some (anyWord S rd x)
  | .shift .srli rd rs sh =>
    match r rs with
    | some e =>
      let (u, fs) := urep S (x + 2) e
      some ((S.setReg rd (some (.var x))).addFacts (fs ++
        [.eq u (((IExpr.var x).smul (2 ^ sh.toNat)).add (.var (x + 1))),
         .le (.lit 0) (.var (x + 1)), .lt (.var (x + 1)) (.lit (2 ^ sh.toNat)),
         .le (.lit 0) (.var x)]))
    | none => some (anyWord S rd x)
  | .auipc rd _ | .iop _ rd _ _ | .addiw rd _ _ | .shift _ rd _ _ | .shiftw _ rd _ _
  | .rop _ rd _ _ | .rwop _ rd _ _ | .uop _ rd _ => some (anyWord S rd x)
  | _ => none

def ldWidth : LdOp → Nat := LdOp.width

/-- The range of a loaded value (sign or zero extension). -/
def ldRange (x : Var) : LdOp → List Constr
  | .lbu => [.le (.lit 0) (.var x), .lt (.var x) (.lit 256)]
  | .lhu => [.le (.lit 0) (.var x), .lt (.var x) (.lit 65536)]
  | .lwu => [.le (.lit 0) (.var x), .lt (.var x) (.lit (2 ^ 32))]
  | .ld => [.le (.lit 0) (.var x), .lt (.var x) (.lit (2 ^ 64))]
  | .lb => [.le (.lit (-128)) (.var x), .lt (.var x) (.lit 128)]
  | .lh => [.le (.lit (-32768)) (.var x), .lt (.var x) (.lit 32768)]
  | .lw => [.le (.lit (-2 ^ 31)) (.var x), .lt (.var x) (.lit (2 ^ 31))]

/-- The access `[a, a + w)` lies in the capability and is aligned. -/
def inCap (S : STy) (a : IExpr) (w : Nat) (c : HCap) (needRw : Bool) : Bool :=
  match c.cap.kind with
  | .bytes b =>
    (!needRw || b.mode == .rw) && S.ent c.cap.guard &&
    S.ent (.and (.le b.base a) (.and (.le (a.add (.lit w)) (b.base.add b.len)) (.dvd w a)))
  | .token _ => false

/-- The constant offset of `a` from the capability's start, when Ψ fixes it. -/
def constOff (a base : IExpr) : Option Nat :=
  match (a.sub base).toLin with
  | ⟨c, []⟩ => if 0 ≤ c then some c.toNat else none
  | _ => none

def load (S : STy) (op : LdOp) (rd rs : Reg) (off : BitVec 12) : Option STy := do
  let e ← S.reg rs
  let a := e.add (.lit off.toInt)
  let c ← S.caps.find? (fun c => inCap S a op.width c false)
  let x := f.freshAt S
  let fieldTy : Option IExpr :=
    match op, c.cap.kind with
    | .ld, .bytes b => (constOff a b.base).bind fun k => (b.fields.find? (·.off == k)).map (·.ty)
    | _, _ => none
  match fieldTy with
  | some t => pure (S.setReg rd (some t))
  | none => pure ((S.setReg rd (some (.var x))).addFacts (ldRange x op))

/-- Fields of `b` that the store to `[a, a + w)` may change are dropped; an 8-byte store at
    a constant offset replaces the field there. -/
def storeFields (S : STy) (b : BytesCap) (a : IExpr) (w : Nat) (v : Option IExpr) : List Field :=
  let keep := b.fields.filter fun g =>
    S.ent (.or (.le (a.add (.lit w)) (b.base.add (.lit g.off)))
               (.le ((b.base.add (.lit g.off)).add (.lit 8)) a))
  match w, constOff a b.base, v with
  | 8, some k, some t => ⟨k, t⟩ :: keep.filter (·.off != k)
  | _, _, _ => keep

def store (S : STy) (op : StOp) (rs1 rs2 : Reg) (off : BitVec 12) : Option STy := do
  let e ← S.reg rs1
  let a := e.add (.lit off.toInt)
  let c ← S.caps.find? (fun c => inCap S a op.width c true)
  match c.cap.kind with
  | .bytes b =>
    let b' := { b with fields := storeFields S b a op.width (S.reg rs2) }
    pure { S with caps := S.caps.map fun d => if d.id == c.id then { d with cap := { d.cap with kind := .bytes b' } } else d }
  | .token _ => none

/-- Branch facts on the taken and fall-through edges. -/
def branchFacts (S : STy) (op : BrOp) (e1 e2 : IExpr) : List Constr × List Constr :=
  let x := f.freshAt S
  match op with
  | .beq => ([Constr.eqMod e1 e2], [.not (Constr.eqMod e1 e2)])
  | .bne => ([.not (Constr.eqMod e1 e2)], [Constr.eqMod e1 e2])
  | .bltu | .bgeu =>
    let (u1, f1) := urep S x e1
    let (u2, f2) := urep S (x + 1) e2
    let lt := Constr.lt u1 u2
    let ge := Constr.le u2 u1
    if op == .bltu then (f1 ++ f2 ++ [lt], f1 ++ f2 ++ [ge]) else (f1 ++ f2 ++ [ge], f1 ++ f2 ++ [lt])
  | .blt | .bge =>
    let (u1, f1) := srep S x e1
    let (u2, f2) := srep S (x + 1) e2
    let lt := Constr.lt u1 u2
    let ge := Constr.le u2 u1
    if op == .blt then (f1 ++ f2 ++ [lt], f1 ++ f2 ++ [ge]) else (f1 ++ f2 ++ [ge], f1 ++ f2 ++ [lt])

/-- The target of a jump or branch at `k` with byte offset `off`. -/
def target (k : Nat) (off : Int) : Option Nat :=
  if off % 4 = 0 && 0 ≤ (k : Int) + off / 4 then some ((k : Int) + off / 4).toNat else none

/-- The return check, under an instantiation of the `out` variables. -/
def retOk (S : STy) (θ : Subst) : Bool :=
  let σ := f.sig
  keptRegs.all (fun r => match S.reg r, f.regVar.lookup r with
    | some e, some x => S.entEqMod e (.var x)
    | _, _ => false) &&
  θ.all (fun p => σ.outVars.contains p.1) &&
  S.sub θ { regs := σ.outRegs, facts := [σ.post] } &&
  σ.borrow.zipIdx.all fun (b, i) =>
    S.caps.any fun c => c.origin == some i && S.capSub θ c { id := c.id, origin := some i, cap := b.exitCap }

/-- The return check. -/
def ret (S : STy) : Bool :=
  f.retOk S (S.instantiate { regs := f.sig.outRegs, facts := [f.sig.post] } f.sig.outVars)

def branchOk (k : Nat) (S : STy) (op : BrOp) (rs1 rs2 : Reg) (off : BitVec 13) : Bool :=
  match target k off.toInt with
  | none => false
  | some k' =>
    match S.reg rs1, S.reg rs2 with
    | some e1, some e2 =>
      f.edge (some k) (S.addFacts (f.branchFacts S op e1 e2).1) k' &&
        f.edge (some k) (S.addFacts (f.branchFacts S op e1 e2).2) (k + 1)
    | _, _ => f.edge (some k) S k' && f.edge (some k) S (k + 1)

def jalOk (k : Nat) (S : STy) (off : BitVec 21) : Bool :=
  match target k off.toInt with
  | some k' => f.edge (some k) S k'
  | none => false

def loadOk (k : Nat) (S : STy) (op : LdOp) (rd rs : Reg) (off : BitVec 12) : Bool :=
  rd != 2 && match f.load S op rd rs off with
    | some S' => f.edge (some k) S' (k + 1)
    | none => false

def storeOk (k : Nat) (S : STy) (op : StOp) (rs1 rs2 : Reg) (off : BitVec 12) : Bool :=
  match store S op rs1 rs2 off with
  | some S' => f.edge (some k) S' (k + 1)
  | none => false

/-- A register write; `sp` is written only by the frame rules (not yet supported). -/
def arithOk (k : Nat) (S : STy) (i : Instr) : Bool :=
  match writesReg i with
  | some rd => rd != 2 && match f.arith S i with
    | some S' => f.edge (some k) S' (k + 1)
    | none => false
  | none => false

/-- Check instruction `k`, decoded as `i`, at a point of type `S`. -/
def instrAt (k : Nat) (S : STy) : Instr → Bool
  | .branch op rs1 rs2 off => f.branchOk k S op rs1 rs2 off
  | .jal rd off => rd == 0 && f.jalOk k S off
  | .jalr rd rs1 off => rd == 0 && rs1 == 1 && off == 0 && f.ret S
  | .load op rd rs off => f.loadOk k S op rd rs off
  | .store op rs1 rs2 off => f.storeOk k S op rs1 rs2 off
  | .ecall => false
  | .unimp => false
  | .lui rd imm => f.arithOk k S (.lui rd imm)
  | .auipc rd imm => f.arithOk k S (.auipc rd imm)
  | .iop op rd rs imm => f.arithOk k S (.iop op rd rs imm)
  | .addiw rd rs imm => f.arithOk k S (.addiw rd rs imm)
  | .shift op rd rs sh => f.arithOk k S (.shift op rd rs sh)
  | .shiftw op rd rs sh => f.arithOk k S (.shiftw op rd rs sh)
  | .rop op rd a b => f.arithOk k S (.rop op rd a b)
  | .rwop op rd a b => f.arithOk k S (.rwop op rd a b)
  | .uop op rd a => f.arithOk k S (.uop op rd a)

/-- Check instruction `k` of the image. -/
def instr (c : Code) (k : Nat) : Bool :=
  match f.tyAt k, c.instr (f.pcOf k) with
  | some S, some i => f.instrAt k S i
  | _, _ => false

/-- The structural conditions: loops nested, variables apart. -/
def structOk : Bool :=
  let σ := f.sig
  σ.take.isEmpty && σ.give.isEmpty && σ.stack == 0 &&
  σ.borrow.all (fun b => match b.cap.kind with | .bytes _ => b.cap.guard == .tt | .token _ => false) &&
  (keptRegs.all fun r => (f.regVar.lookup r).isSome) &&
  (f.protectedVars.Nodup) &&
  (f.protectedVars.all (· < f.fresh)) &&
  (f.loops.all fun L => L.head ≤ L.last && L.last < f.size &&
     L.vars.all (fun x => x < f.fresh && !f.protectedVars.contains x) &&
     L.meas.vars.all (· < f.fresh)) &&
  decide ((f.loops.map (·.head)).Pairwise (· < ·)) &&
  decide (f.entry.toNat % 4 = 0) && decide (4 * f.size < 2 ^ 64) &&
  (f.loops.all fun K => f.loops.all fun L =>
    K.head == L.head || L.last < K.head || K.last < L.head ||
    (K.head < L.head && L.last ≤ K.last) || (L.head < K.head && K.last ≤ L.last)) &&
  -- the signature mentions parameters on entry and parameters and `out` variables on exit
  (f.initTy.maxVar < f.fresh) &&
  (σ.inRegs.all fun p => p.2.vars.all σ.params.contains) &&
  (σ.pre.vars.all σ.params.contains) &&
  (σ.borrow.all fun b => b.cap.guard.vars.all σ.params.contains &&
    match b.cap.kind with
    | .bytes x => (x.base.vars ++ x.len.vars ++ x.fields.flatMap (·.ty.vars)).all σ.params.contains &&
        (b.outFields.flatMap (·.ty.vars)).all (fun y => σ.params.contains y || σ.outVars.contains y)
    | .token _ => true) &&
  (σ.outRegs.all fun p => p.2.vars.all (fun y => σ.params.contains y || σ.outVars.contains y)) &&
  (σ.post.vars.all (fun y => σ.params.contains y || σ.outVars.contains y)) &&
  (σ.outVars.all fun y => !f.protectedVars.contains y) && σ.outVars.Nodup

/-- The whole function. -/
def check (c : Code) : Bool :=
  f.structOk && f.edge none f.initTy 0 && (List.range f.size).all (f.instr c)

end Fn

end NoCompiler.Typed

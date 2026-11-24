import NoCompiler.Spec

/-
The type language of typed RISC-V assembly, v0 (docs/Tab 1.md, "型の言語 v0";
implementation choices in docs/typed/decisions.md).

* Index variables range over the mathematical integers; a valuation gives each one a
  value (I11: variables are numbers).
* Index expressions are linear: `c0 + c1·x1 + …`.
* Constraints are quantifier-free Presburger formulas: `≤`, `=`, `c ∣ e` under `∧ ∨ ¬`.
* A value type is `int(e)`: the 64-bit word is `e` modulo 2^64.
* Capabilities: `e ↦ bytes[n] ro|rw [heap] {k: int(e'), …}`, opaque tokens, and a
  guard `ψ ⇒ c`.
* A signature: universal parameters, entry registers, `borrow`, `take`, entry
  constraint, existential results, exit registers, `give`, exit constraint, stack bytes.

This file is syntax and evaluation only; the meaning of a signature is in
NoCompiler/Typed/Sem.lean. Both are part of what one reads to trust a result
(docs/isa/trust.md).
-/
namespace NoCompiler.Typed

/-- Index variables are numbered (I11). -/
abbrev Var := Nat
/-- A valuation of the index variables. -/
abbrev Val := Var → Int

/-- `const + Σ c·x`. -/
structure IExpr where
  const : Int
  terms : List (Int × Var) := []
  deriving DecidableEq, Repr

namespace IExpr
def eval (ι : Val) (e : IExpr) : Int := e.const + (e.terms.map fun t => t.1 * ι t.2).sum

def lit (c : Int) : IExpr := ⟨c, []⟩
def var (x : Var) : IExpr := ⟨0, [(1, x)]⟩
def add (a b : IExpr) : IExpr := ⟨a.const + b.const, a.terms ++ b.terms⟩
def smul (k : Int) (a : IExpr) : IExpr := ⟨k * a.const, a.terms.map fun t => (k * t.1, t.2)⟩
def sub (a b : IExpr) : IExpr := a.add (b.smul (-1))
/-- The variables the expression mentions. -/
def vars (e : IExpr) : List Var := e.terms.map (·.2)

@[simp] theorem eval_lit (ι : Val) (c : Int) : (lit c).eval ι = c := by simp [lit, eval]
@[simp] theorem eval_var (ι : Val) (x : Var) : (var x).eval ι = ι x := by simp [var, eval]

theorem sum_map_smul (k : Int) (l : List (Int × Var)) (ι : Val) :
    ((l.map fun t => (k * t.1, t.2)).map fun t => t.1 * ι t.2).sum =
      k * (l.map fun t => t.1 * ι t.2).sum := by
  induction l with
  | nil => simp
  | cons h t ih => simp only [List.map_cons, List.sum_cons] at *; rw [ih, Int.mul_add, Int.mul_assoc]

@[simp] theorem eval_add (ι : Val) (a b : IExpr) : (a.add b).eval ι = a.eval ι + b.eval ι := by
  simp only [add, eval, List.map_append, List.sum_append]; omega

@[simp] theorem eval_smul (ι : Val) (k : Int) (a : IExpr) : (a.smul k).eval ι = k * a.eval ι := by
  simp only [smul, eval]; rw [sum_map_smul, Int.mul_add]

@[simp] theorem eval_sub (ι : Val) (a b : IExpr) : (a.sub b).eval ι = a.eval ι - b.eval ι := by
  simp only [sub, eval_add, eval_smul]; omega
end IExpr

/-- Quantifier-free Presburger constraints. -/
inductive Constr
  | tt
  | ff
  | le (a b : IExpr)
  | eq (a b : IExpr)
  /-- The positive constant `c` divides `e`. -/
  | dvd (c : Nat) (e : IExpr)
  | and (p q : Constr)
  | or (p q : Constr)
  | not (p : Constr)
  deriving DecidableEq, Repr

namespace Constr
/-- Evaluation is a `Bool`, so a guard can choose a list of regions. -/
def eval (ι : Val) : Constr → Bool
  | tt => true
  | ff => false
  | le a b => decide (a.eval ι ≤ b.eval ι)
  | eq a b => decide (a.eval ι = b.eval ι)
  | dvd c e => decide ((e.eval ι) % (c : Int) = 0)
  | and p q => p.eval ι && q.eval ι
  | or p q => p.eval ι || q.eval ι
  | not p => !p.eval ι

def holds (ι : Val) (p : Constr) : Prop := p.eval ι = true

/-- `a < b`. -/
def lt (a b : IExpr) : Constr := le (a.add (IExpr.lit 1)) b
/-- The conjunction of a list. -/
def all : List Constr → Constr
  | [] => tt
  | p :: ps => and p (all ps)
end Constr

/-- `w : int(e)`: the word is `e` modulo 2^64 (the proof's D1). -/
def HasInt (ι : Val) (w : Word) (e : IExpr) : Prop :=
  (w.toNat : Int) % 2 ^ 64 = e.eval ι % 2 ^ 64

inductive Mode | ro | rw
  deriving DecidableEq, Repr

/-- A field: the 8-byte word `off` bytes from the capability's start is `int(ty)`. -/
structure Field where
  off : Nat
  ty : IExpr
  deriving DecidableEq, Repr

structure BytesCap where
  base : IExpr
  len : IExpr
  mode : Mode
  heap : Bool := false
  fields : List Field := []
  deriving DecidableEq, Repr

inductive CapKind
  | bytes (b : BytesCap)
  /-- An opaque token, by name (`Heap`). Its meaning is a `TokDef` (Sem.lean). -/
  | token (name : String)
  deriving DecidableEq, Repr

/-- A capability, usable when its guard holds (`p ≠ 0 ⇒ p ↦ bytes[n] rw heap`). -/
structure Cap where
  guard : Constr := .tt
  kind : CapKind
  deriving DecidableEq, Repr

/-- A `borrow` clause: the capability lent, and the fields it comes back with (I6). -/
structure Borrow where
  cap : Cap
  outFields : List Field
  deriving DecidableEq, Repr

structure Sig where
  /-- `[…]`: universal on entry. -/
  params : List Var
  inRegs : List (Reg × IExpr)
  borrow : List Borrow := []
  take : List Cap := []
  pre : Constr := .tt
  /-- Variables new in `out`: existential on exit. -/
  outVars : List Var := []
  outRegs : List (Reg × IExpr) := []
  give : List Cap := []
  post : Constr := .tt
  /-- `stack`: bytes below the entry `sp` the function may use. -/
  stack : Nat := 0
  /-- `partial` (I19): termination is not promised; the meaning is `MeetsP`. -/
  isPartial : Bool := false
  deriving DecidableEq, Repr

end NoCompiler.Typed

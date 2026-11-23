import NoCompiler.Typed.Sem
import NoCompiler.Typed.Search

/-
The type checker, part 1: substitution, state types, subtyping, edges, the shared helpers of
the rules (the rules themselves are in Check.lean and ArithExt.lean).

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
  /-- Φ: the saved words in the frame's slots, by offset from the lowered `sp`. -/
  slots : List (Nat × IExpr) := []
  /-- How far `sp` is below its entry value: 0 or the frame size (S3). -/
  depth : Nat := 0
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
    (max (S.facts.foldr (fun p m => max p.maxVar m) 0)
      (max (S.caps.foldr (fun c m => max (capMaxVar c) m) 0) (S.slots.foldr (fun p m => max p.2.maxVar m) 0)))

/-- The facts every held capability gives (`0 ≤ b`, `0 ≤ n`, `b + n ≤ 2^64` when its guard
    holds), with the recorded facts: the hypotheses of every query. -/
def hyps (S : STy) : List Constr :=
  S.facts ++ S.caps.filterMap fun c =>
    match c.cap.kind with
    | .bytes b => some (Constr.imp c.cap.guard
        (.and (.le (.lit 0) b.base) (.and (.le (.lit 0) b.len) (.le (b.base.add b.len) (.lit (2 ^ 64))))))
    | .token _ => none

/-- The hypotheses that share a variable with the goal, directly or through other kept
    hypotheses (the rest cannot matter for a satisfiable `Ψ`, and dropping hypotheses is
    always sound; it keeps the normal form small). -/
def relevant (hs : List Constr) (ψ : Constr) : List Constr :=
  let grow (vs : List Var) : List Var :=
    hs.foldl (fun acc p => if p.vars.any acc.contains then acc ++ p.vars else acc) vs
  let vs := grow (grow (grow (grow ψ.vars)))
  hs.filter fun p => p.vars.any vs.contains || p.vars.isEmpty

/-- `Ψ ⊢ ψ`. -/
def ent (S : STy) (ψ : Constr) : Bool :=
  let q := Query.mk (relevant S.hyps ψ) ψ
  match ψ with
  | .tt => true
  | .eq a b => a.same b || q.decide
  | .dvd _ e => e.same (.lit 0) || q.decide
  | _ => q.decide

/-- `a ≡ b (mod 2^64)` under Ψ. -/
def entEqMod (S : STy) (a b : IExpr) : Bool := a.same b || S.ent (Constr.eqMod a b)
end STy

/-- A byte capability without fields, renamed by `θ` (a callee's `give`, at the caller). -/
def Cap.subst (θ : Subst) (c : Cap) : Cap :=
  { guard := c.guard.subst θ
    kind := match c.kind with
      | .bytes b => .bytes { b with base := b.base.subst θ, len := b.len.subst θ, fields := [] }
      | .token t => .token t }

/-- The variables a capability mentions. -/
def Cap.vars (c : Cap) : List Var :=
  c.guard.vars ++ match c.kind with
    | .bytes b => b.base.vars ++ b.len.vars ++ b.fields.flatMap (·.ty.vars)
    | .token _ => []

namespace STy
/-- The variables of a type (with repetitions). -/
def vars (S : STy) : List Var :=
  S.regs.flatMap (·.2.vars) ++ S.slots.flatMap (·.2.vars) ++ S.facts.flatMap Constr.vars ++
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
        if (e'.terms.filter (·.2 == y)).length == 1 && rest.vars.all (fun x => known.contains x) then
          if a == 1 || a == -1 then some ((e.sub rest).smul a)
          else
            -- `a·y = e − rest`: solvable when `a` divides every coefficient of `e − rest`
            let l := (e.sub rest).toLin
            if a != 0 && l.c % a == 0 && l.t.all (fun t => t.2 % a == 0) then
              some ⟨l.c / a, l.t.map fun t => (t.2 / a, t.1)⟩
            else none
        else none

/-- Solve `a = b` for `y` (`a` mentions `y` once after normalising, `b` does not). -/
def solveLin (a b : IExpr) (y : Var) : Option IExpr :=
  let la := a.toLin
  match la.t.find? (·.1 == y) with
  | none => none
  | some (_, k) =>
    let rest : IExpr := ⟨la.c, (la.t.filter (·.1 != y)).map fun t => (t.2, t.1)⟩
    let l := (b.sub rest).toLin
    if k != 0 && l.c % k == 0 && l.t.all (fun t => t.2 % k == 0) then
      some ⟨l.c / k, l.t.map fun t => (t.2 / k, t.1)⟩
    else none

/-- Candidates for `y` from a target fact `p` matched against the source facts of the same
    shape: divisibility with the same modulus, or equations (either orientation). -/
def factCands (S : STy) (θ : Subst) (y : Var) (p : Constr) : List IExpr :=
  match p with
  | .dvd c a =>
    S.facts.filterMap fun q => match q with
      | .dvd c' b => if c == c' then solveLin (a.subst θ) b y else none
      | _ => none
  | .eq a1 a2 =>
    S.facts.flatMap fun q => match q with
      | .eq b1 b2 =>
        [solveLin ((a1.sub a2).subst θ) (b1.sub b2) y,
         solveLin ((a1.sub a2).subst θ) (b2.sub b1) y].filterMap id
      | _ => []
  | _ => []

/-- **Owned by agent U** (STATUS.md): more of `θ` after the register passes, e.g. from the
    target's facts. Untrusted like the rest of instantiation: `sub` re-checks any `θ`.
    A variable the registers leave open (an `urep`/`srep` representative, a quotient) is
    matched through the facts it occurs in; the simplest candidate wins. -/
def instantiateExt (S S' : STy) (newVars : List Var) (θ : Subst) : Subst :=
  let pass (θ : Subst) : Subst :=
    newVars.foldl (fun θ y =>
      if (θ.lookup y).isSome then θ else
      let cands := (S'.facts.flatMap fun p =>
        if p.vars.contains y then factCands S θ y p else []).filter
          (fun e => e.vars.all (fun x => !newVars.contains x || (θ.lookup x).isSome))
      match cands.foldl (fun best e => match best with
          | none => some e
          | some b => if e.terms.length < b.terms.length then some e else some b) none with
      | some e => (y, e) :: θ
      | none => θ) θ
  pass (pass θ)

def instantiate (S S' : STy) (newVars : List Var) : Subst :=
  -- passes: each may make more variables known
  let known0 := (S.vars ++ S'.vars).filter (fun x => !newVars.contains x)
  let step (acc : Subst × List Var) : Subst × List Var :=
    newVars.foldl (fun (θ, kn) y =>
      if (θ.lookup y).isSome then (θ, kn) else
      match S.solveFrom S' y kn with
      | some e => ((y, e.subst θ) :: θ, y :: kn)
      | none => (θ, kn)) acc
  S.instantiateExt S' newVars (step (step (step ([], known0)))).1

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
  S'.caps.all (fun c' => S.caps.any fun c => S.capSub θ c c') &&
  S'.depth == S.depth &&
  S'.slots.all (fun (k, e') => match S.slots.lookup k with
    | some e => S.entEqMod e (e'.subst θ)
    | none => false)

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

/-- The frame (I8): `addi sp, sp, -size` in the prologue; 8-byte save slots and
    address-taken ranges `[o, o + l)`, all as offsets from the lowered `sp`. -/
structure Frame where
  size : Nat
  slots : List Nat := []
  addr : List (Nat × Nat) := []
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
  frame : Option Frame := none
  /-- The order τ of the points (word indices) from the export (decisions.md I36); not used by
      the checker yet. -/
  tau : List Nat := []
  /-- Bit counts `k` for which an `xor` result also gets `2^k ∣ x ⇔ 2^k ∣ a − b` (the
      xor-then-mask idiom, I23). A hint from the record; sound for any list (U). -/
  xorBits : List Nat := []
  /-- The functions it calls: entry address and signature (each must meet it; `check_sound`'s
      hypotheses). -/
  callees : List (Word × Sig) := []
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

/-- The position of point `k` in the recorded order τ (I36; the address itself when the
    record has no order). `structOk` requires τ empty or a permutation of the points. -/
def pos (k : Nat) : Nat := if f.tau = [] then k else f.tau.idxOf k

def inside (L : Loop) (k : Nat) : Bool := f.pos L.head ≤ f.pos k && f.pos k ≤ f.pos L.last

/-- The identity of the entry capability of `borrow` clause `i`: the record's at the entry, if
    it lists one with that origin (a hint; `structOk` requires them distinct). -/
def entryId (i : Nat) : Nat :=
  match f.tyAt 0 with
  | some S => ((S.caps.find? (·.origin == some i)).map (·.id)).getD i
  | none => i

/-- The type at the entry, from the signature (T0). -/
def initTy : STy where
  regs := f.sig.inRegs ++ f.regVar.map (fun p => (p.1, .var p.2)) ++
    -- every register's entry value, as a variable from `fresh` up
    (List.finRange 32).map (fun r => (r, .var (f.fresh + r.val)))
  facts := f.sig.pre ::
    (match f.regVar.lookup 2 with
     | some x => [.le (.lit 0) (.var x), .lt (.var x) (.lit (2 ^ 64)), .dvd 16 (.var x),
                  .le (.lit f.sig.stack) (.var x)]
     | none => [])
  -- borrowed and taken capabilities; the origin is the index in `Sig.entryCaps`
  caps := (f.sig.entryCaps.zipIdx.map fun (c, i) =>
    ({ id := f.entryId i, cap := c, origin := some i } : HCap))

/-! ### Edges -/


/-- Check the edge from instruction `k` (or the entry, `k = none`) to `k'`, the type after
    the instruction being `S`. -/
def edgeOk (k : Option Nat) (S S' : STy) (k' : Nat) (θ : Subst) : Bool :=
  let back := match k with | some k => decide (f.pos k' ≤ f.pos k) | none => false
  decide (k' < f.size) &&
  -- θ never binds a protected variable, nor a measure variable of a loop containing both
  -- ends of the edge (other than at the loop's own backward edge)
  θ.all (fun p => !f.protectedVars.contains p.1 &&
    f.loops.all fun K =>
      (match k with
       | some k => !(f.inside K k && f.inside K k' && !(back && K.head == k'))
       | none => true) || !K.meas.vars.contains p.1) &&
  S.sub θ S' &&
  (if back then
    match f.loopAt k', k with
    | some L, some k => decide (f.pos k ≤ f.pos L.last) && S.ent (.le (.lit 0) L.meas) &&
        S.ent (.lt (L.meas.subst θ) L.meas)
    | _, _ => false
   else true)

/-- Check the edge from instruction `k` (or the entry, `k = none`) to `k'`, the type after
    the instruction being `S`; the instantiation is found heuristically. -/
def edge (k : Option Nat) (S : STy) (k' : Nat) : Bool :=
  match f.tyAt k' with
  | none => false
  | some S' =>
    let back := match k with | some k => decide (f.pos k' ≤ f.pos k) | none => false
    let sv := S.vars
    -- new: the loop's variables at a backward edge, the target's variables the source does
    -- not have, and the target's bare register variables whose register changed
    let changed := S'.regs.filterMap fun (r, e') =>
      match e'.asVar with
      | some y => if S.reg r == some e' then none else some y
      | none => none
    let nv := (if back then ((f.loopAt k').map (·.vars)).getD [] else []) ++
      (S'.vars.filter (fun x => !sv.contains x)).eraseDups ++ changed.eraseDups
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

/-- `rd` is the sign-extended low 32 bits of `e`: `x ≡ e (mod 2^32)`, `−2^31 ≤ x < 2^31`. -/
def word32 (S : STy) (rd : Reg) (x : Var) (e : IExpr) : STy :=
  (S.setReg rd (some (.var x))).addFacts
    [.dvd (2 ^ 32) (e.sub (.var x)), .le (.lit (-2 ^ 31)) (.var x), .lt (.var x) (.lit (2 ^ 31))]

end Fn

end NoCompiler.Typed

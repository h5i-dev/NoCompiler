import NoCompiler.Typed.Presburger

/-
Finding cutting-plane certificates: Fourier–Motzkin elimination with rounding.

Not trusted: whatever it returns is checked by `Cert.check` (`Query.check_sound`). It is
incomplete — it gives up after a fuel or size limit, and real-shadow elimination with
rounding does not refute every integer-infeasible system — so a valid entailment may be
reported as not proved, which only makes the type checker reject more programs.
-/
namespace NoCompiler.Typed.Search

structure Item where
  lin : Lin
  idx : Nat

def coef (l : Lin) (x : Var) : Int := ((l.t.find? (·.1 == x)).map (·.2)).getD 0

structure St where
  steps : Array CStep := #[]
  items : List Item := []

def St.push (st : St) (s : CStep) : St × Nat := ({ st with steps := st.steps.push s }, st.steps.size)

/-- Add `0 ≤ l` (derived by step `s`), rounded. -/
def St.add (st : St) (s : CStep) (l : Lin) : St :=
  let (st, i) := st.push s
  let t := Lin.tighten l
  if t == l then { st with items := ⟨l, i⟩ :: st.items }
  else
    let (st, j) := st.push (.tight i)
    { st with items := ⟨t, j⟩ :: st.items }

/-- Keep one constraint per coefficient vector, the strongest. -/
def dedupe (xs : List Item) : List Item :=
  xs.foldl (fun acc it =>
    match acc.find? (fun o => o.lin.t == it.lin.t) with
    | some o => if it.lin.c < o.lin.c then it :: acc.filter (fun o' => o'.idx != o.idx) else acc
    | none => it :: acc) []

def varsOf (xs : List Item) : List Var :=
  xs.foldl (fun acc it => it.lin.t.foldl (fun a t => if a.contains t.1 then a else t.1 :: a) acc) []

def gcdI (a b : Int) : Int := (Nat.gcd a.natAbs b.natAbs : Int)

/-- Eliminate one variable; `none` past the size limit. -/
def elimVar (st : St) (x : Var) (limit : Nat) : Option St :=
  let pos := st.items.filter (fun it => coef it.lin x > 0)
  let neg := st.items.filter (fun it => coef it.lin x < 0)
  let rest := st.items.filter (fun it => coef it.lin x == 0)
  if pos.length * neg.length + rest.length > limit then none else
  let st0 : St := { st with items := rest }
  let st1 := pos.foldl (fun st p => neg.foldl (fun st n =>
    let a := coef p.lin x
    let b := -coef n.lin x
    let g := gcdI a b
    let kp := (b / g).toNat
    let kn := (a / g).toNat
    st.add (.comb p.idx kp n.idx kn) (Lin.add (Lin.smul kp p.lin) (Lin.smul kn n.lin))) st) st0
  some { st1 with items := dedupe st1.items }

/-- The size of the elimination; an inexact one (a coefficient other than ±1 on both
    sides, so the real shadow may lose integer infeasibility) only as a last resort. -/
def cost (xs : List Item) (x : Var) : Nat :=
  let ps := xs.filter (fun it => coef it.lin x > 0)
  let ns := xs.filter (fun it => coef it.lin x < 0)
  let exact := ps.all (fun it => coef it.lin x == 1) || ns.all (fun it => coef it.lin x == -1)
  ps.length * ns.length + (if exact then 0 else 1000000)

def found (st : St) : Bool := st.items.any (fun it => Cert.contra it.lin)

def loop (limit : Nat) : Nat → St → Option St
  | 0, _ => none
  | fuel + 1, st =>
    if found st then some st else
    match varsOf st.items with
    | [] => none
    | v :: vs =>
      let x := vs.foldl (fun b y => if cost st.items y < cost st.items b then y else b) v
      match elimVar st x limit with
      | none => none
      | some st' => loop limit fuel st'

/-- A certificate refuting `0 ≤ h` for all `h ∈ hs`, if the search finds one. -/
def refute (hs : List Lin) (fuel : Nat := 40) (limit : Nat := 400) : Option Cert :=
  let st := (List.range hs.length).foldl (fun st i => st.add (.hyp i) (hs[i]?.getD ⟨0, []⟩)) ({} : St)
  (loop limit fuel { st with items := dedupe st.items }).map (·.steps.toList)

/-- Certificates for every branch of a query. -/
def prove (q : Query) : Option (List Cert) :=
  let bs := q.branches
  if bs.length > 256 then none else bs.mapM (refute ·)

end NoCompiler.Typed.Search

namespace NoCompiler.Typed.Query
/-- `Ψ ⊢ ψ` by the search; sound by `Query.check_sound` whatever the search does. -/
def decide (q : Query) : Bool :=
  match Search.prove q with
  | some cs => q.check cs
  | none => false

theorem decide_sound {q : Query} (h : q.decide = true) (ι : Val)
    (hh : ∀ p ∈ q.hyps, p.holds ι) : q.goal.holds ι := by
  unfold decide at h
  split at h
  · exact check_sound h ι hh
  · cases h
end NoCompiler.Typed.Query

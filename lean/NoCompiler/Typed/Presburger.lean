import NoCompiler.Typed.Lin

/-
Entailment between quantifier-free Presburger constraints: `Ψ ⊢ ψ`, decided by
refuting `Ψ ∧ ¬ψ`.

1. `Constr.dnf` puts a constraint (or its negation) in disjunctive normal form over
   three literals: `a ≤ b`, `c ∣ e`, `¬ (c ∣ e)` (`=` is two `≤`; `¬ ≤` and `¬ =` are
   strict comparisons, which are `≤` over the integers).
2. `Lit.lins` turns a branch into linear constraints `0 ≤ l`, with fresh variables for
   divisibility: `c ∣ e` is `e = c·k`; `¬ (c ∣ e)` is `e = c·k + r ∧ 1 ≤ r ≤ c − 1`.
3. Each branch is refuted by a cutting-plane certificate (NoCompiler/Typed/Lin.lean).

`Query.check` checks given certificates (sound: `Query.check_sound`). `Query.search`
finds certificates by Fourier–Motzkin elimination with rounding; it is not trusted
and it is incomplete (it can fail on a valid entailment), which only makes the type
checker reject more programs.
-/
namespace NoCompiler.Typed

namespace IExpr
def toLin (e : IExpr) : Lin := ⟨e.const, e.terms.foldr (fun t l => Lin.addTerm t.2 t.1 l) []⟩

theorem evalT_toLin (ι : Val) (ts : List (Int × Var)) :
    Lin.evalT ι (ts.foldr (fun t l => Lin.addTerm t.2 t.1 l) []) =
      (ts.map fun t => t.1 * ι t.2).sum := by
  induction ts with
  | nil => simp [Lin.evalT]
  | cons h r ih => simp only [List.foldr_cons, Lin.evalT_addTerm, ih, List.map_cons, List.sum_cons]

@[simp] theorem eval_toLin (ι : Val) (e : IExpr) : e.toLin.eval ι = e.eval ι := by
  simp only [toLin, Lin.eval, evalT_toLin, eval]

theorem eval_congr {ι ι' : Val} (e : IExpr) (h : ∀ x ∈ e.vars, ι x = ι' x) :
    e.eval ι = e.eval ι' := by
  unfold eval vars at *
  congr 1
  generalize e.terms = ts at *
  induction ts with
  | nil => rfl
  | cons t r ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h t.2 (by simp), ih (fun x hx => h x (by simp [hx]))]

@[simp] theorem vars_add (a b : IExpr) : (a.add b).vars = a.vars ++ b.vars := by
  simp [add, vars]
@[simp] theorem vars_smul (k : Int) (a : IExpr) : (a.smul k).vars = a.vars := by
  simp [smul, vars]
@[simp] theorem vars_sub (a b : IExpr) : (a.sub b).vars = a.vars ++ b.vars := by
  simp [sub]
@[simp] theorem vars_var (x : Var) : (var x).vars = [x] := by simp [var, vars]
@[simp] theorem vars_lit (c : Int) : (lit c).vars = [] := by simp [lit, vars]
end IExpr

/-- A literal of the normal form. -/
inductive Lit
  | le (a b : IExpr)
  | dvd (c : Nat) (e : IExpr)
  | ndvd (c : Nat) (e : IExpr)
  deriving DecidableEq, Repr

namespace Lit
def holds (ι : Val) : Lit → Prop
  | le a b => a.eval ι ≤ b.eval ι
  | dvd c e => e.eval ι % (c : Int) = 0
  | ndvd c e => e.eval ι % (c : Int) ≠ 0

def vars : Lit → List Var
  | le a b => a.vars ++ b.vars
  | dvd _ e => e.vars
  | ndvd _ e => e.vars

theorem holds_congr {ι ι' : Val} (l : Lit) (h : ∀ x ∈ l.vars, ι x = ι' x) :
    l.holds ι ↔ l.holds ι' := by
  cases l with
  | le a b =>
    simp only [vars, List.mem_append] at h
    simp only [holds]
    rw [IExpr.eval_congr a (fun x hx => h x (.inl hx)), IExpr.eval_congr b (fun x hx => h x (.inr hx))]
  | dvd c e => simp only [holds]; rw [IExpr.eval_congr e h]
  | ndvd c e => simp only [holds]; rw [IExpr.eval_congr e h]
end Lit

namespace Constr

/-- DNF of `p` (when `pos`) or of `¬ p`. -/
def dnf : Bool → Constr → List (List Lit)
  | true, tt => [[]]
  | false, tt => []
  | true, ff => []
  | false, ff => [[]]
  | true, le a b => [[.le a b]]
  | false, le a b => [[.le (b.add (.lit 1)) a]]
  | true, eq a b => [[.le a b, .le b a]]
  | false, eq a b => [[.le (a.add (.lit 1)) b], [.le (b.add (.lit 1)) a]]
  | true, dvd c e => if c = 0 then [[.le e (.lit 0), .le (.lit 0) e]] else [[.dvd c e]]
  | false, dvd c e =>
    if c = 0 then [[.le (.lit 1) e], [.le e (.lit (-1))]] else [[.ndvd c e]]
  | true, and p q => (dnf true p).flatMap fun b => (dnf true q).map (b ++ ·)
  | false, and p q => dnf false p ++ dnf false q
  | true, or p q => dnf true p ++ dnf true q
  | false, or p q => (dnf false p).flatMap fun b => (dnf false q).map (b ++ ·)
  | pos, not p => dnf (!pos) p

theorem dnf_complete (ι : Val) : ∀ (pos : Bool) (p : Constr),
    p.eval ι = pos → ∃ b ∈ dnf pos p, ∀ l ∈ b, l.holds ι
  | true, tt, _ => ⟨[], by simp [dnf]⟩
  | false, tt, h => by simp [eval] at h
  | true, ff, h => by simp [eval] at h
  | false, ff, _ => ⟨[], by simp [dnf]⟩
  | true, le a b, h => ⟨[.le a b], by simp [dnf], by simp_all [eval, Lit.holds]⟩
  | false, le a b, h => ⟨[.le (b.add (.lit 1)) a], by simp [dnf], by simp_all [eval, Lit.holds]; omega⟩
  | true, eq a b, h => ⟨[.le a b, .le b a], by simp [dnf], by simp_all [eval, Lit.holds]⟩
  | false, eq a b, h => by
    simp only [eval, decide_eq_false_iff_not] at h
    rcases Int.lt_or_gt_of_ne h with h | h
    · exact ⟨[.le (a.add (.lit 1)) b], by simp [dnf], by simp [Lit.holds]; omega⟩
    · exact ⟨[.le (b.add (.lit 1)) a], by simp [dnf], by simp [Lit.holds]; omega⟩
  | true, dvd c e, h => by
    simp only [eval, decide_eq_true_eq] at h
    unfold dnf; split
    · subst_vars; simp at h
      exact ⟨[.le e (.lit 0), .le (.lit 0) e], by simp, by simp [Lit.holds]; omega⟩
    · exact ⟨[.dvd c e], by simp, by simp [Lit.holds, h]⟩
  | false, dvd c e, h => by
    simp only [eval, decide_eq_false_iff_not] at h
    unfold dnf; split
    · subst_vars; simp at h
      rcases Int.lt_or_gt_of_ne h with h | h
      · exact ⟨[.le e (.lit (-1))], by simp, by simp [Lit.holds]; omega⟩
      · exact ⟨[.le (.lit 1) e], by simp, by simp [Lit.holds]; omega⟩
    · exact ⟨[.ndvd c e], by simp, by simp [Lit.holds, h]⟩
  | true, and p q, h => by
    simp only [eval, Bool.and_eq_true] at h
    obtain ⟨b1, h1, k1⟩ := dnf_complete ι true p h.1
    obtain ⟨b2, h2, k2⟩ := dnf_complete ι true q h.2
    refine ⟨b1 ++ b2, List.mem_flatMap.2 ⟨b1, h1, List.mem_map.2 ⟨b2, h2, rfl⟩⟩, ?_⟩
    intro l hl; rcases List.mem_append.1 hl with hl | hl
    · exact k1 l hl
    · exact k2 l hl
  | false, and p q, h => by
    simp only [eval, Bool.and_eq_false_iff] at h
    rcases h with h | h
    · obtain ⟨b, hb, k⟩ := dnf_complete ι false p h
      exact ⟨b, List.mem_append.2 (.inl hb), k⟩
    · obtain ⟨b, hb, k⟩ := dnf_complete ι false q h
      exact ⟨b, List.mem_append.2 (.inr hb), k⟩
  | true, or p q, h => by
    simp only [eval, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨b, hb, k⟩ := dnf_complete ι true p h
      exact ⟨b, List.mem_append.2 (.inl hb), k⟩
    · obtain ⟨b, hb, k⟩ := dnf_complete ι true q h
      exact ⟨b, List.mem_append.2 (.inr hb), k⟩
  | false, or p q, h => by
    simp only [eval, Bool.or_eq_false_iff] at h
    obtain ⟨b1, h1, k1⟩ := dnf_complete ι false p h.1
    obtain ⟨b2, h2, k2⟩ := dnf_complete ι false q h.2
    refine ⟨b1 ++ b2, List.mem_flatMap.2 ⟨b1, h1, List.mem_map.2 ⟨b2, h2, rfl⟩⟩, ?_⟩
    intro l hl; rcases List.mem_append.1 hl with hl | hl
    · exact k1 l hl
    · exact k2 l hl
  | pos, not p, h => by
    simp only [eval] at h
    simp only [dnf]
    exact dnf_complete ι (!pos) p (by cases pos <;> simp_all)

end Constr

namespace Lit
/-- The linear constraints of a literal, with fresh variables from `n`; and the next
    fresh variable. -/
def lins (n : Nat) : Lit → List Lin × Nat
  | le a b => ([(b.sub a).toLin], n)
  | dvd c e =>
    let d := e.sub ((IExpr.var n).smul c)
    ([d.toLin, (d.smul (-1)).toLin], n + 1)
  | ndvd c e =>
    if c = 0 then ([], n) else
    let d := (e.sub ((IExpr.var n).smul c)).sub (IExpr.var (n + 1))
    ([d.toLin, (d.smul (-1)).toLin, ((IExpr.var (n + 1)).sub (.lit 1)).toLin,
      ((IExpr.lit ((c : Int) - 1)).sub (IExpr.var (n + 1))).toLin], n + 2)

theorem lins_next (n : Nat) (l : Lit) : n ≤ (l.lins n).2 := by
  cases l <;> simp only [lins] <;> (try split) <;> simp

/-- Fresh values satisfying a literal's constraints. -/
def fresh (ι : Val) (n : Nat) : Lit → Val
  | le _ _ => ι
  | dvd c e => fun x => if x = n then e.eval ι / (c : Int) else ι x
  | ndvd c e => fun x =>
    if x = n then e.eval ι / (c : Int) else if x = n + 1 then e.eval ι % (c : Int) else ι x

theorem fresh_below (ι : Val) (n : Nat) (l : Lit) : ∀ x < n, l.fresh ι n x = ι x := by
  intro x hx
  cases l <;> simp [fresh, show x ≠ n by omega, show x ≠ n + 1 by omega]

theorem lins_sound {ι : Val} {n : Nat} {l : Lit} (hv : ∀ x ∈ l.vars, x < n) (h : l.holds ι) :
    ∀ c ∈ (l.lins n).1, 0 ≤ c.eval (l.fresh ι n) := by
  have hag : ∀ x ∈ l.vars, ι x = l.fresh ι n x := fun x hx => (fresh_below ι n l x (hv x hx)).symm
  cases l with
  | le a b =>
    simp only [lins, List.mem_singleton, forall_eq, IExpr.eval_toLin, IExpr.eval_sub]
    simp only [holds] at h; simp only [fresh]; omega
  | dvd c e =>
    simp only [vars] at hag
    have he := IExpr.eval_congr e hag
    simp only [holds] at h
    have hm := Int.emod_add_mul_ediv (e.eval ι) c
    simp only [lins, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      IExpr.eval_toLin, IExpr.eval_sub, IExpr.eval_smul, IExpr.eval_var]
    simp only [fresh] at he ⊢
    simp only [ite_true]
    rw [← he]; constructor <;> omega
  | ndvd c e =>
    simp only [lins]
    split
    · simp
    · rename_i hc
      simp only [vars] at hag
      have he := IExpr.eval_congr e hag
      simp only [holds] at h
      have hm := Int.emod_add_mul_ediv (e.eval ι) c
      have h0 := Int.emod_nonneg (e.eval ι) (b := c) (by omega)
      have h1 := Int.emod_lt_of_pos (e.eval ι) (b := c) (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        IExpr.eval_toLin, IExpr.eval_sub, IExpr.eval_smul, IExpr.eval_var, IExpr.eval_lit]
      simp only [fresh] at he ⊢
      have hn1 : (n = n + 1) = False := by simp
      have hn2 : (n + 1 = n) = False := by simp
      simp only [ite_true, hn1, hn2, ite_false]
      rw [← he]
      generalize (c : Int) * (IExpr.eval ι e / c) = q at *
      refine ⟨by omega, by omega, by omega, by omega⟩
end Lit

/-- The linear constraints of a branch, fresh variables from `n`. -/
def linsOf : Nat → List Lit → List Lin
  | _, [] => []
  | n, l :: ls => (l.lins n).1 ++ linsOf (l.lins n).2 ls

/-- Constraints mention only variables below a bound and fresh ones from `n`. -/
def Lin.varsBelow (k : Nat) (c : Lin) : Prop := ∀ t ∈ c.t, t.1 < k

theorem Lin.eval_congr {ι ι' : Val} (c : Lin) (h : ∀ t ∈ c.t, ι t.1 = ι' t.1) :
    c.eval ι = c.eval ι' := by
  unfold eval; congr 1
  generalize c.t = ts at *
  induction ts with
  | nil => rfl
  | cons t r ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    obtain ⟨x, a⟩ := t
    simp only [evalT]; rw [h.1, ih h.2]

theorem Lin.mem_addTerm {x : Var} {a : Int} {l : List (Var × Int)} {t : Var × Int}
    (h : t ∈ addTerm x a l) : t.1 = x ∨ t ∈ l := by
  induction l with
  | nil => unfold addTerm at h; split at h <;> simp_all
  | cons hd r ih =>
    obtain ⟨y, b⟩ := hd
    unfold addTerm at h
    split at h
    · split at h
      · exact .inr h
      · rcases List.mem_cons.1 h with h | h
        · exact .inl (by rw [h])
        · exact .inr h
    · split at h
      · subst_vars; split at h
        · exact .inr (List.mem_cons_of_mem _ h)
        · rcases List.mem_cons.1 h with h | h
          · left; rw [h]
          · exact .inr (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.1 h with h | h
        · exact .inr (by rw [h]; exact List.mem_cons_self ..)
        · rcases ih h with h | h
          · exact .inl h
          · exact .inr (List.mem_cons_of_mem _ h)

theorem IExpr.mem_toLin {e : IExpr} {t : Var × Int} (h : t ∈ e.toLin.t) : t.1 ∈ e.vars := by
  unfold toLin vars at *
  dsimp only at h
  generalize e.terms = ts at *
  induction ts with
  | nil => simp at h
  | cons hd r ih =>
    simp only [List.foldr_cons] at h
    rcases Lin.mem_addTerm h with h | h
    · simp [h]
    · simp [ih h]

theorem Lit.lins_vars (n : Nat) (l : Lit) :
    ∀ c ∈ (l.lins n).1, ∀ t ∈ c.t, t.1 ∈ l.vars ∨ (n ≤ t.1 ∧ t.1 < (l.lins n).2) := by
  intro c hc t ht
  cases l with
  | le a b =>
    simp only [lins, List.mem_singleton] at hc; subst hc
    have := IExpr.mem_toLin ht; simp only [IExpr.vars_sub, List.mem_append] at this
    simp only [vars, List.mem_append]; exact .inl (Or.comm.1 this)
  | dvd k e =>
    simp only [lins, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | hc <;> subst hc <;>
    · have := IExpr.mem_toLin ht
      simp only [IExpr.vars_sub, IExpr.vars_smul, IExpr.vars_var, List.mem_append,
        List.mem_singleton] at this
      simp only [vars]
      by_cases hm : t.1 ∈ e.vars
      · exact .inl hm
      · right; simp only [lins]; simp only [Var] at *; simp [hm] at this; omega
  | ndvd k e =>
    simp only [lins] at hc ⊢
    split at hc
    · simp at hc
    · rename_i hk0
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | hc | hc | hc <;> subst hc <;>
      · have := IExpr.mem_toLin ht
        simp only [IExpr.vars_sub, IExpr.vars_smul, IExpr.vars_var, IExpr.vars_lit,
          List.mem_append, List.mem_singleton, List.not_mem_nil] at this
        simp only [vars]
        by_cases hm : t.1 ∈ e.vars
        · exact .inl hm
        · right; simp only [Var] at *; simp [hm, hk0] at this ⊢; omega

/-- If the literals hold and mention only variables below `n`, the linear constraints hold
    under some valuation that agrees below `n`. -/
theorem linsOf_sound : ∀ (ls : List Lit) (n : Nat) (ι : Val),
    (∀ l ∈ ls, ∀ x ∈ l.vars, x < n) → (∀ l ∈ ls, l.holds ι) →
      ∃ ι' : Val, (∀ x < n, ι' x = ι x) ∧ ∀ c ∈ linsOf n ls, 0 ≤ c.eval ι'
  | [], _, ι, _, _ => ⟨ι, fun _ _ => rfl, by simp [linsOf]⟩
  | l :: ls, n, ι, hv, hh => by
    have hv0 := hv l (by simp)
    have hn := Lit.lins_next n l
    let ι1 := l.fresh ι n
    have hb1 : ∀ x < n, ι1 x = ι x := Lit.fresh_below ι n l
    have hh1 : ∀ l' ∈ ls, l'.holds ι1 := fun l' hl' =>
      (Lit.holds_congr l' (fun x hx => (hb1 x (hv l' (by simp [hl']) x hx)).symm)).1 (hh l' (by simp [hl']))
    obtain ⟨ι', hag, hc⟩ := linsOf_sound ls (l.lins n).2 ι1
      (fun l' hl' x hx => Nat.lt_of_lt_of_le (hv l' (by simp [hl']) x hx) hn) hh1
    refine ⟨ι', fun x hx => (hag x (by omega)).trans (hb1 x hx), ?_⟩
    intro c hcm
    simp only [linsOf, List.mem_append] at hcm
    rcases hcm with hcm | hcm
    · have h0 := Lit.lins_sound hv0 (hh l (by simp)) c hcm
      rw [Lin.eval_congr c (ι' := ι1)] ; exact h0
      intro t ht
      rcases Lit.lins_vars n l c hcm t ht with h | h
      · exact hag _ (Nat.lt_of_lt_of_le (hv0 _ h) hn)
      · exact hag _ h.2
    · exact hc c hcm

/-- One more than the largest variable of the literals. -/
def litsBound (ls : List Lit) : Nat := (ls.flatMap Lit.vars).foldr (fun x m => max (x + 1) m) 0

theorem lt_litsBound {ls : List Lit} {l : Lit} (hl : l ∈ ls) {x : Var} (hx : x ∈ l.vars) :
    x < litsBound ls := by
  unfold litsBound
  have : x ∈ ls.flatMap Lit.vars := List.mem_flatMap.2 ⟨l, hl, hx⟩
  generalize ls.flatMap Lit.vars = xs at this
  induction xs with
  | nil => simp at this
  | cons y r ih =>
    simp only [List.mem_cons] at this; simp only [List.foldr_cons]
    simp only [Var] at *
    rcases this with h | h
    · subst h; omega
    · have := ih h; omega

/-- `Ψ ⊢ ψ`. -/
structure Query where
  hyps : List Constr
  goal : Constr
  deriving DecidableEq, Repr

namespace Query

/-- The branches of `Ψ ∧ ¬ψ`, each as linear constraints. -/
def branches (q : Query) : List (List Lin) :=
  ((Constr.all q.hyps).and (.not q.goal)).dnf true |>.map fun b => linsOf (litsBound b) b

def checkAll : List (List Lin) → List Cert → Bool
  | [], [] => true
  | b :: bs, c :: cs => Cert.check b c && checkAll bs cs
  | _, _ => false

theorem checkAll_mem : ∀ {bs : List (List Lin)} {cs : List Cert}, checkAll bs cs = true →
    ∀ b ∈ bs, ∃ c, Cert.check b c = true
  | [], [], _ => by simp
  | b :: bs, c :: cs, h => by
    simp only [checkAll, Bool.and_eq_true] at h
    intro b' hb'
    rcases List.mem_cons.1 hb' with e | hb'
    · subst e; exact ⟨c, h.1⟩
    · exact checkAll_mem h.2 b' hb'
  | [], _ :: _, h | _ :: _, [], h => by simp [checkAll] at h

/-- Check one certificate per branch. -/
def check (q : Query) (cs : List Cert) : Bool := checkAll q.branches cs

theorem all_holds {ι : Val} : ∀ {ps : List Constr}, (∀ p ∈ ps, p.holds ι) → (Constr.all ps).eval ι = true
  | [], _ => rfl
  | p :: ps, h => by
    simp only [Constr.all, Constr.eval, Bool.and_eq_true]
    exact ⟨h p (by simp), all_holds (fun q hq => h q (by simp [hq]))⟩

theorem check_sound {q : Query} {cs : List Cert} (h : q.check cs = true) (ι : Val)
    (hh : ∀ p ∈ q.hyps, p.holds ι) : q.goal.holds ι := by
  refine Classical.byContradiction fun hg => ?_
  have hall : ((Constr.all q.hyps).and (.not q.goal)).eval ι = true := by
    simp only [Constr.eval, all_holds hh, Bool.true_and, Bool.not_eq_true']
    simpa [Constr.holds] using hg
  obtain ⟨b, hb, hl⟩ := Constr.dnf_complete ι true _ hall
  obtain ⟨ι', -, hc⟩ := linsOf_sound b (litsBound b) ι (fun l hl x hx => lt_litsBound hl hx) hl
  obtain ⟨c, hcc⟩ := checkAll_mem h _ (List.mem_map.2 ⟨b, hb, rfl⟩)
  exact Cert.check_sound hcc ι' hc

end Query

end NoCompiler.Typed

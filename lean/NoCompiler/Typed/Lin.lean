import NoCompiler.Typed.Lang

/-
Linear forms over the integers in a normal form (terms sorted by variable, no zero
coefficient), and cutting-plane certificates of infeasibility.

A certificate is a list of steps, each deriving `0 ≤ l` from the hypotheses or from
earlier steps: a hypothesis, a nonnegative combination of two earlier steps, or the
rounding of one (divide by the gcd of the coefficients, round the constant down: sound
over the integers). It proves the hypotheses infeasible when some step derives a
constant negative form. `Cert.check` decides that, and `Cert.check_sound` proves it
correct; how the certificate was found (NoCompiler/Typed/Presburger.lean, or an
external tool) does not matter.
-/
namespace NoCompiler.Typed

/-- `c + Σ a·x`, meant as the constraint `0 ≤ c + Σ a·x`. -/
structure Lin where
  c : Int
  t : List (Var × Int) := []
  deriving DecidableEq, Repr

namespace Lin

def evalT (ι : Val) : List (Var × Int) → Int
  | [] => 0
  | (x, a) :: r => a * ι x + evalT ι r

def eval (ι : Val) (l : Lin) : Int := l.c + evalT ι l.t

/-- Add `a·x` to sorted terms. -/
def addTerm (x : Var) (a : Int) : List (Var × Int) → List (Var × Int)
  | [] => if a = 0 then [] else [(x, a)]
  | (y, b) :: r =>
    if x < y then (if a = 0 then (y, b) :: r else (x, a) :: (y, b) :: r)
    else if x = y then (if a + b = 0 then r else (y, a + b) :: r)
    else (y, b) :: addTerm x a r

theorem evalT_addTerm (ι : Val) (x : Var) (a : Int) (l : List (Var × Int)) :
    evalT ι (addTerm x a l) = a * ι x + evalT ι l := by
  induction l with
  | nil => unfold addTerm; split <;> simp_all [evalT]
  | cons h r ih =>
    obtain ⟨y, b⟩ := h
    unfold addTerm
    split
    · split <;> simp_all [evalT]
    · split
      · subst_vars; split
        · simp only [evalT]; rename_i h
          have e : a * ι y + b * ι y = 0 := by rw [← Int.add_mul, h, Int.zero_mul]
          omega
        · simp only [evalT]; rw [Int.add_mul]; omega
      · simp only [evalT, ih]; omega

def addTerms : List (Var × Int) → List (Var × Int) → List (Var × Int)
  | [], l => l
  | (x, a) :: r, l => addTerm x a (addTerms r l)

theorem evalT_addTerms (ι : Val) (l₁ l₂ : List (Var × Int)) :
    evalT ι (addTerms l₁ l₂) = evalT ι l₁ + evalT ι l₂ := by
  induction l₁ with
  | nil => simp [addTerms, evalT]
  | cons h r ih => obtain ⟨x, a⟩ := h; simp only [addTerms, evalT_addTerm, ih, evalT]; omega

def add (l₁ l₂ : Lin) : Lin := ⟨l₁.c + l₂.c, addTerms l₁.t l₂.t⟩

@[simp] theorem eval_add (ι : Val) (l₁ l₂ : Lin) : (add l₁ l₂).eval ι = l₁.eval ι + l₂.eval ι := by
  simp only [add, eval, evalT_addTerms]; omega

def smulT (k : Int) : List (Var × Int) → List (Var × Int)
  | [] => []
  | (x, a) :: r => (x, k * a) :: smulT k r

theorem evalT_smulT (ι : Val) (k : Int) (l : List (Var × Int)) :
    evalT ι (smulT k l) = k * evalT ι l := by
  induction l with
  | nil => simp [smulT, evalT]
  | cons h r ih => obtain ⟨x, a⟩ := h; simp only [smulT, evalT, ih, Int.mul_add, Int.mul_assoc]

/-- `k · l`; zero coefficients only for `k = 0`, which gives the zero form. -/
def smul (k : Int) (l : Lin) : Lin := if k = 0 then ⟨0, []⟩ else ⟨k * l.c, smulT k l.t⟩

@[simp] theorem eval_smul (ι : Val) (k : Int) (l : Lin) : (smul k l).eval ι = k * l.eval ι := by
  unfold smul; split
  · subst_vars; simp [eval, evalT]
  · simp only [eval, evalT_smulT, Int.mul_add]

def gcdT : List (Var × Int) → Nat
  | [] => 0
  | (_, a) :: r => Nat.gcd a.natAbs (gcdT r)

def divT (g : Int) : List (Var × Int) → List (Var × Int)
  | [] => []
  | (x, a) :: r => (x, a / g) :: divT g r

theorem evalT_divT (ι : Val) (g : Nat) (l : List (Var × Int)) (h : g ∣ gcdT l) :
    (g : Int) * evalT ι (divT g l) = evalT ι l := by
  induction l with
  | nil => simp [divT, evalT]
  | cons hd r ih =>
    obtain ⟨x, a⟩ := hd
    simp only [gcdT] at h
    have ha : (g : Int) ∣ a := Int.ofNat_dvd_left.2 (Nat.dvd_trans h (Nat.gcd_dvd_left _ _))
    have hr : g ∣ gcdT r := Nat.dvd_trans h (Nat.gcd_dvd_right _ _)
    simp only [divT, evalT, Int.mul_add, ih hr, ← Int.mul_assoc, Int.mul_ediv_cancel' ha]

/-- Divide by the gcd of the coefficients and round the constant down. -/
def tighten (l : Lin) : Lin :=
  let g := gcdT l.t
  if g ≤ 1 then l else ⟨l.c / (g : Int), divT g l.t⟩

theorem tighten_sound (ι : Val) (l : Lin) (h : 0 ≤ l.eval ι) : 0 ≤ (tighten l).eval ι := by
  unfold tighten; dsimp only; split
  · exact h
  · rename_i hg
    simp only [eval] at *
    have hT := evalT_divT ι (gcdT l.t) l.t (Nat.dvd_refl _)
    generalize gcdT l.t = g at *
    generalize evalT ι (divT g l.t) = S at *
    have hgpos : (0 : Int) < g := by omega
    have hdm := Int.emod_add_mul_ediv l.c g
    have hr0 := Int.emod_nonneg l.c (by omega : (g : Int) ≠ 0)
    have hr1 := Int.emod_lt_of_pos l.c hgpos
    generalize l.c / (g : Int) = q at *
    generalize l.c % (g : Int) = r at *
    -- 0 ≤ c + g*S = r + g*q + g*S, so q + S > -1.
    refine Int.not_lt.1 fun hlt => ?_
    have : (g : Int) * (q + S) ≤ (g : Int) * (-1) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    rw [Int.mul_add] at this
    omega

end Lin

/-- One step of a certificate. -/
inductive CStep
  | hyp (i : Nat)
  /-- `ki · (step i) + kj · (step j)`. -/
  | comb (i : Nat) (ki : Nat) (j : Nat) (kj : Nat)
  | tight (i : Nat)
  deriving DecidableEq, Repr

abbrev Cert := List CStep

namespace Cert

/-- What one step derives from the hypotheses and the earlier steps. -/
def stepLin (hs : List Lin) (done : List Lin) : CStep → Option Lin
  | .hyp i => hs[i]?
  | .comb i ki j kj => do
    let a ← done[i]?
    let b ← done[j]?
    pure (Lin.add (Lin.smul ki a) (Lin.smul kj b))
  | .tight i => (done[i]?).map Lin.tighten

/-- Run the steps; `none` when one refers to nothing. -/
def run (hs : List Lin) : List Lin → Cert → Option (List Lin)
  | done, [] => some done
  | done, s :: ss => do
    let l ← stepLin hs done s
    run hs (done ++ [l]) ss

def contra (l : Lin) : Bool := l.t.isEmpty && decide (l.c < 0)

/-- The certificate shows that no valuation satisfies every `0 ≤ h`. -/
def check (hs : List Lin) (cert : Cert) : Bool :=
  match run hs [] cert with
  | some ds => ds.any contra
  | none => false

theorem stepLin_sound {ι : Val} {hs done : List Lin} (hh : ∀ h ∈ hs, 0 ≤ h.eval ι)
    (hd : ∀ d ∈ done, 0 ≤ d.eval ι) {s : CStep} {l : Lin} (e : stepLin hs done s = some l) :
    0 ≤ l.eval ι := by
  cases s with
  | hyp i => exact hh l (List.mem_of_getElem? e)
  | comb i ki j kj =>
    simp only [stepLin, Option.bind_eq_bind] at e
    cases ha : done[i]? with
    | none => simp [ha] at e
    | some a =>
      cases hb : done[j]? with
      | none => simp [ha, hb] at e
      | some b =>
        simp [ha, hb] at e; subst e
        have := hd a (List.mem_of_getElem? ha)
        have := hd b (List.mem_of_getElem? hb)
        simp only [Lin.eval_add, Lin.eval_smul]
        have : (0 : Int) ≤ ki := by omega
        have : (0 : Int) ≤ kj := by omega
        have := Int.mul_nonneg (a := (ki : Int)) (b := a.eval ι) (by omega) (by omega)
        have := Int.mul_nonneg (a := (kj : Int)) (b := b.eval ι) (by omega) (by omega)
        omega
  | tight i =>
    simp only [stepLin] at e
    cases ha : done[i]? with
    | none => simp [ha] at e
    | some a =>
      simp [ha] at e; subst e
      exact Lin.tighten_sound ι a (hd a (List.mem_of_getElem? ha))

theorem run_sound {ι : Val} {hs : List Lin} (hh : ∀ h ∈ hs, 0 ≤ h.eval ι) :
    ∀ (cert : Cert) (done ds : List Lin), (∀ d ∈ done, 0 ≤ d.eval ι) →
      run hs done cert = some ds → ∀ d ∈ ds, 0 ≤ d.eval ι := by
  intro cert
  induction cert with
  | nil => intro done ds hd e; simp [run] at e; subst e; exact hd
  | cons s ss ih =>
    intro done ds hd e
    simp only [run, Option.bind_eq_bind] at e
    cases hl : stepLin hs done s with
    | none => simp [hl] at e
    | some l =>
      simp [hl] at e
      refine ih _ _ ?_ e
      intro d hdm
      rcases List.mem_append.1 hdm with h | h
      · exact hd d h
      · simp at h; subst h; exact stepLin_sound hh hd hl

/-- A certificate that checks proves the hypotheses unsatisfiable. -/
theorem check_sound {hs : List Lin} {cert : Cert} (h : check hs cert = true) (ι : Val) :
    ¬ ∀ h ∈ hs, 0 ≤ h.eval ι := by
  intro hh
  unfold check at h
  split at h
  · rename_i ds e
    obtain ⟨l, hl, hc⟩ := List.any_eq_true.1 h
    have := run_sound hh cert [] ds (by simp) e l hl
    simp only [contra, Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hc
    obtain ⟨ht, hc⟩ := hc
    simp only [Lin.eval, ht, Lin.evalT] at this
    omega
  · cases h

end Cert

end NoCompiler.Typed

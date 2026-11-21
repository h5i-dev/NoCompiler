import NoCompiler.Spec
import NoCompiler.Tactic
import NoCompiler.VC.Explore

/-
The registers a path leaves alone, for `vc_auto` (NoCompiler/Auto.lean).

At a path's end the registers are known only through `Matches`: register `r`
of the end state is the denotation of the symbolic value `S.reg r`. A loop
invariant and a return both need `Same s0 s' rs` (every register outside `rs`
holds its entry value). `sameOk rs S` is a closed check on the symbolic state,
evaluated by the kernel: each register outside `rs` still holds its own
variable. Then `Same.of_den` gives `Same` at the end from `Same` at the cut
point, with no step per register.
-/
namespace NoCompiler.VC.M

/-- Register `n` is in `rs`, or `x0`, or still holds its own variable. -/
def regOk (rs : List Nat) (n : Nat) (x : Sym) : Bool :=
  n == 0 || rs.contains n ||
    match x with
    | .var m => m == n
    | _ => false

/-- `regOk` along the register list from index `n`: one pass (an indexed
    lookup per register made the kernel's check quadratic, 64 ms measured). -/
def sameGo (rs : List Nat) : Nat → List Sym → Bool
  | _, [] => true
  | n, x :: xs => regOk rs n x && sameGo rs (n + 1) xs

/-- Every register outside `rs` (and not `x0`) still holds its own variable. -/
def sameOk (rs : List Nat) (S : SState) : Bool := S.regs.length == 32 && sameGo rs 0 S.regs

theorem sameGo_spec {rs : List Nat} : ∀ {n : Nat} {l : List Sym}, sameGo rs n l = true →
    ∀ i (h : i < l.length), regOk rs (n + i) l[i] = true
  | _, [], _, i, h => absurd h (by simp)
  | n, x :: xs, hg, i, h => by
    simp only [sameGo, Bool.and_eq_true] at hg
    cases i with
    | zero => simpa using hg.1
    | succ i =>
      have := sameGo_spec hg.2 i (by simp at h; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem sameOk_spec {rs : List Nat} {S : SState} (hc : sameOk rs S = true) (n : Nat) (hn : n < 32) :
    regOk rs n (S.regs.getD n (.const 0)) = true := by
  simp only [sameOk, Bool.and_eq_true, beq_iff_eq] at hc
  have h := sameGo_spec hc.2 n (by omega)
  simp only [Nat.zero_add] at h
  have e : S.regs.getD n (.const 0) = S.regs[n]'(by omega) := by
    simp [List.getD, List.getElem?_eq_getElem (show n < S.regs.length by omega)]
  rw [e]; exact h

theorem Same.of_den {s0 u s' : State} {rs : List Nat} {S : SState} {μ : Word → Byte}
    (hS : Same s0 u rs) (hc : sameOk rs S = true)
    (hreg : ∀ r : Reg, s'.reg r = (S.reg r).den (ρOf u) μ) : Same s0 s' rs := by
  intro r hr
  rw [hreg r]
  have h := sameOk_spec hc r.val r.isLt
  unfold regOk at h
  by_cases h0 : r.val = 0
  · have : r = 0 := Fin.ext h0
    subst this
    simp [SState.reg, Sym.den]
  · have hc' : (List.contains rs r.val) = false := by
      cases hh : rs.contains r.val
      · rfl
      · exact absurd (List.contains_iff_mem.1 hh) hr
    have h1 : (r.val == 0) = false := by simp [h0]
    rw [h1, hc', Bool.false_or, Bool.false_or] at h
    have hr' : S.reg r = S.regs.getD r.val (.const 0) := by simp [SState.reg, h0]
    rw [hr']
    split at h
    · rename_i m hm
      rw [hm]
      have hmn : m = r.val := by simpa using h
      show ρOf u m = _
      rw [hmn]
      simp only [ρOf, r.isLt, dite_true]
      exact hS r hr
    · exact absurd h (by simp)

/-! ### Calls

A path that reaches a callee's entry stops there, as at a cut point, and what
is due is the rest of the run from there (`Reach`), which the callee's
`VerifiedImg` theorem gives (`VerifiedImg.call`). The other ends are due `Q`. -/

/-- At a callee's entry the rest of the run, elsewhere `Q`. -/
def CallQ (c : Code) (P : Perm) (D : Dom) (Q : State → Prop) (ces : List Word) (s : State) : Prop :=
  if s.pc ∈ ces then Reach c P D Q s else Q s

theorem Reach.of_exploreCalls {c : Code} {P : Perm} {D : Dom} {Q : State → Prop} {facts : List Fact}
    {cuts ces : List Word} {fuel k : Nat} {p : Word} {s : State} {fetch : Nat → List (BitVec 32)}
    (hb : 4 * c.words.size < 2 ^ 64) (hfe : ∀ k, fetch k = c.words.toList.drop k)
    (hk : p = c.base + BitVec.ofNat 64 (4 * k)) (hpc : s.pc = p) (hx : s.exit = none)
    (hf : ∀ f ∈ facts, f.den (ρOf s) P)
    (hvc : exploreVC (ρOf s) s.mem P (fun s' => s'.trace = s.trace → CallQ c P D Q ces s') facts c D
      (cuts ++ ces) fuel k p fetch) :
    Reach c P D Q s :=
  Reach.trans (Reach.of_exploreAtT hb hfe hk hpc hx hf hvc) fun s' h => by
    unfold CallQ at h
    split at h
    · exact h
    · exact .done h

theorem CallQ.call {c : Code} {P : Perm} {D : Dom} {Q : State → Prop} {ces : List Word} {s : State}
    (h : s.pc ∈ ces) (hr : Reach c P D Q s) : CallQ c P D Q ces s := by
  simp only [CallQ, h, ite_true]; exact hr

theorem CallQ.other {c : Code} {P : Perm} {D : Dom} {Q : State → Prop} {ces : List Word} {s : State}
    (h : s.pc ∉ ces) (hq : Q s) : CallQ c P D Q ces s := by
  simp only [CallQ, h, ite_false]; exact hq

/-- A return end: the return address is the entry's `ra`, which is outside the
    function, so not a callee's entry. -/
theorem CallQ.ret {c : Code} {P : Perm} {D Dc : Dom} {Q : State → Prop} {ces : List Word}
    {entry : Word} {s0 s' : State} {X : Word} {τ : List Event} (he : Entry D entry s0)
    (hcalls : ces.all (fun x => decide (D.mem x)) = true) (hX : X = s0.reg 1)
    (hq : s'.trace = τ → Q (s'.setPc (s0.reg 1))) :
    NoCompiler.aligned (X &&& ~~~1) 4 ∧
      ((s'.setPc (X &&& ~~~1)).trace = τ → CallQ c P Dc Q ces (s'.setPc (X &&& ~~~1))) := by
  have hm : s0.reg 1 &&& ~~~1 = s0.reg 1 := and_not_one_of_aligned he.retAligned
  subst hX
  rw [hm]
  refine ⟨he.retAligned, fun ht => CallQ.other (fun hm' => he.ret ?_) (hq (by simpa using ht))⟩
  exact of_decide_eq_true (List.all_eq_true.1 hcalls _ hm')

/-! ### Opening a path's end without unfolding the goal

`PEnd.Next` on a closed end is a large literal (the symbolic state); `simp
only [PEnd.Next]` and a pattern on `Matches` both traverse it. These lemmas
state the same with the hypotheses curried, so `refine` opens an end by
unification alone. -/

theorem PEnd.cut_intro {ρ : Nat → Word} {μ : Word → Byte} {Q : State → Prop} {S : SState} {cs : List Cond}
    (h : (∀ x ∈ cs, x.den ρ μ) → ∀ s' : State, s'.pc = S.pc → (∀ r : Reg, s'.reg r = (S.reg r).den ρ μ) →
      s'.mem = S.mem.den ρ μ → s'.exit = none → Q s') : PEnd.Next ρ μ Q (.cut S cs) :=
  fun hc s' hm hx => h hc s' hm.2.1 hm.2.2.1 hm.2.2.2 hx

theorem PEnd.ret_intro {ρ : Nat → Word} {μ : Word → Byte} {Q : State → Prop} {S : SState} {cs : List Cond}
    (h : (∀ x ∈ cs, x.den ρ μ) → ∀ s' : State, s'.pc = S.pc → (∀ r : Reg, s'.reg r = (S.reg r).den ρ μ) →
      s'.mem = S.mem.den ρ μ → s'.exit = none →
      NoCompiler.aligned ((S.reg 1).den ρ μ &&& ~~~1) 4 ∧ Q (s'.setPc ((S.reg 1).den ρ μ &&& ~~~1))) :
    PEnd.Next ρ μ Q (.ret S cs) :=
  fun hc s' hm hx => h hc s' hm.2.1 hm.2.2.1 hm.2.2.2 hx

/-! ### Alignment of computed addresses

An address computed from aligned pieces (a register aligned by a precondition or by
sp's alignment, a shifted index, a constant) is aligned: `vc_align` takes a sum apart
and closes the pieces. -/

theorem aligned_add' {a b : Word} {n : Nat} (hn : 2 ^ 64 % n = 0) (ha : NoCompiler.aligned a n)
    (hb : NoCompiler.aligned b n) : NoCompiler.aligned (a + b) n := by
  unfold NoCompiler.aligned at *
  rw [BitVec.toNat_add]
  have h1 : n ∣ a.toNat + b.toNat := Nat.dvd_add (Nat.dvd_of_mod_eq_zero ha) (Nat.dvd_of_mod_eq_zero hb)
  exact Nat.mod_eq_zero_of_dvd ((Nat.dvd_mod_iff (Nat.dvd_of_mod_eq_zero hn)).2 h1)

theorem aligned_shl' {a : Word} {k n : Nat} (hn : 2 ^ 64 % n = 0) (hk : 2 ^ k % n = 0) :
    NoCompiler.aligned (a <<< k) n := by
  unfold NoCompiler.aligned
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have h1 : n ∣ a.toNat * 2 ^ k := Nat.dvd_mul_left_of_dvd (Nat.dvd_of_mod_eq_zero hk) _
  exact Nat.mod_eq_zero_of_dvd ((Nat.dvd_mod_iff (Nat.dvd_of_mod_eq_zero hn)).2 h1)

theorem aligned_weaken {a : Word} {m n : Nat} (h : NoCompiler.aligned a m) (hd : m % n = 0) :
    NoCompiler.aligned a n := by
  unfold NoCompiler.aligned at *
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero hd) (Nat.dvd_of_mod_eq_zero h))

open Lean Elab Tactic Meta in
/-- An alignment goal over a sum of aligned pieces, taken apart by the shape of the address:
    a sum by `aligned_add'`, a shift by `aligned_shl'`, anything else from a hypothesis (or one
    of a larger alignment) or by `decide`. -/
partial def vcAlign (g : MVarId) : TacticM Unit := g.withContext do
  let t ← whnfR (← instantiateMVars (← g.getType))
  let some (a, _) := (if t.isAppOfArity ``NoCompiler.aligned 2 then some (t.getArg! 0, t.getArg! 1) else none)
    | throwError "vc_align: not an alignment goal"
  let a := a.consumeMData
  let tryTac (tac : TSyntax `tactic) : TacticM (Option (List MVarId)) := do
    let st ← saveState
    try return some (← evalTacticAt tac g)
    catch _ => st.restore; return none
  if a.isAppOfArity ``HAdd.hAdd 6 then
    let some gs ← tryTac (← `(tactic| refine NoCompiler.VC.M.aligned_add' (by decide) ?_ ?_))
      | throwError "vc_align: sum"
    for g' in gs do vcAlign g'
    return
  if a.isAppOfArity ``HShiftLeft.hShiftLeft 6 then
    if let some [] ← tryTac (← `(tactic| exact NoCompiler.VC.M.aligned_shl' (by decide) (by decide))) then
      return
  for tac in [← `(tactic| (decide; done)), ← `(tactic| assumption),
      ← `(tactic| (refine NoCompiler.VC.M.aligned_weaken (m := 8) ?_ (by decide); assumption)),
      ← `(tactic| (refine NoCompiler.VC.M.aligned_weaken (m := 16) ?_ (by decide); assumption))] do
    if let some [] ← tryTac tac then return
  throwError "vc_align: cannot show{indentExpr t}"

elab "vc_align" : tactic => do vcAlign (← Lean.Elab.Tactic.getMainGoal)

end NoCompiler.VC.M

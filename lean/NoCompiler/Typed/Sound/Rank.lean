import NoCompiler.Typed.Sound.Inv

/-
Termination (the proof's Theorem C) by a ranking function instead of the outermost-loop
argument: every edge the checker accepts strictly decreases, lexicographically, the list
of one component per loop (by increasing head) — `(2,0)` before the loop, `(1, μ)` inside
it with μ its measure, `(0,0)` after it — followed by the distance to the end.
-/
namespace NoCompiler.Typed

def PLt (a b : Nat × Nat) : Prop := Prod.Lex (· < ·) (· < ·) a b

theorem PLt_wf : WellFounded PLt := (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

/-- Lexicographic order on lists of the same length. -/
inductive LexN : List (Nat × Nat) → List (Nat × Nat) → Prop
  | head {a b : Nat × Nat} {as bs : List (Nat × Nat)} : PLt a b → as.length = bs.length →
      LexN (a :: as) (b :: bs)
  | tail (a : Nat × Nat) {as bs : List (Nat × Nat)} : LexN as bs → LexN (a :: as) (a :: bs)

theorem LexN.length {as bs : List (Nat × Nat)} (h : LexN as bs) : as.length = bs.length := by
  induction h with
  | head _ hl => simp [hl]
  | tail _ _ ih => simp [ih]

theorem LexN.acc_cons : ∀ a, Acc PLt a → ∀ as, Acc LexN as →
    (∀ bs : List (Nat × Nat), bs.length = as.length → Acc LexN bs) → Acc LexN (a :: as) := by
  intro a ha
  induction ha with
  | intro a _ iha =>
    intro as has
    induction has with
    | intro as _ ihas =>
      intro hall
      constructor
      intro y hy
      cases hy with
      | head hplt hlen => exact iha _ hplt _ (hall _ hlen) (fun cs hc => hall cs (hc.trans hlen))
      | tail _ hlex => exact ihas _ hlex (fun cs hc => hall cs (hc.trans hlex.length))

theorem LexN.wf : WellFounded LexN := by
  constructor
  suffices h : ∀ n, ∀ l : List (Nat × Nat), l.length = n → Acc LexN l from fun l => h _ l rfl
  intro n
  induction n with
  | zero =>
    intro l hl
    match l, hl with
    | [], _ => exact ⟨_, fun y h => by cases h⟩
  | succ n ih =>
    intro l hl
    match l, hl with
    | a :: as, hl =>
      have hl' : as.length = n := by simpa using hl
      exact LexN.acc_cons a (PLt_wf.apply a) as (ih as hl') (fun bs hb => ih bs (hb.trans hl'))

def PLe (a b : Nat × Nat) : Prop := PLt a b ∨ a = b

/-- Pointwise not larger, and the last component strictly smaller. -/
theorem lexN_of_le {α : Type} (g h : α → Nat × Nat) : ∀ (Ls : List α) {x y : Nat × Nat},
    (∀ L ∈ Ls, PLe (g L) (h L)) → PLt x y → LexN (Ls.map g ++ [x]) (Ls.map h ++ [y])
  | [], _, _, _, hxy => .head hxy rfl
  | L :: Ls, x, y, hle, hxy => by
    simp only [List.map_cons, List.cons_append]
    rcases hle L (by simp) with hlt | heq
    · exact .head hlt (by simp)
    · rw [heq]; exact .tail _ (lexN_of_le g h Ls (fun K hK => hle K (by simp [hK])) hxy)

/-- Equal before some component, strictly smaller there. -/
theorem lexN_at {α : Type} (g h : α → Nat × Nat) (x y : Nat × Nat) (post : List α) (L : α) :
    ∀ (pre : List α), (∀ K ∈ pre, g K = h K) → PLt (g L) (h L) →
      LexN ((pre ++ L :: post).map g ++ [x]) ((pre ++ L :: post).map h ++ [y])
  | [], _, hlt => by simpa using LexN.head hlt (by simp)
  | K :: pre, heq, hlt => by
    simp only [List.cons_append, List.map_cons]
    rw [heq K (by simp)]
    exact .tail _ (lexN_at g h x y post L pre (fun K' hK' => heq K' (by simp [hK'])) hlt)

namespace Fn

/-- The component of loop `L` at instruction `k`. -/
def comp (L : Loop) (k : Nat) (ι : Val) : Nat × Nat :=
  if k < L.head then (2, 0) else if k ≤ L.last then (1, (L.meas.eval ι + 1).toNat) else (0, 0)

def rank (f : Fn) (k : Nat) (ι : Val) : List (Nat × Nat) :=
  f.loops.map (fun L => comp L k ι) ++ [(0, f.size - k)]

/-- A forward edge: no component grows (measures of loops containing both ends are
    unchanged), and the distance to the end shrinks. -/
theorem rank_fwd (f : Fn) {k k' : Nat} {ι ι' : Val} (hk : k < k') (hk' : k' < f.size)
    (hag : ∀ L ∈ f.loops, Fn.inside L k = true → Fn.inside L k' = true →
      ∀ x ∈ L.meas.vars, ι' x = ι x) : LexN (f.rank k' ι') (f.rank k ι) := by
  unfold rank
  refine lexN_of_le _ _ _ (fun L hL => ?_) (Prod.Lex.right _ (by omega))
  unfold comp PLe PLt
  by_cases h1 : k' < L.head
  · rw [if_pos h1, if_pos (by omega)]; exact .inr rfl
  · rw [if_neg h1]
    by_cases h2 : k < L.head
    · rw [if_pos h2]; split
      · exact .inl (Prod.Lex.left _ _ (by omega))
      · exact .inl (Prod.Lex.left _ _ (by omega))
    · rw [if_neg h2]
      by_cases h3 : k' ≤ L.last
      · rw [if_pos h3, if_pos (by omega)]
        have := hag L hL (by simp only [inside, Bool.and_eq_true, decide_eq_true_eq]; omega)
          (by simp only [inside, Bool.and_eq_true, decide_eq_true_eq]; omega)
        rw [IExpr.eval_congr L.meas (fun x hx => (this x hx).symm)]
        exact .inr rfl
      · rw [if_neg h3]; split
        · exact .inl (Prod.Lex.left _ _ (by omega))
        · exact .inr rfl

/-- Loop intervals nest (what `structOk` checks). -/
def Nested (f : Fn) : Prop :=
  ∀ K ∈ f.loops, ∀ L ∈ f.loops, K.head = L.head ∨ L.last < K.head ∨ K.last < L.head ∨
    (K.head < L.head ∧ L.last ≤ K.last) ∨ (L.head < K.head ∧ K.last ≤ L.last)

/-- A backward edge to the head of `L` from inside it: the components of the loops with
    smaller heads (enclosing or finished) are unchanged, and `L`'s measure decreases. -/
theorem rank_back (f : Fn) {k k' : Nat} {ι ι' : Val} {L : Loop} (hL : L ∈ f.loops)
    (hh : L.head = k') (hk : k' ≤ k) (hkl : k ≤ L.last)
    (hsorted : (f.loops.map (·.head)).Pairwise (· < ·)) (hnest : f.Nested)
    (hag : ∀ K ∈ f.loops, K.head ≠ k' → Fn.inside K k = true → Fn.inside K k' = true →
      ∀ x ∈ K.meas.vars, ι' x = ι x)
    (h0 : 0 ≤ L.meas.eval ι) (hlt : L.meas.eval ι' < L.meas.eval ι) :
    LexN (f.rank k' ι') (f.rank k ι) := by
  obtain ⟨pre, post, he⟩ := List.append_of_mem hL
  unfold rank
  rw [he]
  refine lexN_at _ _ _ _ post L pre (fun K hK => ?_) ?_
  · have hKL : K.head < L.head := by
      rw [he] at hsorted
      simp only [List.map_append, List.map_cons, List.pairwise_append] at hsorted
      exact hsorted.2.2 K.head (List.mem_map.2 ⟨K, hK, rfl⟩) L.head (by simp)
    have hK' : K ∈ f.loops := by rw [he]; simp [hK]
    unfold comp
    rcases hnest K hK' L hL with e | e | e | ⟨-, e⟩ | ⟨e, -⟩
    · omega
    · omega
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]
      have := hag K hK' (by omega) (by simp only [inside, Bool.and_eq_true, decide_eq_true_eq]; omega)
        (by simp only [inside, Bool.and_eq_true, decide_eq_true_eq]; omega)
      rw [IExpr.eval_congr K.meas (fun x hx => (this x hx).symm)]
    · omega
  · unfold comp PLt
    rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]
    exact Prod.Lex.right _ (by omega)

end Fn

end NoCompiler.Typed

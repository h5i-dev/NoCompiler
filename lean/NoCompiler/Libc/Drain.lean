import NoCompiler.Libc.Shape

/-!
# Libc library: the drain shape (port of LPS `theories/Common/DrainSim.v`)

Ported from LPS (rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs, PBC;
prior-art/lps/LICENSE; commit d3f3a701), `theories/Common/DrainSim.v`:
* lines 60-78: the abstract byte-stream fold `procs` and `procs_app`;
* lines 283-400 and 844-966: the per-binary obligation (a loop-head predicate `LH` whose every state
  runs to a read whose continuations reach a new loop head, or the end) and the theorem turning it into
  the whole run (`drain_obs_iff`, via `dinv` / `star_dinv`).

The shape: a program that reads all of its input in blocks, folds the bytes through
`f : A → Byte → Option A` (`none`: stop, e.g. exit with an error), and at the end emits `out a`. slen
is one (`f n _ = some (n + 1)`, `out n` = the decimal digits of `n` and a newline).

What changed in the port: LPS states the end as a trace equivalence over star runs and proves the
no-error and omni facts separately (`drain_no_error`, `drain_omni_*`). Here the end is a `PReachK`
claim, which already says every run gets there without a fault, so those are not separate theorems.
LPS's loop head runs to a read ecall whose EOF and block continuations are case-split by the
theorem; here the obligation is one `PReachK` per round (from a loop head to the next loop head or the
end), the read stepped inside it by the syscall's `_cases` lemma (Linux/SysSteps.lean), and the
termination measure is an argument (for a file behind fd 0, `fileLeft 0`, Examples/Libc/Main.lean)
where LPS's stream semantics needs none.
-/

namespace NoCompiler.Libc
open NoCompiler NoCompiler.Linux

section Proc
variable {A : Type} (f : A → Byte → Option A)

/-- The bytes `bs` folded through `f` from `a` (LPS `procs`, DrainSim.v:66). -/
def procs (a : A) : List Byte → Option A
  | [] => some a
  | b :: rest => match f a b with
    | some a' => procs a' rest
    | none => none

@[simp] theorem procs_nil (a : A) : procs f a [] = some a := rfl

/-- LPS `procs_app` (DrainSim.v:72). -/
theorem procs_app (bs1 bs2 : List Byte) (a : A) :
    procs f a (bs1 ++ bs2) = match procs f a bs1 with
      | some a' => procs f a' bs2
      | none => none := by
  induction bs1 generalizing a with
  | nil => rfl
  | cons b bs1 ih =>
    simp only [List.cons_append, procs]
    cases f a b with
    | some a' => exact ih a'
    | none => rfl

theorem procs_append_of {a a1 : A} {bs1 : List Byte} (h : procs f a bs1 = some a1) (bs2 : List Byte) :
    procs f a (bs1 ++ bs2) = procs f a1 bs2 := by
  rw [procs_app, h]

end Proc

/-- The drain loop (LPS `drain_obs_iff`, DrainSim.v:966, in `PReachK` form). `LH a ds y`: a loop head,
    with `a` the fold of the bytes `ds` consumed so far. If every round from a loop head either consumes
    more bytes `ds'`, the fold going on, and gets back to a loop head with a smaller measure, or ends
    (`Fin a ds`), then from a loop head with nothing consumed every run ends in some `Fin a ds` with `a`
    the fold of all the bytes `ds` consumed. -/
theorem drain {A : Type} {c : Code} {D : Dom} (f : A → Byte → Option A) (a0 : A)
    (LH : A → List Byte → State × Kern → Prop) (Fin : A → List Byte → State × Kern → Prop)
    (μ : State × Kern → Nat)
    (hstep : ∀ a ds y, procs f a0 ds = some a → LH a ds y →
      PReachK c D (fun y' => Fin a ds y' ∨
        ∃ ds' a', procs f a ds' = some a' ∧ LH a' (ds ++ ds') y' ∧ μ y' < μ y) y) :
    ∀ y, LH a0 [] y → PReachK c D (fun y' => ∃ ds a, procs f a0 ds = some a ∧ Fin a ds y') y := by
  intro y hy
  refine PReachK.loop (I := fun x => ∃ a ds, procs f a0 ds = some a ∧ LH a ds x) μ ?_ y ⟨a0, [], rfl, hy⟩
  rintro x ⟨a, ds, hp, hl⟩
  refine PReachK.bind (fun _ h => h) ?_ (hstep a ds x hp hl)
  rintro y' (hf | ⟨ds', a', hp', hl', hlt⟩)
  · exact .done (.inl ⟨ds, a, hp, hf⟩)
  · exact .done (.inr ⟨⟨a', ds ++ ds', by rw [procs_append_of f hp]; exact hp', hl'⟩, hlt⟩)

end NoCompiler.Libc

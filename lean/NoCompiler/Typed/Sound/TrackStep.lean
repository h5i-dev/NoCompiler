import NoCompiler.Typed.Track
import NoCompiler.Typed.Sound.Values

/-
The step checker of the byte-content tracker (docs/typed/value-tracker.md): a frame per point
(the destination cursor register, the bytes stored past it, the cells of tracked registers), an
abstract step per instruction, and side conditions as entailments on the point's recorded type.
-/
namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed NoCompiler.Typed.Bytes

/-- A point's frame: the copied count is `(cur − d) + δ`; `cells` for the tracked registers. -/
structure Frame where
  cur : Reg
  δ : Nat
  cells : List (Reg × Cells)
  deriving DecidableEq, Repr

def Frame.get (fr : Frame) (r : Reg) : Cells := (fr.cells.lookup r).getD []

/-- The copied count of a frame in a state. -/
def Frame.count (fr : Frame) (d : Word) (s : State) : Nat := (s.reg fr.cur - d).toNat + fr.δ

/-- The frame's meaning: memory is the copy so far, the tracked registers hold their cells. -/
def Frame.ok (m0 : Word → Byte) (d srcB : Word) (fr : Frame) (s : State) : Prop :=
  Copied m0 s.mem d srcB (fr.count d s) ∧
  ∀ r : Reg, Cells.ok m0 srcB (fr.count d s) (s.reg r) (fr.get r)

/-- `a` says no more than `b` (each cell unknown or equal). -/
def Cells.le (a b : Cells) : Bool :=
  (List.range 8).all fun i => a.getD i .unk == .unk || a.getD i .unk == b.getD i .unk

theorem Cells.ok_of_le {m0 srcB c w} {a b : Cells} (h : a.le b = true) (hb : Cells.ok m0 srcB c w b) :
    Cells.ok m0 srcB c w a := by
  intro i hi
  have := List.all_eq_true.1 h i (List.mem_range.2 hi)
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with e | e
  · rw [e]; trivial
  · rw [e]; exact hb i hi

/-- The abstract machine state the step computes: cursor, δ, and the cells of every register. -/
structure AState where
  cur : Reg
  δ : Nat
  cells : Reg → Cells

def Frame.toA (fr : Frame) : AState := ⟨fr.cur, fr.δ, fr.get⟩

def AState.set (A : AState) (rd : Reg) (cs : Cells) : AState :=
  { A with cells := fun r => if r = rd then cs else A.cells r }

/-- The frame `fr'` at the next point is implied by the computed state `A`. -/
def Frame.leA (fr' : Frame) (A : AState) : Bool :=
  fr'.cur == A.cur && fr'.δ == A.δ && fr'.cells.all fun p => p.2.le (A.cells p.1)

end NoCompiler.Typed.Track

namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed NoCompiler.Typed.Bytes

/-- The abstract state's meaning: the copied count `(cur − d) + δ` is at most `n`, memory is the
    copy so far, and every register holds its cells. -/
def AState.ok (m0 : Word → Byte) (d srcB : Word) (n : Nat) (A : AState) (s : State) : Prop :=
  (s.reg A.cur - d).toNat + A.δ ≤ n ∧
  Copied m0 s.mem d srcB ((s.reg A.cur - d).toNat + A.δ) ∧
  ∀ r : Reg, Cells.ok m0 srcB ((s.reg A.cur - d).toNat + A.δ) (s.reg r) (A.cells r)

theorem reg_setReg_setPc (s : State) {rd : Reg} (v : Word) (p : Word) (r : Reg) (hrd : rd ≠ 0) :
    ((s.setReg rd v).setPc p).reg r = if r = rd then v else s.reg r := by
  simp only [State.setPc, State.setReg, hrd, if_false, State.reg, State.upd]
  split
  · rename_i h; subst h; simp
    intro h'; exact absurd h'.symm hrd
  · rfl

/-- A register write that misses the cursor: the copy is unchanged, the written register gets
    its new cells. -/
theorem AState.ok_set {m0 d srcB n} {A : AState} {s : State} (h : A.ok m0 d srcB n s) {rd : Reg}
    (hrd : rd ≠ A.cur) (hrd0 : rd ≠ 0) {v : Word} {cs : Cells}
    (hv : Cells.ok m0 srcB ((s.reg A.cur - d).toNat + A.δ) v cs) (p : Word) :
    (A.set rd cs).ok m0 d srcB n ((s.setReg rd v).setPc p) := by
  obtain ⟨hn, hc, hr⟩ := h
  have hcur : ((s.setReg rd v).setPc p).reg A.cur = s.reg A.cur := by
    rw [reg_setReg_setPc s v p _ hrd0, if_neg (Ne.symm hrd)]
  have hmem : ((s.setReg rd v).setPc p).mem = s.mem := by
    simp [State.setPc, State.setReg]; split <;> rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [AState.set]; rw [hcur]; exact hn
  · simp only [AState.set]; rw [hcur, hmem]; exact hc
  · intro r
    simp only [AState.set]
    rw [hcur, reg_setReg_setPc s v p r hrd0]
    split
    · exact hv
    · exact hr r

end NoCompiler.Typed.Track

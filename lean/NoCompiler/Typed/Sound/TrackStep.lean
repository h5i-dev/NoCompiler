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

namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed NoCompiler.Typed.Bytes

/-- The cells of a register-only instruction's result (shifts by whole bytes, `or`, moves;
    anything else unknown). -/
def regCells (A : AState) : Instr → Cells
  | .shift .slli _ rs sh => if sh.toNat % 8 = 0 then (A.cells rs).shl (sh.toNat / 8) else []
  | .shift .srli _ rs sh => if sh.toNat % 8 = 0 then (A.cells rs).shr (sh.toNat / 8) else []
  | .shiftw .srliw _ rs sh =>
    if sh.toNat % 8 = 0 ∧ 1 ≤ sh.toNat / 8 ∧ sh.toNat / 8 ≤ 3 then (A.cells rs).srliw (sh.toNat / 8) else []
  | .rop .or _ a b => (A.cells a).or (A.cells b)
  | .iop .addi _ rs imm => if imm = 0 then A.cells rs else []
  | _ => []

/-- A register-only instruction (it writes `rd`, not the cursor, and no memory): its abstract
    step. -/
def regStep (A : AState) (i : Instr) : Option AState :=
  match writesReg i with
  | some rd => if rd = 0 then some A else if rd = A.cur then none else some (A.set rd (regCells A i))
  | none => none

theorem regCells_ok {m0 d srcB n} {A : AState} {s : State} (h : A.ok m0 d srcB n s) (i : Instr)
    {rd : Reg} (hw : writesReg i = some rd) {s' : State} (hx : exec i s = some s') :
    ∃ v, s' = (s.setReg rd v).setPc (s.pc + 4) ∧
      Cells.ok m0 srcB ((s.reg A.cur - d).toNat + A.δ) v (regCells A i) := by
  have hr := h.2.2
  have unk : ∀ v : Word, Cells.ok m0 srcB ((s.reg A.cur - d).toNat + A.δ) v [] := by
    intro v j hj; simp [Cell.ok]
  cases i <;> simp only [writesReg, Option.some.injEq, reduceCtorEq] at hw <;> subst hw <;>
    simp only [exec, Option.some.injEq] at hx <;> subst hx
  all_goals refine ⟨_, rfl, ?_⟩
  case iop op rd rs imm =>
    cases op <;> simp only [regCells] <;> try exact unk _
    split
    · rename_i h0; subst h0; simp only [evalI]
      rw [show BitVec.signExtend 64 (0 : BitVec 12) = 0 from by decide,
        show s.reg rs + (0 : Word) = s.reg rs from by simp]; exact hr rs
    · exact unk _
  case shift op rd rs sh =>
    cases op <;> simp only [regCells] <;> try exact unk _
    · split
      · rename_i h8; simp only [evalSh]
        have e : sh.toNat = 8 * (sh.toNat / 8) := by omega
        rw [e]; rw [show 8 * (sh.toNat / 8) / 8 = sh.toNat / 8 by omega]; exact Cells.shl_ok _ (hr rs)
      · exact unk _
    · split
      · rename_i h8; simp only [evalSh]
        have e : sh.toNat = 8 * (sh.toNat / 8) := by omega
        rw [e]; rw [show 8 * (sh.toNat / 8) / 8 = sh.toNat / 8 by omega]; exact Cells.shr_ok _ (hr rs)
      · exact unk _
  case shiftw op rd rs sh =>
    cases op <;> simp only [regCells] <;> try exact unk _
    split
    · rename_i h8; simp only [evalShW]
      have e : sh.toNat = 8 * (sh.toNat / 8) := by omega
      rw [e]; rw [show 8 * (sh.toNat / 8) / 8 = sh.toNat / 8 by omega]
      exact Cells.srliw_ok (by omega) (by omega) (hr rs)
    · exact unk _
  case rop op rd a b =>
    cases op <;> simp only [regCells] <;> try exact unk _
    simp only [evalR]; exact Cells.or_ok (hr a) (hr b)
  all_goals simp only [regCells]; exact unk _

theorem AState.ok_setPc {m0 d srcB n} {A : AState} {s : State} (h : A.ok m0 d srcB n s) (p : Word) :
    A.ok m0 d srcB n (s.setPc p) := h

/-- Soundness of the register-only step. -/
theorem regStep_ok {m0 d srcB n} {A A' : AState} {s s' : State} (h : A.ok m0 d srcB n s)
    {i : Instr} (hs : regStep A i = some A') (hx : exec i s = some s') : A'.ok m0 d srcB n s' := by
  unfold regStep at hs
  split at hs
  · rename_i rd hw
    obtain ⟨v, rfl, hv⟩ := regCells_ok h i hw hx
    split at hs
    · rename_i h0
      cases hs; subst h0
      simp only [State.setReg, if_true]
      exact AState.ok_setPc h _
    · split at hs
      · cases hs
      · cases hs
        exact AState.ok_set h (by assumption) (by assumption) hv _
  · cases hs

end NoCompiler.Typed.Track

namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed NoCompiler.Typed.Bytes

/-- Advancing the cursor by `imm ≤ δ` into `rd` keeps the copied count. -/
theorem AState.ok_advance {m0 d srcB n} {A : AState} {s : State} (h : A.ok m0 d srcB n s)
    (hn : n < 2 ^ 64) {rd : Reg} (hrd0 : rd ≠ 0) {imm : Nat} (himm : imm ≤ A.δ) (p : Word) :
    ({ cur := rd, δ := A.δ - imm, cells := (A.set rd []).cells } : AState).ok m0 d srcB n
      ((s.setReg rd (s.reg A.cur + BitVec.ofNat 64 imm)).setPc p) := by
  obtain ⟨hcn, hc, hr⟩ := h
  have hrd : ((s.setReg rd (s.reg A.cur + BitVec.ofNat 64 imm)).setPc p).reg rd = s.reg A.cur + BitVec.ofNat 64 imm := by
    rw [reg_setReg_setPc s _ p rd hrd0, if_pos rfl]
  have hmem : ((s.setReg rd (s.reg A.cur + BitVec.ofNat 64 imm)).setPc p).mem = s.mem := by
    simp [State.setPc, State.setReg]; split <;> rfl
  have hcnt : (s.reg A.cur + BitVec.ofNat 64 imm - d).toNat + (A.δ - imm) = (s.reg A.cur - d).toNat + A.δ := by
    have : (s.reg A.cur + BitVec.ofNat 64 imm - d).toNat = (s.reg A.cur - d).toNat + imm := by
      have e : s.reg A.cur + BitVec.ofNat 64 imm - d = (s.reg A.cur - d) + BitVec.ofNat 64 imm := by bv_omega
      rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
      have := (s.reg A.cur - d).isLt
      rw [Nat.mod_eq_of_lt (a := imm) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  refine ⟨?_, ?_, ?_⟩
  · simp only; rw [hrd, hcnt]; exact hcn
  · simp only; rw [hrd, hcnt, hmem]; exact hc
  · intro r
    simp only [AState.set]
    rw [hrd, hcnt, reg_setReg_setPc s _ p r hrd0]
    split
    · intro j hj; simp [Cell.ok]
    · exact hr r

/-- Switching the cursor to a register holding `cursor + j` (`j ≤ δ`) keeps the copied count. -/
theorem AState.ok_switch {m0 d srcB n} {A : AState} {s : State} (h : A.ok m0 d srcB n s)
    (hn : n < 2 ^ 64) {r : Reg} {j : Nat} (hj : j ≤ A.δ) (hr : s.reg r = s.reg A.cur + BitVec.ofNat 64 j) :
    ({ A with cur := r, δ := A.δ - j } : AState).ok m0 d srcB n s := by
  obtain ⟨hcn, hc, hrr⟩ := h
  have hcnt : (s.reg r - d).toNat + (A.δ - j) = (s.reg A.cur - d).toNat + A.δ := by
    have : (s.reg A.cur + BitVec.ofNat 64 j - d).toNat = (s.reg A.cur - d).toNat + j := by
      have e : s.reg A.cur + BitVec.ofNat 64 j - d = (s.reg A.cur - d) + BitVec.ofNat 64 j := by bv_omega
      rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
      have := (s.reg A.cur - d).isLt
      rw [Nat.mod_eq_of_lt (a := j) (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hr]; omega
  refine ⟨?_, ?_, ?_⟩
  · simp only; rw [hcnt]; exact hcn
  · simp only; rw [hcnt]; exact hc
  · intro r'; simp only; rw [hcnt]; exact hrr r'

/-- A load of the next source bytes into `rd` (not the cursor). -/
theorem AState.ok_load {m0 d srcB n} {A : AState} {s : State} (h : A.ok m0 d srcB n s)
    (hd : Disj d srcB n) {op : LdOp} (hop : op ≠ .lh ∧ op ≠ .lhu) {rd : Reg} (hrd : rd ≠ A.cur)
    (hrd0 : rd ≠ 0) {o : Nat} {addr : Word}
    (haddr : addr = srcB + BitVec.ofNat 64 ((s.reg A.cur - d).toNat + A.δ + o))
    (hin : (s.reg A.cur - d).toNat + A.δ + o + op.width ≤ n) (p : Word) :
    (A.set rd (Cells.load o op.width)).ok m0 d srcB n ((s.setReg rd (loadVal op s.mem addr)).setPc p) := by
  refine AState.ok_set h hrd hrd0 ?_ p
  rw [haddr]
  exact Cells.load_ok h.2.1 hd h.1 op hop o hin

/-- A store at the cursor of a register whose first `w` cells are the next source bytes. -/
theorem AState.ok_store {m0 d srcB n} {A : AState} {s : State} (h : A.ok m0 d srcB n s)
    (hn : n < 2 ^ 64) {w : Nat} (hw : w ≤ 8) {rs2 : Reg} {addr : Word}
    (haddr : addr = s.reg A.cur + BitVec.ofNat 64 A.δ)
    (hbound : (s.reg A.cur - d).toNat + A.δ + w ≤ n)
    (hpre : ∀ i < w, (A.cells rs2).getD i .unk = .src i) (p : Word) :
    ({ A with δ := A.δ + w, cells := fun r => (A.cells r).rebase w } : AState).ok m0 d srcB n
      ((s.setMem (writeLE s.mem addr (s.reg rs2).toNat w)).setPc p) := by
  obtain ⟨hcn, hc, hr⟩ := h
  have hreg : ∀ r, ((s.setMem (writeLE s.mem addr (s.reg rs2).toNat w)).setPc p).reg r = s.reg r :=
    fun r => rfl
  have e : addr = d + BitVec.ofNat 64 ((s.reg A.cur - d).toNat + A.δ) := by
    rw [haddr, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [hreg]; omega
  · simp only [hreg]
    show Copied m0 (writeLE s.mem addr (s.reg rs2).toNat w) d srcB ((s.reg A.cur - d).toNat + (A.δ + w))
    rw [e, ← Nat.add_assoc]
    exact Cells.store_ok hc (hr rs2) hw (by omega) hpre
  · intro r
    simp only [hreg]
    rw [← Nat.add_assoc]
    exact Cells.rebase_ok w (hr r)

end NoCompiler.Typed.Track

namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed NoCompiler.Typed.Bytes

/-- Two words holding expressions that are equal mod 2^64 are equal. -/
theorem word_eq_of_eqMod {ι : Val} {w1 w2 : Word} {e1 e2 : IExpr} (h1 : HasInt ι w1 e1)
    (h2 : HasInt ι w2 e2) (h : (Constr.eqMod e1 e2).holds ι) : w1 = w2 := by
  unfold HasInt at h1 h2
  simp only [Constr.holds, Constr.eqMod, Constr.eval, IExpr.eval_sub, decide_eq_true_eq] at h
  apply BitVec.eq_of_toNat_eq
  have := w1.isLt; have := w2.isLt
  omega

/-- The exact distance of the cursor from `d`, from the bounds `d ≤ cur` and
    `cur − d + k ≤ n` on its expression (`n < 2^64`). -/
theorem toNat_sub_exact {ι : Val} {cur d : Word} {ec : IExpr} {dv nv : Var} {n k : Nat}
    (hc : HasInt ι cur ec) (hd : (d.toNat : Int) % 2 ^ 64 = ι dv % 2 ^ 64) (hn : (n : Int) = ι nv) (hn64 : n < 2 ^ 64)
    (hlo : (Constr.le (.var dv) ec).holds ι)
    (hhi : (Constr.le ((ec.sub (.var dv)).add (.lit k)) (.var nv)).holds ι) :
    ((cur - d).toNat : Int) = ec.eval ι - ι dv ∧ (cur - d).toNat + k ≤ n := by
  unfold HasInt at hc
  simp only [Constr.holds, Constr.eval, IExpr.eval_sub, IExpr.eval_add, IExpr.eval_var, IExpr.eval_lit,
    decide_eq_true_eq] at hlo hhi
  have hcur := cur.isLt; have hd' := d.isLt
  rw [BitVec.toNat_sub]
  constructor <;> omega

end NoCompiler.Typed.Track

namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed NoCompiler.Typed.Bytes

theorem hasInt_ofNat (ι : Val) (k : Nat) : HasInt ι (BitVec.ofNat 64 k) (.lit k) := by
  unfold HasInt; simp [BitVec.toNat_ofNat]

/-- The variables of the copy's parameters: destination, source, length. -/
structure Params where
  dv : Var
  sv : Var
  nv : Var
  deriving DecidableEq, Repr

/-- One abstract step at a point with type `S` (side conditions are entailments on `S`), with
    `o` the load offset hint. -/
def tstep (S : STy) (P : Params) (o : Nat) (A : AState) : Instr → Option AState
  | .store op rs1 rs2 off =>
    match S.reg rs1, S.reg A.cur with
    | some e1, some ec =>
      if op ≠ .sh ∧ ((List.range op.width).all fun i => (A.cells rs2).getD i .unk == .src i) = true ∧
          S.ent (Constr.eqMod (e1.add (.lit off.toInt)) (ec.add (.lit A.δ))) = true ∧
          S.ent (.le (.var P.dv) ec) = true ∧
          S.ent (.le ((ec.sub (.var P.dv)).add (.lit (A.δ + op.width))) (.var P.nv)) = true
      then some { A with δ := A.δ + op.width, cells := fun r => (A.cells r).rebase op.width }
      else none
    | _, _ => none
  | .load op rd rs1 off =>
    match S.reg rs1, S.reg A.cur with
    | some e1, some ec =>
      if op ≠ .lh ∧ op ≠ .lhu ∧ rd ≠ A.cur ∧ rd ≠ 0 ∧
          S.ent (Constr.eqMod (e1.add (.lit off.toInt))
            ((((IExpr.var P.sv).add ec).sub (.var P.dv)).add (.lit (A.δ + o)))) = true ∧
          S.ent (.le (.var P.dv) ec) = true ∧
          S.ent (.le ((ec.sub (.var P.dv)).add (.lit (A.δ + o + op.width))) (.var P.nv)) = true
      then some (A.set rd (Cells.load o op.width))
      else none
    | _, _ => none
  -- a pointer move that is the cursor plus `o ≤ δ` (the hint), by the point's type: the new cursor
  | .iop .addi rd rs imm =>
    match S.reg rs, S.reg A.cur with
    | some e, some ec =>
      if rd ≠ 0 ∧ o ≤ A.δ ∧ S.ent (Constr.eqMod (e.add (.lit imm.toInt)) (ec.add (.lit o))) = true then
        some { cur := rd, δ := A.δ - o, cells := (A.set rd []).cells }
      else regStep A (.iop .addi rd rs imm)
    | _, _ => regStep A (.iop .addi rd rs imm)
  | .rop .add rd a b =>
    match S.reg a, S.reg b, S.reg A.cur with
    | some ea, some eb, some ec =>
      if rd ≠ 0 ∧ o ≤ A.δ ∧ S.ent (Constr.eqMod (ea.add eb) (ec.add (.lit o))) = true then
        some { cur := rd, δ := A.δ - o, cells := (A.set rd []).cells }
      else regStep A (.rop .add rd a b)
    | _, _, _ => regStep A (.rop .add rd a b)
  | .branch _ _ _ _ => some A
  | .jal 0 _ => some A
  | .jalr 0 _ _ => some A
  | i => regStep A i

end NoCompiler.Typed.Track

namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed NoCompiler.Typed.Bytes

/-- An optional cursor switch before a point's instruction: to `r`, which the point's type says
    holds `cursor + j` with `j ≤ δ`. -/
def tswitch (S : STy) (A : AState) : Option (Reg × Nat) → Option AState
  | none => some A
  | some (r, j) =>
    match S.reg r, S.reg A.cur with
    | some e, some ec =>
      if j ≤ A.δ ∧ S.ent (Constr.eqMod e (ec.add (.lit j))) = true then
        some { A with cur := r, δ := A.δ - j }
      else none
    | _, _ => none

theorem LdOp.width_le (op : LdOp) : op.width ≤ 8 := by cases op <;> decide
theorem StOp.width_le (op : StOp) : op.width ≤ 8 := by cases op <;> decide

theorem signExtend_of_small {imm : BitVec 12} (h : imm.toNat < 2 ^ 11) :
    imm.signExtend 64 = BitVec.ofNat 64 imm.toNat := by
  have hm : imm.msb = false := by rw [BitVec.msb_eq_false_iff_two_mul_lt]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]

/-- **Soundness of the abstract step.** -/
theorem tstep_ok {m0 : Word → Byte} {d srcB : Word} {n : Nat} {S : STy} {P : Params} {o : Nat} {A A' : AState} {s s' : State}
    {ι : Val} {i : Instr} (hregs : ∀ p ∈ S.regs, HasInt ι (s.reg p.1) p.2)
    (hent : ∀ ψ, S.ent ψ = true → ψ.holds ι) (hd : (d.toNat : Int) % 2 ^ 64 = ι P.dv % 2 ^ 64)
    (hs : (srcB.toNat : Int) % 2 ^ 64 = ι P.sv % 2 ^ 64) (hn : (n : Int) = ι P.nv) (hn64 : n < 2 ^ 64)
    (hdisj : Disj d srcB n) (h : A.ok m0 d srcB n s) (ht : tstep S P o A i = some A')
    (hx : exec i s = some s') : A'.ok m0 d srcB n s' := by
  cases i
  case store op rs1 rs2 off =>
    simp only [tstep] at ht
    split at ht
    · rename_i e1 ec h1 hc
      split at ht
      · rename_i hcond
        obtain ⟨hop, hpre, haddr, hlo, hhi⟩ := hcond
        cases ht
        simp only [exec] at hx
        split at hx
        · cases hx
          have hw1 := STy.reg_hasInt hregs h1
          have hwc := STy.reg_hasInt hregs hc
          have hea : ea s rs1 off = s.reg A.cur + BitVec.ofNat 64 A.δ :=
            word_eq_of_eqMod (hasInt_add hw1 (hasInt_signExtend (by decide) ι off))
              (hasInt_add hwc (hasInt_ofNat ι A.δ)) (hent _ haddr)
          obtain ⟨-, hb⟩ := toNat_sub_exact (d := d) hwc hd hn hn64 (hent _ hlo) (hent _ hhi)
          exact AState.ok_store h hn64 (StOp.width_le op) hea (by omega)
            (fun i hi => by
              have := List.all_eq_true.1 hpre i (List.mem_range.2 hi)
              simpa using this) _
        · cases hx
      · cases ht
    · cases ht
  case load op rd rs1 off =>
    simp only [tstep] at ht
    split at ht
    · rename_i e1 ec h1 hc
      split at ht
      · rename_i hcond
        obtain ⟨hop1, hop2, hrd, hrd0, haddr, hlo, hhi⟩ := hcond
        cases ht
        simp only [exec] at hx
        split at hx
        · cases hx
          have hw1 := STy.reg_hasInt hregs h1
          have hwc := STy.reg_hasInt hregs hc
          obtain ⟨hex, hb⟩ := toNat_sub_exact (d := d) hwc hd hn hn64 (hent _ hlo) (hent _ hhi)
          have hrhs : HasInt ι (srcB + BitVec.ofNat 64 ((s.reg A.cur - d).toNat + A.δ + o))
              ((((IExpr.var P.sv).add ec).sub (.var P.dv)).add (.lit (A.δ + o))) := by
            unfold HasInt
            simp only [BitVec.toNat_add, BitVec.toNat_ofNat, IExpr.eval_add, IExpr.eval_sub,
              IExpr.eval_var, IExpr.eval_lit]
            have := srcB.isLt
            omega
          have hea : ea s rs1 off = srcB + BitVec.ofNat 64 ((s.reg A.cur - d).toNat + A.δ + o) :=
            word_eq_of_eqMod (hasInt_add hw1 (hasInt_signExtend (by decide) ι off)) hrhs (hent _ haddr)
          exact AState.ok_load h hdisj ⟨hop1, hop2⟩ hrd hrd0 hea (by omega) _
        · cases hx
      · cases ht
    · cases ht
  case iop op rd rs imm =>
    cases op
    case addi =>
      simp only [tstep] at ht
      split at ht
      · rename_i e ec he hc
        split at ht
        · rename_i hcond
          obtain ⟨hrd0, hle, heq⟩ := hcond
          cases ht
          simp only [exec, Option.some.injEq] at hx
          subst hx
          simp only [evalI]
          have hv : s.reg rs + imm.signExtend 64 = s.reg A.cur + BitVec.ofNat 64 o :=
            word_eq_of_eqMod (hasInt_add (STy.reg_hasInt hregs he) (hasInt_signExtend (by decide) ι imm))
              (hasInt_add (STy.reg_hasInt hregs hc) (hasInt_ofNat ι o)) (hent _ heq)
          rw [hv]
          exact AState.ok_advance h hn64 hrd0 hle _
        · exact regStep_ok h ht hx
      · exact regStep_ok h ht hx
    all_goals (simp only [tstep] at ht; exact regStep_ok h ht hx)
  case rop op rd a b =>
    cases op
    case add =>
      simp only [tstep] at ht
      split at ht
      · rename_i ea eb ec ha hb hc
        split at ht
        · rename_i hcond
          obtain ⟨hrd0, hle, heq⟩ := hcond
          cases ht
          simp only [exec, Option.some.injEq] at hx
          subst hx
          simp only [evalR]
          have hv : s.reg a + s.reg b = s.reg A.cur + BitVec.ofNat 64 o :=
            word_eq_of_eqMod (hasInt_add (STy.reg_hasInt hregs ha) (STy.reg_hasInt hregs hb))
              (hasInt_add (STy.reg_hasInt hregs hc) (hasInt_ofNat ι o)) (hent _ heq)
          rw [hv]
          exact AState.ok_advance h hn64 hrd0 hle _
        · exact regStep_ok h ht hx
      · exact regStep_ok h ht hx
    all_goals (simp only [tstep] at ht; exact regStep_ok h ht hx)
  case branch op rs1 rs2 off =>
    simp only [tstep, Option.some.injEq] at ht
    subst ht
    simp only [exec] at hx
    split at hx
    · simp only [jumpTo] at hx; split at hx
      · cases hx; exact AState.ok_setPc h _
      · cases hx
    · cases hx; exact AState.ok_setPc h _
  case jal rd off =>
    by_cases hrd : rd = 0
    · subst hrd
      simp only [tstep, Option.some.injEq] at ht
      subst ht
      simp only [exec, State.setReg, if_true, jumpTo] at hx
      split at hx
      · cases hx; exact AState.ok_setPc h _
      · cases hx
    · have : tstep S P o A (.jal rd off) = regStep A (.jal rd off) := by
        simp only [tstep]; split <;> simp_all
      rw [this] at ht; exact regStep_ok h ht hx
  case jalr rd rs1 off =>
    by_cases hrd : rd = 0
    · subst hrd
      simp only [tstep, Option.some.injEq] at ht
      subst ht
      simp only [exec, State.setReg, if_true, jumpTo] at hx
      split at hx
      · cases hx; exact AState.ok_setPc h _
      · cases hx
    · have : tstep S P o A (.jalr rd rs1 off) = regStep A (.jalr rd rs1 off) := by
        simp only [tstep]; split <;> simp_all
      rw [this] at ht; exact regStep_ok h ht hx
  all_goals (simp only [tstep] at ht; exact regStep_ok h ht hx)

theorem tswitch_ok {m0 : Word → Byte} {d srcB : Word} {n : Nat} {S : STy} {A A' : AState}
    {s : State} {ι : Val} {m : Option (Reg × Nat)} (hregs : ∀ p ∈ S.regs, HasInt ι (s.reg p.1) p.2)
    (hent : ∀ ψ, S.ent ψ = true → ψ.holds ι) (hn64 : n < 2 ^ 64) (h : A.ok m0 d srcB n s)
    (ht : tswitch S A m = some A') : A'.ok m0 d srcB n s := by
  cases m with
  | none => simp only [tswitch, Option.some.injEq] at ht; subst ht; exact h
  | some p =>
    obtain ⟨r, j⟩ := p
    simp only [tswitch] at ht
    split at ht
    · rename_i e ec he hc
      split at ht
      · rename_i hcond
        obtain ⟨hj, heq⟩ := hcond
        cases ht
        exact AState.ok_switch h hn64 hj
          (word_eq_of_eqMod (STy.reg_hasInt hregs he)
            (hasInt_add (STy.reg_hasInt hregs hc) (hasInt_ofNat ι j)) (hent _ heq))
      · cases ht
    · cases ht

end NoCompiler.Typed.Track

namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed

variable {f : Fn}

/-- Points have distinct addresses (`4·size < 2^64`). -/
theorem Fn.pcOf_inj {k k' : Nat} (hsz : 4 * f.size < 2 ^ 64) (hk : k < f.size) (hk' : k' < f.size)
    (h : f.pcOf k = f.pcOf k') : k = k' := by
  unfold Fn.pcOf at h
  have h2 : BitVec.ofNat 64 (4 * k) = BitVec.ofNat 64 (4 * k') := by
    have := congrArg (fun x => x - f.entry) h
    simpa using this
  have := congrArg BitVec.toNat h2
  simp only [BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  omega

/-- The points an instruction at `k` can continue at (inside `f`): `jalr` is left out (a return,
    handled apart). -/
def succs (k : Nat) : Instr → List Nat
  | .branch _ _ _ off => (k + 1) :: (Fn.target k off.toInt).toList
  | .jal _ off => (Fn.target k off.toInt).toList
  | .jalr _ _ _ => []
  | _ => [k + 1]

end NoCompiler.Typed.Track

namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed

variable {f : Fn}

/-- A jump from point `k` by `off` lands on point `k'` exactly when the checker's `target` says so
    (`4·size` far below `2^64`). -/
theorem Fn.target_of_pc {k k' : Nat} {n : Nat} {off : BitVec n} (hn : n ≤ 21)
    (hsz : 4 * f.size + 2 ^ 21 < 2 ^ 64) (hk : k < f.size) (hk' : k' < f.size)
    (h : f.pcOf k' = f.pcOf k + off.signExtend 64) : Fn.target k off.toInt = some k' := by
  unfold Fn.pcOf at h
  have h2 : BitVec.ofNat 64 (4 * k') = BitVec.ofNat 64 (4 * k) + off.signExtend 64 := by
    have := congrArg (fun x => x - f.entry) h
    rw [show f.entry + BitVec.ofNat 64 (4 * k') - f.entry = BitVec.ofNat 64 (4 * k') by bv_omega,
      show f.entry + BitVec.ofNat 64 (4 * k) + BitVec.signExtend 64 off - f.entry =
        BitVec.ofNat 64 (4 * k) + BitVec.signExtend 64 off by bv_omega] at this
    exact this
  have hc := BitVec.toInt_eq_toNat_cond (off.signExtend 64)
  rw [BitVec.toInt_signExtend_of_le (by omega)] at hc
  have hlo := BitVec.le_toInt (x := off)
  have hhi := BitVec.toInt_lt (x := off)
  have hpow : (2 : Int) ^ (n - 1) ≤ 2 ^ 20 := by
    have : n - 1 ≤ 20 := by omega
    exact_mod_cast Nat.pow_le_pow_right (by decide) this
  have := congrArg BitVec.toNat h2
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (a := 4 * k') (by omega), Nat.mod_eq_of_lt (a := 4 * k) (by omega)] at this
  have hlt := (off.signExtend 64).isLt
  unfold Fn.target
  split at hc
  · have e : (4 * k' : Int) = 4 * k + off.toInt := by omega
    rw [if_pos (by simp; omega)]
    congr 1; omega
  · have e : (4 * k' : Int) = 4 * k + off.toInt := by omega
    rw [if_pos (by simp; omega)]
    congr 1; omega

end NoCompiler.Typed.Track

namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed

/-- Where an instruction continues: the next one, unless it is a jump. -/
theorem exec_pc {i : Instr} {s s' : State} (hx : exec i s = some s') :
    match i with
    | .branch _ _ _ off => s'.pc = s.pc + 4 ∨ s'.pc = s.pc + off.signExtend 64
    | .jal _ off => s'.pc = s.pc + off.signExtend 64
    | .jalr _ _ _ => True
    | _ => s'.pc = s.pc + 4 := by
  cases i <;> simp only [exec, jumpTo] at hx ⊢ <;>
    (repeat split at hx) <;> (try cases hx) <;> simp_all [State.setPc, State.setReg, State.setMem] <;>
    (try split <;> rfl)

end NoCompiler.Typed.Track

namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed

variable {f : Fn}

theorem Fn.pcOf_inj_le {k k' : Nat} (hsz : 4 * f.size < 2 ^ 64) (hk : k ≤ f.size) (hk' : k' ≤ f.size)
    (h : f.pcOf k = f.pcOf k') : k = k' := by
  unfold Fn.pcOf at h
  have h2 : BitVec.ofNat 64 (4 * k) = BitVec.ofNat 64 (4 * k') := by
    have := congrArg (fun x => x - f.entry) h
    simpa using this
  have := congrArg BitVec.toNat h2
  simp only [BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  omega

theorem Fn.pcOf_succ (k : Nat) : f.pcOf (k + 1) = f.pcOf k + 4 := by
  unfold Fn.pcOf
  rw [show 4 * (k + 1) = 4 * k + 4 by omega, BitVec.ofNat_add]
  bv_omega

/-- A step from point `k` that lands on point `k'` (not by `jalr`) lands on a successor. -/
theorem succ_mem (hsz : 4 * f.size + 2 ^ 21 < 2 ^ 64) {k k' : Nat} (hk : k < f.size)
    (hk' : k' < f.size) {i : Instr} {s s' : State} (hpc : s.pc = f.pcOf k)
    (hx : exec i s = some s') (hpc' : s'.pc = f.pcOf k') (hj : ∀ a b c, i ≠ .jalr a b c) :
    k' ∈ succs k i := by
  have hp := exec_pc hx
  have next : s'.pc = s.pc + 4 → k' = k + 1 := fun h =>
    (Fn.pcOf_inj_le (f := f) (by omega) (by omega) (by omega)
      (by rw [Fn.pcOf_succ, ← hpc, ← h, hpc'])).symm
  cases i
  case branch op rs1 rs2 off =>
    simp only [succs, List.mem_cons]
    rcases hp with h | h
    · exact .inl (next h)
    · right
      have := Fn.target_of_pc (f := f) (off := off) (by decide) hsz hk hk' (by rw [← hpc', h, hpc])
      rw [this]; simp
  case jal rd off =>
    simp only [succs]
    have := Fn.target_of_pc (f := f) (off := off) (by decide) hsz hk hk' (by rw [← hpc', hp, hpc])
    rw [this]; simp
  case jalr a b c => exact absurd rfl (hj a b c)
  all_goals (simp only [succs, List.mem_singleton]; exact next hp)

end NoCompiler.Typed.Track

namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed

theorem lookup_mem' {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {a : α} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (x, y) :: r, a, b, h => by
    by_cases hx : a = x
    · subst hx; simp [List.lookup] at h; subst h; simp
    · have hb : (a == x) = false := by simpa using hx
      simp [List.lookup, hb] at h
      exact List.mem_cons_of_mem _ (lookup_mem' h)

/-- `fr'` at the next point, implied by the computed state: the same cursor and δ, cells no
    stronger. -/
theorem Frame.ok_of_leA {m0 d srcB n} {fr' : Frame} {A : AState} {s : State} (h : fr'.leA A = true)
    (hA : A.ok m0 d srcB n s) : fr'.toA.ok m0 d srcB n s := by
  simp only [Frame.leA, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨hc, hd⟩, hcs⟩ := h
  obtain ⟨hn, hcp, hr⟩ := hA
  simp only [Frame.toA]
  rw [hc, hd]
  refine ⟨hn, hcp, fun r => ?_⟩
  show Cells.ok m0 srcB _ (s.reg r) ((fr'.cells.lookup r).getD [])
  cases hl : fr'.cells.lookup r with
  | none => intro i hi; simp [Cell.ok]
  | some cs =>
    have := Cells.ok_of_le (hcs (r, cs) (lookup_mem' hl)) (hr r)
    simpa using this

/-- The registers and variables of a copy's arguments. -/
structure CopyArgs where
  dr : Reg
  sr : Reg
  nr : Reg
  P : Params
  deriving DecidableEq, Repr

/-- The table of a value invariant: a frame and a load-offset hint per point. -/
structure Table where
  frames : List (Nat × Frame)
  hints : List (Nat × Nat)
  moves : List (Nat × (Reg × Nat)) := []
  /-- Finished points: returns where the copy is complete (the invariant drops the cursor). -/
  fins : List Nat := []
  deriving Repr

def Table.frame (t : Table) (k : Nat) : Frame := (t.frames.lookup k).getD ⟨0, 0, []⟩
def Table.hint (t : Table) (k : Nat) : Nat := (t.hints.lookup k).getD 0
def Table.move (t : Table) (k : Nat) : Option (Reg × Nat) := t.moves.lookup k
def Table.done (t : Table) (k : Nat) : Bool := t.fins.contains k

end NoCompiler.Typed.Track

namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed

variable {f : Fn}

/-- The converse of `target_of_pc`: the checker's target is where the jump lands. -/
theorem Fn.pc_of_target {k k' : Nat} {n : Nat} {off : BitVec n} (hn : 1 ≤ n) (hn' : n ≤ 21)
    (h : Fn.target k off.toInt = some k') : f.pcOf k' = f.pcOf k + off.signExtend 64 := by
  unfold Fn.target at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [Option.some.injEq] at h
    subst h
    unfold Fn.pcOf
    rw [BitVec.add_assoc]; congr 1
    apply BitVec.eq_of_toNat_eq
    have hc2 := BitVec.toInt_eq_toNat_cond (off.signExtend 64)
    rw [BitVec.toInt_signExtend_of_le (by omega)] at hc2
    have hlo := BitVec.le_toInt (x := off)
    have hhi := BitVec.toInt_lt (x := off)
    have hpow : (2 : Int) ^ (n - 1) ≤ 2 ^ 20 := by
      have : n - 1 ≤ 20 := by omega
      exact_mod_cast Nat.pow_le_pow_right (by decide) this
    have hlt := (off.signExtend 64).isLt
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have hmod : off.toInt % 4 = 0 := by simpa using hc.1
    split at hc2 <;> omega
  · cases h

end NoCompiler.Typed.Track

namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed

/-- What a taken / not-taken `beq`/`bne` says (nothing for the other branches). -/
def brTaken (op : BrOp) (e1 e2 : IExpr) : List Constr :=
  match op with
  | .beq => [Constr.eqMod e1 e2]
  | .bne => [.not (Constr.eqMod e1 e2)]
  | _ => []

def brFall (op : BrOp) (e1 e2 : IExpr) : List Constr :=
  match op with
  | .beq => [.not (Constr.eqMod e1 e2)]
  | .bne => [Constr.eqMod e1 e2]
  | _ => []

/-- The branch facts of the edge `k → k'` (none when both outcomes reach `k'`). -/
def edgeFacts (S : STy) (k k' : Nat) : Instr → List Constr
  | .branch op rs1 rs2 off =>
    match S.reg rs1, S.reg rs2 with
    | some e1, some e2 =>
      if Fn.target k off.toInt = some k' ∧ k' ≠ k + 1 then brTaken op e1 e2
      else if k' = k + 1 ∧ Fn.target k off.toInt ≠ some k' then brFall op e1 e2
      else []
    | _, _ => []
  | _ => []

/-- The copy is complete in the computed state: the point's type, with the facts `fs` of the
    edge, entails `cursor − d + δ = n`. -/
def finOk (S : STy) (C : CopyArgs) (A : AState) (fs : List Constr) : Bool :=
  let S' : STy := { S with facts := fs ++ S.facts }
  match S.reg A.cur with
  | some ec =>
    S'.ent (.le (.var C.P.dv) ec) &&
      S'.ent (.le ((ec.sub (.var C.P.dv)).add (.lit A.δ)) (.var C.P.nv)) &&
      S'.ent (.le (.var C.P.nv) ((ec.sub (.var C.P.dv)).add (.lit A.δ)))
  | none => false

/-- The check at point `k`: a finished point is `jalr x0, 0(ra)` with `ra` still the entry's; a
    return is that and the copy complete; any other instruction's abstract step is defined, its
    jumps have targets, and each successor's frame follows from the computed state (a finished
    successor: a branch edge on which the copy is complete). -/
def pointOk (f : Fn) (c : Code) (C : CopyArgs) (t : Table) (k : Nat) : Bool :=
  match f.tyAt k, c.instr (f.pcOf k) with
  | none, _ => true
  | some _, none => false
  | some S, some i =>
    if t.done k then
      decide (i = .jalr 0 1 0) &&
        match f.regVar.lookup 1 with
        | some x => S.reg 1 == some (.var x)
        | none => false
    else if i = .jalr 0 1 0 then
      match f.regVar.lookup 1, S.reg (t.frame k).cur with
      | some x, some ec =>
        S.reg 1 == some (.var x) && S.ent (.le (.var C.P.dv) ec) &&
          S.ent (.le ((ec.sub (.var C.P.dv)).add (.lit (t.frame k).δ)) (.var C.P.nv)) &&
          S.ent (.le (.var C.P.nv) ((ec.sub (.var C.P.dv)).add (.lit (t.frame k).δ)))
      | _, _ => false
    else
      (match i with
       | .jalr _ _ _ => false
       | .branch _ _ _ off => (Fn.target k off.toInt).isSome
       | .jal _ off => (Fn.target k off.toInt).isSome
       | _ => true) &&
      match (tswitch S (t.frame k).toA (t.move k)).bind (fun A => tstep S C.P (t.hint k) A i) with
      | some A' => (succs k i).all fun k' => decide (k' < f.size) &&
          if t.done k' then
            (match i with | .branch _ _ _ _ => true | _ => false) && finOk S C A' (edgeFacts S k k' i)
          else (t.frame k').leA A'
      | none => false

/-- The table's check: the entry is not finished, its frame is the empty copy at the destination
    register, and every point passes `pointOk`. Decidable; the kernel runs it. -/
def tabOk (f : Fn) (c : Code) (C : CopyArgs) (t : Table) : Bool :=
  !t.done 0 && t.frame 0 == ⟨C.dr, 0, []⟩ && (List.range f.size).all (pointOk f c C t)

end NoCompiler.Typed.Track

namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed

variable {f : Fn} {T : TokEnv}

theorem and_not_one_of_aligned {x : Word} (h : aligned x 4) : x &&& ~~~(1 : Word) = x := by
  unfold aligned at h
  ext j hj
  simp only [BitVec.getElem_and, BitVec.getElem_not]
  by_cases h0 : j = 0
  · subst h0
    have : x[0] = false := by
      rw [← BitVec.getLsbD_eq_getElem, ← BitVec.testBit_toNat]
      simp [Nat.testBit, Nat.shiftRight_zero]; omega
    simp [this]
  · simp [BitVec.getElem_one, h0]

/-- An instruction other than `jalr` whose jumps have targets lands on one of its successors. -/
theorem exists_succ_pc {f : Fn} {k : Nat} {i : Instr} {s s' : State} (hpc : s.pc = f.pcOf k)
    (hnj : (match i with
       | .jalr _ _ _ => false
       | .branch _ _ _ off => (Fn.target k off.toInt).isSome
       | .jal _ off => (Fn.target k off.toInt).isSome
       | _ => true) = true)
    (hx : exec i s = some s') :
    ∃ k' ∈ succs k i, s'.pc = f.pcOf k' := by
  have hp := exec_pc hx
  cases i
  case branch op rs1 rs2 off =>
    simp only at hnj hp
    rcases hp with h1 | h1
    · exact ⟨k + 1, by simp [succs], by rw [h1, hpc, Fn.pcOf_succ]⟩
    · cases htg : Fn.target k off.toInt with
      | none => rw [htg] at hnj; cases hnj
      | some k'' =>
        refine ⟨k'', by simp [succs, htg], ?_⟩
        rw [h1, hpc]
        exact (Fn.pc_of_target (f := f) (off := off) (by decide) (by decide) htg).symm
  case jal rd off =>
    simp only at hnj hp
    cases htg : Fn.target k off.toInt with
    | none => rw [htg] at hnj; cases hnj
    | some k'' =>
      refine ⟨k'', by simp [succs, htg], ?_⟩
      rw [hp, hpc]
      exact (Fn.pc_of_target (f := f) (off := off) (by decide) (by decide) htg).symm
  case jalr => simp at hnj
  all_goals exact ⟨k + 1, by simp [succs], by rw [hp, hpc, Fn.pcOf_succ]⟩

theorem tabOk_point {c : Code} {C : CopyArgs} {t : Table} (ht : tabOk f c C t = true) {k : Nat}
    (hk : k < f.size) : pointOk f c C t k = true := by
  simp only [tabOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at ht
  exact ht.2 k hk

theorem tabOk_entry {c : Code} {C : CopyArgs} {t : Table} (ht : tabOk f c C t = true) :
    t.done 0 = false ∧ t.frame 0 = ⟨C.dr, 0, []⟩ := by
  simp only [tabOk, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at ht
  exact ⟨ht.1.1, ht.1.2⟩

theorem eqMod_of_eq {ι : Val} {w : Word} {e1 e2 : IExpr} (h1 : HasInt ι w e1) (h2 : HasInt ι w e2) :
    (Constr.eqMod e1 e2).holds ι := by
  unfold HasInt at h1 h2
  simp only [Constr.holds, Constr.eqMod, Constr.eval, IExpr.eval_sub, decide_eq_true_eq]
  omega

theorem brTaken_holds {ι : Val} {op : BrOp} {a b : Word} {e1 e2 : IExpr} (h1 : HasInt ι a e1)
    (h2 : HasInt ι b e2) (h : evalBr op a b = true) : ∀ p ∈ brTaken op e1 e2, p.holds ι := by
  cases op <;> simp only [brTaken, List.mem_singleton, List.not_mem_nil, false_imp_iff,
    forall_eq, imp_self, implies_true] <;> simp only [evalBr, beq_iff_eq, bne_iff_ne, ne_eq] at h
  · subst h; exact eqMod_of_eq h1 h2
  · simp only [Constr.holds, Constr.eval, Bool.not_eq_true']
    cases hq : (Constr.eqMod e1 e2).eval ι
    · rfl
    · exact absurd (word_eq_of_eqMod h1 h2 hq) h

theorem brFall_holds {ι : Val} {op : BrOp} {a b : Word} {e1 e2 : IExpr} (h1 : HasInt ι a e1)
    (h2 : HasInt ι b e2) (h : evalBr op a b = false) : ∀ p ∈ brFall op e1 e2, p.holds ι := by
  cases op <;> simp only [brFall, List.mem_singleton, List.not_mem_nil, false_imp_iff,
    forall_eq, imp_self, implies_true] <;>
    simp only [evalBr, beq_eq_false_iff_ne, bne_eq_false_iff_eq, ne_eq] at h
  · simp only [Constr.holds, Constr.eval, Bool.not_eq_true']
    cases hq : (Constr.eqMod e1 e2).eval ι
    · rfl
    · exact absurd (word_eq_of_eqMod h1 h2 hq) h
  · subst h; exact eqMod_of_eq h1 h2

/-- The branch facts of the edge a step took hold. -/
theorem edgeFacts_holds {S : STy} {ι : Val} {k k' : Nat} {i : Instr} {s s' : State}
    (hregs : ∀ p ∈ S.regs, HasInt ι (s.reg p.1) p.2) (hsz : 4 * f.size + 2 ^ 21 < 2 ^ 64)
    (hk : k < f.size) (hk' : k' < f.size) (hpc : s.pc = f.pcOf k) (hx : exec i s = some s')
    (hpc' : s'.pc = f.pcOf k') : ∀ p ∈ edgeFacts S k k' i, p.holds ι := by
  cases i
  case branch op rs1 rs2 off =>
    unfold edgeFacts
    cases he1 : S.reg rs1 with
    | none => simp [he1]
    | some e1 =>
    cases he2 : S.reg rs2 with
    | none => simp [he1, he2]
    | some e2 =>
    · simp only [he1, he2]
      have h1 := STy.reg_hasInt hregs he1
      have h2 := STy.reg_hasInt hregs he2
      simp only [exec] at hx
      split at hx
      · rename_i hev
        unfold jumpTo at hx
        split at hx
        · cases hx
          simp only [State.setPc] at hpc'
          have htg := Fn.target_of_pc (f := f) (off := off) (by decide) hsz hk hk' (by rw [← hpc', hpc])
          by_cases hkk : k' = k + 1
          · rw [if_neg (fun h => h.2 hkk), if_neg (fun h => h.2 htg)]; simp
          · rw [if_pos ⟨htg, hkk⟩]; exact brTaken_holds h1 h2 hev
        · cases hx
      · rename_i hev
        cases hx
        simp only [State.setPc] at hpc'
        have hk1 : k' = k + 1 :=
          (Fn.pcOf_inj_le (f := f) (by omega) (by omega) (by omega)
            (by rw [Fn.pcOf_succ, ← hpc, ← hpc'])).symm
        subst hk1
        rw [if_neg (by simp)]
        by_cases htg : Fn.target k off.toInt = some (k + 1)
        · rw [if_neg (by simp [htg])]; simp
        · rw [if_pos ⟨rfl, htg⟩]
          exact brFall_holds h1 h2 (by simpa using hev)
  all_goals simp [edgeFacts]

/-- A branch changes only the pc. -/
theorem exec_branch {op : BrOp} {rs1 rs2 : Reg} {off : BitVec 13} {s s' : State}
    (hx : exec (.branch op rs1 rs2 off) s = some s') : s'.reg = s.reg ∧ s'.mem = s.mem := by
  simp only [exec, jumpTo] at hx
  split at hx
  · split at hx
    · cases hx; exact ⟨rfl, rfl⟩
    · cases hx
  · cases hx; exact ⟨rfl, rfl⟩

/-- On an edge where `finOk` holds, the computed state's count is `n`. -/
theorem finOk_count {S : STy} {C : CopyArgs} {A : AState} {fs : List Constr} {ι : Val}
    {s : State} {d : Word} {n : Nat} (hregs : ∀ p ∈ S.regs, HasInt ι (s.reg p.1) p.2)
    (hh : ∀ p ∈ S.hyps, p.holds ι) (hfs : ∀ p ∈ fs, p.holds ι)
    (hd : (d.toNat : Int) % 2 ^ 64 = ι C.P.dv % 2 ^ 64) (hn : (n : Int) = ι C.P.nv)
    (hn64 : n < 2 ^ 64) (h : finOk S C A fs = true) :
    (s.reg A.cur - d).toNat + A.δ = n := by
  have hent : ∀ ψ, ({ S with facts := fs ++ S.facts } : STy).ent ψ = true → ψ.holds ι := by
    intro ψ hψ
    refine STy.ent_sound hψ ?_
    intro p hp
    simp only [STy.hyps, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · exact hfs p hp
    · exact hh p (by simp [STy.hyps, hp])
    · exact hh p (by simp only [STy.hyps, List.mem_append]; exact .inr hp)
  unfold finOk at h
  split at h
  · rename_i ec hec
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hlo, hhi⟩, hge⟩ := h
    obtain ⟨hex, hb⟩ := toNat_sub_exact (d := d) (STy.reg_hasInt hregs hec) hd hn hn64
      (hent _ hlo) (hent _ hhi)
    have hge' := hent _ hge
    simp only [Constr.holds, Constr.eval, IExpr.eval_sub, IExpr.eval_add, IExpr.eval_var,
      IExpr.eval_lit, decide_eq_true_eq] at hge'
    omega
  · cases h

/-- **Functional correctness of a copy, from the type check and a checked table** (leaf
    functions): if `tabOk` holds, the function meets its signature with the copy added to the
    post: `d[0, n)` holds the entry bytes of `src[0, n)`, and the rest of memory is the entry's
    (`Copied`), for `d`, `src`, `n` the entry values of the argument registers. -/
theorem Fn.check_sound_track (f : Fn) (c : Code) (T : TokEnv) (h : f.check c = true)
    (hnc : f.callees = []) (hp : f.sig.isPartial = false) {D : Dom}
    (hDf : ∀ k < f.size, D.mem (f.pcOf k)) (hsz : 4 * f.size + 2 ^ 21 < 2 ^ 64)
    (C : CopyArgs) (t : Table) (ht : tabOk f c C t = true)
    (hargs : ∀ a s0, Entry D f.entry s0 → (f.sig.spec T).pre a s0 →
      ((s0.reg C.dr).toNat : Int) % 2 ^ 64 = a.1 C.P.dv % 2 ^ 64 ∧
      ((s0.reg C.sr).toNat : Int) % 2 ^ 64 = a.1 C.P.sv % 2 ^ 64 ∧
      ((s0.reg C.nr).toNat : Int) = a.1 C.P.nv ∧
      C.P.dv ∈ f.sig.params ∧ C.P.sv ∈ f.sig.params ∧ C.P.nv ∈ f.sig.params ∧
      Disj (s0.reg C.dr) (s0.reg C.sr) (s0.reg C.nr).toNat) :
    VerifiedImg c D f.entry
      { f.sig.spec T with
        post := (fun a s s' => (f.sig.spec T).post a s s' ∧
          Copied s.mem s'.mem (s.reg C.dr) (s.reg C.sr) (s.reg C.nr).toNat) } := by
  have hck := h
  unfold Fn.check at hck
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hck
  have hst := Fn.structOk_spec hck.1.1
  refine f.check_sound_val c T h hnc hp hDf
    (fun a s0 k s => if t.done k = true then
        Copied s0.mem s.mem (s0.reg C.dr) (s0.reg C.sr) (s0.reg C.nr).toNat
      else (t.frame k).toA.ok s0.mem (s0.reg C.dr) (s0.reg C.sr) (s0.reg C.nr).toNat s)
    (fun a s0 s' => Copied s0.mem s'.mem (s0.reg C.dr) (s0.reg C.sr) (s0.reg C.nr).toNat)
    ?_ ?_ ?_
  · -- the entry: nothing copied yet
    intro a s0 he hpre
    obtain ⟨hd0, hf0⟩ := tabOk_entry ht
    simp only [hd0, Bool.false_eq_true, if_false]
    rw [hf0]
    unfold AState.ok
    simp only [Frame.toA, BitVec.sub_self, BitVec.toNat_zero, Nat.add_zero]
    refine ⟨Nat.zero_le _, Copied.zero _ _ _, fun r => ?_⟩
    intro i hi; simp [Frame.get, Cell.ok]
  · -- a step between typed points
    intro a s0 he hpre k s k' s' htk hJk hstep htk'
    obtain ⟨hdv, hsv, hnv, hpd, hps, hpn, hdisj⟩ := hargs a s0 he hpre
    have htk0 := htk
    obtain ⟨S, ι0', F, hS, hk, hpc, hI, -⟩ := htk
    obtain ⟨S', ι1, F1, hS', hk', hpc', -, -⟩ := htk'
    have hpt := tabOk_point ht hk
    obtain ⟨ι, hregs, hent, hhyps, hparams⟩ := Fn.Typed.facts hst htk0 hS
    -- a return has no typed successor: it goes to the entry's `ra`, outside the region
    have hret : ∀ {x : Var}, f.regVar.lookup 1 = some x → S.reg 1 = some (.var x) →
        exec (.jalr 0 1 0) s = some s' → False := by
      intro x hx1 hr1 hx
      have hra := Fn.Typed.reg_entry hst htk0 hS hr1 (lookup_mem' hx1)
      simp only [exec, jumpTo, State.setReg, if_true] at hx
      split at hx
      · cases hx
        simp only [State.setPc] at hpc'
        rw [hra, show BitVec.signExtend 64 (0 : BitVec 12) = 0 from by decide,
          show s0.reg 1 + (0 : Word) = s0.reg 1 from by simp,
          and_not_one_of_aligned he.retAligned] at hpc'
        exact he.ret (hpc' ▸ hDf k' hk')
      · cases hx
    cases hstep with
    | sys _ hi _ _ =>
      rw [hpc] at hi
      unfold pointOk at hpt; rw [hS, hi] at hpt
      simp [tstep, regStep, writesReg, Option.bind_eq_none_iff] at hpt
    | @exec i _ hi _ hx =>
      rw [hpc] at hi
      unfold pointOk at hpt; rw [hS, hi] at hpt; simp only at hpt
      split at hpt
      · -- a finished point is a return
        exfalso
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hpt
        obtain ⟨hi0, hra⟩ := hpt
        subst hi0
        split at hra
        · rename_i x hx1
          exact hret hx1 (by simpa using hra) hx
        · cases hra
      rename_i hndk
      simp only [Bool.not_eq_true] at hndk
      simp only [hndk, Bool.false_eq_true, if_false] at hJk
      split at hpt
      · exfalso
        rename_i hi0; subst hi0
        split at hpt
        · rename_i x ec hx1 hec
          simp only [Bool.and_eq_true, beq_iff_eq] at hpt
          exact hret hx1 hpt.1.1.1 hx
        · simp at hpt
      · rename_i hnret
        simp only [Bool.and_eq_true] at hpt
        obtain ⟨hnj, htst⟩ := hpt
        split at htst
        · rename_i A' hA'
          have hdi : ((s0.reg C.dr).toNat : Int) % 2 ^ 64 = ι C.P.dv % 2 ^ 64 := by rw [hparams _ hpd]; exact hdv
          have hsi : ((s0.reg C.sr).toNat : Int) % 2 ^ 64 = ι C.P.sv % 2 ^ 64 := by rw [hparams _ hps]; exact hsv
          have hni : (((s0.reg C.nr).toNat : Nat) : Int) = ι C.P.nv := by rw [hparams _ hpn]; exact hnv
          obtain ⟨A0, h0, h1⟩ := Option.bind_eq_some_iff.1 hA'
          have hJ0 := tswitch_ok hregs hent (s0.reg C.nr).isLt hJk h0
          have hok := tstep_ok hregs hent hdi hsi hni (s0.reg C.nr).isLt hdisj hJ0 h1 hx
          have hnotj : ∀ a b c, i ≠ .jalr a b c := by
            intro a b c he'; subst he'; simp at hnj
          have hmem := succ_mem hsz hk hk' hpc hx hpc' hnotj
          have := List.all_eq_true.1 htst k' hmem
          simp only [Bool.and_eq_true, decide_eq_true_eq] at this
          obtain ⟨-, hsucc⟩ := this
          by_cases hdk' : t.done k' = true
          · -- a finished successor: the edge's facts make the copy complete
            simp only [hdk', if_true, Bool.and_eq_true] at hsucc ⊢
            obtain ⟨hbr, hfin⟩ := hsucc
            cases i
            case branch op rs1 rs2 off =>
              obtain ⟨hreg', hmem'⟩ := exec_branch hx
              have hcnt := finOk_count hregs hhyps
                (edgeFacts_holds hregs hsz hk hk' hpc hx hpc') hdi hni (s0.reg C.nr).isLt hfin
              have hc := hok.2.1
              rw [hreg', hcnt] at hc
              exact hc
            all_goals simp at hbr
          · simp only [Bool.not_eq_true] at hdk'
            simp only [hdk', Bool.false_eq_true, if_false] at hsucc ⊢
            exact Frame.ok_of_leA hsucc hok
        · cases htst
  · -- the return: the copy is complete; nothing else leaves the region
    intro a s0 he hpre k s s' htk hJk hstep hfin hdone
    obtain ⟨hdv, hsv, hnv, hpd, hps, hpn, hdisj⟩ := hargs a s0 he hpre
    have htk0 := htk
    obtain ⟨S, ι0', F, hS, hk, hpc, hI, -⟩ := htk
    have hpt := tabOk_point ht hk
    obtain ⟨ι, hregs, hent, -, hparams⟩ := Fn.Typed.facts hst htk0 hS
    have hdi : ((s0.reg C.dr).toNat : Int) % 2 ^ 64 = ι C.P.dv % 2 ^ 64 := by rw [hparams _ hpd]; exact hdv
    have hni : (((s0.reg C.nr).toNat : Nat) : Int) = ι C.P.nv := by rw [hparams _ hpn]; exact hnv
    cases hstep with
    | sys _ hi _ _ =>
      rw [hpc] at hi
      unfold pointOk at hpt; rw [hS, hi] at hpt
      simp [tstep, regStep, writesReg, Option.bind_eq_none_iff] at hpt
    | @exec i _ hi _ hx =>
      rw [hpc] at hi
      unfold pointOk at hpt; rw [hS, hi] at hpt; simp only at hpt
      split at hpt
      · -- a finished point: the invariant is the complete copy, and a return keeps memory
        rename_i hdk
        simp only [hdk, if_true] at hJk
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hpt
        obtain ⟨hi0, -⟩ := hpt
        subst hi0
        simp only [exec, jumpTo, State.setReg, if_true] at hx
        split at hx
        · cases hx; exact hJk
        · cases hx
      rename_i hndk
      simp only [Bool.not_eq_true] at hndk
      simp only [hndk, Bool.false_eq_true, if_false] at hJk
      split at hpt
      · rename_i hret; subst hret
        split at hpt
        · rename_i x ec hx1 hec
          simp only [Bool.and_eq_true, beq_iff_eq] at hpt
          obtain ⟨⟨⟨-, hlo⟩, hhi⟩, hge⟩ := hpt
          have hwc := STy.reg_hasInt hregs hec
          obtain ⟨hex, hb⟩ := toNat_sub_exact (d := s0.reg C.dr) hwc hdi hni (s0.reg C.nr).isLt
            (hent _ hlo) (hent _ hhi)
          have hge' := hent _ hge
          simp only [Constr.holds, Constr.eval, IExpr.eval_sub, IExpr.eval_add, IExpr.eval_var,
            IExpr.eval_lit, decide_eq_true_eq] at hge'
          have hcount : (s.reg (t.frame k).cur - s0.reg C.dr).toNat + (t.frame k).δ = (s0.reg C.nr).toNat := by
            omega
          simp only [exec, jumpTo, State.setReg, if_true] at hx
          split at hx
          · cases hx
            have hc := hJk.2.1
            simp only [Frame.toA] at hc
            rw [hcount] at hc
            exact hc
          · cases hx
        · simp at hpt
      · -- any other instruction lands on a point inside the region
        exfalso
        simp only [Bool.and_eq_true] at hpt
        obtain ⟨hnj, htst⟩ := hpt
        have hall : ∀ k' ∈ succs k i, k' < f.size := by
          intro k' hk'
          split at htst
          · have := List.all_eq_true.1 htst k' hk'
            simp only [Bool.and_eq_true, decide_eq_true_eq] at this
            exact this.1
          · cases htst
        have hlive : s'.exit = none := (exec_exit hx).1.trans hI.live
        obtain ⟨k', hk'm, hpc'⟩ := exists_succ_pc (f := f) hpc hnj hx
        have hk' := hall k' hk'm
        rcases hfin with h1 | h1
        · exact h1 (hpc' ▸ hDf k' hk')
        · exact h1 hlive

end NoCompiler.Typed.Track

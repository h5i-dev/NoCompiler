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
    (hc : HasInt ι cur ec) (hd : (d.toNat : Int) = ι dv) (hn : (n : Int) = ι nv) (hn64 : n < 2 ^ 64)
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
  | .iop .addi rd rs imm =>
    if rs = A.cur ∧ rd ≠ 0 ∧ imm.toNat < 2 ^ 11 ∧ imm.toNat ≤ A.δ then
      some { cur := rd, δ := A.δ - imm.toNat, cells := (A.set rd []).cells }
    else regStep A (.iop .addi rd rs imm)
  | .branch _ _ _ _ => some A
  | .jal 0 _ => some A
  | .jalr 0 _ _ => some A
  | i => regStep A i

end NoCompiler.Typed.Track

namespace NoCompiler.Typed.Track
open NoCompiler NoCompiler.Typed NoCompiler.Typed.Bytes

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
    (hent : ∀ ψ, S.ent ψ = true → ψ.holds ι) (hd : (d.toNat : Int) = ι P.dv)
    (hs : (srcB.toNat : Int) = ι P.sv) (hn : (n : Int) = ι P.nv) (hn64 : n < 2 ^ 64)
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
      · rename_i hcond
        obtain ⟨hrs, hrd0, hnn, hle⟩ := hcond
        cases ht
        subst hrs
        simp only [exec, Option.some.injEq] at hx
        subst hx
        simp only [evalI]
        rw [signExtend_of_small hnn]
        exact AState.ok_advance h hn64 hrd0 hle _
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

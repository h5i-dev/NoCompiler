import Examples.Musl.MemcpyRecord
import NoCompiler.Typed.Sound.TrackStep

/-
The table producer for a copy's value invariant (untrusted; `tabOk` checks its output in the
kernel). Run: `lake lean scripts/tablegen.lean` from lean/; prints the frames and hints of musl
the table of `F` (Configuration below) as Lean source; for another copy, change the
import, the `open` and the Configuration.
-/
open NoCompiler NoCompiler.Typed NoCompiler.Typed.Track NoCompiler.Typed.Export.memcpy

/-! ## Configuration (the only per-function part): the record, the copy's argument registers
    and variables, and the cursor registers to try first. -/
def F : Fn := fn_memcpy
def PP : Params := ⟨0, 1, 2, 1⟩
def CC : CopyArgs := ⟨10, 11, 12, PP⟩
def cursorPref : List Reg := [13, 16, 10]

/-- The constant of a linear form without variables. -/
def constOf (e : IExpr) : Option Int := let l := e.toLin; if l.t.isEmpty then some l.c else none

/-- The hint at point `k`: a load's source offset, or a pointer move's distance from the cursor. -/
def hintAt (S : STy) (fr : Track.Frame) : Instr → Nat
  | .load _ _ rs1 off =>
    match S.reg rs1, S.reg fr.cur with
    | some e1, some ec =>
      match constOf ((((e1.add (.lit off.toInt)).sub (.var PP.sv)).sub ec).add (.var PP.dv)) with
      | some c => (c - fr.δ).toNat
      | none => 0
    | _, _ => 0
  | .iop .addi _ rs imm =>
    match S.reg rs, S.reg fr.cur with
    | some e, some ec => match constOf ((e.add (.lit imm.toInt)).sub ec) with
      | some c => c.toNat | none => 0
    | _, _ => 0
  | .rop .add _ a b =>
    match S.reg a, S.reg b, S.reg fr.cur with
    | some ea, some eb, some ec => match constOf ((ea.add eb).sub ec) with
      | some c => c.toNat | none => 0
    | _, _, _ => 0
  | _ => 0

def fromA (A : AState) : Track.Frame :=
  ⟨A.cur, A.δ, ((List.finRange 32).filterMap fun r =>
    let cs := A.cells r
    if r ≠ 0 ∧ cs.any (· != .unk) then some (r, cs) else none)⟩

def meetCells (a b : Cells) : Cells :=
  (List.range 8).map fun i => if a.getD i .unk == b.getD i .unk then a.getD i .unk else .unk

def meet (a b : Track.Frame) : Option Track.Frame :=
  if a.cur ≠ b.cur ∨ a.δ ≠ b.δ then none else
  some ⟨a.cur, a.δ, ((List.finRange 32).filterMap fun r =>
    let cs := meetCells (a.get r) (b.get r)
    if r ≠ 0 ∧ cs.any (· != .unk) then some (r, cs) else none)⟩

/-- A cursor switch at a point: a register (not the one the instruction writes) whose expression is
    the cursor's plus `j ≤ δ`. -/
def findMove (S : STy) (fr : Track.Frame) (i : Instr) : Option (Reg × Nat) :=
  match S.reg fr.cur with
  | none => none
  | some ec =>
    (List.finRange 32).findSome? fun r =>
      if r = 0 ∨ r = fr.cur ∨ writesReg i = some r then none else
      match S.reg r with
      | some e => match constOf (e.sub ec) with
        | some c => if 0 ≤ c ∧ c.toNat ≤ fr.δ then some (r, c.toNat) else none
        | none => none
      | none => none

def why (S : STy) (fr : Track.Frame) (o : Nat) : Instr → String
  | .load op rd rs1 off =>
    match S.reg rs1, S.reg fr.cur with
    | some e1, some ec =>
      s!"rd={rd} cur={fr.cur} δ={fr.δ} o={o} e1={reprStr e1} ec={reprStr ec} addr={S.ent (Constr.eqMod (e1.add (.lit off.toInt)) ((((IExpr.var PP.sv).add ec).sub (.var PP.dv)).add (.lit (fr.δ + o))))} lo={S.ent (.le (.var PP.dv) ec)} hi={S.ent (.le ((ec.sub (.var PP.dv)).add (.lit (fr.δ + o + op.width))) (.var PP.nv))}"
    | _, _ => "no reg"
  | .store op rs1 rs2 off =>
    match S.reg rs1, S.reg fr.cur with
    | some e1, some ec =>
      s!"cur={fr.cur} δ={fr.δ} cells={reprStr (fr.get rs2)} addr={S.ent (Constr.eqMod (e1.add (.lit off.toInt)) (ec.add (.lit fr.δ)))} lo={S.ent (.le (.var PP.dv) ec)} hi={S.ent (.le ((ec.sub (.var PP.dv)).add (.lit (fr.δ + op.width))) (.var PP.nv))}"
    | _, _ => "no reg"
  | _ => ""

/-- The cursor a point's type supports: a register whose expression has `d` with coefficient 1
    (a3, then a6, then a0, then any). -/
def desired (S : STy) : Option Reg :=
  let ok (r : Reg) : Bool := match S.reg r with
    | some e => (e.toLin.t.lookup PP.dv) == some 1
    | none => false
  (cursorPref ++ (List.finRange 32)).find? fun r => r ≠ 0 && ok r

def run : IO Unit := do
  let f := F
  let mut frames : Array (Option Track.Frame) := Array.replicate f.size none
  frames := frames.set! 0 (some ⟨CC.dr, 0, []⟩)
  let mut hints : Array Nat := Array.replicate f.size 0
  let mut moves : Array (Option (Reg × Nat)) := Array.replicate f.size none
  let mut conflicts : List Nat := []
  let mut changed := true
  let mut passes := 0
  while changed && passes < 50 do
    changed := false
    passes := passes + 1
    for k in List.range f.size do
      match frames[k]!, ((f.tyAt k).map (·.withCerts .search)), code.instr (f.pcOf k) with
      | some fr, some S, some i =>
        if i = .jalr 0 1 0 then continue
        -- switch the cursor first when the instruction overwrites it or the step fails
        let direct := tstep S PP (hintAt S fr i) fr.toA i
        -- switch to the cursor the successor's type supports
        let tgt : Option Reg :=
          match (succs k i).filterMap (fun k' => if k' < frames.size then (frames[k']!).map (·.cur) else none) with
          | c :: _ => some c
          | [] => match succs k i with
            | k' :: _ => (((f.tyAt k').map (·.withCerts .search))).bind desired
            | [] => none
        let pref : Option (Reg × Nat) :=
          match tgt with
          | none => none
          | some tr =>
          if fr.cur = tr ∨ writesReg i = some tr then none else
          match S.reg tr, S.reg fr.cur with
          | some e, some ec => match constOf (e.sub ec) with
            | some c => if 0 ≤ c ∧ c.toNat ≤ fr.δ then some (tr, c.toNat) else none
            | none => none
          | _, _ => none
        let mv : Option (Reg × Nat) :=
          if pref.isSome then pref
          else if writesReg i = some fr.cur ∨ direct.isNone then findMove S fr i else none
        let fr0 : Track.Frame := match mv with
          | some (r, j) => { fr with cur := r, δ := fr.δ - j }
          | none => fr
        moves := moves.set! k mv
        let h := hintAt S fr0 i
        hints := hints.set! k h
        match (tswitch S fr.toA mv).bind (fun A => tstep S PP h A i) with
        | none => IO.println s!"FAIL step at {k}: {reprStr i} mv={reprStr mv} {why S fr0 h i}"; return
        | some A' =>
          let fa := fromA A'
          for k' in succs k i do
            if k' < f.size then
              match frames[k']! with
              | none => frames := frames.set! k' (some fa); changed := true
              | some old =>
                match meet old fa with
                | none =>
                  -- a return reached with different frames: a finished point (checked below)
                  if code.instr (f.pcOf k') = some (.jalr 0 1 0) then
                    conflicts := conflicts ++ [k']
                    continue
                  IO.println s!"FAIL meet at {k'} from {k}: {reprStr old} vs {reprStr fa}"
                  for kk in List.range 21 do
                    if kk ≥ 6 then IO.println s!"  {kk}: {reprStr frames[kk]!} mv={reprStr moves[kk]!} i={reprStr (code.instr (f.pcOf kk))}"
                  return
                | some m => if m != old then frames := frames.set! k' (some m); changed := true
      | _, _, _ => pure ()
  IO.println s!"-- passes {passes}"
  -- finished returns: the plain return check fails, every predecessor is a branch on whose edge
  -- the copy is complete
  let stepAt (j : Nat) : Option (STy × Instr × AState) :=
    match frames[j]!, ((f.tyAt j).map (·.withCerts .search)), code.instr (f.pcOf j) with
    | some fr, some S, some i =>
      ((tswitch S fr.toA moves[j]!).bind (fun A => tstep S PP hints[j]! A i)).map (S, i, ·)
    | _, _, _ => none
  let retOk (k : Nat) : Bool :=
    match frames[k]!, ((f.tyAt k).map (·.withCerts .search)) with
    | some fr, some S => match S.reg fr.cur with
      | some ec => S.ent (.le (.var PP.dv) ec) &&
          S.ent (.le ((ec.sub (.var PP.dv)).add (.lit fr.δ)) (.var PP.nv)) &&
          S.ent (.le (.var PP.nv) ((ec.sub (.var PP.dv)).add (.lit fr.δ)))
      | none => false
    | _, _ => false
  let mut fins : List Nat := []
  for k in List.range f.size do
    if code.instr (f.pcOf k) = some (.jalr 0 1 0) ∧ (((f.tyAt k).map (·.withCerts .search))).isSome ∧
        (conflicts.contains k || !retOk k) then
      let preds := (List.range f.size).filter fun j =>
        match code.instr (f.pcOf j) with
        | some i => i ≠ .jalr 0 1 0 && (succs j i).contains k
        | none => false
      let ok := preds.all fun j => match stepAt j with
        | some (S, i@(.branch _ _ _ _), A') => finOk S CC A' (edgeFacts S j k i)
        | _ => false
      if ok then fins := fins ++ [k] else IO.println s!"FAIL return at {k}: preds {preds}"
  let fs := (List.range f.size).filterMap fun k => (frames[k]!).map (k, ·)
  let hs := (List.range f.size).filterMap fun k => if hints[k]! = 0 then none else some (k, hints[k]!)
  IO.println s!"def frames : List (Nat × Track.Frame) := {reprStr fs}"
  IO.println s!"def hints : List (Nat × Nat) := {reprStr hs}"
  let ms := (List.range f.size).filterMap fun k => (moves[k]!).map (k, ·)
  IO.println s!"def moves : List (Nat × (Reg × Nat)) := {reprStr ms}"
  IO.println s!"def fins : List Nat := {reprStr fins}"

#eval run

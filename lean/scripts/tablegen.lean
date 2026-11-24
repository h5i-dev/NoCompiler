import Examples.Musl.MemcpyRecord
import NoCompiler.Typed.Sound.TrackStep

/-
The table producer for a copy's value invariant (untrusted; `tabOk` checks its output in the
kernel). Run: `lake lean scripts/tablegen.lean` from lean/; prints the frames and hints of musl
memcpy's table as Lean source.
-/
open NoCompiler NoCompiler.Typed NoCompiler.Typed.Track NoCompiler.Typed.Export.memcpy

def PP : Params := ⟨0, 1, 2⟩
def CC : CopyArgs := ⟨10, 11, 12, PP⟩

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

def run : IO Unit := do
  let f := fn_memcpy
  let mut frames : Array (Option Track.Frame) := Array.replicate f.size none
  frames := frames.set! 0 (some ⟨CC.dr, 0, []⟩)
  let mut hints : Array Nat := Array.replicate f.size 0
  let mut changed := true
  let mut passes := 0
  while changed && passes < 50 do
    changed := false
    passes := passes + 1
    for k in List.range f.size do
      match frames[k]!, f.tyAt k, code.instr (f.pcOf k) with
      | some fr, some S, some i =>
        if i = .jalr 0 1 0 then continue
        let h := hintAt S fr i
        hints := hints.set! k h
        match tstep S PP h fr.toA i with
        | none => IO.println s!"FAIL step at {k}: {reprStr i}"; return
        | some A' =>
          let fa := fromA A'
          for k' in succs k i do
            if k' < f.size then
              match frames[k']! with
              | none => frames := frames.set! k' (some fa); changed := true
              | some old =>
                match meet old fa with
                | none => IO.println s!"FAIL meet at {k'} from {k}: {reprStr old} vs {reprStr fa}"; return
                | some m => if m != old then frames := frames.set! k' (some m); changed := true
      | _, _, _ => pure ()
  IO.println s!"-- passes {passes}"
  let fs := (List.range f.size).filterMap fun k => (frames[k]!).map (k, ·)
  let hs := (List.range f.size).filterMap fun k => if hints[k]! = 0 then none else some (k, hints[k]!)
  IO.println s!"def frames : List (Nat × Track.Frame) := {reprStr fs}"
  IO.println s!"def hints : List (Nat × Nat) := {reprStr hs}"

#eval run

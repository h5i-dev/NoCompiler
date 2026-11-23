import NoCompiler.Auto
import NoCompiler.VC.L2Run

/-!
# `nocompiler_auto_l2`: whole-function proofs for L2 functions through T2/T3 (round 4, QUEUE-C 2)

On a goal `Exec code (sp.perm a s) f_dom (sp.Done a s) s` (after `intro a s he hpre` on a
`VerifiedImg` goal) for an L2 function `f` of a chunk image, the tactic proves the function in
the structured semantics (`Exec.ofS`, `l2Perm`) and explores it with the certificate's facts along
every path (`SReach.of_exploreCallsOnF`). Saving and restoring callee-saved registers is a slot
access (no permission needed, `Frame.isSlot_add`); at a callee's entry the call rule is
`VerifiedImg.callS` and the next path starts with the fact after the call (`InF_afterCall`); at a
return `Preserved` and the entry's `ra` come from T3 (`InF_ret`). No frame, saved-register or
stack obligation is left.

The steps are emitted as tactic text and run.
This first version covers functions without loops and without syscalls.
-/
namespace NoCompiler.AutoL2
open Lean Elab Tactic Meta

/-- Run tactic text on the main goal. -/
def runStr (s : String) : TacticM Unit := do
  match Parser.runParserCategory (← getEnv) `tactic s with
  | .ok stx => evalTactic stx
  | .error e => throwError "nocompiler_auto_l2: cannot parse {e}:\n{s}"

/-- Tactic text on one goal; the goals left. -/
def runOn (g : MVarId) (s : String) : TacticM (List MVarId) := do
  match Parser.runParserCategory (← getEnv) `tactic s with
  | .ok stx =>
    NoCompiler.Auto.traceLine s!"[l2] run:\n{s}"
    let errs := fun (l : MessageLog) => (l.toList.filter (·.severity == .error)).length
    let e0 := errs (← getThe Core.State).messages
    let gs ← NoCompiler.Auto.run g ⟨stx⟩
    let msgs := ((← getThe Core.State).messages.toList.filter (·.severity == .error))
    if msgs.length != e0 then
      for m in msgs.drop e0 do
        NoCompiler.Auto.traceLine s!"[l2] ERROR: {← m.data.toString}"
    for g' in gs do
      NoCompiler.Auto.traceLine s!"[l2] left: {← g'.withContext do return toString (← ppGoal g')}"
    return gs
  | .error e => throwError "nocompiler_auto_l2: cannot parse {e}:\n{s}"

def hexN (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- The names the export gives `f`: from `X_func`, the prefix `X`. -/
def baseName (f : Name) : MetaM String := do
  let s := f.toString
  unless s.endsWith "_func" do throwError "nocompiler_auto_l2: {f} is not an `_func`"
  return String.ofList (s.toList.take (s.length - 5))

/-- `X_chunk : ∀ x, Dom.mem [chunk_N.range B] x → code.instr x = (chunk_N.code B).instr x`: `(chunk_N, B)`. -/
def chunkOf (b : String) : MetaM (Name × Nat × Nat) := do
  let n := b.toName ++ `chunk |>.toString
  let some ci := (← getEnv).find? (b ++ "_chunk").toName |
    throwError "nocompiler_auto_l2: no theorem {b}_chunk (a chunk image is needed)"
  let ty := ci.type
  forallTelescope ty fun _ body => do
    -- body : code.instr x = (Chunk.code B chunk_N).instr x
    let rhs := body.appArg!.appFn!.appArg!
    let ch := rhs.appArg!
    let bE := rhs.appFn!.appArg!
    let some chN := ch.constName? | throwError "nocompiler_auto_l2: {n}: chunk"
    let bN ← NoCompiler.Auto.evalNat (← mkAppM ``BitVec.toNat #[bE])
    let cb ← NoCompiler.Auto.evalNat (← mkAppM ``BitVec.toNat #[mkApp (mkConst ``NoCompiler.Code.base) rhs])
    return (chN, bN, cb)


/-- An aligned address of the function's chunk is the function's (the chunk is the function). -/
theorem contains_of_chunk {f : NoCompiler.Struct.Func} {r : Word × Nat} (hb : r.1 = f.entry)
    (hs : r.2 = 4 * f.len) (hal : NoCompiler.aligned f.entry 4) :
    ∀ x, Dom.mem [r] x → NoCompiler.aligned x 4 → f.contains x = true := by
  intro x hx hax
  simp only [Dom.mem, List.any_cons, List.any_nil, Bool.or_false, decide_eq_true_eq] at hx
  rw [hb, hs] at hx
  unfold NoCompiler.Struct.Func.contains
  unfold NoCompiler.aligned at hal hax
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨hx, ?_⟩
  rw [BitVec.toNat_sub]
  have := x.isLt; have := f.entry.isLt
  omega

/-- What the driver knows of the function and its proof so far. -/
structure Cfg where
  b : String
  spec : String
  specC : String
  a : String
  sN : String
  heN : String
  ch : String
  chBase : Nat
  /-- the chunk's code's base (the chunk's first word) -/
  codeBase : Nat
  entry : Nat
  ces : List (Nat × String × String)
  fuel : Nat
  /-- the next fresh name's index -/
  n : IO.Ref Nat

def fresh (cfg : Cfg) (p : String) : TacticM String := do
  let k ← cfg.n.get; cfg.n.set (k + 1); return s!"{p}{k}"

def cesText (cfg : Cfg) : String :=
  "[" ++ ", ".intercalate (cfg.ces.map fun (e, _, _) => s!"BitVec.ofNat 64 {e}") ++ "]"

def lit (n : Nat) : String := s!"(BitVec.ofNat 64 {n})"

/-- The symbolic state of a path end (`Matches ρ μ S s' → …`). -/
def endState (g : MVarId) : MetaM (Option (Expr × Bool)) := g.withContext do
  let t ← whnfR (← instantiateMVars (← g.getType))
  unless t.isAppOfArity ``NoCompiler.VC.M.PEnd.NextI 5 do return none
  let e := t.getArg! 4
  if e.isAppOfArity ``NoCompiler.VC.M.PEnd.cut 2 then return some (e.getArg! 0, false)
  if e.isAppOfArity ``NoCompiler.VC.M.PEnd.ret 2 then return some (e.getArg! 0, true)
  return none

def evalWord (e : Expr) : MetaM Nat := do NoCompiler.Auto.evalNat (← mkAppM ``BitVec.toNat #[e])

def symOfReg (S : Expr) (r : Nat) : MetaM NoCompiler.VC.M.Sym := do
  let re ← mkNumeral (mkConst ``NoCompiler.Reg) r
  NoCompiler.VC.M.evalSym (← mkAppM ``NoCompiler.VC.M.SState.reg #[S, re])

/-- An offset `k` with `sym = var 2 + k` (`sp` moved by constants). -/
def spOff : NoCompiler.VC.M.Sym → Option Nat
  | .var 2 => some 0
  | .iop .addi a k => (spOff a).map fun o => (o + k.toNat) % 2 ^ 64
  | _ => none

/-- The obligations' closers, with `u.reg 2 = s.reg 2 + d` as `hsp` (or none when `u` is `s`). -/
def obCloser (hsp : Option String) : String :=
  let rw := match hsp with | some h => s!", {h}" | none => ""
  let norm := s!"simp only [NoCompiler.VC.M.den_var2, NoCompiler.VC.M.den_addi{rw}, BitVec.add_assoc, BitVec.reduceAdd]"
  "(intros; first\n" ++
  s!"  | (right; {norm}; rw [NoCompiler.Struct.Frame.isSlot_add]; decide)\n" ++
  s!"  | ({norm}; exact NoCompiler.VC.M.aligned_add' (by decide) (NoCompiler.VC.M.aligned_weaken nocompiler_hspa (by decide)) (by decide))\n" ++
  "  | skip)"

mutual
/-- Explore from state `u` at pc `p` (its fact `hF`, `hpc : u.pc = p`, `hx`, and `hsp` if `u ≠ s`). -/
partial def explore (cfg : Cfg) (g : MVarId) (u hF hpc hx : String) (hsp : Option String) (d : Nat) (p : Nat) :
    TacticM (List MVarId) := do
  let k := (p - cfg.codeBase) / 4
  let ch := cfg.ch
  let txt := s!"(
  refine NoCompiler.VC.M.SReach.of_exploreCallsOnF (f := {cfg.b}_func) (fr := {cfg.b}_frame) (cert := {cfg.b}_cert) (s0 := {cfg.sN})
    (entries := entries) (c' := {ch}.code {lit cfg.chBase}) (De := [{ch}.range {lit cfg.chBase}])
    (facts := []) (cuts := []) (ces := {cesText cfg}) (fuel := {cfg.fuel}) (k := {k})
    (p := {lit p}) (fetch := NoCompiler.VC.M.Chunk.suffix {ch})
    {cfg.b}_chunk (Dom.sub_of_ranges (by decide)) (by decide) (NoCompiler.VC.M.Chunk.suffix_eq _ {ch})
    (NoCompiler.AutoL2.contains_of_chunk (by decide) (by decide) (by decide)) nocompiler_hchk nocompiler_hL2 (by decide) nocompiler_hoff (by decide) {hpc} {hx} (by simp) {hF} ?_
  unfold NoCompiler.VC.M.exploreVCF; vc_run
  simp only [NoCompiler.VC.M.allObS, NoCompiler.VC.M.allNextI, NoCompiler.VC.M.GOb.denS, NoCompiler.VC.M.Ob.denS,
    NoCompiler.VC.M.Ob.den, List.not_mem_nil, false_imp_iff,
    and_true, true_and, List.forall_mem_cons]
  repeat' apply And.intro)"
  let gs ← runOn g txt
  let mut out := []
  for g' in gs do
    if (← endState g').isSome then
      out := out ++ (← pathEnd cfg g' u hsp d)
    else
      out := out ++ (← runOn g' (obCloser hsp))
  return out

/-- One path end from start `u`. -/
partial def pathEnd (cfg : Cfg) (g : MVarId) (_u : String) (hsp : Option String) (d : Nat) : TacticM (List MVarId) := do
  let some (S, isRet) ← endState g | return [g]
  let pc ← evalWord (← mkAppM ``NoCompiler.VC.M.SState.pc #[S])
  let rwsp := match hsp with | some h => s!", {h}" | none => ""
  let intros := "unfold NoCompiler.VC.M.PEnd.NextI\n  intro nocompiler_hcs\n  "
  if isRet then
    let sp' ← fresh cfg "nocompiler_s"
    let txt := s!"(
  {intros}intro {sp'} hm hx' hE
  have hpc' : {sp'}.pc = {lit pc} := hm.2.1
  have hinf : NoCompiler.Struct.InF {cfg.b}_func {cfg.b}_frame {cfg.b}_cert {cfg.sN} {sp'} := by
    rcases hE with h | ⟨_, hnd, _⟩ | ⟨_, hnd⟩
    · exact h
    · exact absurd (by rw [hpc']; decide) hnd
    · exact absurd (by rw [hpc']; decide) hnd
  obtain ⟨hpres, hra1⟩ := NoCompiler.VC.M.InF_ret nocompiler_hL2 hinf (by rw [hpc']; decide)
  apply NoCompiler.VC.M.CallQS.ret {cfg.heN}
  · decide
  · exact (hm.2.2.1 1).symm.trans hra1
  intro _
  refine ⟨.inl (by simpa using ({cfg.heN}).ret), .inl ⟨hx', by simp, fun r hr => by simpa using hpres r hr, by simp [{cfg.specC}]⟩⟩)"
    return ← runOn g txt
  match cfg.ces.find? (·.1 == pc) with
  | none => return [g]
  | some (_, h, cs) =>
    let ra ← symOfReg S 1
    let some raN := (match ra with | .const w => some w.toNat | _ => none) | return [g]
    let some k2 := spOff (← symOfReg S 2) | return [g]
    let dn := (d + k2) % 2 ^ 64
    let sp' ← fresh cfg "nocompiler_s"
    let sp'' ← fresh cfg "nocompiler_s"
    let hF'' ← fresh cfg "nocompiler_hF"
    let hpc'' ← fresh cfg "nocompiler_hpc"
    let hx'' ← fresh cfg "nocompiler_hx"
    let hsp'' ← fresh cfg "nocompiler_hsp"
    let txt := s!"(
  {intros}intro {sp'} hm hx' hE ht
  have hpc' : {sp'}.pc = {lit pc} := hm.2.1
  have hra : {sp'}.reg 1 = {lit raN} := by
    have := hm.2.2.1 1; simpa [NoCompiler.VC.M.SState.reg, NoCompiler.VC.M.Sym.den] using this
  have hsp' : {sp'}.reg 2 = {cfg.sN}.reg 2 + {lit dn} := by
    have := hm.2.2.1 2; simp [NoCompiler.VC.M.SState.reg, NoCompiler.VC.M.Sym.den, NoCompiler.evalI, NoCompiler.VC.M.ρOf] at this
    rw [this{rwsp}]; all_goals bv_omega
  have hci : NoCompiler.Struct.CallInfo {cfg.b}_func {cfg.b}_frame {cfg.b}_cert {cfg.sN} {sp'} := by
    rcases hE with ⟨hin, _⟩ | ⟨_, _, hci | ⟨_, htr⟩⟩ | ⟨hnc, _⟩
    · rw [hpc'] at hin; exact absurd hin (by decide)
    · exact hci
    · exfalso; apply ({cfg.heN}).ret; rw [← htr, hra]; decide
    · exact absurd (by rw [hpc']; decide) hnc
  refine NoCompiler.VC.M.CallQS.call (by rw [hpc']; decide) ?_
  have hP : ({cs}.perm () {sp'}).le (NoCompiler.l2Perm {cfg.spec} {cfg.a} {cfg.sN} {cfg.b}_frame.size) := by
    apply Perm.le_of
    · intro r hr
      simp only [Spec.perm, {cs}, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ⟨_, by simp [NoCompiler.l2Perm, {cfg.specC}], Region.within_refl _⟩
    · intro r hr
      simp only [Spec.perm, {cs}, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      refine ⟨⟨{cfg.sN}.reg 2 - BitVec.ofNat 64 {cfg.spec}.stack, {cfg.spec}.stack - {cfg.b}_frame.size⟩, by simp [NoCompiler.l2Perm], ?_⟩
      simp only [Region.within, Spec.stackRegion, Reg.sp, hsp']
      rw [show ∀ x a b c : Word, x + a - b - (x - c) = a - b + c from fun x a b c => by bv_omega]
      all_goals decide
  refine NoCompiler.VerifiedImg.callS {h} () ⟨hpc'.trans rfl, hx', by simp only [Reg.ra]; rw [hra]; decide,
    by simp only [Reg.ra]; rw [hra]; decide,
    by simp only [Reg.sp]; rw [hsp']; exact NoCompiler.VC.M.aligned_add' (by decide) nocompiler_hspa (by decide)⟩ trivial
    (Dom.sub_of_ranges (by decide)) hP ?_
  intro {sp''} hd hfr
  rcases hd with ⟨{hx''}, {hpc''}, hpres, _⟩ | ⟨hex, hoe⟩
  rotate_left
  · exact absurd hoe (by simp [{cs}])
  have {hF''} := NoCompiler.VC.M.InF_afterCall nocompiler_hwf (by decide) nocompiler_hoff hci
    ⟨{hx''}, {hpc''}, hpres, fun x hx => hfr x (fun hw => hx (NoCompiler.Struct.writable_of_le hP hw))⟩ (by rw [hra]; decide)
  have {hsp''} : {sp''}.reg 2 = {cfg.sN}.reg 2 + {lit dn} := (hpres 2 (by decide)).trans hsp'
  simp only [Reg.ra] at {hpc''}
  rw [hra] at {hpc''})"
    let gs ← runOn g txt
    match gs with
    | [gk] => explore cfg gk sp'' hF'' hpc'' hx'' (some hsp'') dn raN
    | _ => return gs
end

syntax (name := autoL2) "nocompiler_auto_l2 " ident ident ident (" calls " "[" term,* "]")? : tactic

@[tactic autoL2] def evalAutoL2 : Tactic := fun stx => do
  let fId ← realizeGlobalConstNoOverloadWithInfo stx[1]
  let sN := stx[2].getId.toString
  let heN := stx[3].getId.toString
  let b ← baseName fId
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``NoCompiler.Exec 5 do
    throwError "nocompiler_auto_l2: expected `Exec c (sp.perm a s) D Q s` (after `intro a s he hpre`)"
  let pe := t.getArg! 1
  unless pe.isAppOfArity ``NoCompiler.Spec.perm 4 do throwError "nocompiler_auto_l2: the permission is not `sp.perm a s`"
  let spE := pe.getArg! 1
  let aE := pe.getArg! 2
  let some specC := spE.getAppFn.constName? | throwError "nocompiler_auto_l2: the specification must be a constant"
  let specT := (← g.withContext do ppExpr spE).pretty
  let aT ← g.withContext do
    if aE.isFVar then return (← aE.fvarId!.getDecl).userName.toString else return (← ppExpr aE).pretty
  let (chN, chBase, codeBase) ← chunkOf b
  let entry ← evalWord (mkApp (mkConst ``NoCompiler.Struct.Func.entry) (mkConst fId))
  let len ← NoCompiler.Auto.evalNat (mkApp (mkConst ``NoCompiler.Struct.Func.len) (mkConst fId))
  let calleeStx : Array Syntax := if stx[4].isNone then #[] else stx[4][2].getSepArgs
  let mut ces : List (Nat × String × String) := []
  for c in calleeStx do
    let cT := c.reprint.getD (toString c)
    let ty ← g.withContext do instantiateMVars (← inferType (← Term.elabTerm c none))
    unless ty.isAppOfArity ``NoCompiler.VerifiedImg 5 do throwError "nocompiler_auto_l2: {cT} is not a VerifiedImg"
    let e ← evalWord (ty.getArg! 3)
    let some cs := (ty.getArg! 4).getAppFn.constName? | throwError "nocompiler_auto_l2: callee spec"
    ces := ces ++ [(e, cT, cs.toString)]
  let n ← IO.mkRef 0
  let cfg : Cfg := Cfg.mk b specT specC.toString aT sN heN chN.toString chBase codeBase entry ces (len + 2) n
  let setup := s!"(
  have nocompiler_hlev : {b}_level := by unfold {b}_level; decide +kernel
  have nocompiler_hL2 := NoCompiler.Struct.checkL2_of_level nocompiler_hlev
  have nocompiler_hchk := NoCompiler.Struct.check_of_level nocompiler_hlev (by decide)
  have nocompiler_hwf := NoCompiler.Struct.checkL2_wf nocompiler_hL2
  have nocompiler_hspa : NoCompiler.aligned ({sN}.reg 2) 16 := ({heN}).sp
  refine NoCompiler.Exec.ofS (fr := {b}_frame) (Ps := NoCompiler.l2Perm {specT} {aT} {sN} {b}_frame.size)
    (NoCompiler.l2Perm_le (by decide) (by decide)) ?_
  have nocompiler_hoff := NoCompiler.l2Perm_slotsOff (sp := {specT}) (a := {aT}) (s := {sN}) (fr := {b}_frame)
    nocompiler_hwf (by decide) (by decide) (by simp [{specC}])
  unfold NoCompiler.Struct.SExec)"
  let [g1] ← runOn g setup | throwError "nocompiler_auto_l2: setup"
  let left ← explore cfg g1 sN s!"(NoCompiler.VC.M.InF_entry nocompiler_hL2 ({heN}).pc (by decide))"
    s!"({heN}).pc" s!"({heN}).live" none 0 entry
  replaceMainGoal left

end NoCompiler.AutoL2

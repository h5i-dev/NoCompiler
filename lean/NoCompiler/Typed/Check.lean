import NoCompiler.Typed.ArithExt

/-
The type checker, part 2: the rules for each instruction, frames, returns, the whole function.
-/
namespace NoCompiler.Typed

namespace Fn
variable (f : Fn)

/-- The type after a register-writing instruction other than a load. -/
def arith (S : STy) (i : Instr) : Option STy :=
  let x := f.freshAt S
  let r := S.reg
  match i with
  | .lui rd imm => some (S.setReg rd (some (.lit (imm.toInt * 4096))))
  | .iop .addi rd rs imm =>
    some (match r rs with
      | some e => S.setReg rd (some (e.add (.lit imm.toInt)))
      | none => anyWord S rd x)
  | .rop .add rd a b =>
    some (match r a, r b with
      | some e1, some e2 => S.setReg rd (some (e1.add e2))
      | _, _ => anyWord S rd x)
  | .rop .sub rd a b =>
    some (match r a, r b with
      | some e1, some e2 => S.setReg rd (some (e1.sub e2))
      | _, _ => anyWord S rd x)
  | .shift .slli rd rs sh =>
    some (match r rs with
      | some e => S.setReg rd (some (e.smul (2 ^ sh.toNat)))
      | none => anyWord S rd x)
  | .rop .sh1add rd a b | .rop .sh2add rd a b | .rop .sh3add rd a b =>
    let n : Nat := match i with | .rop .sh1add .. => 1 | .rop .sh2add .. => 2 | _ => 3
    some (match r a, r b with
      | some e1, some e2 => S.setReg rd (some ((e1.smul (2 ^ n)).add e2))
      | _, _ => anyWord S rd x)
  | .rop .mul rd a b =>
    some (match r a, r b with
      | some e1, some ⟨c, []⟩ => S.setReg rd (some (e1.smul c))
      | some ⟨c, []⟩, some e2 => S.setReg rd (some (e2.smul c))
      | _, _ => anyWord S rd x)
  | .iop .andi rd rs imm =>
    if 0 ≤ imm.toInt then
      -- with a mask `c = 2^k − 1`, also `e ≡ x (mod 2^k)` (the note's table)
      let mask : List Constr :=
        match r rs with
        | some e =>
          match (List.range 13).find? (fun k => imm.toInt == 2 ^ k - 1) with
          | some k => [.dvd (2 ^ k) (e.sub (.var x))]
          | none => []
        | none => []
      some ((S.setReg rd (some (.var x))).addFacts
        ([.le (.lit 0) (.var x), .le (.var x) (.lit imm.toInt)] ++ mask))
    else some (anyWord S rd x)
  | .shift .srli rd rs sh =>
    match r rs with
    | some e =>
      let (u, fs) := urep S (x + 2) e
      some ((S.setReg rd (some (.var x))).addFacts (fs ++
        [.eq u (((IExpr.var x).smul (2 ^ sh.toNat)).add (.var (x + 1))),
         .le (.lit 0) (.var (x + 1)), .lt (.var (x + 1)) (.lit (2 ^ sh.toNat)),
         .le (.lit 0) (.var x)]))
    | none => some (anyWord S rd x)
  -- 32-bit addition and subtraction: the sign-extended low word `x` (the note's table)
  | .addiw rd rs imm =>
    some (match r rs with
      | some e => word32 S rd x (e.add (.lit imm.toInt))
      | none => anyWord S rd x)
  | .rwop .addw rd a b =>
    some (match r a, r b with
      | some e1, some e2 => word32 S rd x (e1.add e2)
      | _, _ => anyWord S rd x)
  | .rwop .subw rd a b =>
    some (match r a, r b with
      | some e1, some e2 => word32 S rd x (e1.sub e2)
      | _, _ => anyWord S rd x)
  -- every other instruction: the rules of ArithExt.lean (by default a fresh word)
  | _ => f.arithExt S i

def ldWidth : LdOp → Nat := LdOp.width

/-- The range of a loaded value (sign or zero extension). -/
def ldRange (x : Var) : LdOp → List Constr
  | .lbu => [.le (.lit 0) (.var x), .lt (.var x) (.lit 256)]
  | .lhu => [.le (.lit 0) (.var x), .lt (.var x) (.lit 65536)]
  | .lwu => [.le (.lit 0) (.var x), .lt (.var x) (.lit (2 ^ 32))]
  | .ld => [.le (.lit 0) (.var x), .lt (.var x) (.lit (2 ^ 64))]
  | .lb => [.le (.lit (-128)) (.var x), .lt (.var x) (.lit 128)]
  | .lh => [.le (.lit (-32768)) (.var x), .lt (.var x) (.lit 32768)]
  | .lw => [.le (.lit (-2 ^ 31)) (.var x), .lt (.var x) (.lit (2 ^ 31))]

/-- The access `[a, a + w)` lies in the capability and is aligned. -/
def inCap (S : STy) (a : IExpr) (w : Nat) (c : HCap) (needRw : Bool) : Bool :=
  match c.cap.kind with
  | .bytes b =>
    (!needRw || b.mode == .rw) && S.ent c.cap.guard &&
    S.ent (.and (.le b.base a) (.and (.le (a.add (.lit w)) (b.base.add b.len)) (.dvd w a)))
  | .token _ => false

/-- The constant offset of `a` from the capability's start, when Ψ fixes it. -/
def constOff (a base : IExpr) : Option Nat :=
  match (a.sub base).toLin with
  | ⟨c, []⟩ => if 0 ≤ c then some c.toNat else none
  | _ => none

/-- The address of an access `off(rs)` of `w` bytes and the capability it lies in: first as
    `e_rs + off`; failing that, as its unsigned representative `u(e_rs + off)` (I20), whose
    facts are added to the type. -/
def addr (S : STy) (rs : Reg) (off : BitVec 12) (w : Nat) (needRw : Bool) :
    Option (STy × IExpr × HCap) := do
  let e ← S.reg rs
  let a := e.add (.lit off.toInt)
  match S.caps.find? (fun c => inCap S a w c needRw) with
  | some c => pure (S, a, c)
  | none =>
    let (u, fs) := urep S (f.freshAt S) a
    let S1 := S.addFacts fs
    let c ← S1.caps.find? (fun c => inCap S1 u w c needRw)
    pure (S1, u, c)

def load (S : STy) (op : LdOp) (rd rs : Reg) (off : BitVec 12) : Option STy := do
  let (S1, a, c) ← f.addr S rs off op.width false
  let x := f.freshAt S1
  let fieldTy : Option IExpr :=
    match op, c.cap.kind with
    | .ld, .bytes b => (constOff a b.base).bind fun k => (b.fields.find? (·.off == k)).map (·.ty)
    | _, _ => none
  match fieldTy with
  | some t => pure (S1.setReg rd (some t))
  | none => pure ((S1.setReg rd (some (.var x))).addFacts (ldRange x op))

/-- Fields of `b` that the store to `[a, a + w)` may change are dropped; an 8-byte store at
    a constant offset replaces the field there. -/
def storeFields (S : STy) (b : BytesCap) (a : IExpr) (w : Nat) (v : Option IExpr) : List Field :=
  let keep := b.fields.filter fun g =>
    S.ent (.or (.le (a.add (.lit w)) (b.base.add (.lit g.off)))
               (.le ((b.base.add (.lit g.off)).add (.lit 8)) a))
  match w, constOff a b.base, v with
  | 8, some k, some t => ⟨k, t⟩ :: keep.filter (·.off != k)
  | _, _, _ => keep

def store (S : STy) (op : StOp) (rs1 rs2 : Reg) (off : BitVec 12) : Option STy := do
  let (S1, a, c) ← f.addr S rs1 off op.width true
  match c.cap.kind with
  | .bytes b =>
    let b' := { b with fields := storeFields S1 b a op.width (S1.reg rs2) }
    pure { S1 with caps := S1.caps.map fun d =>
      if d.id == c.id then { d with cap := { d.cap with kind := .bytes b' } } else d }
  | .token _ => none

/-- Branch facts on the taken and fall-through edges. -/
def branchFacts (S : STy) (op : BrOp) (e1 e2 : IExpr) : List Constr × List Constr :=
  let x := f.freshAt S
  match op with
  | .beq => ([Constr.eqMod e1 e2], [.not (Constr.eqMod e1 e2)])
  | .bne => ([.not (Constr.eqMod e1 e2)], [Constr.eqMod e1 e2])
  | .bltu | .bgeu =>
    let (u1, f1) := urep S x e1
    let (u2, f2) := urep S (x + 1) e2
    let lt := Constr.lt u1 u2
    let ge := Constr.le u2 u1
    if op == .bltu then (f1 ++ f2 ++ [lt], f1 ++ f2 ++ [ge]) else (f1 ++ f2 ++ [ge], f1 ++ f2 ++ [lt])
  | .blt | .bge =>
    let (u1, f1) := srep S x e1
    let (u2, f2) := srep S (x + 1) e2
    let lt := Constr.lt u1 u2
    let ge := Constr.le u2 u1
    if op == .blt then (f1 ++ f2 ++ [lt], f1 ++ f2 ++ [ge]) else (f1 ++ f2 ++ [ge], f1 ++ f2 ++ [lt])

/-- The target of a jump or branch at `k` with byte offset `off`. -/
def target (k : Nat) (off : Int) : Option Nat :=
  if off % 4 = 0 && 0 ≤ (k : Int) + off / 4 then some ((k : Int) + off / 4).toNat else none

/-- The return check, under an instantiation of the `out` variables. -/
def retOk (S : STy) (θ : Subst) : Bool :=
  let σ := f.sig
  keptRegs.all (fun r => match S.reg r, f.regVar.lookup r with
    | some e, some x => S.entEqMod e (.var x)
    | _, _ => false) &&
  θ.all (fun p => σ.outVars.contains p.1) &&
  S.sub θ { regs := σ.outRegs, facts := [σ.post] } &&
  σ.borrow.zipIdx.all fun (b, i) =>
    S.caps.any fun c => c.origin == some i && S.capSub θ c { id := c.id, origin := some i, cap := b.exitCap }

/-- The return check. -/
def ret (S : STy) : Bool :=
  f.retOk S (S.instantiate { regs := f.sig.outRegs, facts := [f.sig.post] } f.sig.outVars)

def branchOk (k : Nat) (S : STy) (op : BrOp) (rs1 rs2 : Reg) (off : BitVec 13) : Bool :=
  match target k off.toInt with
  | none => false
  | some k' =>
    match S.reg rs1, S.reg rs2 with
    | some e1, some e2 =>
      f.edge (some k) (S.addFacts (f.branchFacts S op e1 e2).1) k' &&
        f.edge (some k) (S.addFacts (f.branchFacts S op e1 e2).2) (k + 1)
    | _, _ => f.edge (some k) S k' && f.edge (some k) S (k + 1)

def jalOk (k : Nat) (S : STy) (off : BitVec 21) : Bool :=
  match target k off.toInt with
  | some k' => f.edge (some k) S k'
  | none => false

def loadOk (k : Nat) (S : STy) (op : LdOp) (rd rs : Reg) (off : BitVec 12) : Bool :=
  rd != 2 && match f.load S op rd rs off with
    | some S' => f.edge (some k) S' (k + 1)
    | none => false

def storeOk (k : Nat) (S : STy) (op : StOp) (rs1 rs2 : Reg) (off : BitVec 12) : Bool :=
  match f.store S op rs1 rs2 off with
  | some S' => f.edge (some k) S' (k + 1)
  | none => false

/-- A register write; `sp` is written only by the frame rules (not yet supported). -/
def arithOk (k : Nat) (S : STy) (i : Instr) : Bool :=
  match writesReg i with
  | some rd => rd != 2 && match f.arith S i with
    | some S' => f.edge (some k) S' (k + 1)
    | none => false
  | none => false

/-- Check instruction `k`, decoded as `i`, at a point of type `S`. -/
def instrAt (k : Nat) (S : STy) : Instr → Bool
  | .branch op rs1 rs2 off => f.branchOk k S op rs1 rs2 off
  | .jal rd off => rd == 0 && f.jalOk k S off
  | .jalr rd rs1 off => rd == 0 && rs1 == 1 && off == 0 && f.ret S
  | .load op rd rs off => f.loadOk k S op rd rs off
  | .store op rs1 rs2 off => f.storeOk k S op rs1 rs2 off
  | .ecall => false
  | .unimp => false
  | .lui rd imm => f.arithOk k S (.lui rd imm)
  | .auipc rd imm => f.arithOk k S (.auipc rd imm)
  | .iop op rd rs imm => f.arithOk k S (.iop op rd rs imm)
  | .addiw rd rs imm => f.arithOk k S (.addiw rd rs imm)
  | .shift op rd rs sh => f.arithOk k S (.shift op rd rs sh)
  | .shiftw op rd rs sh => f.arithOk k S (.shiftw op rd rs sh)
  | .rop op rd a b => f.arithOk k S (.rop op rd a b)
  | .rwop op rd a b => f.arithOk k S (.rwop op rd a b)
  | .uop op rd a => f.arithOk k S (.uop op rd a)

/-- Check instruction `k` of the image. -/
def instr (c : Code) (k : Nat) : Bool :=
  match f.tyAt k, c.instr (f.pcOf k) with
  | some S, some i => f.instrAt k S i
  | _, _ => false

/-- The structural conditions: loops nested, variables apart. -/
def structOk : Bool :=
  let σ := f.sig
  σ.take.isEmpty && σ.give.isEmpty && σ.stack == 0 &&
  σ.borrow.all (fun b => match b.cap.kind with | .bytes _ => b.cap.guard == .tt | .token _ => false) &&
  (keptRegs.all fun r => (f.regVar.lookup r).isSome) &&
  (f.protectedVars.Nodup) &&
  ((List.range f.sig.borrow.length).map f.entryId).Nodup &&
  (f.protectedVars.all (· < f.fresh)) &&
  (f.loops.all fun L => L.head ≤ L.last && L.last < f.size &&
     L.vars.all (fun x => x < f.fresh && !f.protectedVars.contains x) &&
     L.meas.vars.all (· < f.fresh)) &&
  decide ((f.loops.map (·.head)).Pairwise (· < ·)) &&
  decide (f.entry.toNat % 4 = 0) && decide (4 * f.size < 2 ^ 64) &&
  (f.loops.all fun K => f.loops.all fun L =>
    K.head == L.head || L.last < K.head || K.last < L.head ||
    (K.head < L.head && L.last ≤ K.last) || (L.head < K.head && K.last ≤ L.last)) &&
  -- the signature mentions parameters on entry and parameters and `out` variables on exit
  (σ.inRegs.all fun p => p.2.vars.all σ.params.contains) &&
  (σ.pre.vars.all σ.params.contains) &&
  (σ.borrow.all fun b => b.cap.guard.vars.all σ.params.contains &&
    match b.cap.kind with
    | .bytes x => (x.base.vars ++ x.len.vars ++ x.fields.flatMap (·.ty.vars)).all σ.params.contains &&
        (b.outFields.flatMap (·.ty.vars)).all (fun y => σ.params.contains y || σ.outVars.contains y)
    | .token _ => true) &&
  (σ.outRegs.all fun p => p.2.vars.all (fun y => σ.params.contains y || σ.outVars.contains y)) &&
  (σ.post.vars.all (fun y => σ.params.contains y || σ.outVars.contains y)) &&
  (σ.outVars.all fun y => !f.protectedVars.contains y) && σ.outVars.Nodup

/-- The whole function. -/
def check (c : Code) : Bool :=
  f.structOk && f.edge none f.initTy 0 && (List.range f.size).all (f.instr c)

end Fn

end NoCompiler.Typed

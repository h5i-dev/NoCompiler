import NoCompiler.Typed.Ecall

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
    else f.arithExt S i
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

/-- Held capabilities for the `give` clauses: each one exclusive, not the one returned for a
    borrow, distinct from the others (`used`), and covering the given one. -/
def giveFrom (S : STy) (θ : Subst) : List Cap → List Nat → Option (List HCap)
  | [], _ => some []
  | gc :: gs, used =>
    match S.caps.find? (fun c => !used.contains c.id && !(c.origin.any (· < f.sig.borrow.length)) &&
        c.cap.exclusive && S.capSub θ c { id := c.id, origin := c.origin, cap := gc }) with
    | none => none
    | some c => (giveFrom S θ gs (c.id :: used)).map (c :: ·)

/-- The return check, under an instantiation of the `out` variables. -/
def retOkOn (rs : List Reg) (S : STy) (θ : Subst) : Bool :=
  let σ := f.sig
  rs.all (fun r => match S.reg r, f.regVar.lookup r with
    | some e, some x => S.entEqMod e (.var x)
    | _, _ => false) &&
  θ.all (fun p => σ.outVars.contains p.1) &&
  S.sub θ { regs := σ.outRegs, facts := [σ.post] } &&
  (σ.give.isEmpty || (decide (S.depth = 0) && (f.giveFrom S θ σ.give []).isSome)) &&
  σ.borrow.zipIdx.all fun (b, i) =>
    S.caps.any fun c => c.origin == some i && S.capSub θ c { id := c.id, origin := some i, cap := b.exitCap }

/-- The return check. -/
def retOk (S : STy) (θ : Subst) : Bool := f.retOkOn keptRegs S θ

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

/-- The frame slot of an access `off(sp)` inside the frame, if it is one. -/
def slotAt (S : STy) (rs : Reg) (off : BitVec 12) : Option Nat :=
  match f.frame with
  | some F =>
    if rs == 2 && S.depth == F.size && F.size != 0 && 0 ≤ off.toInt && F.slots.contains off.toInt.toNat
    then some off.toInt.toNat else none
  | none => none

def loadOk (k : Nat) (S : STy) (op : LdOp) (rd rs : Reg) (off : BitVec 12) : Bool :=
  rd != 2 && match op, f.slotAt S rs off with
    | .ld, some j => f.edge (some k) (S.setReg rd (S.slots.lookup j)) (k + 1)
    | _, _ => match f.load S op rd rs off with
      | some S' => f.edge (some k) S' (k + 1)
      | none => false

def storeOk (k : Nat) (S : STy) (op : StOp) (rs1 rs2 : Reg) (off : BitVec 12) : Bool :=
  match op, f.slotAt S rs1 off with
  | .sd, some j =>
    f.edge (some k) { S with slots := (match S.reg rs2 with
      | some e => [(j, e)]
      | none => []) ++ S.slots.filter (·.1 != j) } (k + 1)
  | _, _ => match f.store S op rs1 rs2 off with
    | some S' => f.edge (some k) S' (k + 1)
    | none => false

/-- The prologue (Lemma 7 a): `sp` down by the frame size, a `rw` capability per
    address-taken range, with identities from the record at the next point when it has new
    ones. -/
def framePushNew (k : Nat) (S : STy) (F : Frame) (e : IExpr) : List HCap :=
  let newIds := match f.tyAt (k + 1) with
    | some S' => (S'.caps.filter (fun (c : HCap) => !S.caps.any (fun d => d.id == c.id))).map (fun (c : HCap) => c.id)
    | none => []
  let base := S.caps.foldr (fun (c : HCap) m => max (c.id + 1) m) 0
  F.addr.zipIdx.map fun (r, j) =>
    { id := newIds.getD j (base + j), origin := none,
      cap := { kind := .bytes { base := e.add (.lit ((r.1 : Int) - F.size)), len := .lit r.2,
                                mode := .rw } } }

def framePush (k : Nat) (S : STy) (F : Frame) (e : IExpr) : STy :=
  { S with
    regs := (2, e.add (.lit (-(F.size : Int)))) :: S.regs.filter (·.1 != 2)
    depth := F.size
    slots := []
    caps := S.caps ++ f.framePushNew k S F e }

/-- The capabilities the epilogue needs back: one per address-taken range, exactly. -/
def framePopCaps (S : STy) (F : Frame) (e : IExpr) : Option (List HCap) :=
  F.addr.mapM fun (o, l) => S.caps.find? fun c =>
    c.origin == none && c.cap.guard == .tt &&
    match c.cap.kind with
    | .bytes b => b.mode == .rw && S.ent (.eq b.base (e.add (.lit o))) && S.ent (.eq b.len (.lit l))
    | .token _ => false

/-- The epilogue (Lemma 7 b): the frame's capabilities and slots are dropped, `sp` back. -/
def framePop (S : STy) (F : Frame) (e : IExpr) (cs : List HCap) : STy :=
  { S with
    regs := (2, e.add (.lit F.size)) :: S.regs.filter (·.1 != 2)
    depth := 0
    slots := []
    caps := S.caps.filter fun c => !cs.any (·.id == c.id) }

def frameOk (k : Nat) (S : STy) (op : IOp) (rs : Reg) (imm : BitVec 12) : Bool :=
  op == .addi && rs == 2 &&
  match f.frame, S.reg 2 with
  | some F, some e =>
    if S.depth == 0 && F.size != 0 && imm.toInt == -(F.size : Int) then
      ((f.framePush k S F e).caps.map (·.id)).Nodup &&
      S.ent (.le (.lit F.size) e) && S.ent (.lt e (.lit (2 ^ 64))) &&
      f.edge (some k) (f.framePush k S F e) (k + 1)
    else if S.depth == F.size && F.size != 0 && imm.toInt == (F.size : Int) then
      match framePopCaps S F e with
      | some cs => (cs.map (·.id)).Nodup && f.edge (some k) (framePop S F e cs) (k + 1)
      | none => false
    else false
  | _, _ => false

/-- A register write; `sp` is written only by the frame rules (not yet supported). -/
def arithOk (k : Nat) (S : STy) (i : Instr) : Bool :=
  match writesReg i with
  | some rd => rd != 2 && match f.arith S i with
    | some S' => f.edge (some k) S' (k + 1)
    | none => false
  | none => false

/-! ### Calls (the note's 呼出し rule, Lemma 8) -/

/-- A constant the entry constraint fixes `y` to (a conjunct `y = c`), e.g. a static data
    symbol's linked address (I30/I32). -/
def pinned (y : Var) : Constr → Option Int
  | .eq a b =>
    if a.asVar == some y && b.terms.isEmpty then some b.const
    else if b.asVar == some y && a.terms.isEmpty then some a.const
    else none
  | .and p q => (pinned y p).orElse fun _ => pinned y q
  | _ => none

/-- The callee's parameters from the registers its `in` clause types by a bare parameter, or
    from its entry constraint when that fixes them. (Untrusted: the call rule checks the
    entry constraint under the result.) -/
def callInst (S : STy) (g : Sig) : Option Subst :=
  g.params.mapM fun y =>
    match g.inRegs.find? (fun p => p.2.asVar == some y) with
    | some (r, _) => (S.reg r).map fun e => (y, e)
    | none => (pinned y g.pre).map fun c => (y, IExpr.lit c)

/-- The held capability a `borrow` clause is lent from: a byte capability, `rw` for a `rw`
    clause, whose range contains the clause's range of nonnegative length. -/
def lendFrom (S : STy) (b : BytesCap) : Option HCap :=
  S.caps.find? fun c =>
    S.ent c.cap.guard &&
    match c.cap.kind with
    | .bytes h => (b.mode == .ro || h.mode == .rw) &&
        S.ent (.and (.le h.base b.base) (.and (.le (b.base.add b.len) (h.base.add h.len))
          (.le (.lit 0) b.len)))
    | .token _ => false

/-- The clause's fields (its offsets, types in the callee's parameters) are fields of the held
    capability at the same address with an equal type, inside the lent length (I33.1). -/
def fieldsLent (S : STy) (θ : Subst) (b : BytesCap) (c : HCap) : Bool :=
  b.fields.all fun fl =>
    S.ent (.le (.lit ((fl.off : Int) + 8)) b.len) &&
    match c.cap.kind with
    | .bytes h => h.fields.any fun fh =>
        S.ent (.eq (h.base.add (.lit (fh.off : Int))) (b.base.add (.lit (fl.off : Int)))) &&
        S.entEqMod fh.ty (fl.ty.subst θ)
    | .token _ => false

/-- The callee's `borrow` and `take` clauses (instantiated) and the held capabilities they
    are lent from. -/
def lends (S : STy) (g : Sig) (θ : Subst) : Option (List (BytesCap × HCap)) :=
  g.entryCaps.mapM fun c =>
    match c.kind with
    | .bytes x =>
      let x' : BytesCap := { x with base := x.base.subst θ, len := x.len.subst θ }
      (lendFrom S x').bind fun c => if fieldsLent S θ x' c then some (x', c) else none
    | .token _ => none

/-- Two clauses lent from the same capability do not overlap if either is `rw`. -/
def lendsApart (S : STy) (ls : List (BytesCap × HCap)) : Bool :=
  ls.zipIdx.all fun (p, i) => ls.zipIdx.all fun (q, j) =>
    i == j || p.2.id != q.2.id || (p.1.mode == .ro && q.1.mode == .ro) ||
    S.ent (.or (.le (p.1.base.add p.1.len) q.1.base) (.le (q.1.base.add q.1.len) p.1.base))

/-- A capability lent `rw` to a callee: its per-field facts are dropped (the callee may
    have written the bytes). -/
def clearLent (ls : List (BytesCap × HCap)) (c : HCap) : HCap :=
  if ls.any (fun p => p.2.id == c.id && p.1.mode == .rw) then
    match c.cap.kind with
    | .bytes h => { c with cap := { c.cap with kind := .bytes { h with fields := [] } } }
    | .token _ => c
  else c

/-- The held capabilities `take` clauses are lent from: the callee keeps them. -/
def takenIds (g : Sig) (ls : List (BytesCap × HCap)) : List Nat :=
  (ls.drop g.borrow.length).map (·.2.id)

/-- Identities for the capabilities a callee gives, from the record at `k + 1`. -/
def callIds (k : Nat) (S : STy) : List Nat :=
  match f.tyAt (k + 1) with
  | some S' => (S'.caps.filter (fun (c : HCap) => !S.caps.any (fun d => d.id == c.id))).map (·.id)
  | none => []

/-- The type after the call returns: preserved registers kept, the `out` registers with the
    callee's `out` variables renamed to fresh ones, its exit constraint, the fields of
    capabilities lent `rw` forgotten. -/
def afterCall (S : STy) (g : Sig) (θ : Subst) (ls : List (BytesCap × HCap)) (ids : List Nat) : STy :=
  let x := f.freshAt S
  let ρ := θ ++ g.outVars.zipIdx.map fun (p : Var × Nat) => (p.1, IExpr.var (x + p.2))
  let base := S.caps.foldr (fun (c : HCap) m => max (c.id + 1) m) 0
  { S with
    regs := S.regs.filter (fun p => preservedRegs.contains p.1) ++
      g.outRegs.map fun p => (p.1, p.2.subst ρ)
    facts := g.post.subst ρ :: S.facts
    caps := (S.caps.filter (fun c => !(takenIds g ls).contains c.id)).map (clearLent ls) ++
      g.give.zipIdx.map fun (p : Cap × Nat) =>
        { id := ids.getD p.2 (base + p.2), origin := none, cap := p.1.subst ρ } }

/-- A call from point `k` of the callee at `t` (in the table), returning to `k + 1`. -/
def callAt (k : Nat) (S : STy) (t : Word) : Bool :=
  match f.callees.lookup t with
  | none => false
  | some g =>
    match callInst S g with
    | none => false
    | some θ =>
      (g.inRegs.all fun p => match S.reg p.1 with
        | some e => S.entEqMod e (p.2.subst θ)
        | none => false) &&
      S.ent (g.pre.subst θ) &&
      decide (S.depth + g.stack ≤ f.sig.stack) &&
      match lends S g θ with
      | none => false
      | some ls =>
        let S' := f.afterCall S g θ ls (f.callIds k S)
        lendsApart S ls && (ls.drop g.borrow.length).all (·.2.cap.exclusive) &&
        decide ((S'.caps.map (·.id)).Nodup) && f.edge (some k) S' (k + 1)

/-- `jal ra, off` to a callee in the table. -/
def callOk (k : Nat) (S : STy) (off : BitVec 21) : Bool := f.callAt k S (f.pcOf k + off.signExtend 64)

/-- `jalr ra, off(rs)` with `rs` holding a known constant: clang's `call f`, the pair
    `auipc t, %pcrel_hi(f)` + `jalr ra, %pcrel_lo(f)(t)` (I21), with `auipcOk`'s exact rule. -/
def callRegOk (k : Nat) (S : STy) (rs : Reg) (off : BitVec 12) : Bool :=
  match S.reg rs with
  | some e => e.terms.isEmpty && f.callAt k S ((BitVec.ofInt 64 e.const + off.signExtend 64) &&& ~~~1)
  | none => false

/-- A tail call of the callee at `t` (I21 `tail`, 健全性の証明 末尾呼出し): the call's check, at
    depth 0 with `ra` still the entry's, and the type after the callee returns passes this
    function's return check (without `ra`: the callee returned through it). -/
def tailAt (S : STy) (t : Word) : Bool :=
  match f.callees.lookup t with
  | none => false
  | some g =>
    match callInst S g with
    | none => false
    | some θ =>
      (g.inRegs.all fun p => match S.reg p.1 with
        | some e => S.entEqMod e (p.2.subst θ)
        | none => false) &&
      S.ent (g.pre.subst θ) &&
      decide (S.depth = 0) && decide (g.stack ≤ f.sig.stack) &&
      (match S.reg 1, f.regVar.lookup 1 with
        | some e, some x => S.entEqMod e (.var x)
        | _, _ => false) &&
      match lends S g θ with
      | none => false
      | some ls =>
        let S' := f.afterCall S g θ ls []
        lendsApart S ls && (ls.drop g.borrow.length).all (·.2.cap.exclusive) &&
        decide ((S'.caps.map (·.id)).Nodup) &&
        f.retOkOn preservedRegs S'
          (S'.instantiate { regs := f.sig.outRegs, facts := [f.sig.post] } f.sig.outVars)

/-- `jalr zero, off(rs)` with `rs` a known constant: clang's `tail f`. -/
def tailRegOk (S : STy) (rs : Reg) (off : BitVec 12) : Bool :=
  match S.reg rs with
  | some e => e.terms.isEmpty && f.tailAt S ((BitVec.ofInt 64 e.const + off.signExtend 64) &&& ~~~1)
  | none => false

/-- `auipc rd, imm`: the address is known, since the checked image fixes where point `k` is. -/
def auipcOk (k : Nat) (S : STy) (rd : Reg) (imm : BitVec 20) : Bool :=
  rd != 2 && f.edge (some k)
    (S.setReg rd (some (.lit ((f.pcOf k + (imm.setWidth 32 <<< 12).signExtend 64).toNat : Int)))) (k + 1)

/-- Check instruction `k`, decoded as `i`, at a point of type `S`. -/
def instrAt (k : Nat) (S : STy) : Instr → Bool
  | .branch op rs1 rs2 off => f.branchOk k S op rs1 rs2 off
  | .jal rd off => if rd == 1 then f.callOk k S off else rd == 0 && f.jalOk k S off
  | .jalr rd rs1 off =>
    if rd == 1 then f.callRegOk k S rs1 off
    else rd == 0 && ((rs1 == 1 && off == 0 && f.ret S) || f.tailRegOk S rs1 off)
  | .load op rd rs off => f.loadOk k S op rd rs off
  | .store op rs1 rs2 off => f.storeOk k S op rs1 rs2 off
  | .ecall => f.ecallOk k S
  | .unimp => false
  | .lui rd imm => f.arithOk k S (.lui rd imm)
  | .auipc rd imm => f.auipcOk k S rd imm
  | .iop op rd rs imm => if rd == 2 then f.frameOk k S op rs imm else f.arithOk k S (.iop op rd rs imm)
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

/-- The frame fits the stack; its slots and ranges lie inside it and apart (S4). -/
def frameDeclOk : Bool :=
  match f.frame with
  | none => true
  | some F =>
    F.size % 16 == 0 && F.size ≤ f.sig.stack && F.slots.Nodup &&
    F.slots.all (fun j => j % 8 == 0 && j + 8 ≤ F.size) &&
    F.addr.all (fun r => r.1 + r.2 ≤ F.size) &&
    (F.slots.map (fun j => (j, 8)) ++ F.addr).zipIdx.all fun (r, i) =>
      (F.slots.map (fun j => (j, 8)) ++ F.addr).zipIdx.all fun (q, j) =>
        i == j || r.1 + r.2 ≤ q.1 || q.1 + q.2 ≤ r.1

/-- A signature mentions parameters on entry and parameters and `out` variables on exit. -/
def Sig.scoped (σ : Sig) : Bool :=
  (σ.inRegs.all fun p => p.2.vars.all σ.params.contains) &&
  (σ.pre.vars.all σ.params.contains) &&
  (σ.borrow.all fun b => b.cap.guard.vars.all σ.params.contains &&
    match b.cap.kind with
    | .bytes x => (x.base.vars ++ x.len.vars ++ x.fields.flatMap (·.ty.vars)).all σ.params.contains &&
        (b.outFields.flatMap (·.ty.vars)).all (fun y => σ.params.contains y || σ.outVars.contains y)
    | .token _ => true) &&
  (σ.outRegs.all fun p => p.2.vars.all (fun y => σ.params.contains y || σ.outVars.contains y)) &&
  (σ.post.vars.all (fun y => σ.params.contains y || σ.outVars.contains y)) &&
  σ.outVars.Nodup && (σ.outVars.all fun y => !σ.params.contains y)

/-- What the call rule needs of a callee's signature (v0 of the Lean checker): byte
    capabilities without entry fields, no take/give/tokens, `out` registers caller-saved. -/
def calleeOk (g : Sig) : Bool :=
  Sig.scoped g && g.params.Nodup &&
  (g.entryCaps.all fun c => c.guard == .tt &&
    match c.kind with | .bytes _ => true | .token _ => false) &&
  (g.inRegs.all fun p => p.1 != 1) &&
  (g.outRegs.all fun p => !preservedRegs.contains p.1) &&
  (g.take.all fun c => c.vars.all g.params.contains) &&
  (g.give.all fun c => (match c.kind with | .bytes x => x.fields.isEmpty | .token _ => false) &&
    c.vars.all (fun y => g.params.contains y || g.outVars.contains y))

/-- The structural conditions: loops nested, variables apart. -/
def structOk : Bool :=
  let σ := f.sig
  σ.take.all (fun c => (match c.kind with | .bytes _ => true | .token _ => false) &&
    c.vars.all σ.params.contains) &&
  σ.give.all (fun c => (match c.kind with | .bytes _ => true | .token _ => false) && c.exclusive &&
    c.vars.all (fun y => σ.params.contains y || σ.outVars.contains y)) &&
  (f.callees.all fun p => calleeOk p.2) &&
  f.frameDeclOk &&
  σ.borrow.all (fun b => match b.cap.kind with | .bytes _ => b.cap.guard == .tt | .token _ => false) &&
  (keptRegs.all fun r => (f.regVar.lookup r).isSome) &&
  (f.protectedVars.Nodup) &&
  ((List.range f.sig.entryCaps.length).map f.entryId).Nodup &&
  (f.protectedVars.all (· < f.fresh)) &&
  -- τ: none (address order) or a permutation of the points (I36)
  (f.tau.isEmpty || (f.tau.length == f.size && (List.range f.size).all f.tau.contains)) &&
  (f.loops.all fun L => f.pos L.head ≤ f.pos L.last && L.last < f.size &&
     L.vars.all (fun x => x < f.fresh && !f.protectedVars.contains x) &&
     L.meas.vars.all (· < f.fresh)) &&
  decide ((f.loops.map (f.pos ·.head)).Pairwise (· < ·)) &&
  decide (f.entry.toNat % 4 = 0) && decide (4 * f.size < 2 ^ 64) &&
  (f.loops.all fun K => f.loops.all fun L =>
    K.head == L.head || f.pos L.last < f.pos K.head || f.pos K.last < f.pos L.head ||
    (f.pos K.head < f.pos L.head && f.pos L.last ≤ f.pos K.last) ||
    (f.pos L.head < f.pos K.head && f.pos K.last ≤ f.pos L.last)) &&
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

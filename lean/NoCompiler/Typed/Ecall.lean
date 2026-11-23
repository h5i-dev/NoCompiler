import NoCompiler.Typed.ArithExt
import NoCompiler.Env

/-
The `ecall` rule (syscalls, Lemma 9 of 健全性の証明.md; signatures I17, I31). Proved in
NoCompiler/Typed/Sound/Ecall.lean (`Fn.ecall_step`), which the main induction uses.

Owned by agent U (STATUS.md). `a7` must be a known constant (`int(c)`); the environment
(NoCompiler/Env.lean) admits four syscalls:

* `exit` (93), `exit_group` (94): the run ends; nothing else to check.
* `write` (64), `read` (63): `a1 : int(b)`, `a2 : int(n)` with `0 ≤ n < 2^64`, and a held
  capability, its guard entailed, covering `[b, b + n)` (`rw` for `read`). Afterwards `a0` is a
  fresh `x` with `−4095 ≤ x ≤ −1` (an error) or `0 ≤ x ≤ n`, `x ≤ 0x7ffff000` (bytes moved;
  for `write` also `n ≥ 1 ⇒ x ≥ 1`), every other register keeps its type, and `read` drops
  the fields of the capability it wrote into (its bytes are new).
-/
namespace NoCompiler.Typed

/-- The capability with identity `id` loses its fields (its bytes were overwritten). -/
def HCap.dropFields (id : Nat) (d : HCap) : HCap :=
  if d.id == id then
    match d.cap.kind with
    | .bytes bc => { d with cap := { d.cap with kind := .bytes { bc with fields := [] } } }
    | .token _ => d
  else d

def STy.dropFields (S : STy) (id : Nat) : STy := { S with caps := S.caps.map (HCap.dropFields id) }

namespace Fn
variable (f : Fn)

/-- What `a0` is after a `read`/`write` of `n` bytes (Env.lean's `Sys`). -/
def sysResult (write : Bool) (x : Var) (n : IExpr) : Constr :=
  let xv := IExpr.var x
  .or (.and (.le (.lit (-4095)) xv) (.le xv (.lit (-1))))
    (.and (.le (.lit 0) xv) (.and (.le xv n) (.and (.le xv (.lit 0x7ffff000))
      (if write then Constr.imp (.le (.lit 1) n) (.le (.lit 1) xv) else .tt))))

/-- The capability a `read`/`write` of `[b, b + n)` uses. -/
def sysCapOk (S : STy) (b n : IExpr) (needRw : Bool) (c : HCap) : Bool :=
  match c.cap.kind with
  | .bytes bc =>
    (!needRw || bc.mode == .rw) && S.ent c.cap.guard &&
    S.ent (.and (.le bc.base b) (.le (b.add n) (bc.base.add bc.len)))
  | .token _ => false

def sysCap (S : STy) (b n : IExpr) (needRw : Bool) : Option HCap :=
  S.caps.find? (sysCapOk S b n needRw)

/-- The type after a `read` (`write = false`) or `write` that used capability `id`. -/
def sysAfter (S : STy) (write : Bool) (id : Nat) (n : IExpr) : STy :=
  let S1 := if write then S else S.dropFields id
  (S1.setReg 10 (some (.var (f.freshAt S1)))).addFacts [sysResult write (f.freshAt S1) n]

/-- `ecall` at point `k` with type `S` (the successor edge is the rule's to check). -/
def ecallOk (k : Nat) (S : STy) : Bool :=
  match S.reg 17 with
  | some e =>
    if e.terms = [] then
      let w := BitVec.ofInt 64 e.const
      if w = sysExit ∨ w = sysExitGroup then true
      else if w = sysWrite ∨ w = sysRead then
        match S.reg 11, S.reg 12 with
        | some b, some n =>
          S.ent (.and (.le (.lit 0) n) (.lt n (.lit (2 ^ 64)))) &&
          match Fn.sysCap S b n (decide (w = sysRead)) with
          | some cap => f.edge (some k) (f.sysAfter S (decide (w = sysWrite)) cap.id n) (k + 1)
          | none => false
        | _, _ => false
      else false
    else false
  | none => false

end Fn

end NoCompiler.Typed

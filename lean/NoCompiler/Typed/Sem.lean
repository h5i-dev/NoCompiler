import NoCompiler.Typed.Lang

/-
The meaning ⟦σ⟧ of a signature (docs/Tab 1.md, "署名の意味"; docs/健全性の証明.md, D1–D5),
total version: a `Spec` for the existing judgment `VerifiedImg`, so that a function
accepted by the checker, an unsafe function proved by hand, and an assumed contract all
state the same thing.

Part of the trusted base: what a checked or proved function guarantees is exactly what
this file says.

Entry (P1–P6): `Entry` gives P1 (pc at the entry, `ra` 4-aligned, outside the function)
and 16 ∣ sp; `pre` gives the rest: registers as `in` says, the entry constraint, every
`borrow`/`take` capability valid, the capabilities separated, none of them meeting the
stack region, and the stack fitting below sp.

During the run: the permission is one region per capability (read-only for `ro`,
writable for `rw` and for the regions of a token) and the stack region (M7). Every
access stays in it (decision 10: byte by byte), as `Step` enforces.

Exit (Q1–Q4), at the return address: sp, gp, tp, s0–s11 as on entry (`Spec.Done`); a
valuation extending the entry one on the `out` variables under which the `out`
registers have their types and the exit constraint holds; the borrowed capabilities,
with their exit fields, and the given ones valid and separated; every byte of a token
or a given capability one of the bytes of the `take` capabilities and borrowed tokens
(the Pool). A run that ends the process promises nothing more (I9).
-/
namespace NoCompiler.Typed

/-- What an unsafe module says a token means (I10): an invariant of the memory in its
    footprint, which depends only on the bytes of the footprint (U1). -/
structure TokDef where
  inv : List Region → (Word → Byte) → Prop
  local_ : ∀ fp m m', (∀ x, (∃ r ∈ fp, r.mem x) → m x = m' x) → inv fp m → inv fp m'
  /-- The live allocation units, for the allocator's token (`heapTok`): a function of the
      token's footprint (decisions.md I38). -/
  unit : List Region → Region → Prop := fun _ _ => False

abbrev TokEnv := String → TokDef

/-- The allocator's token: a `heap` byte capability is one of its live units. -/
def heapTok : String := "Heap"
/-- The footprint of each token, a logical value chosen with the valuation. -/
abbrev TokFp := String → List Region

/-- The region of a byte capability: `len` bytes from `base`. -/
def BytesCap.region (ι : Val) (b : BytesCap) : Region :=
  ⟨BitVec.ofInt 64 (b.base.eval ι), (b.len.eval ι).toNat⟩

namespace Cap

/-- The regions of a capability's footprint; none when its guard fails. -/
def regions (ι : Val) (F : TokFp) (c : Cap) : List Region :=
  if c.guard.eval ι then
    match c.kind with
    | .bytes b => [b.region ι]
    | .token t => F t
  else []

/-- `x` is in the footprint. -/
def fp (ι : Val) (F : TokFp) (c : Cap) (x : Word) : Prop := ∃ r ∈ c.regions ι F, r.mem x

/-- Writable capabilities and tokens exclude every other footprint (D3). -/
def exclusive (c : Cap) : Bool :=
  match c.kind with
  | .bytes b => b.mode == .rw
  | .token _ => true

/-- A field holds in memory `m` (D2). -/
def Field.holds (ι : Val) (m : Word → Byte) (b : BytesCap) (f : Field) : Prop :=
  (f.off : Int) + 8 ≤ b.len.eval ι ∧ (b.base.eval ι + f.off) % 8 = 0 ∧
    HasInt ι (read64 m (BitVec.ofInt 64 (b.base.eval ι + f.off))) f.ty

/-- A capability is valid in memory `m` (D2): a byte range inside the address space with
    its fields holding, or a token whose invariant holds; anything when the guard fails. -/
def valid (T : TokEnv) (ι : Val) (F : TokFp) (m : Word → Byte) (c : Cap) : Prop :=
  c.guard.holds ι →
    match c.kind with
    | .bytes b =>
      0 ≤ b.base.eval ι ∧ 0 ≤ b.len.eval ι ∧ b.base.eval ι + b.len.eval ι ≤ 2 ^ 64 ∧
        (∀ f ∈ b.fields, Field.holds ι m b f) ∧
        (b.heap = true → (T heapTok).unit (F heapTok) (b.region ι))
    | .token t => (T t).inv (F t) m

end Cap

/-- A list of capabilities is separated (D3): the footprint of each writable capability
    and token meets no other one's. -/
def Separated (ι : Val) (F : TokFp) (cs : List Cap) : Prop :=
  ∀ i j (hi : i < cs.length) (hj : j < cs.length), i ≠ j → cs[i].exclusive = true →
    ∀ x, cs[i].fp ι F x → ¬ cs[j].fp ι F x

/-- A borrowed capability as it comes back: the same range, the exit fields. -/
def Borrow.exitCap (b : Borrow) : Cap :=
  match b.cap.kind with
  | .bytes x => { b.cap with kind := .bytes { x with fields := b.outFields } }
  | .token _ => b.cap

namespace Sig
variable (σ : Sig)

/-- The capabilities held on entry: borrowed, then taken. -/
def entryCaps : List Cap := σ.borrow.map (·.cap) ++ σ.take

/-- The capabilities held on exit: borrowed (with their exit fields), then given. -/
def exitCaps : List Cap := σ.borrow.map Borrow.exitCap ++ σ.give

/-- Where returned tokens and given capabilities may come from: the `take`
    capabilities and the borrowed tokens, at entry (the proof's Pool, D4). -/
def pool (ι : Val) (F : TokFp) (x : Word) : Prop :=
  (∃ c ∈ σ.take, c.fp ι F x) ∨
    (∃ b ∈ σ.borrow, (match b.cap.kind with | .token _ => true | .bytes _ => false) = true ∧
      b.cap.fp ι F x)

/-- The returned capabilities whose footprint must come from the pool: tokens, and
    every given capability. -/
def fresh : List Cap :=
  (σ.borrow.map (·.cap)).filter (fun c => match c.kind with | .token _ => true | .bytes _ => false)
    ++ σ.give

def readRegions (ι : Val) (F : TokFp) : List Region :=
  (σ.entryCaps.filter (fun c => !c.exclusive)).flatMap (·.regions ι F)

def writeRegions (ι : Val) (F : TokFp) : List Region :=
  (σ.entryCaps.filter (·.exclusive)).flatMap (·.regions ι F)

def RegsHave (ι : Val) (s : State) (rs : List (Reg × IExpr)) : Prop :=
  ∀ p ∈ rs, HasInt ι (s.reg p.1) p.2

/-- The entry conditions P2–P6 (P1 and 16 ∣ sp are `Entry`). -/
def Pre (T : TokEnv) (ι : Val) (F : TokFp) (s : State) : Prop :=
  RegsHave ι s σ.inRegs ∧ σ.pre.holds ι ∧
    (∀ c ∈ σ.entryCaps, c.valid T ι F s.mem) ∧ Separated ι F σ.entryCaps ∧
    (∀ c ∈ σ.entryCaps, ∀ x, c.fp ι F x → ¬ (Spec.stackRegion s σ.stack).mem x) ∧
    σ.stack ≤ (s.reg Reg.sp).toNat

/-- The exit conditions Q2–Q4 (Q1 is `Spec.Done`'s `Preserved`). -/
def Post (T : TokEnv) (ι : Val) (F : TokFp) (s : State) (s' : State) : Prop :=
  ∃ ι' : Val, ∃ F' : TokFp, (∀ x, x ∉ σ.outVars → ι' x = ι x) ∧
    RegsHave ι' s' σ.outRegs ∧ σ.post.holds ι' ∧
    (∀ c ∈ σ.exitCaps, c.valid T ι' F' s'.mem) ∧ Separated ι' F' σ.exitCaps ∧
    (∀ c ∈ σ.fresh, ∀ x, c.fp ι' F' x → σ.pool ι F x) ∧
    -- Q5: the allocator's units that miss the Pool and the stack survive (I38)
    (∀ r, (T heapTok).unit (F heapTok) r → (∀ x, r.mem x → ¬ σ.pool ι F x ∧
      ¬ (Spec.stackRegion s σ.stack).mem x) → (T heapTok).unit (F' heapTok) r)

/-- The signature as a specification: the logical argument is the valuation of the
    parameters and the footprints of the entry tokens. -/
def spec (T : TokEnv) : Spec (Val × TokFp) where
  pre a s := σ.Pre T a.1 a.2 s
  post a s s' := σ.Post T a.1 a.2 s s'
  onExit _ _ _ := True
  reads a _ := σ.readRegions a.1 a.2
  writes a _ := σ.writeRegions a.1 a.2
  stack := σ.stack

end Sig

/-- ⟦σ⟧, total: the function at `entry`, with code region `D` in image `c`, meets its
    signature under the token meanings `T`. -/
def Meets (c : Code) (D : Dom) (entry : Word) (T : TokEnv) (σ : Sig) : Prop :=
  VerifiedImg c D entry (σ.spec T)

end NoCompiler.Typed

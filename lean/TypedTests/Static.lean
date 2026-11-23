import NoCompiler.Typed.Sound.Main
/-! Static data in the Lean checker (I30/I32 with the linked image, export.md "Linked image"):
    `auipc a1, 0; ld a0, 16(a1); ret` reads the read-only word at 0x1010. The data symbol's
    capability is a `borrow ℓ ↦ bytes[8] ro` clause and the image gives `ℓ = 0x1010`;
    `auipc`'s literal then meets `ℓ` in the solver, so the access is allowed; with the address
    as the capability's base after the entry (the export's pinned point types) the field is
    read too (`fn42` below). -/
open NoCompiler NoCompiler.Typed

namespace TypedTests.Static

def code : Code := ⟨0x1000#64, #[0x00000597#32, 0x0105b503#32, 0x00008067#32]⟩

-- variables: ℓ = 0, the result r = 26, kept registers 10–25
def ℓ : IExpr := .var 0
def r : IExpr := .var 26
def regVar : List (Reg × Var) := keptRegs.zipIdx.map fun (r, i) => (r, 10 + i)
def kept : List (Reg × IExpr) := regVar.map fun (r, x) => (r, .var x)

def data : Cap := ⟨.tt, .bytes ⟨ℓ, .lit 8, .ro, false, [⟨0, .lit 42⟩]⟩⟩
def cap : HCap := ⟨0, data, some 0⟩
def pre : Constr := .and (.eq ℓ (.lit 0x1010)) (.dvd 8 ℓ)

def sig : Sig where
  params := [0]
  inRegs := []
  borrow := [{ cap := data, outFields := [⟨0, .lit 42⟩] }]
  pre := pre
  outVars := [26]
  outRegs := [(10, r)]
  post := .tt

def fn : Fn where
  sig := sig
  entry := 0x1000#64
  size := 3
  regVar := regVar
  loops := []
  fresh := 30
  types := [
    (0, { regs := kept, facts := [pre], caps := [cap] }),
    (1, { regs := kept ++ [(11, .lit 0x1000)], facts := [pre], caps := [cap] }),
    (2, { regs := kept ++ [(11, .lit 0x1000), (10, .var 31)], facts := [pre], caps := [cap] })]

/-- Accepted (checked by the kernel). -/
theorem fn_checked : fn.check code = true := by decide

theorem read_meets (T : TokEnv) : Meets code [(fn.entry, 4 * fn.size)] fn.entry T sig :=
  Fn.check_sound_leaf fn code T fn_checked rfl

/-- Without the image's `ℓ = 0x1010` the literal address need not be in the capability. -/
def free : Fn := { fn with sig := { sig with pre := .dvd 8 ℓ }, types := fn.types.map fun (k, S) =>
  (k, { S with facts := [.dvd 8 ℓ] }) }
example : free.check code = false := by decide

end TypedTests.Static

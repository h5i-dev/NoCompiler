import NoCompiler.Typed.Sound.Main
/-! The `ecall` rule (Lemma 9, I31): `write(fd, ρ, n)` of a borrowed read-only buffer.
    `li a7, 64; ecall; ret`, encoded by hand (llvm-mc gives the same words). -/
open NoCompiler NoCompiler.Typed

namespace TypedTests.Ecall

def code : Code := ⟨0x1000#64, #[0x04000893#32, 0x00000073#32, 0x00008067#32]⟩

-- variables: n = 0, ρ = 1, the result r = 26, a0 after the call 27, kept registers 10–25
def n : IExpr := .var 0
def ρ : IExpr := .var 1
def regVar : List (Reg × Var) := keptRegs.zipIdx.map fun (r, i) => (r, 10 + i)
def kept : List (Reg × IExpr) := regVar.map fun (r, x) => (r, .var x)

def cap : HCap := ⟨0, ⟨.tt, .bytes ⟨ρ, n, .ro, false, []⟩⟩, some 0⟩

def sig : Sig where
  params := [0, 1]
  inRegs := [(11, ρ), (12, n)]
  borrow := [{ cap := cap.cap, outFields := [] }]
  pre := .lt n (.lit (2 ^ 64))
  outVars := [26]
  outRegs := [(10, .var 26)]

def entryTy : STy := { regs := kept ++ [(11, ρ), (12, n)], facts := [.lt n (.lit (2 ^ 64))], caps := [cap] }

def fn : Fn where
  sig := sig
  entry := 0x1000#64
  size := 3
  regVar := regVar
  loops := []
  fresh := 30
  types := [
    (0, entryTy),
    (1, { entryTy with regs := (17, .lit 64) :: entryTy.regs }),
    (2, { regs := kept ++ [(10, .var 27)], facts := [], caps := [cap] })]

/-- Accepted (checked by the kernel). -/
theorem fn_checked : fn.check code = true := by decide

theorem write_meets (T : TokEnv) : Meets code [(fn.entry, 4 * fn.size)] fn.entry T sig :=
  Fn.check_sound_leaf fn code T fn_checked rfl

/-! Rejected variants. -/
/-- `read` (63) into a read-only buffer. -/
def codeRead : Code := ⟨0x1000#64, #[0x03f00893#32, 0x00000073#32, 0x00008067#32]⟩
def fnRead : Fn := { fn with types := fn.types.map fun (k, S) =>
  if k == 1 then (k, { entryTy with regs := (17, .lit 63) :: entryTy.regs }) else (k, S) }
example : fnRead.check codeRead = false := by decide
/-- The buffer one byte shorter than the request. -/
def short : Fn := { fn with sig := { sig with borrow :=
  [{ cap := ⟨.tt, .bytes ⟨ρ, n.sub (.lit 1), .ro, false, []⟩⟩, outFields := [] }] } }
example : short.check code = false := by decide
/-- An unsupported syscall number (57, close). -/
def codeClose : Code := ⟨0x1000#64, #[0x03900893#32, 0x00000073#32, 0x00008067#32]⟩
def fnClose : Fn := { fn with types := fn.types.map fun (k, S) =>
  if k == 1 then (k, { entryTy with regs := (17, .lit 57) :: entryTy.regs }) else (k, S) }
example : fnClose.check codeClose = false := by decide

end TypedTests.Ecall

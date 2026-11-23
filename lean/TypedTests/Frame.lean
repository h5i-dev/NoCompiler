import NoCompiler.Typed.Sound.Main
/-! A function with a frame (Lemma 7): the prologue, `ra` saved in a slot, a store and a load
    through the frame's address-taken range, the epilogue, the return. Assembled by clang;
    the record is written by hand. Not part of the core library. -/
open NoCompiler NoCompiler.Typed

namespace TypedTests.Frame

/-- `addi sp,sp,-32; sd ra,24(sp); sd zero,0(sp); ld a0,0(sp); ld ra,24(sp); addi sp,sp,32; ret` -/
def code : Code := ⟨0x2000#64, #[0xfe010113#32, 0x00113c23#32, 0x00013023#32, 0x00013503#32,
  0x01813083#32, 0x02010113#32, 0x00008067#32]⟩

def regVar : List (Reg × Var) := keptRegs.zipIdx.map fun (r, i) => (r, 10 + i)
def kept : List (Reg × IExpr) := regVar.map fun (r, x) => (r, .var x)
/-- `sp` is variable 11 on entry; inside the frame it is `sp0 − 32`. -/
def sp0 : IExpr := .var 11
def low : List (Reg × IExpr) := (2, sp0.add (.lit (-32))) :: kept.filter (·.1 != 2)
def facts : List Constr := [.le (.lit 32) sp0, .lt sp0 (.lit (2 ^ 64)), .dvd 16 sp0]
def buf : HCap := ⟨5, ⟨.tt, .bytes ⟨sp0.add (.lit (0 - 32)), .lit 16, .rw, false, []⟩⟩, none⟩

def sig : Sig where
  params := []
  inRegs := []
  outVars := [26]
  outRegs := [(10, .var 26)]
  stack := 32

def fn : Fn where
  sig := sig
  entry := 0x2000#64
  size := 7
  regVar := regVar
  fresh := 30
  frame := some { size := 32, slots := [24], addr := [(0, 16)] }
  types := [
    (0, ⟨kept, facts, [], [], 0⟩),
    (1, ⟨low, facts, [buf], [], 32⟩),
    (2, ⟨low, facts, [buf], [(24, .var 10)], 32⟩),
    (3, ⟨low, facts, [buf], [(24, .var 10)], 32⟩),
    (4, ⟨(10, .var 40) :: low, facts, [buf], [(24, .var 10)], 32⟩),
    (5, ⟨(10, .var 40) :: low, facts, [buf], [(24, .var 10)], 32⟩),
    (6, ⟨(10, .var 40) :: kept, facts, [], [], 0⟩)]

/-- Accepted, so it meets its signature. -/
theorem fn_checked : fn.check code = true := by decide

theorem f_meets (T : TokEnv) : Meets code [(fn.entry, 4 * fn.size)] fn.entry T sig :=
  Fn.check_sound_leaf fn code T fn_checked rfl

/-! Rejected variants. -/
/-- `ra` reloaded from the wrong slot (32 is outside the frame). -/
def codeSlot : Code := ⟨0x2000#64, #[0xfe010113#32, 0x00113c23#32, 0x00013023#32, 0x00013503#32,
  0x02013083#32, 0x02010113#32, 0x00008067#32]⟩
example : fn.check codeSlot = false := by decide
/-- A store past the address-taken range (16 is outside `[0, 16)`, inside no capability). -/
def codeStore : Code := ⟨0x2000#64, #[0xfe010113#32, 0x00113c23#32, 0x00013823#32, 0x00013503#32,
  0x01813083#32, 0x02010113#32, 0x00008067#32]⟩
example : fn.check codeStore = false := by decide
/-- The epilogue gives back only half the frame. -/
def codePop : Code := ⟨0x2000#64, #[0xfe010113#32, 0x00113c23#32, 0x00013023#32, 0x00013503#32,
  0x01813083#32, 0x01010113#32, 0x00008067#32]⟩
example : fn.check codePop = false := by decide
/-- The frame larger than the signature's stack. -/
example : ({ fn with sig := { sig with stack := 16 } } : Fn).check code = false := by decide

end TypedTests.Frame

import NoCompiler.Typed.Check
/-! The note's `sum` (docs/Tab 1.md, 例), assembled by clang, checked by the Lean checker.
    The record below is written by hand (the Rust export will produce it). -/
open NoCompiler NoCompiler.Typed

namespace TypedTests.Sum

/-- `clang --target=riscv64-unknown-elf -march=rv64im_zba_zbb -mno-relax -c` of the note's
    `sum`, `.text`. -/
def code : Code := ⟨0x1000#64, #[0x00000613#32, 0x00058c63#32, 0x00053683#32, 0x00c68633#32,
  0xfff58593#32, 0x00850513#32, 0xfe0598e3#32, 0x00060513#32, 0x00008067#32]⟩

-- variables: n = 0, ρ = 1, m = 2 (loop), result r = 26, entry values of the kept registers 10–25
def n : IExpr := .var 0
def ρ : IExpr := .var 1
def m : IExpr := .var 2
def regVar : List (Reg × Var) := keptRegs.zipIdx.map fun (r, i) => (r, 10 + i)
def kept : List (Reg × IExpr) := regVar.map fun (r, x) => (r, .var x)

def cap : HCap := ⟨0, ⟨.tt, .bytes ⟨ρ, n.smul 8, .ro, false, []⟩⟩, some 0⟩

def sig : Sig where
  params := [0, 1]
  inRegs := [(10, ρ), (11, n)]
  borrow := [{ cap := cap.cap, outFields := [] }]
  pre := .dvd 8 ρ
  outVars := [26]
  outRegs := [(10, .var 26)]

def entryTy : STy := { regs := kept ++ [(10, ρ), (11, n)], facts := [.dvd 8 ρ], caps := [cap] }
def headTy : STy :=
  ⟨kept ++ [(10, (ρ.add (n.smul 8)).sub (m.smul 8)), (11, m)], [.dvd 8 ρ, .le (.lit 1) m, .le m n], [cap]⟩

def fn : Fn where
  sig := sig
  entry := 0x1000#64
  size := 9
  regVar := regVar
  loops := [{ head := 2, last := 6, vars := [2], meas := m }]
  fresh := 30
  types := [
    (0, entryTy),
    (1, { entryTy with regs := (12, .lit 0) :: entryTy.regs }),
    (2, headTy), (3, headTy), (4, headTy),
    (5, { headTy with regs := kept ++ [(10, (ρ.add (n.smul 8)).sub (m.smul 8)), (11, m.sub (.lit 1))] }),
    (6, { headTy with regs := kept ++ [(10, ((ρ.add (n.smul 8)).sub (m.smul 8)).add (.lit 8)),
                                      (11, m.sub (.lit 1))] }),
    (7, { regs := kept, facts := [], caps := [cap] }),
    (8, { regs := kept ++ [(10, .var 27)], facts := [], caps := [cap] })]

/-- Accepted (checked by the kernel). -/
example : fn.check code = true := by decide

/-! Rejected variants. -/
/-- The buffer one word too short: the last load is out of range. -/
def short : Fn := { fn with sig := { sig with borrow := [{ cap := ⟨.tt, .bytes ⟨ρ, (n.smul 8).sub (.lit 8), .ro, false, []⟩⟩, outFields := [] }] } }
example : short.check code = false := by decide
/-- No alignment fact: `ld` may be misaligned. -/
def unaligned : Fn := { fn with sig := { sig with pre := .tt } }
example : unaligned.check code = false := by decide
/-- A measure that does not decrease. -/
def noDecrease : Fn := { fn with loops := [{ head := 2, last := 6, vars := [2], meas := n }] }
example : noDecrease.check code = false := by decide
/-- The record claims a fact the code does not establish (`m ≥ 2` at the head). -/
def badInv : Fn := { fn with types := fn.types.map fun (k, S) =>
  if k == 2 then (k, { S with facts := .le (.lit 2) m :: S.facts }) else (k, S) }
example : badInv.check code = false := by decide
/-- The same code with `ld a3, 8(a0)`: reads one word past the buffer on the last trip. -/
def code8 : Code := ⟨0x1000#64, #[0x00000613#32, 0x00058c63#32, 0x00853683#32, 0x00c68633#32,
  0xfff58593#32, 0x00850513#32, 0xfe0598e3#32, 0x00060513#32, 0x00008067#32]⟩
example : fn.check code8 = false := by decide
/-- The same code returning with `a1` in `ra`'s place: `jalr zero, 0(a1)` is not a return. -/
def codeRet : Code := ⟨0x1000#64, #[0x00000613#32, 0x00058c63#32, 0x00053683#32, 0x00c68633#32,
  0xfff58593#32, 0x00850513#32, 0xfe0598e3#32, 0x00060513#32, 0x00058067#32]⟩
example : fn.check codeRet = false := by decide

end TypedTests.Sum

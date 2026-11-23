import TypedTests.ArithExt
open NoCompiler NoCompiler.Typed

namespace TypedTests.ArithExt

/-- `ori a0, a0, 1` on an 8-aligned pointer: the bits are disjoint, so the result is p + 1. -/
def pre8 : Constr := .and pre (.dvd 8 p)
def tagSig : Sig where
  params := [0]
  inRegs := [(10, p)]
  pre := pre8
  outVars := [26]
  outRegs := [(10, r)]
  post := .eq r (p.add (.lit 1))
def tag : Fn := mkFn tagSig { regs := kept ++ [(10, p)], facts := [pre8] }
  { regs := kept ++ [(10, p.add (.lit 1))], facts := [pre8] }
theorem tag_checked : tag.check (mkCode 0x00156513#32) = true := by decide
/-- Without the alignment the bits may overlap: rejected. -/
def tagNoAlign : Fn := mkFn { tagSig with pre := pre } { regs := kept ++ [(10, p)], facts := [pre] }
  { regs := kept ++ [(10, p.add (.lit 1))], facts := [pre] }
example : tagNoAlign.check (mkCode 0x00156513#32) = false := by decide

end TypedTests.ArithExt

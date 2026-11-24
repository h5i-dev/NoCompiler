import TypedTests.ArithExt
open NoCompiler NoCompiler.Typed

namespace TypedTests.ArithExt

/-- `clz a0, a0`: at most 64. -/
def cntSig : Sig where
  params := [0]
  inRegs := [(10, p)]
  outVars := [26]
  outRegs := [(10, r)]
  post := .and (.le (.lit 0) r) (.le r (.lit 64))
def cnt : Fn := mkFn cntSig { regs := kept ++ [(10, p)], facts := [] }
  { regs := kept ++ [(10, q)], facts := Fn.boundFacts 30 64 }
theorem cnt_checked : cnt.check (mkCode 0x60051513#32) = true := by decide

end TypedTests.ArithExt

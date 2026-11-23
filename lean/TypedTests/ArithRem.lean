import TypedTests.ArithExt
open NoCompiler NoCompiler.Typed

namespace TypedTests.ArithExt

/-- `remu a0, a0, a1` with 0 < b: the remainder is below b and at most a. -/
def preAB : Constr := .and pre (.and (.lt (.lit 0) b) (.lt b (.lit (2 ^ 64))))
def remSig : Sig where
  params := [0, 1]
  inRegs := [(10, p), (11, b)]
  pre := preAB
  outVars := [26]
  outRegs := [(10, r)]
  post := .and (.lt r b) (.le r p)
def rem : Fn := mkFn remSig { regs := kept ++ [(10, p), (11, b)], facts := [preAB] }
  { regs := kept ++ [(10, q), (11, b)], facts := [preAB] ++ Fn.divBound false 30 p b }
theorem rem_checked : rem.check (mkCode 0x02b57533#32) = true := by decide
/-- A divisor that may be 0: rejected (remu by 0 returns a, which need not be below b). -/
def remZero : Fn := mkFn { remSig with pre := pre } { regs := kept ++ [(10, p), (11, b)], facts := [pre] }
  { regs := kept ++ [(10, q), (11, b)], facts := [pre] ++ Fn.divBound false 30 p b }
example : remZero.check (mkCode 0x02b57533#32) = false := by decide

end TypedTests.ArithExt

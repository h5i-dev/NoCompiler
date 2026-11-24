import TypedTests.ArithExt
open NoCompiler NoCompiler.Typed

namespace TypedTests.ArithExt

/-- `slliw a0, a0, 3`: the sign-extended low word of 8p, in [−2^31, 2^31). -/
def wordSig : Sig where
  params := [0]
  inRegs := [(10, p)]
  outVars := [26]
  outRegs := [(10, r)]
  post := .and (.le (.lit (-2 ^ 31)) r) (.lt r (.lit (2 ^ 31)))
def wordS0 : STy := { regs := kept ++ [(10, p)], facts := [] }
def word : Fn := mkFn wordSig wordS0 (Fn.word32 wordS0 10 30 (p.smul 8))
theorem word_checked : word.check (mkCode 0x0035151b#32) = true := by decide

/-- `srlw a0, a0, a1` with `a1 = 5`: the low word divided by 32, below 2^27. -/
def shrSig : Sig where
  params := [0]
  inRegs := [(10, p), (11, .lit 5)]
  outVars := [26]
  outRegs := [(10, r)]
  post := .and (.le (.lit 0) r) (.lt r (.lit (2 ^ 27)))
def shr : Fn := mkFn shrSig { regs := kept ++ [(10, p), (11, .lit 5)], facts := [] }
  { regs := kept ++ [(10, q), (11, .lit 5)],
    facts := Fn.lowFacts 31 p 32 ++ Fn.quotFacts 30 (.var 31) (2 ^ 5) }
theorem shr_checked : shr.check (mkCode 0x00b5553b#32) = true := by decide
/-- The post claims a bound the shift by 5 does not give. -/
def shrWrong : Fn := { shr with sig := { shrSig with post := .lt r (.lit (2 ^ 26)) } }
example : shrWrong.check (mkCode 0x00b5553b#32) = false := by decide

end TypedTests.ArithExt

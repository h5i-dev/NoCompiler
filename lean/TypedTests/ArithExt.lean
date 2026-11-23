import NoCompiler.Typed.Sound.Main
/-! ArithExt rules on small functions, checked by the kernel. `align`: `andi a0, a0, -8; ret`
    (decisions.md I23, the −2^k mask) rounds a pointer down to a multiple of 8. -/
open NoCompiler NoCompiler.Typed

namespace TypedTests.ArithExt

def code : Code := ⟨0x1000#64, #[0xff857513#32, 0x00008067#32]⟩

-- variables: p = 0, the result r = 26, the quotient q = 30, kept registers 10–25
def p : IExpr := .var 0
def r : IExpr := .var 26
def q : IExpr := .var 30
def regVar : List (Reg × Var) := keptRegs.zipIdx.map fun (r, i) => (r, 10 + i)
def kept : List (Reg × IExpr) := regVar.map fun (r, x) => (r, .var x)

def pre : Constr := .and (.le (.lit 0) p) (.lt p (.lit (2 ^ 64)))

def sig : Sig where
  params := [0]
  inRegs := [(10, p)]
  pre := pre
  outVars := [26]
  outRegs := [(10, r)]
  post := .and (.dvd 8 r) (.and (.le r p) (.lt p (r.add (.lit 8))))

def fn : Fn where
  sig := sig
  entry := 0x1000#64
  size := 2
  regVar := regVar
  loops := []
  fresh := 30
  types := [
    (0, { regs := kept ++ [(10, p)], facts := [pre] }),
    (1, { regs := kept ++ [(10, q.smul 8)], facts := [pre] ++ Fn.quotFacts 30 p 8 })]

/-- Accepted (checked by the kernel). -/
theorem fn_checked : fn.check code = true := by decide

theorem align_meets (T : TokEnv) : Meets code [(fn.entry, 4 * fn.size)] fn.entry T sig :=
  Fn.check_sound_leaf fn code T fn_checked rfl

/-- The post claims 16-alignment, which `andi −8` does not give. -/
def wrong : Fn := { fn with sig := { sig with post := .and (.dvd 16 r) (.le r p) } }
example : wrong.check code = false := by decide

/-! The same shape for other rules: one instruction, then `ret`. -/
def mkCode (w : BitVec 32) : Code := ⟨0x1000#64, #[w, 0x00008067#32]⟩
def mkFn (σ : Sig) (S0 S1 : STy) : Fn :=
  { sig := σ, entry := 0x1000#64, size := 2, regVar := regVar, loops := [], fresh := 30,
    types := [(0, S0), (1, S1)] }

def b : IExpr := .var 1

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

import NoCompiler.Lib.Div
/-! Library division (NoCompiler/Lib/Div.lean): gcc's x / 10 by its magic constant, every side condition by `decide`. -/
open NoCompiler NoCompiler.Lib
-- test: x / 10, gcc's magic 0xCCCCCCCCCCCCCCCD with shift 3
example (x : Word) : (mulhUU x (BitVec.ofNat 64 0xCCCCCCCCCCCCCCCD) >>> 3).toNat = x.toNat / 10 :=
  udiv_magic x (d := 10) (e := 2) (by decide) (by decide) (by decide) (by decide)

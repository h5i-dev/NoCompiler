-- Per-image facts for fuzz_qdisc plain (generated image, examples/qdisc/gen_qdisc_images.sh): codeAgree on the code of
-- its executable segment (the NoCompiler `Code` built from the same bytes; B's export gives the same words).
import LPS.Bridge.Image
import Examples.LPS.Images.QdiscPlainE5r
open LPS LPS.Bridge LPS.RiscvSemantics

def hexNib (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87
def hexBytes (s : String) : Array (BitVec 8) :=
  let cs := s.toList.toArray
  (Array.range (cs.size / 2)).map fun k => BitVec.ofNat 8 (16 * hexNib cs[2*k]! + hexNib cs[2*k+1]!)

/-- The NoCompiler code of the executable segment: its 32-bit little-endian words from its base. -/
def codeOf (s : Segment) : NoCompiler.Code :=
  let b := (s.seg_bytes.map hexBytes).foldl (· ++ ·) #[]
  ⟨BitVec.ofNat 64 s.seg_base, (Array.range (b.size / 4)).map fun k =>
    b[4*k+3]! ++ b[4*k+2]! ++ b[4*k+1]! ++ b[4*k]!⟩

def execSeg : Segment := ((Images.QdiscPlainE5r.loaded_segments.filter seg_executable).head?).getD ⟨0, 0, "", []⟩

#eval (codeOf execSeg).words.size
#eval codeAgree Images.QdiscPlainE5r.loaded_segments (codeOf execSeg)

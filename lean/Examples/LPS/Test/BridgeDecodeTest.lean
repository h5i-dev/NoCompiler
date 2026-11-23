-- Evaluation check (#eval, not a proof) of the bridge's decode agreement (LPS/Bridge/Decode.lean) on every
-- 32-bit word at a 2-byte offset of the executable segments of both fuzz_qdisc plain images:
-- (agreeing words, Zba/Zbb words with no LPS counterpart, offsets of disagreeing words).
import LPS.Bridge.Decode
import Examples.LPS.Images.QdiscPlainE5r
import Examples.LPS.Images.QdiscPlainOvp
open LPS LPS.Bridge

def hexNib (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87
def hexBytes (s : String) : List (BitVec 8) :=
  let cs := s.toList.toArray
  (List.range (cs.size / 2)).map fun k => BitVec.ofNat 8 (16 * hexNib cs[2*k]! + hexNib cs[2*k+1]!)
def execBytes (segs : List Segment) : List (List (BitVec 8)) :=
  (segs.filter seg_executable).map fun s => (s.seg_bytes.map hexBytes).flatten

#eval (execBytes Images.QdiscPlainE5r.loaded_segments).map fun b => let (a, z, bad) := agreeOn b; (b.length, a, z, bad.take 10)
#eval (execBytes Images.QdiscPlainOvp.loaded_segments).map fun b => let (a, z, bad) := agreeOn b; (b.length, a, z, bad.take 10)

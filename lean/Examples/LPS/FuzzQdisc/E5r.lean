import Examples.LPS.FuzzQdisc.Statements
import Examples.LPS.Images.QdiscPlainE5r
import Examples.LPS.Images.QdiscUbsanE5r

/-!
# fuzz_qdisc's statements for our e5r builds (round 4 goal (a))

oss-verify's statements (Statements.lean, ported from their Statements.v) applied to our builds' memory
images, generated from B's e5r ELFs by scripts/lps/elf_snapshot_lean.py (LPS's elf_snapshot `_parse_elf`;
sha256 of each ELF in its image module's header). Only the plain and UBSan builds exist so far, so the
ASan statements are not instantiated yet. These are the statements, not proofs: nothing here claims they hold.
-/

namespace LPS.OSSVerify.ReacPw.FuzzQdisc.E5r
open LPS LPS.OSSVerify

def plain : Image := mkImage Images.QdiscPlainE5r.loaded_segments Images.QdiscPlainE5r.init_pc Images.QdiscPlainE5r.phdrs
def ubsan : Image := mkImage Images.QdiscUbsanE5r.loaded_segments Images.QdiscUbsanE5r.init_pc Images.QdiscUbsanE5r.phdrs

def plain_halts : Prop := FuzzQdisc.plain_halts plain
def ubsan_halts : Prop := FuzzQdisc.ubsan_halts ubsan
def plain_halts_may_fail : Prop := FuzzQdisc.plain_halts_may_fail plain
def ubsan_halts_may_fail : Prop := FuzzQdisc.ubsan_halts_may_fail ubsan
def ubsan_agrees : Prop := FuzzQdisc.ubsan_agrees plain ubsan

end LPS.OSSVerify.ReacPw.FuzzQdisc.E5r

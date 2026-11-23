import LPS.OSSVerify.Core.Shapes

/-!
# reac-pw / fuzz_qdisc: theorem statements

Port of `projects/reac-pw/fuzz_qdisc/Statements.v` of theorem-labs/oss-verify-proofs (at 90e648c1; MIT
License, Copyright (c) 2026 Theorem Labs, PBC): the same nine statements, the same names, the same shapes
and parameters. Statements.v applies them to `Images.plain` .. `Images.asan_ubsan`, the memory images of
oss-verify's four published builds; here each takes the images it is about, so the same statements are stated
for oss-verify's binaries (goal b) and for our e5r builds (goal a, `FuzzQdisc/E5r.lean`). Read Statements.v's comments for what each one claims and does not claim.
-/

namespace LPS.OSSVerify.ReacPw.FuzzQdisc
open LPS LPS.OSSVerify

/-! Each statement takes the images it is about (Statements.v's `Images.plain`, `Images.ubsan`, `Images.asan`,
`Images.asan_ubsan`), so it can be stated for oss-verify's published builds and for ours. -/

/-! ### Halting -/
def plain_halts (plain : Image) : Prop := halts_within_budget Budgets.Standard.lim_source Exits.ok_or_refused plain
def ubsan_halts (ubsan : Image) : Prop := halts_within_budget Budgets.Standard.lim_source Exits.ok_or_refused ubsan
def asan_halts (asan : Image) : Prop := halts_within_budget Budgets.Standard.lim_source Exits.ok_or_refused asan
def asan_ubsan_halts (asan_ubsan : Image) : Prop :=
  halts_within_budget Budgets.Standard.lim_source Exits.ok_or_refused asan_ubsan
def plain_halts_may_fail (plain : Image) : Prop := halts_may_fail Exits.any plain
def ubsan_halts_may_fail (ubsan : Image) : Prop := halts_may_fail Exits.any ubsan

/-! ### Agreement of each sanitizer build with the plain build -/
def asan_agrees (plain asan : Image) : Prop :=
  agrees_in Env.alloc_forced_only Budgets.Asan.lim_source Budgets.Asan.lim_target plain asan
def ubsan_agrees (plain ubsan : Image) : Prop :=
  agrees_in Env.alloc_forced_only Budgets.Standard.lim_source Budgets.Standard.lim_target plain ubsan
def asan_ubsan_agrees (plain asan_ubsan : Image) : Prop :=
  agrees_in Env.alloc_forced_only Budgets.Asan.lim_source Budgets.Asan.lim_target plain asan_ubsan

end LPS.OSSVerify.ReacPw.FuzzQdisc

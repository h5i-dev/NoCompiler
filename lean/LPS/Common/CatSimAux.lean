import LPS.Common.PropExec7

/-!
# Stand-ins for the items CatExec.v needs that the PropExec port does not carry

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/StackLayout.v` at f1006fe8: this file held `_cat`-suffixed copies of the
PropExec.v items `Common/CatExec.v` cites, pending their port; they are now ported under their Rocq
names in `PropExec6`/`PropExec7` (imported here), and CatExec1/CatExec2 use those. What remains is the
one item with no PropExec.v counterpart: StackLayout.v's `length_auxv_bytes`, as `length_auxv_bytes_cat`
(not yet in `LPS/LinuxProcessSem/StackLayout.lean`). Statement is StackLayout.v's; the proof is Lean's.
-/

namespace LPS
open RiscvSemantics

theorem length_auxv_bytes_cat : ∀ ph at_random uid hwcap, (auxv_bytes ph at_random uid hwcap).length = auxv_size :=
  fun _ _ _ _ => rfl

end LPS

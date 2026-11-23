import NoCompiler

/-
Controls for the two profile changes of 2026-11-22 (docs/isa/profile.md):

* `unimp` (0xc0001073) is a trap: it decodes, has no step (the process dies
  with SIGILL; LPS's `MachineFault`), and the neighbouring CSR word
  `csrrw zero, cycle, a0` is still outside the profile.
* R2: a call may be a function's last instruction (to a function that never
  returns), and so may `unimp`; any other last instruction still falls through.
-/
namespace Examples.TrapControls
open NoCompiler

example : decode 0xc0001073#32 = some .unimp := by decide
example : decode 0xc0051073#32 = none := by decide
example (s : State) : exec .unimp s = none := exec_unimp s

/-- `auipc ra, 1; jalr ra, 0(ra)` at 0x1000: a call to 0x2000, the last instruction. -/
def callEnd : Code := ⟨0x1000#64, #[0x00001097#32, 0x000080e7#32]⟩
example : Struct.check callEnd ⟨0x1000#64, 2, []⟩ [0x1000#64, 0x2000#64] = true := by decide

/-- `addi a0, a0, 1` last: it falls through. -/
def addiEnd : Code := ⟨0x1000#64, #[0x00150513#32]⟩
example : Struct.check addiEnd ⟨0x1000#64, 1, []⟩ [0x1000#64] = false := by decide

/-- `addi a0, a0, 1; unimp`: the trap ends the function. -/
def unimpEnd : Code := ⟨0x1000#64, #[0x00150513#32, 0xc0001073#32]⟩
example : Struct.check unimpEnd ⟨0x1000#64, 2, []⟩ [0x1000#64] = true := by decide

end Examples.TrapControls

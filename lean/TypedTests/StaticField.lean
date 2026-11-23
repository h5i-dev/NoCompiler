import TypedTests.Static
open NoCompiler NoCompiler.Typed

namespace TypedTests.Static

/-! Reading the field through the literal address: the record gives the data capability the
    image's address as its base after the entry (`capSub` compares bases by entailment, and the
    entry constraint has `ℓ = 0x1010`), so the load at the literal address finds field 0. -/
def capLit : HCap := ⟨0, ⟨.tt, .bytes ⟨.lit 0x1010, .lit 8, .ro, false, [⟨0, .lit 42⟩]⟩⟩, some 0⟩
def sig42 : Sig := { sig with post := .eq r (.lit 42) }
def fn42 : Fn := { fn with sig := sig42, types := [
    (0, { regs := kept, facts := [pre], caps := [cap] }),
    (1, { regs := kept ++ [(11, .lit 0x1000)], facts := [pre], caps := [capLit] }),
    (2, { regs := kept ++ [(11, .lit 0x1000), (10, .lit 42)], facts := [pre], caps := [capLit] })] }

theorem fn42_checked : fn42.check code = true := by decide

theorem read42_meets (T : TokEnv) : Meets code [(fn42.entry, 4 * fn42.size)] fn42.entry T sig42 :=
  Fn.check_sound_leaf fn42 code T fn42_checked rfl

/-- The word claimed to be 43: rejected. -/
def fn43 : Fn := { fn42 with sig := { sig with post := .eq r (.lit 43) } }
example : fn43.check code = false := by decide

end TypedTests.Static

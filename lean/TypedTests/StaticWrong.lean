import TypedTests.StaticField
open NoCompiler NoCompiler.Typed

namespace TypedTests.Static

/-- The word claimed to be 43: rejected. -/
def fn43 : Fn := { fn42 with sig := { sig with post := .eq r (.lit 43) } }
example : fn43.check code = false := by decide

end TypedTests.Static

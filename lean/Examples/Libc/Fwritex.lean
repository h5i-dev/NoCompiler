import Examples.Libc.StdioWrite
import Examples.Libc.Musl.Fwrite2

/-!
# `__fwritex` (musl src/stdio/fwrite.c): the rule lemmas are the library's (Examples/Libc/Musl/Fwritex1..3)
-/
set_option maxRecDepth 20000
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage

/-- musl's `memcpy` specification, from the library (Examples/Libc/Musl/Memcpy1.lean). -/
abbrev memcpySpec : SpecP (Word × Word × Word) := NoCompiler.Libc.Musl.Memcpy.memcpySpec

export NoCompiler.Libc.Musl.Fwritex (fw_slot_same)

end Examples.Libc.Slen

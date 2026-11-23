import NoCompiler.Libc.Tactic
import NoCompiler.Libc.Place
import Examples.Libc.Musl.MemcpyAt
import Examples.Libc.Musl.SmallAt
import Examples.Libc.Musl.StdioWrite4
import Examples.Libc.Musl.Toread
import Examples.Libc.Musl.Fwritex2
import Examples.Libc.Musl.StdioRead3
import Examples.Libc.Musl.Fread3
import Examples.Libc.Musl.Fwrite2

/-! slen's musl functions (lean/Examples/Libc/Musl): specifications and proofs of the musl functions slen calls,
    each over its words in libc-slen.elf (scripts/libc/fn_image.py), so they hold for those bytes only; another image
    with the same words at the same addresses gets them by `VerifiedProc.of_code_eq` (and pcFree leaf functions at
    another address by `VerifiedProc.placeAt`). Some specs are narrowed to slen's uses (e.g. `memsetSpec`'s `32 ≤ n`,
    fwrite on a FILE written by `__stdout_write`); Examples/Libc/README.md lists them. -/

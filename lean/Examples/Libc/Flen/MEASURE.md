# flen: hand proofs per function (round 8, B)

flen = `examples/elf/libc-flen.elf` (`examples/libc/flen.c`: argv[1] -> its length on stdout, through
fopen/fread/fclose; musl 1.2.5, MIT). Reach from `_start`, `main`, `exit` (scripts/libc/reach.py): 55 functions, 15
byte-identical to slen's, 16 different, 24 not in slen (re-measured 2026-11-23 after reach.py stopped cutting
functions at assembler-local labels; the first count, 52 / 13 / 14 / 25, was off). `nocompiler check`: 43 of 70 conform, 41 at L2.

Each row: a function proved over flen's own bytes (image by `scripts/libc/fn_image.py --struct`), the hand-written
lines of its spec and proof (the spec counted once where shared), and the time from start to a checked proof.

| function | bytes | level | spec lines | proof lines | time | notes |
| --- | --- | --- | --- | --- | --- | --- |
| `__vm_wait` | 4 | L2 | 3 (shared `nopSpec`) | 3 | 1 min for both | `ret`; `nocompiler_auto` |
| `__unlist_locked_file` | 4 | L2 | (shared) | 3 | (with `__vm_wait`) | `ret`; `nocompiler_auto` |

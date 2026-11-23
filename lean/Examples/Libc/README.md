# lean/Examples/Libc: slen (and the musl functions it calls), proved over libc-slen.elf's bytes

Everything here is specific to examples/elf/libc-slen.elf (a musl static binary that prints the length of its
standard input). The images (`SlenImage`, `Musl/*Img.lean`) hold that file's words at its addresses; the proofs
hold for those bytes only (`VerifiedProc.of_code_eq` carries a theorem to another image with the same words at the
same addresses, nothing more). Generic pieces live in lean/NoCompiler (Libc/Mem, Word, Shape, Drain, Transfer,
Relocate, Place, Tactic).

## What is proved

The whole-program claims are stated in `SlenSpec.lean`: `SlenCorrect` (from any launch `SlenLaunch s k d`, every run
stays in `.text`, exits with 0 and has written a prefix of `output d` to fd 1) and `SlenCorrectW` (the runs in which no
write fails write exactly `output d`).

- **`SlenCorrect` is not proved.** `slen_correct_of_pre` (Compose3.lean) proves its conclusion for one launch, given
  `hpre : ∀ z, StartCall s z → slenL.pre () z k`: the precondition of the start-up chain at `__libc_start_main`'s
  entry. **`SlenCorrectW` is not proved.**
- Unfinished: discharging `hpre`. SlenPre3..12 prove parts of it from `SlenLaunch` (`SL.initLibcPre`,
  `SL.imgEq_main`, `SL.mainPre`, ...), not yet composed into `hpre`.
- Per function of slen's own code (over `code`, SlenImage), in Examples/Libc/*.lean: `_start_c_verified`,
  `lsm_verified` (`__libc_start_main`), `init_libc_verified`, `init_tls_verified`, `__init_ssp_verified`,
  `__set_thread_area_verified`, `__libc_start_init_verified`, `_init_verified`, `main_verified`, `exit_verified`,
  `__funcs_on_exit_verified`, `__libc_exit_fini_verified`, `__stdio_exit_verified`, `__ofl_lock_verified`,
  `__lock_verified`, and the musl ones below re-exported over `code`.

## The musl functions (Musl/, over slen's bytes; each image a `Musl/*Img.lean`)

| theorem | file | spec | limits of the spec |
| --- | --- | --- | --- |
| `memcpy_verified` | Memcpy4 | `memcpySpec` | `d`, `src` regions disjoint, readable/writable |
| `memset_verified` | Memset | `memsetSpec` | `32 ≤ n < 2^63` (slen's one caller: `n` = 304); bytes written not stated |
| `_Exit_verified`, `___errno_location_verified`, `__towrite_verified` | Small | `exitSpec`, `errnoP`, `towriteSpec` | `__towrite`: the FILE's fields at 136/88 |
| `__syscall_ret_verified` | StdioWrite1 | `syscallRetSpec` | errno's word (tp - 164) 4-aligned and apart from the 16-byte frame |
| `__stdio_write_verified(F)` | StdioWrite4 | `stdioWriteSpec(F)` | the FILE's fd nonnegative (`< 2^31`), pending + len `< 2^63` |
| `__stdout_write_verified` | StdoutWrite | `stdoutWriteSpec` | given `__stdio_write`'s theorem |
| `__fwritex_stdout_verified`, `fwrite_stdout_verified` | Fwrite1, Fwrite2 | `fwxStdoutP`, `fwriteStdoutP` | only a FILE whose write is `__stdout_write` (slen's stdout), given memcpy's theorem |
| `__toread_verified` | Toread | `toreadP` | no pending write (`wpos = wbase`, f+40 = f+56); FILE's 144 bytes and the frame writable, apart |
| `__stdio_read_verified` | StdioRead3 | `stdioReadP` | `len > 0`; buffer size (f+96) ≠ 0, `len` + it `< 2^63`; fd `< 2^31`; FILE, frame, errno, `buf`, buffer writable and pairwise apart |
| `fread_verified` | Fread3 | `freadP` | given memcpy's theorem; element size 1; `StdinFile`: the FILE's read function is slen's `__stdio_read` (0x12308), its lock word `≥ 2^31` (no locking), not in write mode, buffer size ≠ 0; `n` + buffer size `< 2^63`; fd `< 2^31` |

Axioms: `#print axioms` of these and of `slen_correct_of_pre` give `propext`, `Classical.choice`, `Quot.sound`.

## flen (Flen/, B, round 8)

Over examples/elf/libc-flen.elf's bytes: `__vm_wait_verified` and `__unlist_locked_file_verified` (Flen/Small.lean,
both against `nopSpec`: a function that returns at once). Flen/MEASURE.md records the lines and time per function.
Nothing else of flen is proved.

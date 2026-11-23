# fuzz_qdisc: OSS Verify's smallest target, built here (round 4, QUEUE-B 1)

`projects/reac-pw/fuzz_qdisc` of theorem-labs/oss-verify-proofs is the target to re-prove:
the same statements as theirs (`plain_halts` and the rest, harness.yaml) on our build.
This directory builds it the way their plain build is linked. Our code is compiled into the
profile, and their exact musl and compiler-rt are linked as they are.

```
examples/qdisc/build.sh       # fetch.sh, toolchain.sh, compile, link, check, qemu runs
examples/qdisc/gen_libc_imgs.sh ELF [FUNC ...]   # per-function images into lean/Examples/Libc/Qdisc (git-ignored)
```

- `fetch.sh` downloads the harness and reac-pw's `reac_qdisc.c` (GPL-3.0-or-later) and OSS
  Verify's driver (their recipe's `src/cli.c` and headers; no licence stated), at pinned
  commits, with every SHA-256 checked. None of it is committed.
- `toolchain.sh` streams their pinned toolchain image's one layer (1.1 GB) and keeps about
  350 MB: musl's headers, `libc.a`, `crt1.o`, `crti.o`, `crtn.o`, and compiler-rt. It checks the layer
  digest and the four SHA-256s harness.yaml gives (`libc.a`, `crt1.o`,
  `libclang_rt.builtins.a`, `clang_rt.crtbegin.o`); all four match.
- `src/plugin.c` (ours) is the target's plugin for their driver, written as their OSS-Fuzz
  targets' plugin.c is. `shim/` (ours) declares the function and the qdisc delta.
- `src/count.py` counts `nocompiler check` by rule and by origin, from ld.lld's map.

**The ELF and its export are not committed.** They hold GPL-3.0-or-later code, and this repo
takes no GPL files (round-3 rule); whether to commit them, with a GPL notice as the e5r-demo
case study did, is asked of the lead (STATUS-B). The build is reproducible: same SHA-256 on
every run (plain `a7ed3fa9...990b`, ubsan `1a30890b...f39a`, asan `264291c8...ed45`,
asan-ubsan `e49f653f...1233`), with their clang 20.1.8 from the same image (toolchain.sh keeps
it and runs it through the image's musl loader) and ld.lld from the pinned Lean toolchain.

## How it differs from their plain build

| | theirs (harness.yaml, recipe tools/build-body.sh) | here |
| --- | --- | --- |
| our code: harness, `reac_qdisc_etf_catchup_slots`, driver `cli.c`, plugin | their clang 20, `-march=rv64g -mabi=lp64d -Os -g -ffunction-sections -fdata-sections -fno-stack-protector -fno-plt` | `nocompiler cc -c` with their clang 20.1.8: the profile's flags, `-O2`; `-march=rv64imfd -mabi=lp64d`: the ABI tag (ld.lld does not link lp64 with lp64d objects; no F or D instruction in our functions), and no Zba/Zbb, so our code is inside RV64GC, which LPS models (D's bridge needs that) |
| reac-pw | a static library of its nine input readers | only `reac_qdisc_etf_catchup_slots`, extracted verbatim and checked, with the shim's declarations; the harness calls nothing else of it |
| `wrap_getenv`, `wrap_getpid` | linked | not linked: this harness calls neither |
| musl, compiler-rt | as built in their image | the same files (SHA-256s checked) |
| link | `clang --config=musl.cfg -static -no-pie -Wl,--gc-sections -Wl,--strip-all` | ld.lld: crt1, crti, crtbegin, objects, libc.a, builtins, crtend, crtn, `-static --gc-sections`; not stripped |
| size, plain / ubsan / asan / asan-ubsan | 43,152 / 43,200 / 554,952 / 555,016 (stripped) | 97,384 / 97,464 / 4,311,656 / 4,311,752 (symbols kept) |

Under qemu-riscv64, it behaves like their driver. Config byte 3 asks for 4 calls, which print 0
four times and exit 0. A short header exits 2.

## `nocompiler check` (2026-11-22)

`nocompiler check`: 62 of 111 functions conform, all at L2.

| origin | functions | L2 | L0 | below L0 (R1) | functions with a violation of R1 / R2 / R3 |
| --- | --- | --- | --- | --- | --- |
| ours | 15 | 14 | 1 | 0 | 0 / 1 / 0 |
| musl | 82 | 43 | 28 | 11 | 11 / 19 / 9 |
| compiler-rt | 14 | 5 | 6 | 3 | 3 / 2 / 4 |

Two flags for our code (build.sh says why) took ours from 11 to 14 at L2:
- `-D_Noreturn=` fixes `check_slots` and `oft_exit_guard`. With real musl, `abort` and `_exit`
  are `_Noreturn`, so clang ended each function on that call and the last instruction fell
  through (R2). (The e5r-demo build declared `abort` without `noreturn` in its own shim.)
- `-mllvm -enable-tail-merge=false` fixes their driver's `main`. Merged error tails made a
  later tail jump back into an earlier one, which reads as a loop entered in its middle (R3).

Left in ours: `target_run` (their adapter), R2. It calls the weak `LLVMFuzzerInitialize`,
which this harness does not define, so ld.lld resolves the call to 0, and with pc-relative
code that is `auipc ra, 0; jalr ra`, a call to its own address. A null test guards it, so it
never runs, but the checker cannot know that.

**ubsan** (`fuzz_qdisc.ubsan.elf`; their flags `-fsanitize=undefined -fno-sanitize-recover=all
-fsanitize-trap=all -fno-sanitize=function` on the harness, the function and the plugin, not the
driver, as their recipe does): the same counts, except that `LLVMFuzzerTestOneInput` is below L0.
The trap clang emits for a failed check is `unimp` (0xc0001073). It was not in the profile
(R1) until the user's decision of 2026-11-22: it is now a trap with LPS's meaning, the process
dies with SIGILL, and like every fault it has no step, so a proof that the checks never fire
is a `Verified` theorem. Under qemu it behaves as plain.

**asan, asan-ubsan**: their sealed static ASan link (asan-musl-sealed.cfg as clang's driver
spells it: the runtime whole, libunwind, the wrap list, `__sanitizer_sealed_init`, and their
asan flavours' `__sanitizer_silent_reports`), with `libclang_rt.asan.a` and `libunwind.a`
checked against harness.yaml. The instrumentation must match the runtime. Built with the
system clang 15 the program faulted on its shadow under qemu, and with their clang 20 it runs
as their binaries do (theirs run under the same qemu, from the reac-pw-bin release asset).

| build | functions | conforming | ours (of which L2) | musl | libunwind | compiler-rt (incl. ASan) |
| --- | --- | --- | --- | --- | --- | --- |
| plain | 111 | 62 | 15 (14) | 43 of 82 | | 5 of 14 |
| ubsan | 111 | 61 | 15 (13) | 43 of 82 | | 5 of 14 |
| asan | 1,244 | 540 | 17 (12) | 101 of 216 | 12 of 45 | 414 of 966 |
| asan-ubsan | 1,244 | 540 | 17 (12) | 101 of 216 | 12 of 45 | 414 of 966 |

After the two profile changes of 2026-11-22 (R2: a call may end a function; `unimp` is a trap
with LPS's meaning, the process dies with SIGILL; docs/isa/profile.md):

| build | conforming | ours at L2 | musl | libunwind | compiler-rt |
| --- | --- | --- | --- | --- | --- |
| plain | 68 of 111 | 14 of 15 | 49 of 82 | | 5 of 14 |
| ubsan | 68 of 111 | 14 of 15 | 49 of 82 | | 5 of 14 |
| asan | 689 of 1,244 | 15 of 17 (and emit_printf at L1) | 128 of 216 | 13 of 45 | 532 of 966 |
| asan-ubsan | 689 of 1,244 | 15 of 17 (and emit_printf at L1) | 128 of 216 | 13 of 45 | 532 of 966 |

Of ours, only `target_run` is below L1 in every build (the guarded call to the undefined weak
`LLVMFuzzerInitialize`). It stays at L0 (lead, 2026-11-22 15:04): its proof steps the guard by
hand, since the weak symbol's address is 0 and the branch skips the call.

Before the R2 change, in the asan builds, `LLVMFuzzerTestOneInput`, `reac_etf_qdisc_state` and `oft_exit_guard`
fell through their last instruction (R2). They end on a call ASan inserts to a noreturn
report function, which `-D_Noreturn=` cannot remove. `-fsanitize-recover` would remove it
but changes behaviour. The profile now allows exactly that: a call may end a function, and
the caller's proof shows from the callee's spec that it never returns (lead, 2026-11-22).

`nocompiler export --process` also writes what a whole-process proof needs: `elfEntry`,
`phdrInfo` (`NoCompiler.Linux.PhdrInfo`: what `AT_PHDR`, `AT_PHENT` and `AT_PHNUM` give, which
musl's `__init_libc`/`__init_tls` read), and `seg_phdrs` (the program headers' bytes where the
first `PT_LOAD` maps them; not in `segments`). The `--process` export of this build checks in
Lean: 18.0 s, 1.69 GB, load 9.

Not yet in: `__set_thread_area`, `__syscall_cp_asm` and crt1's `_start` are assembly with
size-0 symbols, which the loader skips, so a call to one is "not a function entry". A loader fix
(on branch `b-loader-size0`) sizes them up to the next symbol. It gives 64 of 113 here and
libc-slen 23 of 42 (was 20 of 40). But it changes A's committed `lean/Examples/Libc/SlenImage.lean`
(`_start` becomes a function and domains grow), so it waits for A.

The chunk export (`nocompiler export --format chunks`, the L1+ functions) takes 0.17 s and
is 240 KB. `lake env lean` accepts it: 10.4 s, 1.68 GB, load 4.0 (before the two flags).

## musl rebuilt with options against the jump-into-loop shape (QUEUE-B 2)

musl 1.2.5 built as examples/libc/build.sh does, plus the flags below; slen.c linked against
each build. Conforming functions, with the loader fix (of 42):

| musl built with | conforming |
| --- | --- |
| as now | 23 |
| `-mllvm -disable-block-placement` | 27 |
| `-mllvm -rotation-max-header-size=0` (no loop rotation) | 22 (memset breaks) |
| `-mllvm -enable-tail-merge=false` | 23 |
| block placement off and tail merge off | 27 |
| block placement off and rotation off | 29 |
| the same, and `-D_Noreturn=` | 29 |

Block placement and rotation both off fixes all five R3 functions: `__init_libc`, `fwrite`,
`__stdio_read`, `__stdio_write` and `memcpy`. What is left is R2 (calls through function
pointers in stdio and the init/fini arrays; `exit` ending on `_Exit`) and R1 (the `A`
atomics in `__lock`). A rebuilt musl changes the bytes A's slen proofs are about, so
adopting it is A's and the lead's call.

For fuzz_qdisc, their musl (f21a9653 with static-asan's musl patches, their `-march=rv64g
-mabi=lp64d -ffunction-sections -fdata-sections`) rebuilt with the system clang 15 (before the switch to their clang), without
the loader fix:

| their musl rebuilt with | conforming (of 110) | musl at L1+ (of 81) | musl R3 |
| --- | --- | --- | --- |
| no extra flags | 66 | 47 | 9 |
| block placement off | 70 | 51 | 5 |
| block placement and rotation off | 71 | 52 | 4 |
| the same, and `-D_Noreturn=` | 71 | 52 | 4 |
| block placement, rotation and tail merge off | 72 | 53 | 3 |

With their exact `libc.a` it is 62 of 111 (musl 43 of 82). A rebuilt musl is no longer
their binary's libc, so adopting it for fuzz_qdisc trades the like-for-like comparison
for 10 more conforming musl functions (53 of 81 against 43 of 82). That is the lead's call.

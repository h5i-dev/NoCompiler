#!/usr/bin/env bash
# fuzz_qdisc (OSS Verify's projects/reac-pw/fuzz_qdisc), plain build, linked as theirs is:
# their driver and the OSS-Fuzz adapter (recipe src/cli.c, ossfuzz_adapter.h), the
# harness and reac_qdisc_etf_catchup_slots, with their exact musl libc.a/crt*.o and
# compiler-rt builtins (toolchain.sh checks the SHA-256s harness.yaml gives).
#
# What differs from their plain build (harness.yaml, recipe tools/build-body.sh):
# - Our code is compiled by `nocompiler cc -c` (the profile's flags, -O2) with their clang 20.1.8
#   (toolchain.sh; the ASan instrumentation must match their runtime) instead of `-march=rv64g -mabi=lp64d -Os -g -ffunction-sections
#   -fdata-sections -fno-stack-protector -fno-plt`. Our code: fuzz_qdisc.c, the
#   extracted reac_qdisc_etf_catchup_slots, the driver cli.c and the plugin.
#   `-march=rv64imfd -mabi=lp64d`: the float ABI tag their libraries carry (ld.lld will
#   not link lp64 objects with lp64d ones; `nocompiler check` shows no F or D instruction in
#   our functions), and no Zba/Zbb, which `nocompiler cc` would otherwise allow: LPS models
#   RV64GC, so the LPS statements (D, QUEUE-D 3) need our code inside it as theirs is.
# - reac-pw: only reac_qdisc_etf_catchup_slots, extracted verbatim, with the shim's
#   declarations and the delta constant (shim/), not their static library of reac-pw's
#   nine readers. The harness calls nothing else of it.
# - Their wrap_getenv/wrap_getpid objects are not linked: this harness calls neither.
# - The plugin is ours (src/plugin.c), written as their OSS-Fuzz targets' plugin.c is.
# - Linked by ld.lld directly: crt1.o crti.o crtbegin.o, the objects, libc.a,
#   libclang_rt.builtins.a, crtend.o crtn.o, -static --gc-sections (their musl.cfg's link).
#   Not stripped.
#
#   SCRATCH=DIR examples/qdisc/build.sh [--update]
#                                          writes $SCRATCH/fuzz_qdisc.{plain,ubsan,asan,asan-ubsan}.elf and
#                                          checks them against SHA256SUMS (--update rewrites it)
# CLANG, LLD and QEMU override the tools; under QEMU it runs a few inputs.
set -euo pipefail
cd "$(dirname "$0")/../.."
SCRATCH=${SCRATCH:-examples/build/qdisc}
NOCOMPILER=${NOCOMPILER:-target/release/nocompiler}
LLD=${LLD:-$(command -v ld.lld || command -v ld.lld-20 || echo ld.lld)}
QEMU=${QEMU:-$(command -v qemu-riscv64 || command -v qemu-riscv64-static || true)}
examples/qdisc/fetch.sh >/dev/null
examples/qdisc/toolchain.sh >/dev/null
U="$SCRATCH/upstream"; T="$SCRATCH/toolchain"; O="$SCRATCH/obj"
lib="$T/opt/musl-sysroot/usr/lib"; rt="$T/opt/asan-rt/lib/clang/20/lib/riscv64-unknown-linux-musl"
mkdir -p "$O"
export CLANG=${CLANG:-$T/bin/clang}   # their clang 20.1.8 (toolchain.sh); nocompiler cc runs it
res=$("$CLANG" -print-resource-dir)
# Two flags for our code beyond `nocompiler cc`'s, each removing a shape the profile rejects
# without changing what the code does:
# - `-D_Noreturn=`: musl declares abort, exit and _exit `_Noreturn`, so clang ends a function on
#   such a call and its last instruction falls through past it (R2: check_slots, oft_exit_guard).
#   Without the attribute a return follows the call; the call still never returns, which a proof
#   shows from musl's code rather than assumes. (-ffreestanding keeps clang from knowing abort.)
# - `-mllvm -enable-tail-merge=false`: branch folding merges the driver's error tails
#   (`DIAG(...); free(buf); return 2`), and a later one jumps back into an earlier one, which reads
#   as a loop entered in its middle (R3: main).
musl=(--target=riscv64-unknown-linux-musl -march=rv64imfd -mabi=lp64d -O2
  -nostdinc -isystem "$res/include" -isystem "$T/opt/musl-sysroot/usr/include"
  -D_Noreturn= -mllvm -enable-tail-merge=false)
shim=(-I examples/qdisc/shim -include reac/transport/reac_etf_qdisc.h -include reac_qdisc.h)
cc() { "$NOCOMPILER" cc -c "${musl[@]}" "$@"; }
# Their flavours (recipe tools/build-body.sh): the sanitizer flags go to the harness, the
# library and the plugin, never to the driver (cli.c gets their BASE_CFLAGS only). ubsan traps
# inline (`-fsanitize-trap=all`), with no runtime; asan links their sealed static ASan runtime.
ub="-fsanitize=undefined -fno-sanitize-recover=all -fsanitize-trap=all -fno-sanitize=function"
declare -A SAN=([plain]="" [ubsan]="$ub" [asan]="-fsanitize=address" [asan-ubsan]="-fsanitize=address $ub")
srt="$T/opt/asan-static-rt/lib/clang/20/lib/riscv64-unknown-linux-musl"
cc -I "$U/recipe" "$U/recipe/cli.c" -o "$O/cli.o"
for flav in plain ubsan asan asan-ubsan; do
  mkdir -p "$O/$flav"
  san=(${SAN[$flav]})
  cc "${san[@]}" "${shim[@]}" "$U/fuzz_qdisc.c" -o "$O/$flav/fuzz_qdisc.o"
  cc "${san[@]}" "${shim[@]}" "$U/reac_qdisc_etf_catchup_slots.c" -o "$O/$flav/slots.o"
  cc "${san[@]}" -I "$U/recipe" examples/qdisc/src/plugin.c -o "$O/$flav/plugin.o"
  elf="$SCRATCH/fuzz_qdisc.$flav.elf"
  objs=("$O/cli.o" "$O/$flav/plugin.o" "$O/$flav/fuzz_qdisc.o" "$O/$flav/slots.o")
  case $flav in
  plain|ubsan)
    "$LLD" -static --gc-sections --build-id=none "$lib/crt1.o" "$lib/crti.o" "$rt/clang_rt.crtbegin.o" \
      "${objs[@]}" "$lib/libc.a" "$rt/libclang_rt.builtins.a" "$rt/clang_rt.crtend.o" "$lib/crtn.o" \
      -Map="${elf%.elf}.map" -o "$elf" ;;
  *)
    # Their asan-musl-sealed.cfg's static link, as clang's driver spells it: the ASan runtime
    # whole, libunwind, the wrap list, the sealed-init seal, and their asan flavours'
    # __sanitizer_silent_reports. musl's libdl/libpthread (libunwind's dependent libraries)
    # are empty archives: --no-dependent-libraries.
    "$LLD" -static --gc-sections --no-warn-backrefs --no-dependent-libraries --build-id=none \
      "$lib/crt1.o" "$lib/crti.o" "$srt/clang_rt.crtbegin.o" \
      --whole-archive "$srt/libclang_rt.asan_static.a" "$srt/libclang_rt.asan.a" --no-whole-archive \
      "${objs[@]}" --start-group "$srt/libclang_rt.builtins.a" "$lib/libunwind.a" "$lib/libc.a" --end-group \
      "$srt/clang_rt.crtend.o" "$lib/crtn.o" @"$srt/libclang_rt.asan.a.wrap" \
      --defsym=__sanitizer_sealed_init=1 --defsym=__sanitizer_silent_reports=1 \
      -Map="${elf%.elf}.map" -o "$elf" ;;
  esac
  echo "built $elf, SHA-256 $(sha256sum "$elf" | cut -c1-64)"
  # The profile check, counted by rule and by where each function comes from.
  "$NOCOMPILER" check --json "$elf" > "${elf%.elf}.check.json" || true
  python3 -I examples/qdisc/src/count.py "${elf%.elf}.check.json" "${elf%.elf}.map"
done
# The builds are reproducible: each ELF is the SHA-256 examples/qdisc/SHA256SUMS records (the ELFs
# themselves are not committed: GPL). `--update` records the current ones instead.
if [ "${1:-}" = --update ]; then
  (cd "$SCRATCH" && sha256sum fuzz_qdisc.plain.elf fuzz_qdisc.ubsan.elf fuzz_qdisc.asan.elf fuzz_qdisc.asan-ubsan.elf) \
    > examples/qdisc/SHA256SUMS
elif ! (cd "$SCRATCH" && sha256sum -c --quiet "$OLDPWD/examples/qdisc/SHA256SUMS"); then
  echo "build.sh: a build differs from examples/qdisc/SHA256SUMS"; exit 1
fi
echo "ok   the four ELFs are the SHA-256s examples/qdisc/SHA256SUMS records"
if [ -n "$QEMU" ]; then
  # Their driver's input: a 2-byte config word (length, and bit 15 to count allocations),
  # the config, 4 bytes, the payload; config byte 0 & 3 picks 1 to 4 calls, each printed.
  status=0
  for flav in plain ubsan asan asan-ubsan; do
  printf '\001\000\003\000\000\000\000abcdefghijklmnopqrstuvwxyz0123456789' > "$O/in.ok"
  got=$("$QEMU" "$SCRATCH/fuzz_qdisc.$flav.elf" "$O/in.ok" | tr '\n' ' ') || status=1
  [ "$got" = "0 0 0 0 " ] || { echo "$flav, 4 calls: printed '$got'"; status=1; }
  printf '\001' > "$O/in.short"
  "$QEMU" "$SCRATCH/fuzz_qdisc.$flav.elf" "$O/in.short" 2>/dev/null && { echo "$flav: a short input exited 0"; status=1; }
  done
  [ $status = 0 ] && echo "ok   plain, ubsan, asan, asan-ubsan under $(basename "$QEMU"): 4 calls print 0 four times and exit 0; a short header exits 2"
  exit $status
fi

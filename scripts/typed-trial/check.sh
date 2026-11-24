#!/bin/bash
# Checks the annotated trial files against the objects compiled from C (I15), with the
# default rules and with proposal P1 (--loops natural).
#   scripts/typed-trial/check.sh [BUILD_DIR]
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"
B=${1:-/mnt/scratch/$USER/typed-trial-build}
T=${NOCOMPILER_TYPED:-${CARGO_TARGET_DIR:-target}/release/nocompiler-typed}
for a in examples/typed/ann/*.ann; do
  f=$(basename "$a" .ann)
  echo "== $f (S2)"; "$T" check "examples/typed/$f.s" --object "$B/$f.o"
  echo "== $f (P1)"; "$T" check "examples/typed/$f.s" --object "$B/$f.o" --loops natural
done
# Run the programs that have a _start under qemu (a sanity check of the compiled code).
LLD=${LLD:-$(command -v ld.lld || command -v ld.lld-20 || true)}
QEMU=${QEMU_RISCV64:-$(command -v qemu-riscv64-static || command -v qemu-riscv64 || true)}
if [ -n "$LLD" ] && [ -n "$QEMU" ]; then
  "$LLD" -static -e _start -o "$B/hello.elf" "$B/hello.o"
  out=$("$QEMU" "$B/hello.elf"); rc=$?
  [ "$out" = "nocompiler" ] && [ $rc -eq 0 ] && echo "qemu hello: ok" || echo "qemu hello: FAILED ($out, $rc)"
  "$LLD" -static -e _start -o "$B/sum.elf" "$B/sum.o"
  "$QEMU" "$B/sum.elf"; rc=$?
  [ $rc -eq 24 ] && echo "qemu sum: ok (24)" || echo "qemu sum: FAILED ($rc)"
else
  echo "qemu run skipped: needs ld.lld and qemu-riscv64"
fi

#!/bin/bash
# Compiles the note's trial functions (docs/typed/note-trial.md) as-is, with the musl trial's
# pinned flags (docs/typed/musl-trial.md) except -std=gnu99 (the sources use inline asm for
# ecall), to assembly and objects in $OUT.
#   scripts/typed-trial/build.sh [OUT]      (default: /mnt/scratch/$USER/typed-trial-build)
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
OUT=${1:-/mnt/scratch/$USER/typed-trial-build}
CC=${CC:-clang}
"$CC" --version | head -1 | grep -q 'clang version 15.0.7' || { echo "need clang 15.0.7" >&2; exit 1; }
mkdir -p "$OUT"
ARCHF="--target=riscv64-linux-musl -march=rv64im_zba_zbb -mabi=lp64 -mno-relax -mcmodel=medany -fno-pic -fno-jump-tables"
CFLAGS="-O2 -std=gnu99 -nostdinc -ffreestanding -fno-builtin -fno-stack-protector -fomit-frame-pointer \
 -fno-unwind-tables -fno-asynchronous-unwind-tables -ffunction-sections -fdata-sections -msmall-data-limit=0"
for s in sum cobs hello; do
  "$CC" $ARCHF $CFLAGS -S -o "$OUT/$s.s" "examples/typed/src/$s.c"
  "$CC" $ARCHF $CFLAGS -c -o "$OUT/$s.o" "examples/typed/src/$s.c"
done
echo "$CC $ARCHF $CFLAGS" > "$OUT/FLAGS"
echo "built in $OUT"

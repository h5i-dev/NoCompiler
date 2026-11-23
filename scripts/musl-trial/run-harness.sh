#!/usr/bin/env bash
# Link the objects assembled from examples/musl/*.s (run verify.sh first) with harness.c and run
# under qemu-riscv64. Usage: run-harness.sh [OUT]
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=${1:-/mnt/scratch/ec2-user/musl-trial-build}
QEMU=${QEMU:-/mnt/scratch/ec2-user/bin/qemu-riscv64-static}
LLD=${LLD:-$(command -v ld.lld || command -v ld.lld-20)}
clang --target=riscv64-linux-musl -march=rv64im_zba_zbb -mabi=lp64 -mno-relax -mcmodel=medany \
  -O1 -ffreestanding -fno-builtin -nostdinc -fno-stack-protector -c "$HERE/harness.c" -o "$OUT/harness.o"
objs=$(grep -v '^#' "$HERE/functions.txt" | awk 'NF{print $1}' | while read -r n; do
  [ -f "$OUT/$n.ann.o" ] && echo "$OUT/$n.ann.o"; done)
"$LLD" -static -nostdlib -e _start -o "$OUT/harness.elf" "$OUT/harness.o" $objs --defsym=memrchr=__memrchr
"$QEMU" "$OUT/harness.elf"

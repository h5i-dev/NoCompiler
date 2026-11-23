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
# Run 1: the base objects. Run 2: each variant NAME-SUFFIX replaces NAME.
names=$(grep -v '^#' "$HERE/functions.txt" | awk 'NF{print $1}')
base=$(for n in $names; do case $n in *-*) ;; *) echo "$n";; esac; done)
link_run() { # $1 = label, rest = names
  local label=$1; shift; local objs=""
  for n in "$@"; do [ -f "$OUT/$n.ann.o" ] && objs="$objs $OUT/$n.ann.o"; done
  "$LLD" -static -nostdlib -e _start -o "$OUT/harness-$label.elf" "$OUT/harness.o" $objs --defsym=memrchr=__memrchr
  echo -n "[$label] "; "$QEMU" "$OUT/harness-$label.elf"
}
link_run base $base
variants=$(for n in $names; do case $n in *-*) echo "$n";; esac; done)
if [ -n "$variants" ]; then
  link_run variants $(for n in $base; do v=$(echo "$variants" | grep "^$n-" | head -1); echo "${v:-$n}"; done)
fi

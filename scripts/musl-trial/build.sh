#!/usr/bin/env bash
# Build the musl trial functions from pinned musl 1.2.5 source with pinned flags.
# Usage: build.sh [OUT]   (default OUT=/mnt/scratch/ec2-user/musl-trial-build)
# Writes OUT/<name>.o, OUT/<name>.dis (disassembly with encodings), OUT/<name>.text (raw .text
# bytes of the function's section), OUT/<name>.err on compile failure. Never commit OUT.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
MUSL=${MUSL_SRC:-/mnt/scratch/ec2-user/libc-a/src/musl-1.2.5}
OUT=${1:-/mnt/scratch/ec2-user/musl-trial-build}
CC=${CC:-clang}
mkdir -p "$OUT/include/bits" "$OUT/internal"

# Pinned toolchain and source.
"$CC" --version | head -1 | grep -q 'clang version 15.0.7' || { echo "need clang 15.0.7" >&2; exit 1; }
# Digest over every file the build can read (sources, headers, header generators).
tree_digest() { (cd "$MUSL" && find COPYRIGHT include arch/riscv64 arch/generic src tools/mkalltypes.sed -type f | LC_ALL=C sort | xargs sha256sum | sha256sum | cut -d' ' -f1); }
[ "$(tree_digest)" = "$(cat "$HERE/musl-tree.sha256")" ] || { echo "musl source differs from pin" >&2; exit 1; }

# Generated headers, as musl's Makefile makes them.
sed -f "$MUSL/tools/mkalltypes.sed" "$MUSL/arch/riscv64/bits/alltypes.h.in" "$MUSL/include/alltypes.h.in" > "$OUT/include/bits/alltypes.h"
{ cat "$MUSL/arch/riscv64/bits/syscall.h.in"; sed -n -e 's/__NR_/SYS_/p' < "$MUSL/arch/riscv64/bits/syscall.h.in"; } > "$OUT/include/bits/syscall.h"
echo '#define VERSION "1.2.5"' > "$OUT/internal/version.h"

ARCHF="--target=riscv64-linux-musl -march=rv64im_zba_zbb -mabi=lp64 -mno-relax -mcmodel=medany -fno-pic -fno-jump-tables"
CFLAGS="-O2 -std=c99 -nostdinc -ffreestanding -fno-builtin -frounding-math -fno-strict-aliasing \
 -fno-stack-protector -fomit-frame-pointer -fno-unwind-tables -fno-asynchronous-unwind-tables \
 -ffunction-sections -fdata-sections -msmall-data-limit=0 -w -D_XOPEN_SOURCE=700"
INC="-I$MUSL/arch/riscv64 -I$MUSL/arch/generic -I$OUT/internal -I$MUSL/src/include -I$MUSL/src/internal -I$OUT/include -I$MUSL/include"
echo "$CC $ARCHF $CFLAGS -c" > "$OUT/FLAGS"

grep -v '^#' "$HERE/functions.txt" | while read -r name src sym; do
  [ -n "$name" ] || continue
  rm -f "$OUT/$name".{o,dis,text,err}
  if ! $CC $ARCHF $CFLAGS $INC -c -o "$OUT/$name.o" "$MUSL/src/$src" 2> "$OUT/$name.err"; then
    echo "$name: COMPILE FAILED (see $OUT/$name.err)"; continue
  fi
  rm -f "$OUT/$name.err"
  llvm-objdump -d -r -M no-aliases --mattr=+m,+zba,+zbb "$OUT/$name.o" > "$OUT/$name.dis"
  llvm-objcopy -O binary --only-section=".text.$sym" "$OUT/$name.o" "$OUT/$name.text"
  echo "$name: $(stat -c %s "$OUT/$name.text") bytes, sha256 $(sha256sum < "$OUT/$name.text" | cut -c1-16)"
done

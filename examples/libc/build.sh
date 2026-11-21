#!/usr/bin/env bash
# The libc example (STATUS-A plan, lead 16:47): static musl programs proved as
# whole processes. Builds musl 1.2.5 with the profile's flags, then slen.c and
# flen.c against it, and compares with the committed ELFs, examples/elf/libc-{slen,flen}.elf
# (with the other committed binaries; `*.elf` is ignored elsewhere).
#
#   MUSL_TARBALL=musl-1.2.5.tar.gz examples/libc/build.sh [--update]
#
# The tarball is checked against the pinned SHA-256 (https://musl.libc.org).
# musl is built soft-float without C, F or D; A only because musl's inline
# atomics must assemble (they are in __lock/__unlock, which return before them
# while the process has one thread). Under QEMU (qemu-riscv64 or
# qemu-riscv64-static on PATH) each program is also run on a few inputs.
# CLANG, LLD, SCRATCH override the tools and the build directory.
set -euo pipefail
cd "$(dirname "$0")/../.."
CLANG=${CLANG:-clang}
LLD=${LLD:-$(command -v ld.lld || command -v ld.lld-20 || echo ld.lld)}
SCRATCH=${SCRATCH:-examples/build/libc}
MUSL_SHA256=a9a118bbe84d8764da0ea0d28b3ab3fae8477fc7e4085d90102b8596fc7c75e4
: "${MUSL_TARBALL:?set MUSL_TARBALL to musl-1.2.5.tar.gz}"
echo "$MUSL_SHA256  $MUSL_TARBALL" | sha256sum -c --quiet
mkdir -p "$SCRATCH"
SCRATCH=$(cd "$SCRATCH" && pwd)
sys="$SCRATCH/sysroot"
if [ ! -f "$sys/lib/libc.a" ]; then
  rm -rf "$SCRATCH/src" "$SCRATCH/obj" && mkdir -p "$SCRATCH/src" "$SCRATCH/obj"
  tar xzf "$MUSL_TARBALL" -C "$SCRATCH/src"
  (cd "$SCRATCH/obj" && "$SCRATCH/src/musl-1.2.5/configure" --target=riscv64-linux-musl --prefix="$sys" \
    --disable-shared CC="$CLANG --target=riscv64-linux-musl -march=rv64ima_zba_zbb -mabi=lp64 -mcmodel=medany \
-mno-relax -fno-pic -fno-jump-tables" AR=llvm-ar RANLIB=llvm-ranlib CFLAGS=-O2 LIBCC=' ' > configure.log &&
    make -j"${JOBS:-4}" > make.log && make install > install.log)
fi
cflags=(--target=riscv64-linux-musl -march=rv64im_zba_zbb -mabi=lp64 -mcmodel=medany -mno-relax -fno-pic
  -fno-jump-tables -O2 -ffreestanding -fno-asynchronous-unwind-tables -fno-unwind-tables -fno-ident
  -nostdinc -isystem "$sys/include")
qemu=$(command -v qemu-riscv64 || command -v qemu-riscv64-static || true)
status=0
for name in slen flen; do
  "$CLANG" "${cflags[@]}" -c "examples/libc/$name.c" -o "$SCRATCH/$name.o"
  "$LLD" -static -e _start --build-id=none -z noseparate-code "$sys/lib/crt1.o" "$sys/lib/crti.o" \
    "$SCRATCH/$name.o" "$sys/lib/libc.a" "$sys/lib/crtn.o" -o "$SCRATCH/$name.elf"
  # Not `nocompiler annotate`d: it refuses a binary whose functions do not all
  # conform, and musl's do not (`nocompiler check`); no proof needs the section.
  if [ -n "$qemu" ]; then
    for n in 0 1 12 64 65 1000; do
      head -c "$n" /dev/zero > "$SCRATCH/in.$n"
      if [ $name = slen ]; then got=$("$qemu" "$SCRATCH/$name.elf" < "$SCRATCH/in.$n")
      else got=$("$qemu" "$SCRATCH/$name.elf" "$SCRATCH/in.$n"); fi
      [ "$got" = "$n" ] || { echo "$name on $n bytes: printed '$got'"; status=1; }
    done
  fi
  if [ "${1:-}" = --update ]; then
    cp "$SCRATCH/$name.elf" "examples/elf/libc-$name.elf"
  elif ! cmp -s "$SCRATCH/$name.elf" "examples/elf/libc-$name.elf"; then
    echo "libc-$name.elf: the build differs from examples/elf/"; status=1
  fi
done
[ $status = 0 ] && echo "ok   slen, flen${qemu:+ (and their outputs under $(basename "$qemu"))}"
exit $status

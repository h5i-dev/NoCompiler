#!/usr/bin/env bash
# The C1 test (lean/Examples/Linux/AutoP.lean): assemble autop.s, link it, export the image.
#   examples/linux-autop/build.sh      (NOCOMPILER, LLD override the tools)
# The committed examples/elf/linux-autop.elf was linked by LLD 23.1.4 (llvm f738f3b0; the rust-lld of Rust
# nightly-2026-11-01, run as `rust-lld -flavor gnu`); with it this script reproduces both outputs byte for
# byte (checked 2026-11-23). Other LLD versions give the same 15 code words but a different symbol table,
# so the ELF's sha256, and elfSha256 in lean/Examples/Linux/AutoPImg.lean, differ.
set -euo pipefail
cd "$(dirname "$0")/../.."
NOCOMPILER=${NOCOMPILER:-target/release/nocompiler}
LLD=${LLD:-$(command -v ld.lld || echo ld.lld)}
out=examples/build/linux-autop
mkdir -p "$out"
"$NOCOMPILER" asm examples/linux-autop/autop.s -o "$out/autop.o" >/dev/null
"$LLD" -static -e _start --build-id=none "$out/autop.o" -o examples/elf/linux-autop.elf
"$NOCOMPILER" export --lean-level-check examples/elf/linux-autop.elf --namespace Examples.Linux.AutoPImg \
  -o lean/Examples/Linux/AutoPImg.lean

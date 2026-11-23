#!/usr/bin/env bash
# The libraries OSS Verify's fuzz_qdisc builds link, exactly: musl's libc.a, crt1.o,
# crti.o, crtn.o, libunwind.a and headers, and LLVM compiler-rt (builtins, crtbegin/crtend, and the
# sanitizer runtimes, with the sealed static ASan runtime and its wrap list), from their pinned toolchain image
# (release.yaml: ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:6a6b4816...,
# one layer), and their clang (Alpine clang 20.1.8, with its libraries and the image's musl
# loader; $SCRATCH/toolchain/bin/clang runs it). The layer (1.1 GB) is streamed and only these
# paths are kept (about 900 MB in $SCRATCH/toolchain). Its digest, and the SHA-256s harness.yaml gives
# for libc.a, crt1.o, libclang_rt.builtins.a and clang_rt.crtbegin.o, are checked.
# musl is MIT; compiler-rt is Apache-2.0 WITH LLVM-exception.
#
#   SCRATCH=DIR examples/qdisc/toolchain.sh   (default examples/build/qdisc)
set -euo pipefail
cd "$(dirname "$0")/../.."
SCRATCH=${SCRATCH:-examples/build/qdisc}
T="$SCRATCH/toolchain"
REPO=theorem-labs/oss-fuzz-theorems-toolchain
LAYER=681ec304e5e1cbbc26e833ef7ebbf8de3bdda7100dac677aff8ddbb8e6582ab0
lib=opt/musl-sysroot/usr/lib
rt=opt/asan-rt/lib/clang/20/lib/riscv64-unknown-linux-musl
want() {  # file, sha256
  echo "$2  $T/$1" | sha256sum -c --quiet || { echo "toolchain.sh: $1 has the wrong SHA-256" >&2; exit 1; }
}
if [ ! -f "$T/.done-3" ]; then
  rm -rf "$T" && mkdir -p "$T"
  tok=$(curl -sSf -m 60 "https://ghcr.io/token?scope=repository:$REPO:pull" |
    python3 -I -c 'import json,sys; print(json.load(sys.stdin)["token"])')
  got=$(curl -sSfL -m 3000 -H "Authorization: Bearer $tok" "https://ghcr.io/v2/$REPO/blobs/sha256:$LAYER" |
    python3 -I examples/qdisc/src/layer.py "$T" opt/musl-sysroot/usr/include/ \
      $lib/libc.a $lib/crt1.o $lib/crti.o $lib/crtn.o $lib/libunwind.a opt/asan-rt/ opt/asan-static/ \
      opt/asan-static-rt/lib/clang/20/lib/riscv64-unknown-linux-musl/ lib/ usr/lib/llvm20/ usr/lib/lib)
  [ "$got" = "$LAYER" ] || { echo "toolchain.sh: the layer's digest is $got, not $LAYER" >&2; exit 1; }
  # Their clang (Alpine clang 20.1.8, linked against musl) runs through the image's own loader.
  chmod +x "$T/lib/ld-musl-x86_64.so.1" "$T"/usr/lib/llvm20/bin/*
  mkdir -p "$T/bin"
  abs=$(cd "$T" && pwd)
  printf '#!/bin/sh\nexec %s/lib/ld-musl-x86_64.so.1 --library-path %s/usr/lib:%s/usr/lib/llvm20/lib %s/usr/lib/llvm20/bin/clang-20 -resource-dir=%s/usr/lib/llvm20/lib/clang/20 "$@"\n' \
    "$abs" "$abs" "$abs" "$abs" "$abs" > "$T/bin/clang"
  chmod +x "$T/bin/clang"
  touch "$T/.done-3"
fi
want $lib/libc.a f19509197da87e158d2111bde83f0943296a4ee5506b024004f1d68c63c496e9
want $lib/crt1.o 111e0dda16a02983fee66cc70e332b41860dccad42d8fb0990776814ef70930a
want $rt/libclang_rt.builtins.a 7e376dbc917599242272aa6e70e66b249ed063d78bd707e88e607e6ed375fa29
want $rt/clang_rt.crtbegin.o 0ba7749fe1a9cfc61b7b4dbb8616ce4cffad430bdd04ec029cd291d030925e72
# The asan builds' runtime (the sealed config's resource dir) and libunwind (harness.yaml, asan).
srt=opt/asan-static-rt/lib/clang/20/lib/riscv64-unknown-linux-musl
want $srt/libclang_rt.asan.a 078168dea88da7f13cccc6ca7305c6e2df0202f4f0364c7caa23a20a1faa5418
want $srt/libclang_rt.builtins.a 7e376dbc917599242272aa6e70e66b249ed063d78bd707e88e607e6ed375fa29
want $srt/clang_rt.crtbegin.o 0ba7749fe1a9cfc61b7b4dbb8616ce4cffad430bdd04ec029cd291d030925e72
want $lib/libunwind.a 80167e95a699a1a21d3933967631fe5484817812aeda2cb98a55b652d608f812
"$T/bin/clang" --version | grep -q "clang version 20.1.8" || { echo "toolchain.sh: their clang does not run" >&2; exit 1; }
echo "ok   $T: their musl, compiler-rt and clang 20.1.8; the SHA-256s harness.yaml gives"

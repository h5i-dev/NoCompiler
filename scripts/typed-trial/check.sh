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

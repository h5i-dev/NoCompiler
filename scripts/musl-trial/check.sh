#!/usr/bin/env bash
# Run the Rust checker on every annotated musl file against the object compiled from musl
# (--object, I15: the checked instructions are the object's bytes). Run verify.sh first.
# Usage: [CHECK_FLAGS="--loops natural"] check.sh [OUT]   (CHECKER defaults to the release build in target-nc-v)
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../.." && pwd)
OUT=${1:-/mnt/scratch/ec2-user/musl-trial-build}
CHECKER=${CHECKER:-/mnt/scratch/ec2-user/target-nc-v/release/nocompiler-typed}
while read -r name src sym extra; do
  [[ -z "$name" || "$name" == \#* ]] && continue
  f="$ROOT/examples/musl/$name.s"; [ -f "$f" ] || continue
  printf '%-12s ' "$name"; "$CHECKER" check "$f" --object "$OUT/$name.o" ${CHECK_FLAGS:-} 2>&1 | head -1 | cut -c1-160
done < "$HERE/functions.txt"

#!/usr/bin/env bash
# Regenerate unannotated skeletons OUT/<name>.skel.s for every function in functions.txt.
# (The annotated files in examples/musl/ start as a copy of these and only gain `#:` lines.)
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); OUT=${1:-/mnt/scratch/ec2-user/musl-trial-build}
while read -r name src sym; do
  [[ -z "$name" || "$name" == \#* ]] && continue
  [ -f "$OUT/$name.o" ] && python3 "$HERE/skeleton.py" "$OUT/$name.o" "$sym" > "$OUT/$name.skel.s"
done < "$HERE/functions.txt"

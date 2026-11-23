#!/usr/bin/env bash
# Whole-program check (I34) over the musl trial: first all base files together (reports every
# rejection and every declaration/definition mismatch), then the largest closed subset that is
# safe: accepted functions whose declared safe callees are accepted too.
# Usage: [CHECK_FLAGS="--loops natural"] link.sh
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../.." && pwd)
CHECKER=${CHECKER:-/mnt/scratch/ec2-user/target-nc-v/release/nocompiler-typed}
files=$(grep -v '^#' "$HERE/functions.txt" | awk 'NF && $1 !~ /-/ {print $1}' | while read -r n; do
  [ -f "$ROOT/examples/musl/$n.s" ] && echo "$ROOT/examples/musl/$n.s"; done)
echo "== all base files"; "$CHECKER" link $files "$ROOT/examples/musl/malloc-free.s" ${CHECK_FLAGS:-} 2>&1 | grep -E '\[sig\]|\[recursion\]' || echo "no declaration mismatch, no recursion"
# Closed subset: drop rejected functions, then (repeatedly) functions declaring a dropped one.
keep=$(for f in $files; do o=$("$CHECKER" check "$f" ${CHECK_FLAGS:-} 2>&1); case "$o" in *REJECTED*) ;; *) echo "$f";; esac; done)
while :; do
  out=$("$CHECKER" link $keep ${CHECK_FLAGS:-} 2>&1); bad=$(echo "$out" | sed -n "s|^\(.*\.s\):[0-9]*: \[sig\] safe function .* is declared but defined in none.*|\1|p" | sort -u)
  [ -z "$bad" ] && break
  keep=$(for f in $keep; do echo "$bad" | grep -qx "$f" || echo "$f"; done)
done
"$CHECKER" link $keep ${CHECK_FLAGS:-} > /dev/null 2>&1; rc=$?
echo "== closed safe subset: $(echo $keep | wc -w) functions, link rc=$rc"; for f in $keep; do basename "$f" .s; done | tr '\n' ' '; echo

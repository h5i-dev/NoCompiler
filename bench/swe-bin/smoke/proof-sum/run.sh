#!/usr/bin/env bash
# QUEUE-D 2a: check_proof on the sum A/B example. base = examples/elf/refine-sum-a.elf; the
# submission = base with sum_b_only.s's `sum` (the loop's add commuted; sum_b.s without _start)
# linked in by the environment's `link` (swb-elf link); Proof.lean = a valid bonus proof for it.
# Then smoke/proofcheck_test.py runs the valid file and six broken variants.
#   run.sh WORKDIR        (NOCOMPILER, SWB_ELF, PY override the tools; run it through bin/slot)
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
W=${1:?WORKDIR}
NC=${NOCOMPILER:-/mnt/scratch/ec2-user/target-nc-d/release/nocompiler}
SW=${SWB_ELF:-/mnt/scratch/ec2-user/target-nc-d/release/swb-elf}
PY=${PY:-/mnt/scratch/ec2-user/swe-bin/venv/bin/python}
mkdir -p "$W"
cp "$ROOT/examples/elf/refine-sum-a.elf" "$W/base.elf"
"$NC" asm -o "$W/b.o" "$HERE/sum_b_only.s"
"$SW" link "$W/base.elf" "$W/b.o" "$W/sub.elf"
cp "$HERE/Proof.lean" "$W/Proof.lean"
PY=$PY "$PY" "$HERE/../proofcheck_test.py" "$W"

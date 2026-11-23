#!/bin/bash
# Annotates the compiled trial functions: examples/typed/ann/<f>.ann merged into the
# assembly from build.sh (clang's comments on label lines dropped, instructions unchanged),
# written to examples/typed/<f>.s. That the instructions are unchanged is checked by
# 'nocompiler-typed check examples/typed/<f>.s --object BUILD_DIR/<f>.o' (I15), see check.sh.
#   scripts/typed-trial/annotate.sh [BUILD_DIR]
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
B=${1:-/mnt/scratch/$USER/typed-trial-build}
for a in examples/typed/ann/*.ann; do
  f=$(basename "$a" .ann)
  sed -E 's/^(\.?[A-Za-z_0-9.$]+:)[[:space:]]+#.*$/\1/' "$B/$f.s" > "$B/$f.skel.s"
  python3 -I scripts/musl-trial/annotate.py "$B/$f.skel.s" "$a" > "examples/typed/$f.s"
done
echo "annotated: $(ls examples/typed/ann/*.ann | wc -l) files"

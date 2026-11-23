#!/usr/bin/env bash
# Per-build regeneration of what library proofs need (round 7, B's row): for one build ELF,
#   OUT/Image.lean    `nocompiler export --format chunks --process`: the image in chunks with every
#                     function's structure, plus elfEntry, phdrInfo, seg_phdrs (whole-process proofs);
#   OUT/Module.lean   `nocompiler module --format chunks`: the relocatable module (reuse theorems);
#   and, given the proofs file of an earlier build (OLD.nocompiler-proofs):
#   OUT/Reuse.lean, OUT/new.nocompiler-proofs   `nocompiler status --lean --record`: the reuse theorems
#                     for the proofs whose code is unchanged, and this build's proofs file (by-key).
# Generated files only; nothing is committed by this script (and no GPL-derived image may be).
#
#   scripts/gen/regen-images.sh ELF NAMESPACE OUT [OLD.nocompiler-proofs]
set -euo pipefail
elf=$1; ns=$2; out=$3; old=${4:-}
NOCOMPILER=${NOCOMPILER:-target/release/nocompiler}
mkdir -p "$out"
"$NOCOMPILER" export "$elf" --format chunks --process --namespace "$ns.Image" -o "$out/Image.lean" 2>"$out/export.log"
"$NOCOMPILER" module "$elf" --format chunks --namespace "$ns.Module" -o "$out/Module.lean" 2>"$out/module.log"
echo "ok   $out/Image.lean ($(grep -c '_entry : Word' "$out/Image.lean") functions), $out/Module.lean"
if [ -n "$old" ]; then
  set +e
  "$NOCOMPILER" status "$elf" --proofs "$old" --lean "$out/Reuse.lean" --namespace "$ns.Reuse" \
    --record "$out/new.nocompiler-proofs" > "$out/status.txt"
  st=$?
  set -e
  [ $st -le 1 ] || { echo "status failed ($st): $out/status.txt"; exit $st; }
  grep "proofs:" "$out/status.txt"
  echo "ok   $out/Reuse.lean, $out/new.nocompiler-proofs"
fi

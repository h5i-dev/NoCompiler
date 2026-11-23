#!/bin/bash
# Generate the fuzz_qdisc LPS images from their ELFs. None is stored in git: they are memory images of GPL-3.0
# code (the harness and reac-pw), kept off next like the ELFs themselves.
# usage: gen_qdisc_images.sh OVP_BIN_DIR [E5R_DIR]
#   OVP_BIN_DIR: the extracted reac-pw-bin.tar.zst of oss-verify-proofs v2026.11.1
#   E5R_DIR: our build's output dir (examples/qdisc/build.sh SCRATCH=DIR), for QdiscPlainE5r / QdiscUbsanE5r
# Each ELF's sha256 is checked against the one projects/reac-pw/fuzz_qdisc/harness.yaml pins.
set -euo pipefail
D=$1; here=$(cd "$(dirname "$0")" && pwd); out="$here/../../lean/Examples/LPS/Images"; lps="$here/../../scripts/lps"
mkdir -p "$out"
declare -A SHA=([plain]=21aef4ffae5c23d080ddeebd09817f912a84239c8be43339b3406726e9126d2c
  [ubsan]=a58ba8cbf19652111605a31fe2a6185a9efe43e81a1b8a74f3f11b3401d3b9fc
  [asan]=980e2b8458528060633e6c98fff20d2f46b97738c06eae4307d09f59c82c890e
  [asan-ubsan]=eb657d77bd4b27038d93f75626dcc6b37a48be09c889fda664b4f451c6602062)
declare -A NAME=([plain]=QdiscPlainOvp [ubsan]=QdiscUbsanOvp [asan]=QdiscAsanOvp [asan-ubsan]=QdiscAsanUbsanOvp)
for b in plain ubsan asan asan-ubsan; do
  f="$D/fuzz_qdisc.$b"; got=$(sha256sum "$f" | cut -c1-64)
  [ "$got" = "${SHA[$b]}" ] || { echo "sha256 mismatch for $f: $got" >&2; exit 1; }
  python3 -I "$lps/elf_snapshot_lean.py" "$f" "${NAME[$b]}" "$out/${NAME[$b]}.lean"
done
if [ $# -ge 2 ]; then
  for b in plain ubsan; do
    N=Qdisc${b^}E5r; f="$2/fuzz_qdisc.$b.elf"
    python3 -I "$lps/elf_snapshot_lean.py" "$f" "$N" "$out/$N.lean"
  done
fi
# Build the statement modules on the images (outside the default build and the axiom audit's walk, which skips
# every module in lean/Audit.lean's generatedImageModules; the Examples/LPS/Test runs: docs/design/lps-bridge.md).
cd "$here/../../lean"
lake build Examples.LPS.FuzzQdisc.Ovp
if [ $# -ge 2 ]; then lake build Examples.LPS.FuzzQdisc.E5r; fi

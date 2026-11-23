#!/usr/bin/env bash
# Download what the fuzz_qdisc build needs from upstream, at pinned commits, into
# $SCRATCH/upstream (not committed), and check every file's SHA-256:
#   fuzz_qdisc.c, fuzz.h   the harness as OSS Verify publishes it (theorem-labs/oss-verify-proofs,
#                          projects/reac-pw/fuzz_qdisc/source/; FreeREAC/reac-pw's fuzz/ unmodified).
#                          GPL-3.0-or-later.
#   reac_qdisc.c           FreeREAC/reac-pw src/reac_qdisc.c, GPL-3.0-or-later; from it
#                          reac_qdisc_etf_catchup_slots is extracted verbatim (its definition
#                          line to the first `}` line) and checked against a hash.
#   recipe/src/*           OSS Verify's driver (cli.c and the headers it and the OSS-Fuzz
#                          adapter include), from their release v2026.10.0-src recipe.tar.zst.
#                          No licence is stated for these files: they are not committed.
# The ELF built from these is GPL-3.0-or-later (it holds the harness and reac-pw's code).
#
#   SCRATCH=DIR examples/qdisc/fetch.sh      (default examples/build/qdisc)
set -euo pipefail
cd "$(dirname "$0")/../.."
SCRATCH=${SCRATCH:-examples/build/qdisc}
U="$SCRATCH/upstream"
mkdir -p "$U/recipe"
OSSV=32c8baf6e92f173b445903857770da103ba307e0
REAC=f86a30a3d06e84e8a7d6ec647cae77c4cbc9137b
check() {  # file, sha256
  echo "$2  $1" | sha256sum -c --quiet || { echo "fetch.sh: $1 has the wrong SHA-256" >&2; exit 1; }
}
get() {  # url, file, sha256
  [ -f "$2" ] || curl -sSfL -m 300 -o "$2.part" "$1" && { [ -f "$2" ] || mv "$2.part" "$2"; }
  check "$2" "$3"
}
raw=https://raw.githubusercontent.com
get "$raw/theorem-labs/oss-verify-proofs/$OSSV/projects/reac-pw/fuzz_qdisc/source/fuzz_qdisc.c" \
  "$U/fuzz_qdisc.c" e5bab7e8e3f39036dc59bf799ac77761f242720da283c701e92112575e7bd0c1
get "$raw/theorem-labs/oss-verify-proofs/$OSSV/projects/reac-pw/fuzz_qdisc/source/fuzz.h" \
  "$U/fuzz.h" f6603a1a421d6d74f2653f38b85daac0cc8ef031fdb1aa03f7a8631e753cb2c1
get "$raw/FreeREAC/reac-pw/$REAC/src/reac_qdisc.c" \
  "$U/reac_qdisc.c" 39f1d80b7d556e0bd5a01a8f17f96b9acca41d18dbf097ca3666b097f8c172b3
sed -n '/^int reac_qdisc_etf_catchup_slots(unsigned lead_us, int fps)$/,/^}$/p' "$U/reac_qdisc.c" \
  > "$U/reac_qdisc_etf_catchup_slots.c"
check "$U/reac_qdisc_etf_catchup_slots.c" 7cab32ef05193f35127c0e0424e32a8566adcfd4a6e34f203350f4802a321d9c
rel=https://github.com/theorem-labs/oss-verify-proofs/releases/download
get "$rel/v2026.10.0-src/recipe.tar.zst" "$U/recipe.tar.zst" \
  0339bf3221b15cd39513d46abe99062bac9cce874ed7ba5947753f75b6219ae5
tar -I zstd -xf "$U/recipe.tar.zst" -C "$U/recipe" --strip-components=2 \
  recipe/src/cli.c recipe/src/emit.h recipe/src/grow_buf.h recipe/src/ossfuzz_adapter.h \
  recipe/src/rel_str.h recipe/src/target.h
while read -r sha f; do check "$U/recipe/$f" "$sha"; done <<'SUMS'
391d784f25f6f7f66b3d9943bce5c7278b91964bc5499f78e22a60373b772d68 cli.c
6ad03a47e57d8b36d15e1b6ab8e9c83b5305dcb09efe7ac20e4aca7682d72fdd emit.h
dc46eb15f981765a22e501c22d2a975f0106cebe5b28c3aad7edb5c4f592a1f0 grow_buf.h
b15ca27aef4dab0dcee3e83b1b619a6670d68100b4c9ac8243e7fae92e8c4370 ossfuzz_adapter.h
cae08a1f00f28a2d277841880b14301d98e15a3956135af794c5d45e287783df rel_str.h
ccdea435b7b48a779d84cd8a1582d1d8002d6e6e6ed4dbf152dc8fa9a9a32f8e target.h
SUMS
echo "ok   $U: harness, reac_qdisc.c (and the extracted function), OSS Verify's driver: SHA-256s match"

#!/usr/bin/env bash
# Check that every annotated file examples/musl/<name>.s is the compiled code, unchanged:
#  1. build the functions fresh (build.sh, pinned source + flags),
#  2. assemble <name>.s and compare its .text bytes with the fresh object's .text.<sym>,
#  3. compare relocations (offset, type, symbol),
#  4. check every `# <off>: <word> [<word>]` comment against the fresh bytes.
# Usage: verify.sh [OUT]
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../.." && pwd)
OUT=${1:-/mnt/scratch/ec2-user/musl-trial-build}
"$HERE/build.sh" "$OUT" > "$OUT.buildlog"
"$HERE/skeletons.sh" "$OUT"
fail=0; n=0
while read -r name src sym extra; do
  [[ -z "$name" || "$name" == \#* ]] && continue
  f="$ROOT/examples/musl/$name.s"; [ -f "$f" ] || continue
  n=$((n+1))
  # 0. the committed file is exactly skeleton + annotations (examples/musl/ann/<name>.ann)
  if [ -f "$ROOT/examples/musl/ann/$name.ann" ]; then
    python3 "$HERE/annotate.py" "$OUT/$name.skel.s" "$ROOT/examples/musl/ann/$name.ann" | cmp -s - "$f" \
      || { echo "$name: .s IS NOT skeleton + ann (run annotate.py)"; fail=1; continue; }
  fi
  clang --target=riscv64-linux-musl -march=rv64im_zba_zbb -mabi=lp64 -mno-relax -c "$f" -o "$OUT/$name.ann.o"
  llvm-objcopy -O binary --only-section=.text "$OUT/$name.ann.o" "$OUT/$name.ann.text"
  if ! cmp -s "$OUT/$name.ann.text" "$OUT/$name.text"; then echo "$name: BYTES DIFFER"; fail=1; continue; fi
  r1=$(llvm-objdump -r "$OUT/$name.ann.o" | awk '/R_RISCV/{if ($2 ~ /PCREL_LO12/) $3="(auipc)"; print $1,$2,$3}')
  r2=$(llvm-objdump -r "$OUT/$name.o" | awk -v s="[.text.$sym]:" '/^RELOCATION RECORDS/{on=($4==s)} on && /R_RISCV/{if ($2 ~ /PCREL_LO12/) $3="(auipc)"; print $1,$2,$3}')
  if [ "$r1" != "$r2" ]; then echo "$name: RELOCATIONS DIFFER"; fail=1; continue; fi
  # Read-only data the function references (constant pools) must be byte-identical too.
  for sec in $(llvm-readelf -S --wide "$OUT/$name.ann.o" | awk '{for(i=1;i<=NF;i++) if ($i ~ /^\.rodata/) print $i}'); do
    llvm-objcopy -O binary --only-section="$sec" "$OUT/$name.ann.o" "$OUT/$name.ann.sec"
    llvm-objcopy -O binary --only-section="$sec" "$OUT/$name.o" "$OUT/$name.ref.sec"
    cmp -s "$OUT/$name.ann.sec" "$OUT/$name.ref.sec" || { echo "$name: DATA $sec DIFFERS"; fail=1; continue 2; }
  done
  # A PCREL_LO12 must point at the auipc just before it in both objects (checked by position:
  # the skeleton labels each auipc, and the bytes and HI20 targets above are equal).
  bad=$(python3 -I - "$f" "$OUT/$name.text" <<'PY'
import re, sys
txt = open(sys.argv[2], 'rb').read()
bad = 0
for line in open(sys.argv[1]):
    m = re.search(r'#\s*([0-9a-f]+):\s+([0-9a-f]{8})(?:\s+([0-9a-f]{8}))?\s*$', line)
    if not m or line.lstrip().startswith('#'): continue
    off = int(m[1], 16)
    for k, w in enumerate([m[2], m[3]]):
        if w and int.from_bytes(txt[off+4*k:off+4*k+4], 'little') != int(w, 16): bad += 1
print(bad)
PY
)
  if [ "$bad" != 0 ]; then echo "$name: $bad ENCODING COMMENTS WRONG"; fail=1; continue; fi
  echo "$name: OK ($(stat -c %s "$OUT/$name.text") bytes, sha256 $(sha256sum < "$OUT/$name.text" | cut -c1-16))"
done < "$HERE/functions.txt"
# The corpus copies (tests/typed/corpus/musl/*.s) must be byte copies of examples/musl/*.s.
for f in "$ROOT"/examples/musl/*.s; do
  c="$ROOT/tests/typed/corpus/musl/$(basename "$f")"
  cmp -s "$f" "$c" || { echo "$(basename "$f"): corpus copy differs (cp examples/musl/*.s tests/typed/corpus/musl/)"; fail=1; }
done
for c in "$ROOT"/tests/typed/corpus/musl/*.s; do
  [ -f "$ROOT/examples/musl/$(basename "$c")" ] || { echo "$(basename "$c"): corpus copy without an example"; fail=1; }
done
exit $fail

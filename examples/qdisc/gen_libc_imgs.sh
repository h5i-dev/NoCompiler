#!/bin/bash
# Per-function images of fuzz_qdisc plain's musl functions, for the library proofs over its own bytes (round 7
# correction: the next binary is proved from the library, not from slen's bytes).
#
#   examples/qdisc/gen_libc_imgs.sh ELF [FUNC ...]
#
# ELF is fuzz_qdisc.plain.elf (examples/qdisc/build.sh); its sha256 must be the one examples/qdisc/SHA256SUMS
# pins. Writes, relative to the repository (so each agent runs it in its own worktree):
#   lean/Examples/Libc/Qdisc/QdiscExport.lean   `nocompiler export --format chunks` of the whole ELF
#   lean/Examples/Libc/Qdisc/<F>Img.lean         scripts/libc/fn_image.py ELF FUNC Examples.Libc.Qdisc.<F>Img
#                                                  --struct QdiscExport.lean, one per FUNC
# <F> is FUNC in camel case without underscores (memset -> MemsetImg, __syscall_ret -> SyscallRetImg).
# All of these are images of GPL-3.0 code: lean/Examples/Libc/Qdisc/.gitignore keeps them out of git
# (NOTICE; like the ELF itself). Nothing here is committed but this script and the .gitignore.
# Without FUNCs, the musl functions fuzz_qdisc reaches from _start (scripts/libc/reach.py).
# NOCOMPILER: the nocompiler binary (default: target/release/nocompiler).
set -euo pipefail
[ $# -ge 1 ] || { sed -n 2,17p "$0" | sed 's/^# \{0,1\}//'; exit 2; }
elf=$1; shift
root=$(cd "$(dirname "$0")/../.." && pwd)
NOCOMPILER=${NOCOMPILER:-$root/target/release/nocompiler}
[ -x "$NOCOMPILER" ] || { echo "no nocompiler at $NOCOMPILER (cargo build --release, or set NOCOMPILER)" >&2; exit 2; }
want=$(awk '$2 == "fuzz_qdisc.plain.elf" {print $1}' "$root/examples/qdisc/SHA256SUMS")
got=$(sha256sum "$elf" | cut -c1-64)
[ "$got" = "$want" ] || { echo "sha256 mismatch for $elf: $got (SHA256SUMS: $want)" >&2; exit 1; }

out="$root/lean/Examples/Libc/Qdisc"
mkdir -p "$out"

if [ $# -eq 0 ]; then
  set -- _Exit ___errno_location __set_thread_area __init_libc __init_ssp __init_tls __libc_start_main __lock \
    __syscall_ret _start _start_c memcpy memset abort raise __block_all_sigs __block_app_sigs __restore_sigs \
    __stack_chk_fail
fi

"$NOCOMPILER" export "$elf" --format chunks --namespace Examples.Libc.Qdisc.QdiscExport \
  -o "$out/QdiscExport.lean" 2> "$out/.export.log" || { echo "export failed: $out/.export.log" >&2; exit 1; }

camel() { echo "$1" | sed -E 's/^_+//; s/_+([a-z0-9])/\U\1/g; s/^([a-z])/\U\1/'; }
n=0
for f in "$@"; do
  F=$(camel "$f")
  if python3 -I "$root/scripts/libc/fn_image.py" "$elf" "$f" "Examples.Libc.Qdisc.${F}Img" \
      --struct "$out/QdiscExport.lean" > "$out/${F}Img.lean.tmp"; then
    mv "$out/${F}Img.lean.tmp" "$out/${F}Img.lean"; n=$((n + 1))
    echo "ok   $f -> lean/Examples/Libc/Qdisc/${F}Img.lean"
  else
    rm -f "$out/${F}Img.lean.tmp"; echo "FAIL $f (fn_image.py)" >&2
  fi
done
echo "$n of $# images written; export: lean/Examples/Libc/Qdisc/QdiscExport.lean"
[ "$n" -eq $# ]

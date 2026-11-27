#!/bin/bash
# Compile and verify the Rust set example, then check the unchecked control build.
set -euo pipefail
cd "$(dirname "$0")/../.."

build_dir=${1:-$(mktemp -d)}
mkdir -p "$build_dir"
build_dir=$(cd "$build_dir" && pwd)
checker=${NOCOMPILER_TYPED:-${CARGO_TARGET_DIR:-target}/release/nocompiler-typed}
source_file=examples/rust-typed/set.rs
contract=examples/rust-typed/set.ann

compile() {
    local variant=$1
    shift
    local output="$build_dir/$variant"
    rustc --edition=2024 --target riscv64imac-unknown-none-elf --crate-type lib \
        -C opt-level=2 -C target-feature=-c,-zca -C panic=abort \
        --emit="asm=$output.s,obj=$output.o" "$@" "$source_file"
    cat "$contract" "$output.s" > "$output.annotated.s"
    ld.lld --no-relax -static -e set -o "$output.elf" "$output.o"
}

echo "Artifacts: $build_dir"
compile checked
compile unchecked --cfg nocompiler_unchecked

"$checker" check "$build_dir/checked.annotated.s" --object "$build_dir/checked.o" \
    --image "$build_dir/checked.elf" \
    --prove --export-lean "$build_dir/Checked.lean" --ledger "$build_dir/checked.json"

status=0
"$checker" check "$build_dir/unchecked.annotated.s" --object "$build_dir/unchecked.o" \
    --image "$build_dir/unchecked.elf" --ledger "$build_dir/unchecked.json" || status=$?

python3 - "$build_dir" "$status" <<'PY'
import json
import sys
from pathlib import Path

build_dir = Path(sys.argv[1])


def result(variant):
    ledger = json.loads((build_dir / f"{variant}.json").read_text())
    functions = ledger["functions"]
    if ledger["global_errors"] or len(functions) != 1 or functions[0]["name"] != "set":
        raise SystemExit(f"Unexpected {variant} ledger: {ledger}")
    return functions[0]


if result("checked")["status"] != "proved":
    raise SystemExit("Expected a Lean proof for the checked build")
unchecked = result("unchecked")
if sys.argv[2] != "1" or unchecked["status"] != "rejected" or unchecked["error"]["rule"] != "mem-bounds":
    raise SystemExit("Expected the unchecked build to fail the memory bounds check")
print("Checked build: Lean proof. Unchecked build: rejected for memory bounds.")
PY

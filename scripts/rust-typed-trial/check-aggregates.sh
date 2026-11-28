#!/bin/bash
# Verify concrete collection layouts, variable-stride loops, and heap caller obligations.
set -euo pipefail
cd "$(dirname "$0")/../.."
export PATH="$PWD/target/release:$PATH"
artifacts=$(mktemp -d)
echo "Aggregate and ownership artifacts: $artifacts"
fixture=examples/rust-typed/fixtures/heapless_probe
heapless=(--manifest-path "$fixture/Cargo.toml" --bin heapless_probe)
method='heapless::vec::VecInner::<u64, usize, heapless::vec::storage::VecStorageInner<[core::mem::MaybeUninit<u64>; 8]>>'

cargo nocompiler check "${heapless[@]}" --invariants "$fixture/invariants.json" \
    --function 'heapless_probe::read::<4>' --function 'heapless_probe::read::<8>' \
    --function heapless_probe::append --function heapless_probe::copy_first \
    --function "$method::as_slice" --function "$method::push" \
    --artifacts "$artifacts/collections"

cargo nocompiler check --manifest-path examples/rust-typed/fixtures/buffer_ops/Cargo.toml \
    --bin buffer_ops --function buffer_ops::scan_records --function buffer_ops::read_spilled \
    --function buffer_ops::write_split --function buffer_ops::write_two_halves \
    --artifacts "$artifacts/scan"

cargo nocompiler check "${heapless[@]}" --allocator-contracts "$fixture/allocator-contracts.json" \
    --allow-assumptions --function heapless_probe::allocation_round_trip \
    --function heapless_probe::resize_round_trip --function heapless_probe::resize_or_keep \
    --artifacts "$artifacts/heap"

status=0
cargo nocompiler check "${heapless[@]}" --allocator-contracts "$fixture/allocator-contracts.json" \
    --allow-assumptions --function heapless_probe::use_after_release \
    --function heapless_probe::use_after_resize --function heapless_probe::double_release \
    --artifacts "$artifacts/negative" || status=$?
if [ "$status" -ne 1 ]; then
    echo "Expected a verification failure, got status $status" >&2
    exit 1
fi

python3 - "$artifacts" <<'PY'
import json
import sys
from pathlib import Path

root = Path(sys.argv[1])
contracts = (root / "collections/contracts.s").read_text().splitlines()
collection_report = json.loads((root / "collections/report.json").read_text())
assert len(collection_report["functions"]) == 6
assert any("heapless::vec::VecInner" in callee and callee.endswith("::push")
           for callee in collection_report["mir_direct_callees"]["heapless_probe::append"])
assert any("bytes[40]" in line and "<= 4" in line for line in contracts)
assert any("bytes[72]" in line and "<= 8" in line and "_after" in line for line in contracts)
scan = json.loads((root / "scan/report.json").read_text())
spilled = scan["functions"]["buffer_ops::read_spilled"]
assert scan["inferred_raw_pointer_requirements"][spilled["name"]]["a0"]["bytes"] == 16
heap = json.loads((root / "heap/report.json").read_text())["functions"]
assert len(heap) == 3 and all(result["status"] == "proved_assuming" for result in heap.values())
negative = json.loads((root / "negative/report.json").read_text())["functions"]
for name, rule in (
    ("use_after_release", "mem-bounds"),
    ("use_after_resize", "mem-bounds"),
    ("double_release", "call-cap"),
):
    item = negative[f"heapless_probe::{name}"]
    assert item["status"] == "rejected" and item["error"]["rule"] == rule
PY

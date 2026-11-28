#!/bin/bash
# Verify relational joins and capabilities inferred for called raw-pointer functions.
set -euo pipefail
cd "$(dirname "$0")/../.."
export PATH="$PWD/target/release:$PATH"
artifacts=$(mktemp -d)
echo "Relational inference artifacts: $artifacts"
buffer=(--manifest-path examples/rust-typed/fixtures/buffer_ops/Cargo.toml --bin buffer_ops)

cargo nocompiler check "${buffer[@]}" --function buffer_ops::sum_after_prefix \
    --function buffer_ops::read_pair_raw --function buffer_ops::read_pair_offset \
    --function buffer_ops::read_pair_slice \
    --function buffer_ops::read_pair_stack --function buffer_ops::write_raw \
    --function buffer_ops::write_slice --artifacts "$artifacts/positive"

status=0
cargo nocompiler check "${buffer[@]}" --function buffer_ops::read_pair_raw \
    --function buffer_ops::read_pair_short --artifacts "$artifacts/negative" || status=$?
if [ "$status" -ne 1 ]; then
    echo "Expected a verification failure, got status $status" >&2
    exit 1
fi

python3 - "$artifacts" <<'PY'
import json
from pathlib import Path
import sys

directory = Path(sys.argv[1])
positive = directory / "positive"
report = json.loads((positive / "report.json").read_text())
assert len(report["functions"]) == 7
inferred = report["inferred_raw_pointer_requirements"]
assert len(inferred) == 3
assert {
    (region["a0"]["bytes"], region["a0"]["alignment"], region["a0"]["access"])
    for region in inferred.values()
} == {(16, 8, "ro"), (8, 8, "rw"), (24, 8, "ro")}
assembly = (positive / "annotated.s").read_text()
assert "#: join [prefix" in assembly and "#: inv [" in assembly
contracts = (positive / "contracts.s").read_text().splitlines()
assert any("read_pair_stack" in line and "addr [" in line for line in contracts)

negative = json.loads((directory / "negative/report.json").read_text())["functions"]
assert negative["buffer_ops::read_pair_raw"]["status"] == "proved"
assert negative["buffer_ops::read_pair_short"]["error"]["rule"] == "call-cap"
PY

cargo nocompiler check "${buffer[@]}" --function buffer_ops::read_through_join_copy \
    --artifacts "$artifacts/copy-join"
jq -e '.functions["buffer_ops::read_through_join_copy"].status == "proved"' \
    "$artifacts/copy-join/report.json"
rg -A1 '#: join \[offset[0-9]+_[0-9]+\].*8\*offset' "$artifacts/copy-join/annotated.s" |
    rg -q '^\s+mv\s'

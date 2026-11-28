#!/bin/bash
# Compare compiler-generated loop invariants with the signature-only baseline.
set -euo pipefail
cd "$(dirname "$0")/../.."
export PATH="$PWD/target/release:$PATH"
artifacts=$(mktemp -d)
echo "Loop evaluation artifacts: $artifacts"

buffer=(--manifest-path examples/rust-typed/fixtures/buffer_ops/Cargo.toml --bin buffer_ops)
scans=(--function buffer_ops::sum --function buffer_ops::fill --function buffer_ops::contains
       --function buffer_ops::sum_two --function buffer_ops::fill_rows)

expect_failure() {
    local status=0
    "$@" || status=$?
    if [ "$status" -ne 1 ]; then
        echo "Expected a verification failure, got status $status" >&2
        exit 1
    fi
}

expect_failure cargo nocompiler check "${buffer[@]}" "${scans[@]}" \
    --no-infer-loops --artifacts "$artifacts/baseline"
cargo nocompiler check "${buffer[@]}" "${scans[@]}" --artifacts "$artifacts/scans"
cargo nocompiler check "${buffer[@]}" --function buffer_ops::stack_word \
    --function buffer_ops::stack_byte --function buffer_ops::stack_call --artifacts "$artifacts/stack"
expect_failure cargo nocompiler check "${buffer[@]}" --function buffer_ops::sum_shifted \
    --artifacts "$artifacts/shifted"
memchr=(--manifest-path examples/rust-typed/fixtures/memchr_probe/Cargo.toml
        --bin memchr_probe --function memchr_probe::find)
expect_failure cargo nocompiler check "${memchr[@]}" \
    --no-infer-loops --artifacts "$artifacts/memchr-baseline"
cargo nocompiler check "${memchr[@]}" --artifacts "$artifacts/memchr"

python3 - "$artifacts" <<'PY'
import json
from pathlib import Path
import sys

artifacts = Path(sys.argv[1])


def results(case):
    return json.loads((artifacts / case / "report.json").read_text())["functions"]


def check_missing_invariant(entry):
    assert entry["status"] == "rejected"
    assert entry["error"]["rule"] == "cfg"
    assert "without an 'inv' annotation" in entry["error"]["message"]
    assert entry["error"]["line"] > 0


baseline = results("baseline")
scans = results("scans")
assert len(baseline) == 5 and baseline.keys() == scans.keys()
for entry in baseline.values():
    check_missing_invariant(entry)
assert all(entry["status"] == "proved" for entry in scans.values())
assert (artifacts / "scans/contracts.s").read_bytes() == (artifacts / "baseline/contracts.s").read_bytes()
assembly = (artifacts / "scans/annotated.s").read_text()
assert assembly.count("#: inv [") == 7
assert "#: join where 1 <= n1" in assembly

assert all(entry["status"] == "proved" for entry in results("stack").values())
stack = (artifacts / "stack/contracts.s").read_text().splitlines()
assert any("stack_word" in line and "frame 16 slots 8 stack 16" in line for line in stack)
assert any("stack_byte" in line and "frame 16 addr " in line for line in stack)
assert any("stack_call" in line and line.endswith("stack 32") for line in stack)

shifted, = results("shifted").values()
assert shifted["status"] == "rejected" and shifted["error"]["rule"] == "mem-bounds"
assert "#: inv [remaining]" in (artifacts / "shifted/annotated.s").read_text()
check_missing_invariant(results("memchr-baseline")["memchr_probe::find"])
assert results("memchr")["memchr_probe::find"]["status"] == "proved"
memchr_assembly = (artifacts / "memchr/annotated.s").read_text()
assert memchr_assembly.count("#: inv [") == 5
assert "#: join [tail" in memchr_assembly
PY

cargo nocompiler check "${buffer[@]}" --no-mir-hints \
    --function buffer_ops::advance_by_one_or_two --artifacts "$artifacts/multi-latch"
jq -e '.functions["buffer_ops::advance_by_one_or_two"].status == "proved"' \
    "$artifacts/multi-latch/report.json"
rg -q '#: inv .*decreases remaining' "$artifacts/multi-latch/annotated.s"

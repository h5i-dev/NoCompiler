#!/bin/bash
# Exercise MIR-derived contracts against the linked RV64 image.
set -euo pipefail
cd "$(dirname "$0")/../.."
artifacts=$(mktemp -d)
echo "MIR contract artifacts: $artifacts"
check=(target/release/cargo-nocompiler check
    --manifest-path examples/rust-typed/fixtures/buffer_ops/Cargo.toml --bin buffer_ops)
targets=(--function buffer_ops::copy_last --function buffer_ops::copy_last_shifted
    --function buffer_ops::middle --function buffer_ops::read_middle --function buffer_ops::clear)
"${check[@]}" "${targets[@]}" --artifacts "$artifacts/positive"
jq -e '.functions | length == 5 and all(.[]; .status == "proved")' "$artifacts/positive/report.json"
jq -e '
    [.functions[] | .raw_requirements[] | .bytes] == ["8*x2", "8*x2"] and
    any(.functions[]; .returned_view == {"argument": 0, "offset": "8", "length": "2"}) and
    any(.functions[]; .field_writes == [{"argument": 0, "offset": 0, "value": "0"}])
' "$artifacts/positive/contracts.json"

status=0
"${check[@]}" --function buffer_ops::copy_last --function buffer_ops::copy_last_short \
    --artifacts "$artifacts/negative" || status=$?
test "$status" -eq 1
jq -e '.functions["buffer_ops::copy_last"].status == "proved" and
    .functions["buffer_ops::copy_last_short"].error.rule == "call-cap"' "$artifacts/negative/report.json"

status=0
"${check[@]}" "${targets[@]}" --no-mir-hints --artifacts "$artifacts/baseline" || status=$?
test "$status" -eq 1
jq -e '.mir_hints == false and
    .functions["buffer_ops::copy_last"].status == "rejected" and
    .functions["buffer_ops::read_middle"].status == "rejected"' "$artifacts/baseline/report.json"

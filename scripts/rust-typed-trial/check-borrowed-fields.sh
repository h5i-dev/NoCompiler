#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")/../.."
artifacts=$(mktemp -d)
echo "Borrowed-field proof artifacts: $artifacts"
check=(target/release/cargo-nocompiler check
    --manifest-path examples/rust-typed/fixtures/buffer_ops/Cargo.toml --bin buffer_ops
    --function buffer_ops::clear --function buffer_ops::reset_and_read)
"${check[@]}" --artifacts "$artifacts/positive"
jq -e '.proof_attempt.status == "proved" and
    (.functions | length == 2 and all(.[]; .status == "proved"))' "$artifacts/positive/report.json"

status=0
"${check[@]}" --no-mir-hints --artifacts "$artifacts/no-guarantee" || status=$?
test "$status" -eq 1
jq -e '.functions["buffer_ops::reset_and_read"].error.rule == "mem-bounds"' \
    "$artifacts/no-guarantee/report.json"

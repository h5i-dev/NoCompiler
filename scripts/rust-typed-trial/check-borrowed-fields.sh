#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")/../.."
artifacts=$(mktemp -d)
echo "Borrowed-field proof artifacts: $artifacts"
check=(target/release/cargo-nocompiler check
    --manifest-path examples/rust-typed/fixtures/buffer_ops/Cargo.toml --bin buffer_ops)
field_update=(--function buffer_ops::clear --function buffer_ops::reset_and_read)
"${check[@]}" "${field_update[@]}" --artifacts "$artifacts/positive"
jq -e '.proof_attempt.status == "proved" and
    (.functions | length == 2 and all(.[]; .status == "proved"))' "$artifacts/positive/report.json"

status=0
"${check[@]}" "${field_update[@]}" --no-mir-hints --artifacts "$artifacts/no-guarantee" || status=$?
test "$status" -eq 1
jq -e '.functions["buffer_ops::reset_and_read"].error.rule == "mem-bounds"' \
    "$artifacts/no-guarantee/report.json"

"${check[@]}" --function buffer_ops::initialize_disjoint_words     --function buffer_ops::update_initialized_word --artifacts "$artifacts/initialization"
jq -e '.functions | length == 2 and all(.[]; .status == "proved")'     "$artifacts/initialization/report.json"
jq -e '.functions | any(to_entries[];
    (.key | endswith("initialize_disjoint_words")) and .value.initialized_words == [[0,0],[0,8]])'     "$artifacts/initialization/contracts.json"

"${check[@]}" --function buffer_ops::initialize_via_pointer     --function buffer_ops::update_initialized_word --function buffer_ops::initialize_word_alternate     --artifacts "$artifacts/indirect-initialization"
jq -e '.functions | length == 3 and all(.[]; .status == "proved")'     "$artifacts/indirect-initialization/report.json"
jq -e '.functions | any(to_entries[]; (.key | endswith("initialize_via_pointer"))
    and .value.initialized_words == [[0,0],[0,8]]
    and (.value.mir_resolved_callees | length) == 2)'     "$artifacts/indirect-initialization/contracts.json"

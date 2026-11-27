#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")/../.."
artifacts=$(mktemp -d)
echo "Call scope artifacts: $artifacts"
status=0
target/release/cargo-nocompiler check \
    --manifest-path examples/rust-typed/fixtures/buffer_ops/Cargo.toml --bin buffer_ops \
    --function buffer_ops::clear --function buffer_ops::reset_and_read \
    --function buffer_ops::invoke_runtime_target --artifacts "$artifacts/check" || status=$?
test "$status" -eq 1
jq -e '
    .functions["buffer_ops::invoke_runtime_target"].error.rule == "profile" and
    (.static_call_scope["buffer_ops::invoke_runtime_target"].unresolved_indirect_sites | length == 1) and
    (.static_call_scope["buffer_ops::reset_and_read"].selected_bodies | length == 2 and
        any(.[]; endswith("clear"))) and
    (.static_call_scope["buffer_ops::reset_and_read"].unresolved_indirect_sites | length == 0)
' "$artifacts/check/report.json"

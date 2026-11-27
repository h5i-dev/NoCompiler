#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")/../.."
artifacts=$(mktemp -d)
echo "MIR callee summaries: $artifacts"
target/release/cargo-nocompiler check \
    --manifest-path examples/rust-typed/fixtures/buffer_ops/Cargo.toml --bin buffer_ops \
    --function buffer_ops::reset_and_get_relay --function buffer_ops::reset_and_get \
    --function buffer_ops::clear --artifacts "$artifacts/check"
jq -e '.functions | length == 3 and all(.[]; .status == "proved")' "$artifacts/check/report.json"
jq -e '
    [.functions | to_entries[] | select(.key | contains("reset_and_get")) | .value] |
    length == 2 and all(.[]; .scalar_result == "0" and
        .field_writes == [{"argument":0,"offset":0,"value":"0"}] and
        .unresolved_mir_access == false)
' "$artifacts/check/contracts.json"

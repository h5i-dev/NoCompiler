#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")/../.."
artifacts=$(mktemp -d)
echo "Runtime relation artifacts: $artifacts"
check=(target/release/cargo-nocompiler check
    --manifest-path examples/rust-typed/fixtures/buffer_ops/Cargo.toml --bin buffer_ops)
"${check[@]}" --llvm-hints --function buffer_ops::repeat_store \
    --function buffer_ops::choose_many_suffixes --function buffer_ops::choose_inconsistent_suffix --function buffer_ops::trim_many_suffixes --function buffer_ops::repeat_two_stores --function buffer_ops::repeat_nested_stores \
    --artifacts "$artifacts/hints"
jq -e '.functions | length == 6 and all(.[]; .status == "proved")' "$artifacts/hints/report.json"
jq -e '
    any(.functions | to_entries[]; (.key | endswith("choose_many_suffixes")) and
        .value.returned_view_end == {"argument": 0, "stride": 8, "offset": "64"} and .value.mir_widened_view_joins > 0) and
    any(.functions | to_entries[]; (.key | endswith("choose_inconsistent_suffix")) and
        .value.returned_view_end == null) and
    any(.functions | to_entries[]; (.key | endswith("trim_many_suffixes")) and
        .value.returned_view_end == {"argument": 0, "stride": 8, "offset": "56"} and .value.mir_widened_view_joins > 0) and
    any(.functions | to_entries[]; (.key | endswith("repeat_store")) and
        .value.llvm_loop_trip != null and .value.llvm_loop_trip.iterations == null and .value.llvm_loop_trip.count_arg_register == "a1") and
    any(.functions | to_entries[]; (.key | endswith("repeat_two_stores")) and
        ([.value.llvm_loop_trips[].count_arg_register] | sort) == ["a2", "a3"]) and
    any(.functions | to_entries[]; (.key | endswith("repeat_nested_stores")) and
        ([.value.llvm_loop_trips[].count_arg_register] | sort) == ["a1", "a2"])
' "$artifacts/hints/contracts.json"
rg -q '#: inv .*remaining <= x1 decreases remaining' "$artifacts/hints/annotated.s"
rg -q '#: inv .*remaining <= x2 decreases remaining' "$artifacts/hints/annotated.s"
rg -q '#: inv .*remaining1 <= x3 decreases remaining1' "$artifacts/hints/annotated.s"
"${check[@]}" --function buffer_ops::repeat_store --artifacts "$artifacts/rv64-only"
jq -e '.functions["buffer_ops::repeat_store"].status == "proved"' "$artifacts/rv64-only/report.json"
rg -q '#: inv .*remaining <= x1 decreases remaining' "$artifacts/rv64-only/annotated.s"

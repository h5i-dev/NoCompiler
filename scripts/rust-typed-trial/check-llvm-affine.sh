#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")/../.."
artifacts=$(mktemp -d)
echo "LLVM affine SSA proof artifacts: $artifacts"
check=(target/release/cargo-nocompiler check
    --manifest-path examples/rust-typed/fixtures/buffer_ops/Cargo.toml --bin buffer_ops
    --no-mir-hints --function buffer_ops::affine_result --function buffer_ops::read_affine_result
    --function buffer_ops::affine_spilled_result --function buffer_ops::affine_spilled_across_join
    --function buffer_ops::differing_stack_writes)
"${check[@]}" --llvm-hints --artifacts "$artifacts/hints"
jq -e '.functions | length == 5 and all(.[]; .status == "proved")' "$artifacts/hints/report.json"
jq -e 'any(.functions[]; .llvm_affine_result == {"register":"a0","expression":"2*x0 + 3"})' \
    "$artifacts/hints/contracts.json"

jq -e 'any(.functions[]; .llvm_affine_result == {"register":"a0","expression":"x0 + 6"})' \
    "$artifacts/hints/contracts.json"
rg -q 'affine_spilled_result.*out a0: int\(x0 \+ 6\).*slots' "$artifacts/hints/contracts.s"

jq -e 'any(.functions | to_entries[];
        (.key | endswith("affine_spilled_across_join")) and
        .value.llvm_affine_result.expression == "x0 + 6") and
    any(.functions | to_entries[];
        (.key | endswith("differing_stack_writes")) and .value.llvm_affine_result == null)' \
    "$artifacts/hints/contracts.json"

status=0
"${check[@]}" --artifacts "$artifacts/baseline" || status=$?
test "$status" -eq 1
jq -e '.functions["buffer_ops::read_affine_result"].error.rule == "mem-bounds"' \
    "$artifacts/baseline/report.json"

jq -e '.functions | any(to_entries[];
    (.key | endswith("affine_spilled_result")) and
    any(.value.llvm_affine_locations[]; .entry_sp_offset == -8 and (.values | length) > 0))'     "$artifacts/hints/contracts.json"

target/release/cargo-nocompiler check \
    --manifest-path examples/rust-typed/fixtures/buffer_ops/Cargo.toml --bin buffer_ops \
    --llvm-hints --no-mir-hints --function buffer_ops::spill_into_output \
    --artifacts "$artifacts/void-pointer"
jq -e '.functions["buffer_ops::spill_into_output"].status == "proved"' \
    "$artifacts/void-pointer/report.json"
jq -e '.functions | any(to_entries[];
    (.key | endswith("spill_into_output")) and
    any(.value.llvm_affine_locations[]; has("entry_sp_offset")) and
    (.value | has("llvm_affine_result") | not))' "$artifacts/void-pointer/contracts.json"

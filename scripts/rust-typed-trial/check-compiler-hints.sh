#!/bin/bash
# Compare proofs with and without compiler-derived annotation candidates.
set -euo pipefail
cd "$(dirname "$0")/../.."
artifacts=$(mktemp -d)
echo "Compiler hint artifacts: $artifacts"
check=(target/release/cargo-nocompiler check
    --manifest-path examples/rust-typed/fixtures/buffer_ops/Cargo.toml --bin buffer_ops
    --function buffer_ops::choose_suffix --function buffer_ops::bounded_word
    --function buffer_ops::bounded_read --function buffer_ops::fixed_store
    --function buffer_ops::stack_via_register)
"${check[@]}" --llvm-hints --artifacts "$artifacts/hints"
jq -e '.functions | length == 5 and all(.[]; .status == "proved")' "$artifacts/hints/report.json"
jq -e '
    any(.functions[]; .returned_view_end == {"argument": 0, "offset": "32", "stride": 8}) and
    any(.functions[]; .llvm_result_range == {"register": "a0", "lower": 0, "upper_exclusive": 8}) and
    any(.functions[]; .llvm_loop_trip.iterations == "1024") and
    any(.functions[]; .llvm_stack == {"frame_size": 16, "slots": [[8, 16]]})
' "$artifacts/hints/contracts.json"
rg -q '#: inv .*remaining <= 1024 decreases remaining' "$artifacts/hints/annotated.s"
rg -q 'out .*view_ptr.*view_len.*where view_ptr \+ 8\*view_len = ' "$artifacts/hints/contracts.s"

rg -q 'stack_via_register.*frame 16 addr \[8, 16\)' "$artifacts/hints/contracts.s"

status=0
"${check[@]}" --no-mir-hints --artifacts "$artifacts/baseline" || status=$?
test "$status" -eq 1
jq -e '.functions["buffer_ops::bounded_read"].status == "rejected" and
    .functions["buffer_ops::fixed_store"].status == "rejected" and
    .functions["buffer_ops::stack_via_register"].status == "rejected"' "$artifacts/baseline/report.json"
if rg -q 'view_ptr|llvm_result|#: inv' "$artifacts/baseline/annotated.s"; then
    echo "Compiler-only annotations unexpectedly present in baseline" >&2
    exit 1
fi

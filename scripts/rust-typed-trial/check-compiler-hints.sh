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
    .functions["buffer_ops::fixed_store"].status == "proved" and
    .functions["buffer_ops::stack_via_register"].status == "proved"' "$artifacts/baseline/report.json"
rg -q '#: inv .*remaining <= 1024 decreases remaining' "$artifacts/baseline/annotated.s"
if rg -q 'view_ptr|llvm_result' "$artifacts/baseline/annotated.s"; then
    echo "Compiler-only annotations unexpectedly present in baseline" >&2
    exit 1
fi

target/release/cargo-nocompiler check \
    --manifest-path examples/rust-typed/fixtures/buffer_ops/Cargo.toml --bin buffer_ops \
    --no-mir-hints --function buffer_ops::stack_after_register_setup \
    --artifacts "$artifacts/delayed-frame"
jq -e '.functions["buffer_ops::stack_after_register_setup"].status == "proved"' \
    "$artifacts/delayed-frame/report.json"
rg -q 'stack_after_register_setup.*frame 16 addr \[8, 16\)' "$artifacts/delayed-frame/contracts.s"
awk '
    /stack_after_register_setup:$/ { inside = 1; next }
    inside && /^[[:space:]]+[[:alpha:]]/ {
        seen = 1
        if ($1 != "addi" || $2 == "sp,") exit 1
        exit
    }
    END { if (!seen) exit 1 }
' "$artifacts/delayed-frame/annotated.s"

# LLVM infers the word range, but the checker currently loses it through OR.
byteorder=(target/release/cargo-nocompiler check --locked
    --manifest-path benchmarks/rust/probes/Cargo.toml --bin rust100_probe
    --function rust100_probe::read_u32 --llvm-hints)
"${byteorder[@]}" --artifacts "$artifacts/llvm-result-fallback"
fallback="$artifacts/llvm-result-fallback"
jq -e '.functions["rust100_probe::read_u32"].status == "proved" and
    (.llvm_result_fallbacks | [.[]] == ["ret-out"])' "$fallback/report.json"
jq -e '.["rust100_probe::read_u32"] == "[p0] in a0: int(p0) borrow p0 |-> bytes[4] ro out a0: int"'     "$fallback/entry-contracts.json"

# A previously reviewed baseline remains usable with LLVM hints enabled.
"${byteorder[@]}" --entry-contracts "$fallback/entry-contracts.json"     --artifacts "$artifacts/llvm-result-reviewed"
jq -e '.functions["rust100_probe::read_u32"].status == "proved" and
    .llvm_result_fallbacks == {}' "$artifacts/llvm-result-reviewed/report.json"

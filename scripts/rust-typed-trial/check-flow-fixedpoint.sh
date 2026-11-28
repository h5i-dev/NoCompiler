#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")/../.."
artifacts=$(mktemp -d)
echo "CFG analysis artifacts: $artifacts"
check=(target/release/cargo-nocompiler check
    --manifest-path examples/rust-typed/fixtures/buffer_ops/Cargo.toml --bin buffer_ops)
"${check[@]}" --no-mir-hints --llvm-hints --function buffer_ops::repeat_store_raw \
    --artifacts "$artifacts/cyclic"
jq -e '
    .functions["buffer_ops::repeat_store_raw"].status == "proved" and
    any(.inferred_raw_pointer_requirements[]; .a0.bytes == 8 and .a0.access == "rw")
' "$artifacts/cyclic/report.json"

status=0
"${check[@]}" --function buffer_ops::safe_signature_without_bounds \
    --artifacts "$artifacts/unguarded" || status=$?
test "$status" -eq 1
jq -e '.functions["buffer_ops::safe_signature_without_bounds"].error.rule == "mem-bounds"' \
    "$artifacts/unguarded/report.json"

status=0
"${check[@]}" --function buffer_ops::safe_raw_without_permission     --artifacts "$artifacts/raw-without-permission" || status=$?
test "$status" -eq 1
jq -e '
    .functions["buffer_ops::safe_raw_without_permission"] as $f |
    $f.error.rule == "mem-bounds" and
    .inferred_raw_pointer_requirements[$f.name].a0.bytes == 8
' "$artifacts/raw-without-permission/report.json"

"${check[@]}" --no-mir-hints --function buffer_ops::read_masked_raw     --artifacts "$artifacts/masked-offset"
jq -e '
    .functions["buffer_ops::read_masked_raw"] as $f |
    $f.status == "proved" and
    .inferred_raw_pointer_requirements[$f.name].a0.bytes == 8
' "$artifacts/masked-offset/report.json"

"${check[@]}" --no-mir-hints --function buffer_ops::read_masked_word_raw     --artifacts "$artifacts/aligned-offset"
jq -e '
    .functions["buffer_ops::read_masked_word_raw"] as $f |
    $f.status == "proved" and
    (.inferred_raw_pointer_requirements[$f.name].a0 | .bytes == 64 and .alignment == 8)
' "$artifacts/aligned-offset/report.json"

"${check[@]}" --no-mir-hints --function buffer_ops::read_prefix_and_index \
    --artifacts "$artifacts/dynamic-extent"
jq -e '.functions["buffer_ops::read_prefix_and_index"].status == "proved"' \
    "$artifacts/dynamic-extent/report.json"
rg -q 'borrow p0 \|-> bytes\[8\*x1 \+ 8\] ro' "$artifacts/dynamic-extent/contracts.s"

"${check[@]}" --no-mir-hints --function buffer_ops::read_guarded_index     --artifacts "$artifacts/guarded-extent"
jq -e '.functions["buffer_ops::read_guarded_index"].status == "proved"'     "$artifacts/guarded-extent/report.json"
rg -q 'borrow p0 \|-> bytes\[8\*x1\] ro' "$artifacts/guarded-extent/contracts.s"

"${check[@]}" --no-mir-hints --function buffer_ops::read_guarded_index     --function buffer_ops::read_guarded_relay --artifacts "$artifacts/guarded-relay"
jq -e '.functions["buffer_ops::read_guarded_relay"].status == "proved"'     "$artifacts/guarded-relay/report.json"
rg -q 'read_guarded_relay .*borrow p0 \|-> bytes\[8\*x1 \+ 8\] ro'     "$artifacts/guarded-relay/contracts.s"

"${check[@]}" --no-mir-hints --function buffer_ops::read_two_guarded_offsets \
    --artifacts "$artifacts/combined-guards"
jq -e '.functions["buffer_ops::read_two_guarded_offsets"].status == "proved"' \
    "$artifacts/combined-guards/report.json"
rg -Fq 'borrow p0 |-> bytes[16*x1] ro' "$artifacts/combined-guards/contracts.s"

#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")/../.."
artifacts=$(mktemp -d)
check=(target/release/cargo-nocompiler check
    --manifest-path examples/rust-typed/fixtures/buffer_ops/Cargo.toml --bin buffer_ops
    --function buffer_ops::bounded_word --no-source-trace --locked --no-default-features)
cat > "$artifacts/reviewed.json" <<'JSON'
{"buffer_ops::bounded_word":"[x0] in a0: u64(x0) out a0: int"}
JSON
"${check[@]}" --entry-contracts "$artifacts/reviewed.json" --artifacts "$artifacts/positive"
jq -e '.reviewed_entries == ["buffer_ops::bounded_word"] and .proof_attempt.status == "proved" and .functions["buffer_ops::bounded_word"].status == "proved"' "$artifacts/positive/report.json"
jq -e '.cargo.locked and (.cargo.default_features == false)' "$artifacts/positive/report.json"
jq -e '.artifacts | any(.[]; .target == "buffer_ops" and .kind == ["bin"])' "$artifacts/positive/cargo-build.json"
"${check[@]}" --entry-contracts "$artifacts/reviewed.json" \
    --deployment-elf "$artifacts/positive/verified.elf" --artifacts "$artifacts/deploy"
jq -e '.deployment_elf_matched' "$artifacts/deploy/report.json"
cat > "$artifacts/different.json" <<'JSON'
{"buffer_ops::bounded_word":"[x0] in a0: u64(x0) where x0 < 8 out a0: int"}
JSON
status=0
"${check[@]}" --entry-contracts "$artifacts/different.json" --artifacts "$artifacts/changed" || status=$?
test "$status" -eq 1
jq -e '.checker_exit_code == null and .proof_attempt == null and .functions["buffer_ops::bounded_word"].status == "entry_contract_mismatch"' "$artifacts/changed/report.json"
status=0
"${check[@]}" --deployment-elf "$artifacts/different.json" --artifacts "$artifacts/wrong-elf" || status=$?
test "$status" -eq 2
test ! -e "$artifacts/wrong-elf/Proof.lean"
status=0
"${check[@]}" --lean-dir "$artifacts" --artifacts "$artifacts/no-lean" || status=$?
test "$status" -eq 1
jq -e '.proof_attempt.status == "failed" and
    .functions["buffer_ops::bounded_word"].status == "checked"' "$artifacts/no-lean/report.json"

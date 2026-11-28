#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")/../.."
solver=${1:-z3}
artifacts=$(mktemp -d)
echo "Horn reachability artifacts: $artifacts"
check=(target/release/cargo-nocompiler check
    --manifest-path examples/rust-typed/fixtures/buffer_ops/Cargo.toml --bin buffer_ops
    --no-mir-hints --function buffer_ops::horn_branch_read)
"${check[@]}" --artifacts "$artifacts/default"
"${check[@]}" --chc-solver "$solver" --artifacts "$artifacts/refined"
"${check[@]}" --chc-solver "$artifacts/no-solver" --artifacts "$artifacts/unavailable"
check_result() {
    jq -e --argjson bytes "$1" --argjson removed "$2" '
        .functions["buffer_ops::horn_branch_read"] as $f |
        $f.status == "proved" and
        .inferred_raw_pointer_requirements[$f.name].a0.bytes == $bytes and
        (.chc_pruned_edges[$f.name] // 0) == $removed
    ' "$3/report.json"
}
check_result 65 0 "$artifacts/default"
check_result 1 1 "$artifacts/refined"
check_result 65 0 "$artifacts/unavailable"

cat > "$artifacts/wrong-solver" <<'SOLVER'
#!/bin/sh
printf '%s\n' unsat unsat
SOLVER
chmod +x "$artifacts/wrong-solver"
status=0
"${check[@]}" --chc-solver "$artifacts/wrong-solver" --artifacts "$artifacts/invalid" || status=$?
test "$status" -eq 1
jq -e '.functions["buffer_ops::horn_branch_read"].error.rule == "mem-bounds"'     "$artifacts/invalid/report.json"

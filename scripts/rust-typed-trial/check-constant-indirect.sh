#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")/../.."
artifacts=$(mktemp -d)
echo "Constant indirect call proof: $artifacts"
checker=${NOCOMPILER_TYPED:-target/release/nocompiler-typed}
cat > "$artifacts/indirect.s" <<'ASM'
#: fn target [x] in a0: int(x) out a0: int(x + 1) stack 0
#: fn entry [x] in a0: int(x) out a0: int(x + 1) frame 16 slots 0 stack 16
.text
.globl target
.type target,@function
target:
    addi a0, a0, 1
    ret
.size target, .-target
.globl entry
.type entry,@function
entry:
    addi sp, sp, -16
    sd ra, 0(sp)
    beq a0, zero, .Lentry_zero
    lui t0, 0x20
    j .Lentry_call
.Lentry_zero:
    lui t0, 0x20
.Lentry_call:
    jalr ra, 0(t0)
    ld ra, 0(sp)
    addi sp, sp, 16
    ret
.size entry, .-entry
ASM
link() {
    clang --target=riscv64-unknown-elf -march=rv64ima -c "$1.s" -o "$1.o"
    ld.lld --no-relax -static -Ttext=0x20000 -e entry "$1.o" -o "$1.elf"
}
link "$artifacts/indirect"
"$checker" check "$artifacts/indirect.s" \
    --image "$artifacts/indirect.elf" --export-lean "$artifacts/Proof.lean" --prove --certs \
    --ledger "$artifacts/positive.json"
jq -e '.proof_attempt.status == "proved" and
    any(.functions[]; .name == "entry" and .status == "proved" and .evidence.callees == ["target"])' \
    "$artifacts/positive.json"

sed '/^\.Lentry_zero:$/ { n; s/lui t0, 0x20/addi t0, a0, 0/; }' "$artifacts/indirect.s" > "$artifacts/unknown.s"
link "$artifacts/unknown"
status=0
"$checker" check "$artifacts/unknown.s" --image "$artifacts/unknown.elf" \
    --export-lean "$artifacts/Unknown.lean" --prove --certs --ledger "$artifacts/negative.json" || status=$?
test "$status" -eq 1
jq -e 'any(.functions[]; .name == "entry" and .error.rule == "profile")' "$artifacts/negative.json"

# The Rust-side candidate must not stand in for validation of the linked JALR.
status=0
"$checker" check "$artifacts/indirect.s" --image "$artifacts/unknown.elf" \
    --export-lean "$artifacts/Mismatched.lean" --prove --certs \
    --ledger "$artifacts/mismatch.json" || status=$?
test "$status" -eq 1
jq -e '.proof_attempt.status == "failed" and
    any(.functions[]; .name == "entry" and .status == "checked")' "$artifacts/mismatch.json"

cat > "$artifacts/finite.s" <<'ASM'
#: fn target [x] in a0: int(x) out a0: int(x + 1) stack 0
#: fn alternate [x] in a0: int(x) out a0: int(x + 1) stack 0
#: fn entry [x] in a0: int(x) out a0: int(x + 1) frame 16 slots 0 stack 16
.text
.globl target
.type target,@function
target:
    addi a0, a0, 1
    ret
.size target, .-target
.balign 16
.globl alternate
.type alternate,@function
alternate:
    addi a0, a0, 1
    ret
.size alternate, .-alternate
.globl entry
.type entry,@function
entry:
    addi sp, sp, -16
    sd ra, 0(sp)
    lui t0, 0x20
    beq a0, zero, .Lfinite_call
    addi t0, t0, 16
.Lfinite_call:
    jalr ra, 0(t0)
    ld ra, 0(sp)
    addi sp, sp, 16
    ret
.size entry, .-entry
ASM
link "$artifacts/finite"
"$checker" check "$artifacts/finite.s" --image "$artifacts/finite.elf" \
    --export-lean "$artifacts/Finite.lean" --prove --certs --ledger "$artifacts/finite.json"
jq -e '.proof_attempt.status == "proved" and
    any(.functions[]; .name == "entry" and .status == "proved" and
        (.evidence.callees | sort) == ["alternate", "target"])' "$artifacts/finite.json"

# The representative callee is "alternate", which still returns x + 1.
# Lean must also check "target", even though the candidate record came from the representative.
sed -e '/^#: fn target /s/x + 1/x + 2/' -e '/^target:$/ { n; s/a0, a0, 1/a0, a0, 2/; }' \
    "$artifacts/finite.s" > "$artifacts/finite-bad.s"
link "$artifacts/finite-bad"
status=0
"$checker" check "$artifacts/finite-bad.s" --image "$artifacts/finite-bad.elf" \
    --export-lean "$artifacts/FiniteBad.lean" --prove --certs --ledger "$artifacts/finite-bad.json" || status=$?
test "$status" -eq 1
jq -e '.proof_attempt.status == "failed" and
    any(.functions[]; .name == "entry" and .status == "checked")' "$artifacts/finite-bad.json"

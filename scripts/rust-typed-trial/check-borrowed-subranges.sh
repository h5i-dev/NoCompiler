#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")/../.."
artifacts=$(mktemp -d)
echo "Borrowed subrange proof artifacts: $artifacts"
checker=${NOCOMPILER_TYPED:-target/release/nocompiler-typed}
cat > "$artifacts/subrange.s" <<'ASM'
#: fn write_word [p, v] in a0: int(p), a1: int(v) borrow p |-> bytes[8] rw {} -> {0: int(v)} where 8 | p out a0: int(p) stack 0
#: fn update_second [p, v, old] in a0: int(p), a1: int(v), a2: int(old) borrow p |-> bytes[16] rw {0: int(old), 8: int(old)} -> {0: int(old), 8: int(v)} where 8 | p out a0: int(v), a1: int(old) frame 16 slots 0 stack 16
#: fn write_two [p, v, w] in a0: int(p), a1: int(v), a2: int(w) borrow p |-> bytes[8] rw {} -> {0: int(v)}, p + 8 |-> bytes[8] rw {} -> {0: int(w)} where 8 | p out a0: int(p) stack 0
#: fn update_two [p, v, w] in a0: int(p), a1: int(v), a2: int(w) borrow p |-> bytes[24] rw {} -> {8: int(v), 16: int(w)} where 8 | p out a0: int(v), a1: int(w) frame 16 slots 0 stack 16
.text
.globl write_word
.type write_word,@function
write_word:
    sd a1, 0(a0)
    ret
.size write_word, .-write_word
.globl update_second
.type update_second,@function
update_second:
    addi sp, sp, -16
    sd ra, 0(sp)
    addi a0, a0, 8
    call write_word
    ld a1, -8(a0)
    ld a0, 0(a0)
    ld ra, 0(sp)
    addi sp, sp, 16
    ret
.size update_second, .-update_second
.globl write_two
.type write_two,@function
write_two:
    sd a1, 0(a0)
    sd a2, 8(a0)
    ret
.size write_two, .-write_two
.globl update_two
.type update_two,@function
update_two:
    addi sp, sp, -16
    sd ra, 0(sp)
    addi a0, a0, 8
    call write_two
    ld a1, 8(a0)
    ld a0, 0(a0)
    ld ra, 0(sp)
    addi sp, sp, 16
    ret
.size update_two, .-update_two
ASM
link() {
    clang --target=riscv64-unknown-elf -march=rv64ima -c "$1.s" -o "$1.o"
    ld.lld --no-relax -static -e update_second "$1.o" -o "$1.elf"
}
link "$artifacts/subrange"
"$checker" check "$artifacts/subrange.s" --image "$artifacts/subrange.elf" \
    --export-lean "$artifacts/Proof.lean" --prove --certs --ledger "$artifacts/positive.json"
jq -e '.proof_attempt.status == "proved" and
    (.functions | length == 4 and all(.[]; .status == "proved"))' "$artifacts/positive.json"

sed 's/ld a0, 0(a0)/ld a0, -8(a0)/' "$artifacts/subrange.s" > "$artifacts/wrong-field.s"
link "$artifacts/wrong-field"
status=0
"$checker" check "$artifacts/wrong-field.s" --image "$artifacts/wrong-field.elf" \
    --ledger "$artifacts/negative.json" || status=$?
test "$status" -eq 1
jq -e 'any(.functions[]; .name == "update_second" and .error.rule == "ret-out")' "$artifacts/negative.json"

sed 's/ld a1, -8(a0)/ld a1, 0(a0)/' "$artifacts/subrange.s" > "$artifacts/stale-field.s"
link "$artifacts/stale-field"
status=0
"$checker" check "$artifacts/stale-field.s" --image "$artifacts/stale-field.elf" \
    --ledger "$artifacts/stale.json" || status=$?
test "$status" -eq 1
jq -e 'any(.functions[]; .name == "update_second" and .error.rule == "ret-out")' "$artifacts/stale.json"

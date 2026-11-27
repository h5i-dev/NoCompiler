#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")/../.."
artifacts=$(mktemp -d)
echo "Owned-field proof artifacts: $artifacts"
checker=${NOCOMPILER_TYPED:-target/release/nocompiler-typed}

cat > "$artifacts/owned.s" <<'ASM'
#: fn write_owned [p, v] in a0: int(p), a1: int(v) take p |-> bytes[8] rw where 8 | p out a0: int(p) give p |-> bytes[8] rw {0: int(v)} stack 0
#: fn read_owned [p, v] in a0: int(p), a1: int(v) take p |-> bytes[8] rw where 8 | p out a0: int(v) give p |-> bytes[8] rw {0: int(v)} frame 16 slots 0 stack 16
.text
.globl write_owned
.type write_owned,@function
write_owned:
    sd a1, 0(a0)
    ret
.size write_owned, .-write_owned
.globl read_owned
.type read_owned,@function
read_owned:
    addi sp, sp, -16
    sd ra, 0(sp)
    call write_owned
    ld a0, 0(a0)
    ld ra, 0(sp)
    addi sp, sp, 16
    ret
.size read_owned, .-read_owned
ASM

link() {
    clang --target=riscv64-unknown-elf -march=rv64ima -c "$1.s" -o "$1.o"
    ld.lld --no-relax -static -e read_owned "$1.o" -o "$1.elf"
}
link "$artifacts/owned"
"$checker" check "$artifacts/owned.s" --image "$artifacts/owned.elf" \
    --export-lean "$artifacts/Proof.lean" --prove --certs --ledger "$artifacts/owned.json"
jq -e '.proof_attempt.status == "proved" and
    (.functions | length == 2 and all(.[]; .status == "proved"))' "$artifacts/owned.json"

sed 's/sd a1, 0(a0)/nop/' "$artifacts/owned.s" > "$artifacts/missing-write.s"
link "$artifacts/missing-write"
status=0
"$checker" check "$artifacts/missing-write.s" --image "$artifacts/missing-write.elf" \
    --ledger "$artifacts/missing-write.json" || status=$?
test "$status" -eq 1
jq -e 'any(.functions[]; .name == "write_owned" and .error.rule == "ret-give")' "$artifacts/missing-write.json"

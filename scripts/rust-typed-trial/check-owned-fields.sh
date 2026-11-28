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

# Both finite JALR targets return the consumed region with the initialized word.
awk '
    NR == 1 { alternate = $0; sub(/write_owned/, "write_alternate", alternate); print alternate }
    /^    call write_owned$/ {
        print "    beq a1, zero, .Lother"
        print ".Lfirst_hi:"
        print "    auipc t0, %pcrel_hi(write_owned)"
        print "    addi t0, t0, %pcrel_lo(.Lfirst_hi)"
        print "    j .Lowned_join"
        print ".Lother:"
        print ".Lother_hi:"
        print "    auipc t0, %pcrel_hi(write_alternate)"
        print "    addi t0, t0, %pcrel_lo(.Lother_hi)"
        print ".Lowned_join:"
        print "    jalr ra, 0(t0)"
        next
    }
    { print }
    END {
        print ".globl write_alternate"
        print ".type write_alternate,@function"
        print "write_alternate:"
        print "    sd a1, 0(a0)"
        print "    ret"
        print ".size write_alternate, .-write_alternate"
    }
' "$artifacts/owned.s" > "$artifacts/indirect-owned.s"
link "$artifacts/indirect-owned"
"$checker" check "$artifacts/indirect-owned.s" --image "$artifacts/indirect-owned.elf"     --export-lean "$artifacts/IndirectOwned.lean" --prove --certs --ledger "$artifacts/indirect-owned.json"
jq -e '.proof_attempt.status == "proved" and
    any(.functions[]; .name == "read_owned" and .status == "proved" and
        (.evidence.callees | sort) == ["write_alternate", "write_owned"])'     "$artifacts/indirect-owned.json"

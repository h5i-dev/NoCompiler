"""Translate explicitly supplied allocator ABI contracts to Heap capabilities."""

import re

from loop_inference import function_bodies


def allocator_contracts(specification, linked, selected):
    if not isinstance(specification, dict):
        raise ValueError("allocator contracts must be an object keyed by linked symbol")
    contracts = {}
    budgets = {}
    for symbol, spec in specification.items():
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", symbol) or symbol not in linked or symbol in selected:
            raise ValueError(f"allocator {symbol} must name a linked symbol outside the selected targets")
        if not isinstance(spec, dict):
            raise ValueError(f"invalid allocator specification for {symbol}")
        op = spec.get("operation")
        stack = spec.get("stack")
        align = spec.get("alignment", 16)
        if type(stack) is not int or stack < 0 or type(align) is not int or align <= 0 or align & (align - 1):
            raise ValueError(f"invalid allocator stack budget or alignment for {symbol}")
        if isinstance(op, str) and op.startswith("rust_"):
            signature = rust_allocator_signature(op, spec.get("registers", {}))
        elif op == "allocate":
            signature = (
                "[n] in a0: u64(n) borrow Heap out a0: u64(p) "
                f"give p != 0 => p |-> bytes[n] rw heap where {align} | p"
            )
        elif op == "deallocate":
            signature = "[p, n] in a0: int(p), a1: u64(n) take p |-> bytes[n] rw heap borrow Heap"
        elif op in {"reallocate", "reallocate_nonnull"}:
            prefix = (
                "[p, old, n] in a0: int(p), a1: u64(old), a2: u64(n) "
                "take p |-> bytes[old] rw heap borrow Heap out a0: u64(q) "
            )
            if op == "reallocate":
                signature = prefix + (
                    "give q = 0 => p |-> bytes[old] rw heap, "
                    f"q != 0 => q |-> bytes[n] rw heap where {align} | q"
                )
            else:
                signature = prefix + f"give q |-> bytes[n] rw heap where q != 0, {align} | q"
        else:
            raise ValueError(f"unknown allocator operation for {symbol}: {op}")
        contracts[symbol] = f"#: extern fn {symbol} {signature} stack {stack}\n"
        budgets[symbol] = stack
    return contracts, budgets


def heap_callers(source, selected, allocators):
    callers = {
        symbol: {args[-1] for op, *args in instructions if op in {"call", "tail"} and args}
        for symbol, _, instructions, _ in function_bodies(source, selected)
    }
    uses_heap = set(allocators)
    while newly_reached := {s for s, callees in callers.items() if callees & uses_heap} - uses_heap:
        uses_heap.update(newly_reached)
    return uses_heap & selected


def add_heap_borrow(contract):
    position = re.search(r" (borrow|where|out|stack) ", contract)
    before, after = contract[:position.start()], contract[position.start():]
    if position[1] == "borrow":
        return before + " borrow Heap," + after.removeprefix(" borrow")
    return before + " borrow Heap" + after

RUST_ALLOCATOR = re.compile(
    r"^_RNv(?:Cs[A-Za-z0-9]+_)?7___rustc\d+_"
    r"(__rust_(?:alloc(?:_zeroed)?|dealloc|realloc|no_alloc_shim_is_unstable_v2))$"
)


def forwarder(instructions, count):
    """Recover argument moves of a compiler-emitted tail forwarding shim."""
    if not instructions or instructions[-1][0] != "tail":
        return None
    state = {f"a{i}": f"a{i}" for i in range(count)}
    moved = []
    for instruction in instructions[:-1]:
        if len(instruction) == 3 and instruction[0] == "mv":
            _, destination, source = instruction
            if source not in state or not re.fullmatch(r"a[0-7]", destination):
                return None
            state[destination] = state[source]
            moved.append(destination)
        else:
            return None
    aliases = {}
    for reg in [*reversed(moved), *state]:
        aliases.setdefault(state[reg], reg)
    if len(aliases) != count:
        return None
    return instructions[-1][1], aliases


def discover_rust_allocators(source, body, selected, linked, stack):
    runtimes = {symbol: f"rust_{match[1].removeprefix('__rust_')}"
                for symbol in linked if (match := RUST_ALLOCATOR.fullmatch(symbol))}
    calls = {args[-1] for _, _, instructions, _ in function_bodies(body, selected)
             for op, *args in instructions if op in {"call", "tail"} and args}
    operations = {
        symbol: {"operation": op, "stack": 0 if op.startswith("rust_no_alloc_shim") else stack}
        for symbol, op in runtimes.items() if symbol in calls
    }
    widths = {"rust_alloc": 2, "rust_alloc_zeroed": 2, "rust_dealloc": 3, "rust_realloc": 4}
    for symbol, _, instructions, _ in function_bodies(source, runtimes):
        op = runtimes[symbol]
        if op not in widths:
            continue
        candidate = forwarder(instructions, widths[op])
        if candidate and candidate[0] in calls and candidate[0] in linked and candidate[0] not in selected:
            callee, registers = candidate
            operations[callee] = {"operation": op, "stack": stack,
                                  "registers": registers, "forwarding_shim": symbol}
    return operations


def rust_allocator_signature(operation, registers):
    signature = canonical_rust_allocator_signature(operation)
    if not registers:
        return signature
    inputs, sep, rest = signature.partition(" borrow")
    inputs = re.sub(r"\ba[0-7](?=:)", lambda match: registers.get(match[0], match[0]), inputs)
    return inputs + sep + rest


def canonical_rust_allocator_signature(operation):
    alignments = [1 << n for n in range(7)]
    supported = "(" + " || ".join(f"a = {n}" for n in alignments) + ")"
    limits = f"n > 0, {supported}"
    post = ", ".join(f"(a = {n} => {n} | q)" for n in alignments if n > 1)
    if operation in {"rust_alloc", "rust_alloc_zeroed"}:
        return (f"[n, a] in a0: u64(n), a1: u64(a) borrow Heap where {limits} "
                f"out a0: u64(q) give q != 0 => q |-> bytes[n] rw heap where {post}")
    if operation == "rust_dealloc":
        return (f"[p, n, a] in a0: u64(p), a1: u64(n), a2: u64(a) "
                f"borrow Heap take p |-> bytes[n] rw heap where {limits}")
    if operation == "rust_realloc":
        return (f"[p, old, a, n] in a0: u64(p), a1: u64(old), a2: u64(a), a3: u64(n) "
                f"borrow Heap take p |-> bytes[old] rw heap where old > 0, {limits} "
                f"out a0: u64(q) give q = 0 => p |-> bytes[old] rw heap, "
                f"q != 0 => q |-> bytes[n] rw heap where {post}")
    if operation == "rust_no_alloc_shim_is_unstable_v2":
        return "[]"
    raise ValueError(f"unknown Rust allocator operation: {operation}")

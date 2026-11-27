"""Infer fixed-frame annotations and stack budgets for direct calls."""

import re

from loop_inference import function_bodies
from memory_inference import stack_call_ranges

ACCESS = re.compile(r"(-?(?:0x[\da-fA-F]+|\d+))\(sp\)")
WIDTHS = {
    "lb": 1, "lbu": 1, "lh": 2, "lhu": 2, "lw": 4, "lwu": 4, "ld": 8,
    "sb": 1, "sh": 2, "sw": 4, "sd": 8,
}


def frame(instructions, address_taken):
    size = 0
    if instructions and instructions[0][:3] == ["addi", "sp", "sp"]:
        try:
            size = -int(instructions[0][3], 0)
        except (IndexError, ValueError):
            pass
    if size <= 0 or size % 16:
        return 0, ""

    address_taken = {(start, end) for start, end in address_taken if 0 <= start < end <= size}
    accesses = address_taken.copy()
    for op, *args in instructions:
        if op in WIDTHS and args and (address := ACCESS.fullmatch(args[-1])):
            start = int(address[1], 0)
            end = start + WIDTHS[op]
            if 0 <= start and end <= size:
                accesses.add((start, end))

    slots = []
    ranges = []
    for start, end in sorted(accesses):
        if ((start, end) not in address_taken and end - start == 8 and start % 8 == 0 and not any(
            other_start < end and start < other_end and (other_start, other_end) != (start, end)
            for other_start, other_end in accesses
        )):
            slots.append(str(start))
        elif ranges and start <= ranges[-1][1]:
            ranges[-1] = (ranges[-1][0], max(end, ranges[-1][1]))
        else:
            ranges.append((start, end))

    text = f"frame {size}"
    if slots:
        text += " slots " + ", ".join(slots)
    if ranges:
        text += " addr " + ", ".join(f"[{start}, {end})" for start, end in ranges)
    return size, text


def stack_annotations(source, symbols, requirements, external_budgets=None):
    frames = {}
    calls = {}
    for symbol, _, instructions, labels in function_bodies(source, symbols):
        frames[symbol] = frame(instructions, stack_call_ranges(instructions, labels, requirements))
        calls[symbol] = [
            (op, args[-1]) for op, *args in instructions if op in {"call", "tail"} and args
        ]

    budgets = dict(external_budgets or {})

    def budget(symbol, visiting):
        if symbol in budgets:
            return budgets[symbol]
        if symbol in visiting or symbol not in frames:
            return None
        size, _ = frames[symbol]
        total = size
        for op, callee in calls[symbol]:
            child = budget(callee, visiting | {symbol})
            if child is None:
                return None
            total = max(total, child + (size if op == "call" else 0))
        budgets[symbol] = total
        return total

    annotations = {}
    for symbol, (size, declaration) in frames.items():
        total = budget(symbol, set())
        if total is None:
            total = size  # Unknown callees remain subject to the checker call rules.
        annotations[symbol] = f"{declaration} stack {total}".strip()
    return annotations

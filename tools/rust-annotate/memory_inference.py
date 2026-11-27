"""Infer fixed raw-pointer footprints from RV64 loads and stores."""

import re

from loop_inference import (
    LOADS, MEMORY, STORES, affine, constant, control_flow, function_bodies, merge, order_nodes, transfer,
)


def after_call(state):
    return {reg: value for reg, value in state.items()
            if isinstance(reg, str) and (reg == "sp" or re.fullmatch(r"s\d+", reg))}


def footprint(instructions, labels, pointers, callees):
    """Infer a prefix for each accessed raw pointer in an acyclic CFG."""
    preds = control_flow(instructions, labels)
    order = order_nodes(preds, {})
    if not order or any(op in {"jal", "jalr", "jr", "ecall"} for op, *_ in instructions):
        return {}
    states = {}
    regions = {}
    for node in order:
        state = ({"sp": {"entrysp": 1}, **{reg: {name: 1} for reg, name in pointers.items()}} if node == 0
                 else merge([states[p] for p in sorted(preds[node])]))
        op, *args = instructions[node]
        width = LOADS.get(op) or STORES.get(op)
        accesses = []
        if width and (address := MEMORY.fullmatch(args[-1])):
            value = affine(state.get(address[2]), constant(int(address[1], 0)))
            accesses.append((value, width, width, op in STORES))
        if op in {"call", "tail"}:
            for reg, (size, align, writable) in callees.get(args[-1], {}).items():
                accesses.append((state.get(reg), size, align, writable))
        for value, size, align, writable in accesses:
            for register, name in pointers.items():
                if value is None or value.get(name) != 1 or value.keys() - {name, ""}:
                    continue
                start = value.get("", 0)
                if start < 0 or start % align:
                    continue  # Leave this access to the checker.
                end, alignment, write = regions.get(register, (0, 1, False))
                regions[register] = (max(end, start + size), max(alignment, align), write or writable)
        if op == "call":
            state = after_call(state)
        elif not transfer(state, instructions[node]):
            state.clear()
        states[node] = state
    return regions


def infer_requirements(source, pointers):
    bodies = {
        symbol: (instructions, labels)
        for symbol, _, instructions, labels in function_bodies(source, pointers)
        if pointers[symbol]
    }
    graph = {
        symbol: {args[-1] for op, *args in instructions
                 if op in {"call", "tail"} and args and args[-1] in bodies}
        for symbol, (instructions, _) in bodies.items()
    }
    requirements = {}
    while ready := sorted(symbol for symbol in graph if graph[symbol] <= requirements.keys()):
        for symbol in ready:
            instructions, labels = bodies[symbol]
            requirements[symbol] = footprint(instructions, labels, pointers[symbol], requirements)
            del graph[symbol]
    return requirements


def stack_call_ranges(instructions, labels, requirements):
    """Collect fixed stack addresses passed to callees with inferred footprints."""
    preds = control_flow(instructions, labels)
    order = order_nodes(preds, {})
    if not order:
        return set()
    states = {}
    ranges = set()
    for node in order:
        state = ({"sp": {"entrysp": 1}} if node == 0 else
                 merge([states[p] for p in sorted(preds[node])]))
        op, *args = instructions[node]
        if op == "call":
            for reg, (size, _, _) in requirements.get(args[-1], {}).items():
                value = affine(state.get(reg), state.get("sp"), -1)
                if value is not None and value.keys() <= {""}:
                    start = value.get("", 0)
                    ranges.add((start, start + size))
            state = after_call(state)
        elif not transfer(state, instructions[node]):
            state.clear()
        states[node] = state
    return ranges

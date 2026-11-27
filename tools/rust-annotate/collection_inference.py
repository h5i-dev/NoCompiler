"""Discover candidate length/capacity invariants for inline array storage."""

import re

from loop_inference import function_bodies
from memory_inference import MEMORY


def struct_fields(descriptor):
    type_name, *descriptors = descriptor.split(";")
    fields = {}
    for item in filter(None, descriptors):
        name, offset, detail = item.split("@")
        fields[name] = (int(offset), detail)
    return type_name, fields


def checked_growth(instructions, pointer, offset, capacity):
    """Look for a word length load, capacity comparison, and increment store."""
    lengths = set()
    increments = set()
    constants = {}
    comparison = False
    for op, *args in instructions:
        if len(args) == 2 and (address := MEMORY.fullmatch(args[1])):
            register, displacement = address[2], int(address[1], 0)
            if register == pointer and displacement == offset:
                if op == "ld":
                    lengths.add(args[0])
                if op == "sd" and args[0] in increments and comparison:
                    return True
        if op == "li":
            constants[args[0]] = int(args[1], 0)
        elif op in {"bltu", "bgeu", "sltu"} and len(args) == 3:
            operands = args[:2] if op != "sltu" else args[1:]
            if any(reg in lengths and constants.get(other) in {capacity, capacity - 1}
                   for reg, other in (operands, operands[::-1])):
                comparison = True
        elif op == "addi" and args[1] in lengths and args[2] == "1":
            increments.add(args[0])
    return False


def discover(source, layouts):
    candidates = {}
    conflicting = set()
    for symbol, _, instructions, _ in function_bodies(source, layouts):
        _, args = layouts[symbol]
        register = 0
        for arg in args:
            if arg.startswith("struct:"):
                _, _, align, access, descriptor = arg.split(":", 4)
                type_name, fields = struct_fields(descriptor)
                lengths = [(field, offset) for field, (offset, mode) in fields.items()
                           if field in {"len", "length"} and mode == "word"]
                arrays = [(field, int(mode)) for field, (_, mode) in fields.items() if mode.isdecimal()]
                if access == "rw" and int(align) >= 8 and len(lengths) == len(arrays) == 1:
                    (field, offset), = lengths
                    (array, capacity), = arrays
                    if capacity > 0 and checked_growth(instructions, f"a{register}", offset, capacity):
                        found = candidates.setdefault(type_name, {"fields": {field: array}, "witnesses": []})
                        if found["fields"] != {field: array}:
                            conflicting.add(type_name)
                        found["witnesses"].append(symbol)
            register += 2 if arg.startswith("slice:") else 1
    return {name: info for name, info in candidates.items() if name not in conflicting}

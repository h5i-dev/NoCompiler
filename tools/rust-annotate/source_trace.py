"""Read LLVM's inline call stacks from the linked ELF's DWARF."""

import json
import re
import subprocess

DEBUG_SECTION = re.compile(r'^\s*\.section\s+"?\.debug(?:_|\b)')


def without_debug_sections(source):
    keep = True
    for line in source.splitlines(keepends=True):
        directive = line.strip().split(maxsplit=1)
        if directive and directive[0] in {".section", ".text", ".data", ".bss"}:
            keep = not DEBUG_SECTION.match(line)
        if keep:
            yield line


def inline_traces(symbolizer, image, linked, symbols):
    addresses = {}
    for path, symbol in symbols.items():
        if symbol in linked:
            start, size = linked[symbol]
            for address in range(start, start + size, 4):
                addresses.setdefault(address, []).append(path)
    if not addresses:
        return {}
    result = subprocess.run(
        [symbolizer, "--inlines", "--output-style=JSON", "--obj", image],
        input="".join(f"{address:#x}\n" for address in addresses),
        text=True, stdout=subprocess.PIPE, check=True,
    )
    traces = {}
    for line in result.stdout.splitlines():
        event = json.loads(line)
        frames = event.get("Symbol", [])
        if len(frames) < 2:
            continue
        address = int(event["Address"], 16)
        stack = [
            {"function": f["FunctionName"], "file": f["FileName"],
             "line": f["Line"], "column": f["Column"]}
            for f in frames
        ]
        for path in addresses[address]:
            ranges = traces.setdefault(path, [])
            if ranges and ranges[-1]["end"] == address and ranges[-1]["frames"] == stack:
                ranges[-1]["end"] += 4
            else:
                ranges.append({"start": address, "end": address + 4, "frames": stack})
    return traces

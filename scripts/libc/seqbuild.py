#!/usr/bin/env python3
"""Build Lean modules one at a time (at most one `lean` process): `lake build` has no job limit, so this walks the
local import graph from the given roots in dependency order and runs `lake build M` per module (with M's imports
already built, lake compiles M alone).

    seqbuild.py ROOT [ROOT...]        (run in lean/, with lake on PATH)

Stops at the first module that fails, printing lake's output for it. Prints `Build completed successfully` at the end
(the line the landing scripts look for).
"""
import os
import re
import subprocess
import sys


def path_of(mod):
    return mod.replace('.', '/') + '.lean'


def imports(mod):
    p = path_of(mod)
    if not os.path.exists(p):
        return None  # not a local module (Lean core, Std, ...)
    out = []
    for line in open(p):
        m = re.match(r'import\s+(\S+)', line)
        if m:
            out.append(m.group(1))
        elif line.strip() and not line.startswith('import') and not line.startswith('--') \
                and not line.startswith('/-') and not line.startswith('prelude'):
            if not line.startswith(' ') and not line.startswith('-/'):
                pass
    return out


def topo(roots):
    order, seen = [], set()
    sys.setrecursionlimit(100000)

    def visit(m):
        if m in seen:
            return
        seen.add(m)
        deps = imports(m)
        if deps is None:
            return
        for d in deps:
            visit(d)
        order.append(m)
    for r in roots:
        visit(r)
    return order


def main():
    mods = topo(sys.argv[1:])
    for i, m in enumerate(mods):
        r = subprocess.run(['lake', 'build', m], capture_output=True, text=True)
        if r.returncode != 0:
            sys.stdout.write(r.stdout + r.stderr)
            print(f'seqbuild: {m} failed ({i + 1}/{len(mods)})')
            sys.exit(1)
    print(f'Build completed successfully ({len(mods)} modules, one at a time).')


if __name__ == '__main__':
    main()

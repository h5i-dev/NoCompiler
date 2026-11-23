#!/usr/bin/env python3
"""Rewrite hand step proofs (A's nocompiler_wstep style) into nocompiler_run calls.

runify.py FILE.lean OUTDIR [THEOREM...] [--bounded] [--mem] [--drop=FACT ...]
For each theorem (all `theorem X ... := by` blocks by default) writes OUTDIR/<X>.lean: a test that imports
FILE's module and proves the same statement as `X_run`, with
  * maximal sequences of `nocompiler_wstep [..]` / `refine ⟨<perm>, ?_⟩` lines at one indentation merged
    into `nocompiler_run [union of the facts] using [LEMMAS]`;
  * a `have` sitting between two such sequences at the same indentation hoisted above the first.
Options: --whole=OUT rewrites the whole file into OUT (same theorem names, the run tactic's import added;
--skip=THM keeps a theorem as it is; --exact merges only consecutive steps with the same
facts (each step keeps exactly its own; fewer lines saved, fewer failures), --exact-for=THM does so for one
theorem in whole mode; --heartbeats=THM:N puts `set_option maxHeartbeats N in` before it); --step=pstep converts nocompiler_pstep proofs (nocompiler_prun_n), --step=wstepD A's region-aware
nocompiler_wstepD hD (nocompiler_runD_n N hD; steps merged only under the same hD); a step that starts a bullet
(`· nocompiler_…`) starts a block;
--bounded emits nocompiler_run_n N (N the block's step count: the run stops where the hand proof
cut it); --mem emits nocompiler_runm (reads after disjoint writes); --drop=FACT leaves a fact out of the
merged lists. The tactics: NoCompiler/Linux/Run.lean, RunMem.lean, RunN.lean.
Prints per theorem: original lines, new lines. A test file carries the options its theorem has in FILE (top-level `set_option`s and the `set_option ... in`
above it), nothing more, so a check of it is a check in FILE's setting. Each output must be checked (`lake env lean OUTDIR/X.lean`):
merging gives every step the union of its block's facts, which can change the form of the final state.
"""
import re, sys, os
BOUNDED = False
EXACT = '--exact' in sys.argv
EXACT_FOR = {a[12:] for a in sys.argv if a.startswith('--exact-for=')}

STEPNAME = next((a[7:] for a in __import__("sys").argv if a.startswith("--step=")), "wstep")
STEP = (re.compile(r"^\s*nocompiler_wstepD\s+(\S+)\s*\[(.*)\]\s*$") if STEPNAME == "wstepD"
        else re.compile(r"^\s*nocompiler_" + STEPNAME + r"(\s*\[(.*)\])?\s*$"))
PERM = re.compile(r"^\s*refine ⟨(.*), \?_⟩\s*$")
HAVE = re.compile(r"^\s*have ")


def ind(l):
    return len(l) - len(l.lstrip())


def is_perm(l):
    m = PERM.match(l)
    if not (bool(m) and ".done" not in l and "?_" not in m.group(1)): return False
    t = re.sub(r"^(NoCompiler\.)?Perm\.canRead_of_canWrite\s*\(?", "", m.group(1).strip()).strip()
    h = re.match(r"[A-Za-z_][A-Za-z0-9_'.]*", t)
    return bool(h) and h.group(0) not in ("fun", "by", "show", "if", "match")


def split_facts(s):
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "([{⟨": depth += 1
        if ch in ")]}⟩": depth -= 1
        if ch == "," and depth == 0:
            out.append(cur.strip()); cur = ""
        else:
            cur += ch
    if cur.strip(): out.append(cur.strip())
    return out


def items(lines):
    """Group lines into (kind, [lines]) where a `have` keeps its continuation lines."""
    res, i = [], 0
    lines = list(lines)
    bullets = set()
    for j, l in enumerate(lines):
        m = re.match(r"^(\s*)· (.*)$", l)
        if m and STEP.match(m.group(1) + "  " + m.group(2)):
            lines[j] = m.group(1) + "  " + m.group(2); bullets.add(j)
    while i < len(lines):
        l = lines[i]
        if STEP.match(l):
            if i in bullets: res.append(("bstep", [l])); i += 1; continue
            res.append(("step", [l])); i += 1
        elif is_perm(l):
            res.append(("perm", [l])); i += 1
        elif HAVE.match(l):
            j = i + 1
            while j < len(lines) and lines[j].strip() and ind(lines[j]) > ind(l):
                j += 1
            res.append(("have", lines[i:j])); i = j
        else:
            res.append(("other", [l])); i += 1
    return res


def runify(body, lemmas, tac="nocompiler_run", drop=(), exact=None):
    exact = EXACT if exact is None else exact
    its = items(body)
    # hoist: a have between two step runs at the same indentation moves above the first run
    changed = True
    while changed:
        changed = False
        for k in range(1, len(its) - 1):
            if its[k][0] != "have": continue
            d = ind(its[k][1][0])
            a = k - 1
            while a >= 0 and its[a][0] in ("step", "perm", "have") and ind(its[a][1][0]) == d:
                a -= 1
            a += 1
            b = k + 1
            if b < len(its) and its[b][0] in ("step", "perm") and ind(its[b][1][0]) == d:
                # the block of haves ending at k (adjacent, same indentation) moves, in order, before the
                # first step of the run before it
                bs = k
                while bs - 1 >= a and its[bs - 1][0] == "have": bs -= 1
                if not any(its[x][0] in ("step", "perm") for x in range(a, bs)): continue
                f = next(x for x in range(a, bs) if its[x][0] in ("step", "perm"))
                blk = its[bs:k + 1]; del its[bs:k + 1]
                its[f:f] = blk; changed = True
                break
    out, k = [], 0
    while k < len(its):
        kind, ls = its[k]
        if kind in ("step", "perm", "bstep"):
            bul = kind == "bstep"
            if bul: its[k] = ("step", ls)
            d = ind(ls[0]); facts = []; nsteps = 0; first = None; hdD = None
            while k < len(its) and its[k][0] in ("step", "perm") and ind(its[k][1][0]) == d:
                m = STEP.match(its[k][1][0])
                if m and STEPNAME == "wstepD":
                    if hdD is None: hdD = m.group(1)
                    elif m.group(1) != hdD: break
                if m and exact:
                    fl = split_facts(m.group(2)) if m.group(2) else []
                    if first is None: first = fl
                    elif fl != first: break
                if m: nsteps += 1
                if m and m.group(2):
                    for f in split_facts(m.group(2)):
                        if f not in facts and f not in drop: facts.append(f)
                k += 1
            t = f"{tac}_n {nsteps}" if BOUNDED else tac
            if STEPNAME == "wstepD": t = f"nocompiler_runD_n {nsteps} {hdD}"
            pre = " " * (d - 2) + "· " if bul else " " * d
            out.append(pre + f"{t} [{', '.join(facts)}] using [{', '.join(lemmas)}]")
        else:
            out.extend(ls); k += 1
    return out


def theorems(src):
    lines = src.split("\n")
    res = []
    for i, l in enumerate(lines):
        m = re.match(r"^theorem (\S+)", l)
        if not m: continue
        j = i + 1
        while j < len(lines) and (lines[j].startswith(" ") or not lines[j].strip()):
            j += 1
        while lines[j - 1].strip() == "": j -= 1
        res.append((m.group(1), i, j))
    return lines, res


def opts(lines, a):
    """The options the theorem at line a runs under in its file: top-level `set_option` lines before it (not
    `... in`), then the `set_option ... in` lines directly above it."""
    top = [l for l in lines[:a] if l.startswith("set_option ") and not l.rstrip().endswith(" in")]
    j, local = a - 1, []
    while j >= 0 and lines[j].startswith("set_option ") and lines[j].rstrip().endswith(" in"):
        local.insert(0, lines[j]); j -= 1
    return top + local


def main():
    path, outdir = sys.argv[1], sys.argv[2]
    want = [a for a in sys.argv[3:] if not a.startswith("--")]
    global BOUNDED
    BOUNDED = "--bounded" in sys.argv
    tac = "nocompiler_runm" if "--mem" in sys.argv else ("nocompiler_prun" if STEPNAME == "pstep" else "nocompiler_run")
    drop = tuple(a[7:] for a in sys.argv if a.startswith("--drop="))
    src = open(path).read()
    lines, ths = theorems(src)
    mod = path.replace("/", ".").removesuffix(".lean")
    head = [l for l in lines[:40] if l.startswith(("namespace ", "open "))]
    ns = [l for l in head if l.startswith("namespace ")][:1]
    whole = next((a[8:] for a in sys.argv if a.startswith("--whole=")), None)
    skip = {a[7:] for a in sys.argv if a.startswith("--skip=")}
    if whole:
        out = list(lines)
        imp = "import NoCompiler.Linux.RunN" if BOUNDED else ("import NoCompiler.Linux.RunMem" if tac.endswith("m") else "import NoCompiler.Linux.Run")
        for name, a, b in reversed(ths):
            if name in skip or (want and name not in want): continue
            body = lines[a:b]
            if not any(STEP.match(l) for l in body): continue
            lem = []
            for l in body:
                m = PERM.match(l)
                if m and is_perm(l):
                    t = re.sub(r"^(NoCompiler\.)?Perm\.canRead_of_canWrite\s*\(?", "", m.group(1).strip()).strip()
                    w = re.match(r"[A-Za-z_][A-Za-z0-9_'.]*", t)
                    if w and w.group(0) not in lem: lem.append(w.group(0))
            new = runify(body, lem, tac, drop, exact=EXACT or name in EXACT_FOR)
            hb = next((x.split(":")[1] for x in sys.argv if x.startswith(f"--heartbeats={name}:")), None)
            if hb: new = [f"set_option maxHeartbeats {hb} in"] + new
            out[a:b] = new
            print(f"{name}\t{b - a}\t{len(new)}")
        last = max(i for i, l in enumerate(out) if l.startswith("import "))
        if imp not in out: out.insert(last + 1, imp)
        open(whole, "w").write("\n".join(out))
        return
    os.makedirs(outdir, exist_ok=True)
    for name, a, b in ths:
        if want and name not in want: continue
        body = lines[a:b]
        if not any(STEP.match(l) for l in body): continue
        # the permission lemmas the proof names in its refine lines
        lem = []
        for l in body:
            m = PERM.match(l)
            if m and is_perm(l):
                t = m.group(1).strip()
                t = re.sub(r"^(NoCompiler\.)?Perm\.canRead_of_canWrite\s*\(?", "", t).strip()
                w = re.match(r"[A-Za-z_][A-Za-z0-9_'.]*", t)
                if w and w.group(0) not in lem: lem.append(w.group(0))
        new = runify(body, lem, tac, drop)
        new[0] = new[0].replace(f"theorem {name}", f"theorem {name}_run", 1)
        txt = "\n".join([f"import {mod}", ("import NoCompiler.Linux.RunN" if BOUNDED else "import NoCompiler.Linux.RunMem" if tac.endswith("m") else "import NoCompiler.Linux.Run")] + head
                        + opts(lines, a) + new
                        + [f"#print axioms {name}_run"]
                        + ([f"end {ns[0].split()[1]}"] if ns else []))
        open(os.path.join(outdir, f"{name}.lean"), "w").write(txt + "\n")
        print(f"{name}\t{b - a}\t{len(new)}")


main()

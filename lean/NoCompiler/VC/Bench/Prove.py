# Usage: python3 -I Prove.py WORKDIR [N] [--specs safe,anyread,anymem,alignargs] [--jobs J] [--calls] [--loops]
#   [--only FILE]  (FILE: one function name per line; their callees are run too)
# The whole nocompiler_auto proof (explore and the goals after it) on a binary's functions, one module
# per function, each capped (6 GB, no swap, 300 s); cost = every profile category but import and
# initialization, per instruction. WORKDIR is Art.py's (Art.lean, ArtImg.olean).
#
# Which functions: those a safety specification can take, the N largest (default 20; 0 for all):
#   a `_dom` (every callee passed the profile check), no loops (an invariant and a measure would be the
#   function's own), and, without --calls, no callees. With --calls, also functions whose callees (every
#   function in their `_dom`) are such functions: callees first (a callee's `_dom` is inside its
#   caller's), each caller with `calls [...]` of its callees' theorems; its stack bound is its frame plus
#   its callees' largest bound, so that a callee's stack lies in its caller's.
# With --loops, also the functions with exactly one loop (no callees): the invariant is the loop's back
# edge's condition (a branch to its head comparing rs1 and rs2: rs1 ≠ rs2 for bne, rs1 < rs2 for bltu,
# rs2 ≤ rs1 for bgeu, else True; the frame is added by the tactic), and the measure is tried as
# (rs2 - rs1).toNat, then (rs1 - rs2).toNat. (Several loops need a measure
# that also decreases from one loop's head to the next; not tried.)
# Specifications, tried in order until one proves the function (--specs; a caller starts at its
# callees' strictest, since a callee's permission must lie in its caller's):
#   safe       any entry; returns, preserving the ABI; reads only .rodata; writes only its frame;
#   anyread    the same, but reads anywhere (reads through argument pointers);
#   anymem     the same, but reads and writes anywhere (writes through argument pointers);
#   rodata     alignargs, and memory holds .rodata at entry (seg_rodata.Loaded s.mem, what the loader
#              establishes); writes anywhere but .rodata, so it stays loaded. For functions that search a
#              .rodata table (C's 05:02 note); C's closers read a constant .rodata address under it.
#   offframe   alignargs, and for each (pointer, length) argument pair the previous attempt stored
#              through (`s.reg p + s.reg n` in a store of its unsolved goals): the buffer [p, p + n) does
#              not wrap and is not the function's frame (the `stack` bytes below the entry sp). A spec
#              choice (STATUS-D, QUEUE-D C2); tried only when such a store was seen.
#   alignargs  anymem, with a0-a7 8-aligned as preconditions (an argument pointer aligned to its type;
#              stronger than a byte pointer needs, so a proof that needs it says so).
# "Anywhere" is the region ⟨0, 2^65⟩, which covers every access. Every specification still requires
# alignment, termination and the ABI (the callee-saved registers, sp, the return).
import concurrent.futures
import threading, os, re, subprocess, sys

work = sys.argv[1]
specs = ["safe"]
img_mod, img_ns = "ArtImg", "Art.T"
lib_file = None
jobs = 1
with_calls = "--calls" in sys.argv
with_loops = "--loops" in sys.argv
only = None
rest = []
i = 2
while i < len(sys.argv):
    a = sys.argv[i]
    if a == "--image":
        img_mod, img_ns = sys.argv[i + 1].split(":"); i += 2; continue
    if a == "--lib":
        lib_file = sys.argv[i + 1]; i += 2; continue
    if a == "--specs":
        specs = sys.argv[i + 1].split(","); i += 2; continue
    if a == "--jobs":
        jobs = int(sys.argv[i + 1]); i += 2; continue
    if a == "--only":
        only = [l.split()[0] for l in open(sys.argv[i + 1]) if l.strip() and not l.startswith("#")]; i += 2; continue
    if not a.startswith("--"):
        rest.append(a)
    i += 1
top = int(rest[0]) if rest else 20
here = os.path.dirname(os.path.abspath(__file__))
lean_dir = os.path.abspath(os.path.join(here, "..", "..", ".."))
lean_path = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=lean_dir, capture_output=True,
                           text=True, check=True).stdout.strip() + ":" + work
unit = {"ns": 1e-6, "us": 1e-3, "μs": 1e-3, "ms": 1.0, "s": 1000.0}

src = open(os.path.join(work, "Art.lean")).read()
funcs = {}
loops = {}
for m in re.finditer(r"def (\w+)_func : Struct.Func := ⟨(0x[0-9a-f]+)#64, (\d+), (\[.*?\])⟩", src):
    funcs[m.group(1)] = (int(m.group(2), 16), int(m.group(3)), ".loop" in m.group(4))
    loops[m.group(1)] = [(int(a, 16), int(b, 16)) for a, b in
                         re.findall(r"⟨\.loop, (0x[0-9a-f]+)#64, (0x[0-9a-f]+)#64⟩", m.group(4))]
text = int(re.search(r"def code : Code := Code.ofChunks (0x[0-9a-f]+)#64 chunks", src).group(1), 16)
chunkk = dict(re.findall(r"theorem (\w+)_chunk : ∀ x, Dom.mem \[chunk_(\d+)\.range", src))
chunkd = {a: (int(b), int(c), int(d, 0)) for a, b, c, d in
          re.findall(r"def chunk_(\d+) : Chunk := ⟨(\d+), (\d+), (0x[0-9a-f]+|\d+)⟩", src)}


def cfg_loops(n):
    """For a function without a tree: a loop per backward branch inside it from whose target the
    branch is reached again, (target, branch pc + 4). A backward jump to a shared exit is no loop."""
    entry, ln = funcs[n][0], funcs[n][1]
    off, cl, bits = chunkd[chunkk[n]]
    base = text + 4 * off
    hi = entry + 4 * ln

    def word(pc):
        k = (pc - base) // 4
        return (bits >> (32 * k)) & 0xffffffff if 0 <= k < cl else 0

    def btarget(pc, w):
        imm = (((w >> 31) & 1) << 12) | (((w >> 7) & 1) << 11) | (((w >> 25) & 0x3f) << 5) | (((w >> 8) & 0xf) << 1)
        return pc + (imm - 0x2000 if imm & 0x1000 else imm)

    def jtarget(pc, w):
        imm = (((w >> 31) & 1) << 20) | (((w >> 12) & 0xff) << 12) | (((w >> 20) & 1) << 11) | (((w >> 21) & 0x3ff) << 1)
        return pc + (imm - 0x200000 if imm & 0x100000 else imm)

    def succs(pc):
        w = word(pc)
        op, rd = w & 0x7f, (w >> 7) & 0x1f
        if op == 0x63:
            l = [pc + 4, btarget(pc, w)]
        elif op == 0x6f and rd == 0:
            l = [jtarget(pc, w)]
        elif op == 0x67 and rd == 0:
            l = []
        else:
            l = [pc + 4]
        return [t for t in l if entry <= t < hi]

    def reach(t):
        seen, work = set(), [t]
        while work:
            x = work.pop()
            if x not in seen:
                seen.add(x)
                work += succs(x)
        return seen

    out = []
    for pc in range(entry, hi, 4):
        w = word(pc)
        t = btarget(pc, w) if w & 0x7f == 0x63 else (
            jtarget(pc, w) if w & 0x7f == 0x6f and (w >> 7) & 0x1f == 0 else None)
        if t is not None:
            if entry <= t <= pc and pc in reach(t):
                out.append((t, pc + 4))
    return sorted(set(out))


def back_edges(n):
    """The branches inside each loop of n that go to its head: (head, rs1, rs2)."""
    off, ln, bits = chunkd[chunkk[n]]
    base = text + 4 * off
    out = []
    for st, sp in loops[n]:
        for pc in range(st, sp, 4):
            w = (bits >> (32 * ((pc - base) // 4))) & 0xffffffff
            if w & 0x7f == 0x63:
                imm = (((w >> 31) & 1) << 12) | (((w >> 7) & 1) << 11) | (((w >> 25) & 0x3f) << 5) | (((w >> 8) & 0xf) << 1)
                if imm & 0x1000:
                    imm -= 0x2000
                if pc + imm == st:
                    out.append((st, (w >> 15) & 31, (w >> 20) & 31, (w >> 12) & 7))
        if not any(b[0] == st for b in out):
            # Only an unconditional jump back (`j head`, e.g. _Exit's `ecall; j 1b`, which the exit syscall
            # never lets iterate): invariant True, measure 0 (the zero register's form below).
            for pc in range(st, sp, 4):
                w = (bits >> (32 * ((pc - base) // 4))) & 0xffffffff
                if w & 0x7f == 0x6f and (w >> 7) & 31 == 0:
                    imm = (((w >> 31) & 1) << 20) | (((w >> 12) & 0xff) << 12) | (((w >> 20) & 1) << 11) | (((w >> 21) & 0x3ff) << 1)
                    if imm & 0x100000:
                        imm -= 0x200000
                    if pc + imm == st:
                        out.append((st, 0, 0, -1))
                        break
    return out
# Functions without a tree (they failed the profile check): loops from their backward branches.
notree = set(re.findall(r"def (\w+)_func : Struct.Func := ⟨0x[0-9a-f]+#64, \d+, \[\]⟩", src))
for n in notree:
    if n in chunkk:
        loops[n] = cfg_loops(n)
        funcs[n] = (funcs[n][0], funcs[n][1], bool(loops[n]))


frame = {m[0]: int(m[1]) for m in re.findall(r"def (\w+)_frame : Struct.Frame := ⟨(\d+),", src)}
doms = dict(re.findall(r"def (\w+)_dom : Dom := (\[.*?\])\n", src))
byentry = {v[0]: n for n, v in funcs.items()}
rodata = "seg_rodata" in src
# The functions in a `_dom` other than the function itself: its callees, transitively.
deps = {n: [byentry.get(int(a, 16)) for a in re.findall(r"\((0x[0-9a-f]+)#64", doms[n])
            if int(a, 16) != funcs[n][0]] for n in doms}
leaf = [n for n in funcs if n in doms and not funcs[n][2] and not deps[n]]
caller = [n for n in funcs if n in doms and not funcs[n][2] and deps[n]]
cats = {"no _dom (a callee failed the profile check)": [n for n in funcs if n not in doms],
        "loops (an invariant and a measure are the function's own)":
            [n for n in funcs if n in doms and funcs[n][2]],
        "calls": caller, "leaves (no loop, no callee)": leaf}
for k, v in cats.items():
    print(f"CATEGORY {k}: {len(v)} functions, {sum(funcs[n][1] for n in v)} instructions", flush=True)
cands = sorted(leaf, key=lambda n: -funcs[n][1])
if top:
    cands = cands[:top]
done = {}  # function -> (spec, module)
thm_of = {}  # function -> its theorem (a library one, or the generated Art.Q<j>.safe)
lib = set()
if lib_file:
    # lines: FUNCTION THEOREM MODULE (a hand-proved VerifiedImg theorem of the same image)
    for l in open(lib_file):
        if l.strip() and not l.startswith("#"):
            fn, thm, mod = l.split()
            if fn in funcs:
                done[fn] = ("library", mod); thm_of[fn] = thm; lib.add(fn)
cands = cands + [n for n in lib if n not in cands]
def disjoint(ls):
    ls = sorted(ls)
    return all(ls[i][1] <= ls[i + 1][0] for i in range(len(ls) - 1))


# Loops that are not nested, each with one back edge to its head.
def nest(ls):
    """The loops as a forest of depth at most 2: {loop: parent or None}; None when two loops overlap
    without one containing the other, or loops nest deeper."""
    par = {}
    for a in ls:
        outs = [b for b in ls if b != a and b[0] <= a[0] and a[1] <= b[1]]
        for b in ls:
            if b != a and not (a[1] <= b[0] or b[1] <= a[0]) and not (b[0] <= a[0] and a[1] <= b[1]) \
                    and not (a[0] <= b[0] and b[1] <= a[1]):
                return None
        if len(outs) > 1:
            return None
        par[a] = outs[0] if outs else None
    if any(par[p] is not None for p in par.values() if p is not None):
        return None
    return par


def loop_ok(n):
    # one back edge to each head; loops disjoint or nested two deep (round 5: nested loops)
    return (nest(loops[n]) is not None and len(back_edges(n)) == len(loops[n])
            and sorted(b[0] for b in back_edges(n)) == sorted(st for st, _ in loops[n]))


loopers = [n for n in funcs if n in doms and funcs[n][2] and loop_ok(n)
           and (not deps[n] or with_calls)] if with_loops else []
# With --calls, a caller (with or without loops) whose callees are all attempted, to a fixed point:
# its callees' theorems come first (`calls [...]`), its loops get their back edges' invariants.
if with_calls:
    have = set(cands) | {n for n in loopers if not deps[n]} | lib
    more = list(caller) + [n for n in loopers if deps[n]]
    grew = True
    while grew:
        grew = False
        for n in more:
            if n not in have and all(d in have for d in deps[n] if d):
                have.add(n)
                grew = True
    cands = cands + [n for n in more if n in have and n not in cands]
    loopers = [n for n in loopers if n in have]
cands = cands + [n for n in loopers if n not in cands]
# Why each function is or is not attempted, for `nocompiler prove`'s report (WORKDIR/selection.tsv).
with open(os.path.join(work, "selection.tsv"), "w") as f:
    for n in sorted(funcs):
        if n in cands:
            why = "attempted"
        elif n not in doms:
            why = "not attempted: no _dom (a callee failed the profile check)"
        elif funcs[n][2] and with_loops and loop_ok(n) and deps[n]:
            why = "not attempted: a callee is not one the generator attempts"
        elif funcs[n][2]:
            why = ("not attempted: loops nested, or a loop with more than one back edge to its head" if with_loops
                   else "not attempted: loops (run without --loops)")
        elif deps[n]:
            why = ("not attempted: a callee is not one the generator attempts" if with_calls
                   else "not attempted: calls (run without --calls)")
        else:
            why = "not attempted: not among the N largest leaves"
        f.write(f"{n}\t{funcs[n][1]}\t{why}\n")
ids = {n: k for k, n in enumerate(sorted(cands))}
# Callees first: a callee's `_dom` is inside its caller's, so it has fewer ranges.
if only is not None:
    # Only these functions and their callees (a caller needs its callees' theorems).
    keep = set(only) | {d for n in only if n in deps for d in deps[n] if d}
    cands = [n for n in cands if n in keep]
order = sorted(cands, key=lambda n: len(deps[n]))
ro = "[seg_rodata.region]" if rodata else "[]"
# "Anywhere" lists .rodata too, so that a callee proved with `safe` (reads .rodata) is within it by name.
anywhere = "[seg_rodata.region, ⟨0, 2 ^ 65⟩]" if rodata else "[⟨0, 2 ^ 65⟩]"


def own_frame(n):
    """The function's frame: its export's, or for one without a tree (a frame set up on some paths
    only, not by an entry prologue) the sum of its `addi sp, sp, -k` (an upper bound)."""
    if n in frame or n not in notree or n not in chunkk:
        return frame.get(n, 0)
    entry, ln = funcs[n][0], funcs[n][1]
    off, cl, bits = chunkd[chunkk[n]]
    base = text + 4 * off
    tot = 0
    for pc in range(entry, entry + 4 * ln, 4):
        k = (pc - base) // 4
        if not 0 <= k < cl:
            continue
        w = (bits >> (32 * k)) & 0xffffffff
        if w & 0x7fff == 0x0113 and (w >> 15) & 0x1f == 2:
            imm = w >> 20
            if imm & 0x800:
                tot += 0x1000 - imm
    return tot


def stack(n, memo={}):
    if n not in memo:
        memo[n] = own_frame(n) + max([stack(d) for d in deps[n] if d] or [0])
    return memo[n]





rows_lock = threading.Lock()


def tsv(n, spec, rc, err):
    """Every row also in WORKDIR/rows.tsv, with the function's full name (for --only lists)."""
    with rows_lock, open(os.path.join(work, "rows.tsv"), "a") as f:
        f.write(f"{n}\t{funcs[n][1]}\t{spec}\t{rc}\t{(err or '').replace(chr(9), ' ')[:200]}\n")


def has_ecall(n):
    if n not in chunkk:
        return False
    entry, ln = funcs[n][0], funcs[n][1]
    off, cl, bits = chunkd[chunkk[n]]
    base = text + 4 * off
    return any((bits >> (32 * ((entry + 4 * i - base) // 4))) & 0xffffffff == 0x73 for i in range(ln))


# The process-level route (lead 16:14): a function making a syscall (other than the machine's read/write/exit, which
# the process route covers too) or calling one that is proved at the process level: VerifiedProc with the `safe` rung
# as `specSafe.toP` (its permission within the kernel's; the anywhere rungs would be vacuous there), nocompiler_auto_p.
proc = set()


def prove(n):
    j = ids[n]
    start = max([specs.index(done[d][0]) for d in deps[n] if d in done and done[d][0] in specs] or [0])
    if any(d not in done for d in deps[n]):
        print(f"{n[-40:]:40} {funcs[n][1]:4} instr  -         rc -1  ERROR a callee is not proved", flush=True)
        tsv(n, "-", -1, "a callee is not proved")
        return (n, funcs[n][1], -1, 0.0, 0.0, "a callee is not proved", None)
    if n in loopers:
        # One clause per loop, in address order; a later loop has a lower rank, so going from one loop
        # to the next decreases rank * 2^64 + the loop's own measure (which is below 2^64).
        bes = sorted(back_edges(n))
        L = len(bes)

        def clauses(t):
            # t: the measure's direction (t % 2), and (t // 2 = 1) invariant True instead of the back
            # edge's condition (false on entry of a rotated loop whose entry path does not test it).
            o, plain = t % 2, t // 2
            out = ""
            ms, invs = {}, {}
            for i, (st, r1, r2, f3) in enumerate(bes):
                # The zero register as the literal (`u.reg 0` is not rewritten to 0 by the tactic, so an
                # invariant `a2 ≠ u.reg 0` would not give a count-down's measure its `a2 ≠ 0`).
                R1 = "0#64" if r1 == 0 else f"u.reg {r1}"
                R2 = "0#64" if r2 == 0 else f"u.reg {r2}"
                if r1 == 0 or r2 == 0:
                    v = R2 if r1 == 0 else R1
                    m = f"({v}).toNat" if o == 0 else f"(0#64 - {v}).toNat"
                else:
                    m = f"({R2} - {R1}).toNat" if o == 0 else f"({R1} - {R2}).toNat"
                # The back edge's own condition holds at the head (the branch is the loop's last step).
                inv = {1: f"{R1} ≠ {R2}", 6: f"({R1}).toNat < ({R2}).toNat",
                       7: f"({R2}).toNat ≤ ({R1}).toNat"}.get(f3, "True")
                if plain:
                    inv = "True"
                ms[st], invs[st] = m, inv
            # Lexicographic over the nesting (two deep): a top-level loop of rank r (later loops lower)
            # weighs r * 2^200; an outer loop with K inner loops has, with W = K * 2^64 + 1, measure
            # M * W + K * 2^64 at its head and M * W + (K - 1 - j) * 2^64 + m_j at its j-th inner head
            # (entering, iterating and leaving an inner loop, and the next outer turn, all decrease).
            par = nest(loops[n]) or {}
            head = {lp: lp[0] for lp in loops[n]}
            tops = sorted(lp for lp in loops[n] if par.get(lp) is None)
            for ti, top in enumerate(tops):
                pre = f"{len(tops) - 1 - ti} * 2 ^ 200 + " if len(tops) > 1 else ""
                kids = sorted(lp for lp in loops[n] if par.get(lp) == top)
                K = len(kids)
                M = ms.get(head[top], "0")
                if K == 0:
                    out += f"\n    loop_inv 0x{head[top]:x}#64 (fun u => {invs.get(head[top], 'True')}) measure (fun u => {pre}{M})"
                    continue
                W = K * 2 ** 64 + 1
                out += (f"\n    loop_inv 0x{head[top]:x}#64 (fun u => {invs.get(head[top], 'True')}) "
                        f"measure (fun u => {pre}{M} * {W} + {K} * 2 ^ 64)")
                for j, kid in enumerate(kids):
                    inv = f"({invs.get(head[kid], 'True')}) ∧ ({invs.get(head[top], 'True')})"
                    out += (f"\n    loop_inv 0x{head[kid]:x}#64 (fun u => {inv}) "
                            f"measure (fun u => {pre}{M} * {W} + {K - 1 - j} * 2 ^ 64 + {ms.get(head[kid], '0')})")
            return out
        measures = [0, 1, 2, 3]
        tries = [(sp, m) for sp in specs[start:] for m in measures]
    else:
        tries = [(sp, None) for sp in specs[start:]]
    prev_out = ""
    is_proc = has_ecall(n) or any(d in proc for d in deps[n])
    if is_proc:
        proc.add(n)
        tries = [(sp, m) for (sp, m) in tries if sp == "safe"]
    # A measure whose attempt left no permission goal (no `perm_` case): a larger specification cannot help it.
    no_perm = set()
    for spec, meas in tries:
        if meas in no_perm:
            continue
        pairs = []
        if spec == "rodata" and not rodata:
            continue
        if spec == "offframe":
            # stores at `s.reg p + s.reg n` (the entry state's argument registers) the previous attempt left
            flat = re.sub(r"\s+", " ", prev_out)
            for blk in re.findall(r"writeLE (.{0,200})", flat):
                m = re.match(r".*?\(s\.reg (\d+) \+ s\.reg (\d+)", blk)
                if m and m.group(1) != m.group(2) and all(10 <= int(x) <= 17 for x in m.groups()):
                    pairs.append((int(m.group(1)), int(m.group(2))))
            pairs = sorted(set(pairs))
            if not pairs:
                continue
        li = clauses(meas) if meas is not None else ""
        mod = f"Q{j}_{spec}" + (f"_m{meas}" if meas is not None else "")
        path = os.path.join(work, mod + ".lean")
        # everywhere but .rodata: below it and above it
        notro = ("[⟨0, seg_rodata.base.toNat⟩, ⟨seg_rodata.base + BitVec.ofNat 64 seg_rodata.bytes.size, "
                 "2 ^ 64 - (seg_rodata.base.toNat + seg_rodata.bytes.size)⟩]")
        reads = {"safe": ro, "anyread": anywhere, "anymem": anywhere, "alignargs": anywhere, "offframe": anywhere,
                 "rodata": anywhere}[spec]
        writes = {"safe": "[]", "anyread": "[]", "anymem": anywhere, "alignargs": anywhere, "offframe": anywhere,
                  "rodata": notro}[spec]
        # a0-a7 and tp (libc's thread pointer, which the start-up sets 8-aligned: errno is at a fixed offset from it)
        conj = [f"aligned (s.reg {r}) 8" for r in list(range(10, 18)) + [4]] if spec in ("alignargs", "offframe", "rodata") else []
        names = [f"ha{r}" for r in list(range(10, 18)) + [4]] if conj else []
        if spec == "rodata":
            conj.append("seg_rodata.Loaded s.mem")
            names.append("hro")
        st = stack(n)
        for (pr, nr) in pairs:
            conj += [f"(s.reg {pr}).toNat + (s.reg {nr}).toNat ≤ 2 ^ 64",
                     f"Region.Disjoint ⟨s.reg {pr}, (s.reg {nr}).toNat⟩ ⟨s.reg 2 - {st}#64, {st}⟩"]
            names += [f"hnw{pr}_{nr}", f"hoff{pr}_{nr}"]
        pre = ("fun _ s => " + " ∧ ".join(conj)) if conj else "fun _ _ => True"
        pat = ("⟨" + ", ".join(names) + "⟩") if names else "_"
        imports = "".join(f"import {done[d][1]}\n" for d in deps[n])
        # (The tactic gives the image's segments to the permission check at a call itself.)
        facts = ""
        def cref(d):
            t = thm_of.get(d, f"Art.Q{ids[d]}.safe")
            # a machine-level callee in a process-level caller: its theorem over the process step
            return f"(NoCompiler.Linux.VerifiedImg.toProc {t})" if is_proc and d not in proc else t
        calls = (" calls [" + ", ".join(cref(d) for d in deps[n]) + "]") if deps[n] else ""
        if is_proc:
            thm = f"""theorem safe : NoCompiler.Linux.VerifiedProc code {n}_dom {n}_entry specSafe.toP := by
  apply NoCompiler.Linux.VerifiedProc.of_execP
  rintro _ s k he ⟨{pat}, nocompiler_hle⟩
  nocompiler_auto_p {n}_func s he [nocompiler_hle]{calls}{li}"""
        else:
            thm = f"""theorem safe : VerifiedImg code {n}_dom {n}_entry specSafe := by
  rintro _ s he {pat}
  nocompiler_auto {n}_func s he{facts}{calls}{li}"""
        open(path, "w").write(f"""import {img_mod}
import NoCompiler.Auto
{"import NoCompiler.Linux.AutoP" + chr(10) if is_proc else ""}{imports}namespace Art.Q{j}
open NoCompiler {img_ns}

def specSafe : Spec Unit where
  pre := {pre}
  post := fun _ _ _ => True
  reads := fun _ _ => {reads}
  writes := fun _ _ => {writes}
  stack := {stack(n)}

set_option nocompiler.auto.closeBV true in
-- The join lemmas of a large function without a tree run past the default 200000 (the run's
-- wall-clock timeout still bounds it).
set_option maxHeartbeats 2000000 in
{thm}

end Art.Q{j}
""")
        cmd = ["systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=6G", "-p", "MemorySwapMax=0",
               f"--setenv=PATH={os.environ['PATH']}", f"--setenv=LEAN_PATH={lean_path}", "timeout", "300",
               "/usr/bin/time", "-f", "MAXRSS %M", "lean", "-Dprofiler=true", "--root=" + work,
               "-o", os.path.join(work, mod + ".olean"), path]
        r = subprocess.run(cmd, cwd=lean_dir, capture_output=True, text=True)
        out = r.stdout + r.stderr
        open(path[:-5] + ".out", "w").write(out)
        prev_out = out
        prof = {}
        for m in re.finditer(r"^\s+(.+?) ([\d.]+)(ns|us|μs|ms|s)$", out.split("cumulative profiling times:")[-1],
                             re.M):
            prof[m.group(1)] = float(m.group(2)) * unit[m.group(3)]
        total = sum(v for k, v in prof.items() if k not in ("import", "initialization"))
        kern = prof.get("type checking", 0.0)
        rss = int((re.findall(r"MAXRSS (\d+)", out) or ["0"])[-1])
        err = next((l for l in out.splitlines() if "error" in l), None) if r.returncode else None
        ln = funcs[n][1]
        print(f"{n[-40:]:40s} {ln:4d} instr  {spec:9s} rc {r.returncode}  total {total:8.0f} ms "
              f"{total / ln:7.2f} ms/instr  kernel {kern / ln:6.2f} ms/instr  peak {rss // 1024} MB"
              + (f"  ERROR {err[:110]}" if err else ""), flush=True)
        tsv(n, spec, r.returncode, err)
        if r.returncode == 0:
            if n not in lib:  # a library function's callers keep its (stronger) library theorem
                done[n] = (spec, mod)
            # Where the theorem is, for `nocompiler prove`'s report.
            with rows_lock, open(os.path.join(work, "proved.tsv"), "a") as f:
                f.write(f"{n}\t{spec}\t{mod}.lean\tArt.Q{j}.safe\n")
            return (n, ln, 0, total, kern, None, spec)
        if r.returncode != 0 and re.search(r"^⊢ False$", out, re.M):
            # explore returned none (an indirect jump, e.g. a jump table, or an instruction it does not
            # cover): no specification changes that.
            tsv(n, spec, r.returncode, "explore stopped: an indirect jump or an instruction it does not cover")
            return (n, ln, r.returncode, total, kern, "explore stopped: an indirect jump or an instruction it does not cover", spec)
        if r.returncode == 1 and meas is not None and not re.search(r"^case perm_", out, re.M):
            no_perm.add(meas)
        if r.returncode == 124:
            # A timeout is the run's size (paths), not the specification: the next one would time out too.
            return (n, ln, 124, total, kern, "timeout (300 s)", spec)
        if (spec, meas) == tries[-1]:
            return (n, ln, r.returncode, total, kern, err, spec)
    return (n, funcs[n][1], -1, 0.0, 0.0, "no specification left", None)


# Levels of the call order: a function runs once its callees are done.
rows = []
pending = list(order)
while pending:
    level = [n for n in pending if all(d not in pending for d in deps[n])]
    if not level:
        # The rest call each other in a cycle (recursion): no callee theorem comes first.
        rows += [(n, funcs[n][1], -2, 0.0, 0.0, "a cycle of calls (recursion): no callee theorem first", None)
                 for n in pending]
        break
    pending = [n for n in pending if n not in level]
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
        rows += list(ex.map(prove, level))

checked = set(re.findall(r"\(as `(\w+)_checked`\)", src))
print(f"FUNCTIONS {len(funcs)}, of which {len(checked)} passed the profile check (L1+), "
      f"{len(funcs) - len(checked)} did not (exported since 338a943 with entry, region and _dom only)")
ok_c = [r for r in rows if r[2] == 0 and r[0] in checked]
print(f"PROVED among the L1+ functions: {len(ok_c)} of {len(checked)} ({sum(r[1] for r in ok_c)} of "
      f"{sum(funcs[n][1] for n in checked)} instructions)")
ok_u = [r for r in rows if r[2] == 0 and r[0] not in checked]
print(f"PROVED among the others: {len(ok_u)} of {len(funcs) - len(checked)} ({sum(r[1] for r in ok_u)} instructions)")
ok = [r for r in rows if r[2] == 0]
ti = sum(r[1] for r in ok)
tt = sum(r[3] for r in ok)
tk = sum(r[4] for r in ok)
print(f"PROVED {len(ok)} of {len(rows)}: {ti} instr, total {tt:.0f} ms, {tt / max(ti, 1):.2f} ms/instr, "
      f"kernel {tk / max(ti, 1):.2f} ms/instr")
for sp in specs:
    k = [r for r in ok if r[6] == sp]
    print(f"  by spec {sp}: {len(k)} functions, {sum(r[1] for r in k)} instructions")
reasons = {}
for r in rows:
    if r[2] != 0:
        e = r[5] or f"rc {r[2]}"
        key = re.sub(r"^.*?error: ", "", e)[:70]
        reasons.setdefault(key, []).append(r[0])
for k, v in sorted(reasons.items(), key=lambda x: -len(x[1])):
    nc = sum(1 for n in v if n in checked)
    print(f"  FAILED {len(v)} ({nc} L1+): {k}  (e.g. {v[0][-40:]})")

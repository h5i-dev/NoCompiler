# Usage: python3 -I Prove.py WORKDIR [N] [--specs safe,anyread,anymem,alignargs] [--jobs J] [--calls] [--loops]
# The whole nocompiler_auto proof (explore and the goals after it) on a binary's functions, one module
# per function, each capped (6 GB, no swap, 900 s); cost = every profile category but import and
# initialization, per instruction. WORKDIR is Art.py's (Art.lean, ArtImg.olean).
#
# Which functions: those a safety specification can take, the N largest (default 20; 0 for all):
#   a `_dom` (every callee passed the profile check), no loops (an invariant and a measure would be the
#   function's own), and, without --calls, no callees. With --calls, also functions whose callees (every
#   function in their `_dom`) are such functions: callees first (a callee's `_dom` is inside its
#   caller's), each caller with `calls [...]` of its callees' theorems; its stack bound is its frame plus
#   its callees' largest bound, so that a callee's stack lies in its caller's.
# With --loops, also the functions with exactly one loop (no callees): the invariant is `True` (the
# frame is added by the tactic) and the measure is tried from the loop's back edge, a branch to its
# head comparing rs1 and rs2: (rs2 - rs1).toNat, (rs1 - rs2).toNat. (Several loops need a measure
# that also decreases from one loop's head to the next; not tried.)
# Specifications, tried in order until one proves the function (--specs; a caller starts at its
# callees' strictest, since a callee's permission must lie in its caller's):
#   safe       any entry; returns, preserving the ABI; reads only .rodata; writes only its frame;
#   anyread    the same, but reads anywhere (reads through argument pointers);
#   anymem     the same, but reads and writes anywhere (writes through argument pointers);
#   alignargs  anymem, with a0-a7 8-aligned as preconditions (an argument pointer aligned to its type;
#              stronger than a byte pointer needs, so a proof that needs it says so).
# "Anywhere" is the region ⟨0, 2^65⟩, which covers every access. Every specification still requires
# alignment, termination and the ABI (the callee-saved registers, sp, the return).
import concurrent.futures, os, re, subprocess, sys

work = sys.argv[1]
specs = ["safe"]
jobs = 1
with_calls = "--calls" in sys.argv
with_loops = "--loops" in sys.argv
rest = []
i = 2
while i < len(sys.argv):
    a = sys.argv[i]
    if a == "--specs":
        specs = sys.argv[i + 1].split(","); i += 2; continue
    if a == "--jobs":
        jobs = int(sys.argv[i + 1]); i += 2; continue
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
                    out.append((st, (w >> 15) & 31, (w >> 20) & 31))
    return out
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
if with_calls:
    ok_callers = [n for n in caller if all(d in leaf or d in caller for d in deps[n] if d)]
    cands = cands + ok_callers
loopers = [n for n in funcs if n in doms and funcs[n][2] and not deps[n] and len(loops[n]) == 1
           and len(back_edges(n)) == 1] if with_loops else []
cands = cands + loopers
ids = {n: k for k, n in enumerate(sorted(cands))}
# Callees first: a callee's `_dom` is inside its caller's, so it has fewer ranges.
order = sorted(cands, key=lambda n: len(deps[n]))
ro = "[seg_rodata.region]" if rodata else "[]"
# "Anywhere" lists .rodata too, so that a callee proved with `safe` (reads .rodata) is within it by name.
anywhere = "[seg_rodata.region, ⟨0, 2 ^ 65⟩]" if rodata else "[⟨0, 2 ^ 65⟩]"


def stack(n, memo={}):
    if n not in memo:
        memo[n] = frame.get(n, 0) + max([stack(d) for d in deps[n] if d] or [0])
    return memo[n]


done = {}  # function -> (spec, module)


def prove(n):
    j = ids[n]
    start = max([specs.index(done[d][0]) for d in deps[n] if d in done] or [0])
    if any(d not in done for d in deps[n]):
        return (n, funcs[n][1], -1, 0.0, 0.0, "a callee is not proved", None)
    if n in loopers:
        st, r1, r2 = back_edges(n)[0]
        measures = [f"(u.reg {r2} - u.reg {r1}).toNat", f"(u.reg {r1} - u.reg {r2}).toNat"]
        tries = [(sp, m) for sp in specs[start:] for m in measures]
    else:
        tries = [(sp, None) for sp in specs[start:]]
    for spec, meas in tries:
        li = (f"\n    loop_inv 0x{st:x}#64 (fun u => True) measure (fun u => {meas})" if meas else "")
        mod = f"Q{j}_{spec}" + ("_m" + str(measures.index(meas)) if meas else "")
        path = os.path.join(work, mod + ".lean")
        reads = {"safe": ro, "anyread": anywhere, "anymem": anywhere, "alignargs": anywhere}[spec]
        writes = {"safe": "[]", "anyread": "[]", "anymem": anywhere, "alignargs": anywhere}[spec]
        pre = ("fun _ s => " + " ∧ ".join(f"aligned (s.reg {r}) 8" for r in range(10, 18))
               if spec == "alignargs" else "fun _ _ => True")
        pat = ("⟨" + ", ".join(f"ha{r}" for r in range(10, 18)) + "⟩") if spec == "alignargs" else "_"
        imports = "".join(f"import {done[d][1]}\n" for d in deps[n])
        # (The tactic gives the image's segments to the permission check at a call itself.)
        facts = ""
        calls = (" calls [" + ", ".join(f"Art.Q{ids[d]}.safe" for d in deps[n]) + "]") if deps[n] else ""
        open(path, "w").write(f"""import ArtImg
import NoCompiler.Auto
{imports}namespace Art.Q{j}
open NoCompiler Art.T

def specSafe : Spec Unit where
  pre := {pre}
  post := fun _ _ _ => True
  reads := fun _ _ => {reads}
  writes := fun _ _ => {writes}
  stack := {stack(n)}

theorem safe : VerifiedImg code {n}_dom {n}_entry specSafe := by
  rintro _ s he {pat}
  nocompiler_auto {n}_func s he{facts}{calls}{li}

end Art.Q{j}
""")
        cmd = ["systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=6G", "-p", "MemorySwapMax=0",
               f"--setenv=PATH={os.environ['PATH']}", f"--setenv=LEAN_PATH={lean_path}", "timeout", "900",
               "/usr/bin/time", "-f", "MAXRSS %M", "lean", "-Dprofiler=true", "--root=" + work,
               "-o", os.path.join(work, mod + ".olean"), path]
        r = subprocess.run(cmd, cwd=lean_dir, capture_output=True, text=True)
        out = r.stdout + r.stderr
        open(path[:-5] + ".out", "w").write(out)
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
        if r.returncode == 0:
            done[n] = (spec, mod)
            return (n, ln, 0, total, kern, None, spec)
        if (spec, meas) == tries[-1]:
            return (n, ln, r.returncode, total, kern, err, spec)
    return (n, funcs[n][1], -1, 0.0, 0.0, "no specification left", None)


# Levels of the call order: a function runs once its callees are done.
rows = []
pending = list(order)
while pending:
    level = [n for n in pending if all(d not in pending for d in deps[n])]
    pending = [n for n in pending if n not in level]
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
        rows += list(ex.map(prove, level))

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
    print(f"  FAILED {len(v)}: {k}  (e.g. {v[0][-40:]})")

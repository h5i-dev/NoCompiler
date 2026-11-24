#!/usr/bin/env python3
"""Certificates for the kernel check (docs/typed/export.md "Certificates").

Input: a generated module with the record and `def code` (the linked .text), as
`corpus.py --link --keep DIR` writes it. Each function is evaluated point by point with every
type in `CertMode.log` (compiled evaluation, `lake lean`): the search's certificates are printed
as `CERT <goal> ::: <certs>`. The output module is the input's declarations plus, per function,
`fnc_<f>`: `fn_<f>` with each point's certificates as a `CertMode.table` (no search in the
kernel), and the theorem `chk_<f> : fnc_<f>.check code = true` by `decide +kernel`. With
--split the theorem is assembled from one kernel computation per point (`Fn.check_of_parts`,
`rangeAll_succ`), for functions too big for one declaration.

The certificates are untrusted hints: the kernel re-checks each one (`Query.check`), and a
missing or wrong one only makes the check fail.

Usage: lean/scripts/certgen.py IN.lean OUT.lean [--split] [--only FN]
"""
import argparse
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def base_of(text):
    """The declarations of a generated module: everything before its first #eval."""
    i = text.find("\n#eval")
    return text if i < 0 else text[: i + 1]


def run_lean(path, timeout):
    pre = []
    mem = os.environ.get("CERTGEN_MEM")
    if mem:
        pre = ["systemd-run", "--user", "--scope", "--quiet", "-p", f"MemoryMax={mem}",
               "-p", "MemorySwapMax=0"]
    return subprocess.run([*pre, "lake", "lean", path], cwd=os.path.join(ROOT, "lean"),
                          capture_output=True, text=True, timeout=timeout)


ENTRY = 999999


def log_module(base, fns):
    """Every type of function i in `CertMode.log (i·10^6 + k)` for its point k (the entry edge:
    `i·10^6 + 999999`), so each printed certificate names its point; one #eval forces them all."""
    out = [base]
    for i, f in enumerate(fns):
        t = i * 1000000
        out.append(f"""
def fnlog_{f} : Fn :=
  {{ fn_{f} with
    types := fn_{f}.types.map (fun p => (p.1, {{ p.2 with certs := .log ({t} + p.1) }})),
    entryCerts := .log {t + ENTRY} }}

-- behind a runtime value (z = 0), so the compiler cannot hoist a check into a closed term
-- evaluated outside the #eval (its certificates would not be printed here)
#eval show IO Unit from do
  let t ← IO.monoMsNow
  let z := t - t
  IO.println s!"DONE {f} {{fnlog_{f}.structOk && fnlog_{f}.edge none fnlog_{f}.initTy z}} {{(List.range fnlog_{f}.size).map (fun k => fnlog_{f}.instr code (k + z))}}"
""")
    return "\n".join(out)


def parse_log(output, fns):
    """{(fn, point): [(goal, certs)]} and {fn: DONE line} from the log run's output."""
    certs, done = {}, {}
    splits = SPLITS
    for line in output.splitlines():
        if line.startswith("CERT "):
            tag, n, rest = line[5:].split(" ", 2)
            if " ::: " not in rest or not rest.rstrip().endswith("]"):
                continue  # a broken line: that query just gets no certificate
            parts = rest.split(" ::: ")
            if len(parts) != 3:
                continue
            g, keep, cs = parts
            # the entry: goal, its query's number of hypotheses, the hypotheses kept, certificates
            g = f"{g}, {n}, {keep}"
            i, k = divmod(int(tag), 1000000)
            key = (fns[i], "entry" if k == ENTRY else str(k))
            lst = certs.setdefault(key, [])
            if (g, cs) not in lst:
                lst.append((g, cs))
        elif line.startswith("SPLIT ") or line.startswith("ENT "):
            kind, tag, g = line.split(" ", 2)
            i, k = divmod(int(tag), 1000000)
            key = (fns[i], "entry" if k == ENTRY else str(k))
            sp = (splits if kind == "SPLIT" else OKS).setdefault(key, [])
            if g not in sp:
                sp.append(g)
        elif line.startswith("DONE "):
            _, f, rest = line.split(" ", 2)
            done[f] = rest
    return certs, done


SPLITS = {}  # (fn, point) -> goals the case split proved (parse_log fills it)
OKS = {}  # (fn, point) -> goals `STy.ent` proved


def short(g):
    """A goal's repr with the namespace the module opens dropped (half the text to elaborate)."""
    return g.replace("NoCompiler.Typed.", "")


def table(entries, key=None):
    sp = SPLITS.get(key, []) if key else []
    ok = OKS.get(key, []) if key else []
    ts = "[" + ", ".join(f"({short(g)}, {cs})" for g, cs in entries) + "]"
    return f".table {ts} [{', '.join(map(short, sp))}] [{', '.join(map(short, ok))}]"


def out_module(base, fns, sizes, certs, split):
    out = [base]
    for f in fns:
        pts = sorted({k for (g, k) in list(certs) + list(SPLITS) + list(OKS)
                      if g == f and k != "entry"},
                     key=int)
        # one declaration per point (a single literal of all of them is too big to elaborate);
        # a point without one gets an empty table (no search in the kernel either)
        for k in pts:
            out.append(f"""set_option maxHeartbeats 0 in
def certs_{f}_{k} : CertMode := {table(certs.get((f, k), []), (f, k))}
""")
        rows = ", ".join(f"({k}, certs_{f}_{k})" for k in pts)
        out.append(f"""
/-- `{f}`'s certificates per point (untrusted hints, re-checked by `Query.check`). -/
def certs_{f} : List (Nat × CertMode) := [{rows}]

def fnc_{f} : Fn :=
  {{ fn_{f} with
    types := fn_{f}.types.map (fun p => (p.1, {{ p.2 with certs := (certs_{f}.lookup p.1).getD (.table []) }})),
    entryCerts := {table(certs.get((f, "entry"), []), (f, "entry"))} }}
""")
        if not split:
            out.append(f"""set_option maxRecDepth 100000 in
theorem chk_{f} : fnc_{f}.check code = true := by decide +kernel

#print axioms chk_{f}
""")
            continue
        n = sizes[f]
        out.append(f"""set_option maxRecDepth 100000 in
theorem chk_{f}_s : (fnc_{f}.structOk && fnc_{f}.edge none fnc_{f}.initTy 0) = true := by
  decide +kernel
""")
        for k in range(n):
            out.append(f"""set_option maxRecDepth 100000 in
theorem chk_{f}_{k} : fnc_{f}.instr code {k} = true := by decide +kernel
""")
        term = f"(rangeAll_zero (fnc_{f}.instr code))"
        for k in range(n):
            term = f"(rangeAll_succ {term} chk_{f}_{k})"
        out.append(f"""set_option maxRecDepth 100000 in
theorem chk_{f} : fnc_{f}.check code = true :=
  Fn.check_of_parts_n _ (n := {n}) rfl chk_{f}_s {term}

#print axioms chk_{f}
""")
    return "\n".join(out)


def prog_theorems(base):
    """Theorem D for the module's `prog` (callee-first, as the export lists it), with each
    function's certificate-carrying version `fnc_<f>` (same signature and code, so the same
    meaning) and its kernel theorem `chk_<f>`."""
    m = re.search(r"^def prog : List Fn := \[(.*)\]", base, re.M)
    if not m:
        return ""
    names = [n.strip()[len("fn_"):] for n in m.group(1).split(",") if n.strip()]
    progc = ", ".join(f"fnc_{n}" for n in names)
    chks = ", ".join(f"chk_{n}" for n in names)
    return f"""
/-- The program with each function's certificate tables (same signatures and code). -/
def progc : List Fn := [{progc}]

set_option maxRecDepth 100000 in
/-- Theorem D's check, by the kernel, from the per-function kernel theorems. -/
theorem prog_checked : Prog.check code [] progc = true := by
  simp only [progc, Prog.check, {chks}, Bool.true_and]
  decide +kernel

/-- Every function of the program meets its signature (⟦σ⟧, total), for every meaning of tokens. -/
theorem prog_meets (T : TokEnv) :
    ∀ e ∈ Prog.env [] progc, Meets code e.2.2 e.1 T e.2.1 :=
  Prog.check_sound_closed prog_checked

#print axioms prog_meets
"""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("inp")
    ap.add_argument("out")
    ap.add_argument("--split", action="store_true")
    ap.add_argument("--only")
    ap.add_argument("--reuse", help="a module certgen wrote: keep its tables, rewrite only the theorems")
    ap.add_argument("--prog", action="store_true",
                    help="also theorem D for the module's `prog` (progc, prog_checked, prog_meets)")
    ap.add_argument("--timeout", type=int, default=int(os.environ.get("LEAN_TIMEOUT", "900")))
    a = ap.parse_args()
    text = open(a.inp, encoding="utf-8").read()
    base = base_of(text)
    if not re.search(r"^def code : Code", base, re.M):
        sys.exit(f"{a.inp}: no `def code` (generate it with corpus.py --link --keep)")
    fns = re.findall(r"^def fn_(\w+) : Fn where", base, re.M)
    if a.only:
        fns = [f for f in fns if f == a.only]
    sizes = {}
    for f in fns:
        m = re.search(rf"^def fn_{f} : Fn where.*?^  size := (\d+)", base, re.M | re.S)
        sizes[f] = int(m.group(1)) if m else 0
    if a.reuse:
        prev = open(a.reuse, encoding="utf-8").read()
        cut = re.search(r"^set_option maxRecDepth 100000 in\ntheorem chk_", prev, re.M)
        head = prev[: cut.start()] if cut else prev
        thms = out_module("", fns, sizes, {}, a.split)
        thms = "\n".join(t for t in re.split(r"(?=^set_option maxRecDepth)", thms, flags=re.M)
                         if t.startswith("set_option"))
        open(a.out, "w", encoding="utf-8").write(head + thms)
        print(f"{a.out}: theorems rewritten ({'split' if a.split else 'whole'})")
        return
    log_path = os.path.splitext(a.out)[0] + ".log.lean"
    open(log_path, "w", encoding="utf-8").write(log_module(base, fns))
    r = run_lean(log_path, a.timeout)
    errs = [l for l in (r.stdout + r.stderr).splitlines() if ": error" in l]
    if errs:
        # a log module that does not elaborate records nothing reliable (a structure update that
        # fails to parse leaves its types in .search, so their certificates are not printed)
        sys.exit(f"{log_path}: {errs[0][:300]}")
    certs, done = parse_log(r.stdout + "\n" + r.stderr, fns)
    bad = [f for f in fns if f not in done or "false" in done[f]]
    if r.returncode != 0 or bad:
        print(f"log run: rc={r.returncode}, not accepted: {bad}", file=sys.stderr)
        print((r.stdout + r.stderr)[-2000:], file=sys.stderr)
    text = out_module(base, fns, sizes, certs, a.split)
    if a.prog:
        text += prog_theorems(base)
    open(a.out, "w", encoding="utf-8").write(text)
    n = sum(len(v) for v in certs.values())
    print(f"{a.out}: {len(fns)} functions, {len(certs)} points, {n} certificate lists")


if __name__ == "__main__":
    main()

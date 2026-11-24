#!/usr/bin/env python3
"""Kernel-check the Lean checker's verdicts on linked images, one function at a time.

For each typed-assembly file: assemble and link it as corpus.py --link does (ret stubs for
undefined callees), export the record against the linked image (`--image`), and for each
function named (or every function in the record) prove

    theorem chk_<f> : fn_<f>.check code = true := by decide +kernel

in its own Lean process under `systemd-run --scope -p MemoryMax=$KERNEL_MEM` (default 8G),
followed by `#print axioms chk_<f>`. One process at a time; before each, wait until
MemAvailable is at least $KERNEL_MEM (another agent's large Lean job). `Fn.check_sound` turns
each theorem into `Meets` for the function (its callees' signatures assumed). The kernel never
runs native code; a proof counts only with the standard axioms.

Prints one JSON line per function: file, function, result (proved | not-proved |
out-of-memory | timeout | lean-error), seconds, peak KB, axioms, first error line.

Usage: lean/scripts/kernelcheck.py [--checker PATH] [--out FILE.jsonl] FILE.s[:fn,fn] ...
"""
import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, os.path.dirname(__file__))
import corpus  # noqa: E402  (link, section_words, section_addr, CLANG, CFLAGS)

ROOT = corpus.ROOT
MEM = os.environ.get("KERNEL_MEM", "8G")
TIMEOUT = int(os.environ.get("KERNEL_TIMEOUT", "3600"))
LOGDIR = os.environ.get("KERNEL_LOGDIR")
STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def mem_bytes(s):
    return int(s[:-1]) * {"K": 1 << 10, "M": 1 << 20, "G": 1 << 30}[s[-1]] if s[-1] in "KMG" else int(s)


def mem_available():
    for line in open("/proc/meminfo"):
        if line.startswith("MemAvailable:"):
            return int(line.split()[1]) * 1024
    return 0


def module(src, checker, tmp):
    """The exported record on the linked image with `def code`, and the functions in it."""
    stem = re.sub(r"[^A-Za-z0-9_]", "_", os.path.splitext(os.path.basename(src))[0])
    obj = os.path.join(tmp, stem + ".o")
    if subprocess.run([corpus.CLANG, *corpus.CFLAGS, src, "-o", obj], capture_output=True).returncode:
        return None, [], "assemble failed"
    elf, _ = corpus.link(src, obj, tmp, stem)
    if not elf:
        return None, [], "link failed"
    exp = os.path.join(tmp, stem + ".export.lean")
    subprocess.run([checker, "check", src, "--export-lean", exp, "--image", elf], capture_output=True)
    if not os.path.exists(exp):
        return None, [], "no record"
    text = open(exp, encoding="utf-8").read()
    words = corpus.section_words(elf, ".text", tmp)
    base = corpus.section_addr(elf, ".text")
    if words is None or base is None:
        return None, [], "no linked .text"
    ns = re.search(r"^namespace (\S+)", text, re.M).group(1)
    ws = ", ".join(f"0x{w:08x}#32" for w in words)
    head = "\n".join([text, "", f"open {ns}", "open NoCompiler NoCompiler.Typed", "",
                      f"def code : Code := ⟨0x{base:x}#64, #[{ws}]⟩", ""])
    names = re.findall(r"/-- `([^`]+)`: section \S+ offset 0x[0-9a-fA-F]+", text)
    return head, names, None


def prove(head, name, tmp):
    ident = re.sub(r"[^A-Za-z0-9_]", "_", name)
    f = os.path.join(tmp, f"chk_{ident}.lean")
    with open(f, "w", encoding="utf-8") as fh:
        fh.write(head + f"set_option maxRecDepth 100000 in\ntheorem chk_{ident} : fn_{ident}.check code = true := by decide +kernel\n\n#print axioms chk_{ident}\n")
    while mem_available() < mem_bytes(MEM):
        time.sleep(30)
    t0 = time.time()
    unit = f"kernelcheck-{os.getpid()}-{ident}"
    r = subprocess.run(["systemd-run", "--user", "--scope", "--quiet", f"--unit={unit}", "-p", f"MemoryMax={MEM}",
                        "-p", "MemorySwapMax=0", f"--setenv=PATH={os.environ.get('PATH', '')}",
                        "--", "/usr/bin/time", "-f", "PEAK %M", "timeout", str(TIMEOUT),
                        "lake", "env", "lean", f],
                       cwd=os.path.join(ROOT, "lean"), capture_output=True, text=True)
    secs = round(time.time() - t0, 1)
    out = r.stdout + r.stderr
    peak = next((int(m.group(1)) for m in re.finditer(r"PEAK (\d+)", out)), None)
    ax = None
    m = re.search(r"depends on axioms: \[([^\]]*)\]", out)
    if m:
        ax = [a.strip() for a in m.group(1).split(",") if a.strip()]
    elif "does not depend on any axioms" in out:
        ax = []
    err = next((l for l in out.splitlines() if "error" in l), None)
    if LOGDIR:
        with open(os.path.join(LOGDIR, f"{ident}.log"), "w", encoding="utf-8") as fh:
            fh.write(f"returncode {r.returncode}\n{out}")
    # the scope's OOM kill takes /usr/bin/time down too (no PEAK line); the journal says so
    j = subprocess.run(["journalctl", "--user", "-u", f"{unit}.scope", "--no-pager", "-q"],
                       capture_output=True, text=True).stdout
    oom = "oom" in j.lower() or "memory" in j.lower() and "kill" in j.lower()
    if oom or r.returncode in (137, 143) or "Killed" in out or (peak is None and r.returncode == -9):
        res = "out-of-memory"
    elif r.returncode == 124:
        res = "timeout"
    elif err is not None and "heartbeat" in err:
        res = "heartbeats"
    elif err is None and ax is not None and set(ax) <= STANDARD:
        res = "proved"
    elif err is not None and "decide" in err:
        res = "not-proved"
    else:
        res = "lean-error"
    return {"function": name, "result": res, "seconds": secs, "peak_kb": peak, "axioms": ax,
            "returncode": r.returncode, "error": err}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--checker", default=os.path.join(
        os.environ.get("CARGO_TARGET_DIR", os.path.join(ROOT, "target")), "release", "nocompiler-typed"))
    ap.add_argument("--out", help="append the JSON lines here")
    ap.add_argument("files", nargs="+", help="FILE.s or FILE.s:fn1,fn2")
    args = ap.parse_args()
    for spec in args.files:
        src, _, only = spec.partition(":")
        with tempfile.TemporaryDirectory() as tmp:
            head, names, why = module(src, args.checker, tmp)
            if head is None:
                rows = [{"function": "*", "result": why}]
            else:
                rows = [prove(head, n, tmp) for n in names if not only or n in only.split(",")]
        for row in rows:
            row = {"file": os.path.relpath(src, ROOT), **row}
            line = json.dumps(row, ensure_ascii=False)
            print(line, flush=True)
            if args.out:
                with open(args.out, "a", encoding="utf-8") as fh:
                    fh.write(line + "\n")


if __name__ == "__main__":
    main()

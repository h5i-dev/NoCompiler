#!/usr/bin/env python3
"""Run the Lean checker on the shared corpus (tests/typed/corpus/, TWO-AGENTS.md).

For each typed-assembly file: the Rust checker exports its record (`--export-lean`,
docs/typed/export.md); clang assembles the file; the Lean checker (`Fn.check`) runs on
the object's code words with that record. Prints one line per function:

    FILE NAME expected=<#! expect> rust=<accept|reject> lean=<accept|reject|no-record>

and a summary. The Lean verdict here is compiled evaluation (`#eval`), which is enough to
compare verdicts; a theorem needs the kernel (`decide`), as lean/TypedTests/Sum.lean does.

Usage: lean/scripts/corpus.py [--checker PATH] [--keep DIR] [FILES or DIRS ...]
"""
import argparse
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
CLANG = os.environ.get("CLANG", "clang")
OBJCOPY = os.environ.get("OBJCOPY", "llvm-objcopy")
TIMEOUT = int(os.environ.get("LEAN_TIMEOUT", "180"))
CFLAGS = ["--target=riscv64-unknown-elf", "-march=rv64im_zba_zbb", "-mabi=lp64", "-mno-relax", "-c"]


def corpus_files(paths):
    out = []
    for p in paths:
        if os.path.isdir(p):
            for d, _, fs in os.walk(p):
                out += [os.path.join(d, f) for f in fs if f.endswith(".s")]
        else:
            out.append(p)
    return sorted(out)


def expectations(src):
    exp = {}
    for line in open(src, encoding="utf-8"):
        m = re.search(r"#!\s*expect\s+(\S+):\s*(.*)$", line)
        if m:
            exp[m.group(1)] = m.group(2).strip()
    return exp


def section_words(obj, sec, tmp):
    out = os.path.join(tmp, "sec.bin")
    r = subprocess.run([OBJCOPY, "-O", "binary", f"--only-section={sec}", obj, out],
                       capture_output=True)
    if r.returncode != 0 or not os.path.exists(out):
        return None
    b = open(out, "rb").read()
    os.remove(out)
    return [int.from_bytes(b[i:i + 4], "little") for i in range(0, len(b) - len(b) % 4, 4)]


def run_file(src, checker, tmp, keep, why=None):
    stem = re.sub(r"[^A-Za-z0-9_]", "_", os.path.splitext(os.path.basename(src))[0])
    exp_lean = os.path.join(tmp, stem + ".export.lean")
    r = subprocess.run([checker, "check", src, "--export-lean", exp_lean],
                       capture_output=True, text=True)
    rust_out = r.stdout + r.stderr
    rust = {}
    for line in rust_out.splitlines():
        m = re.match(r"(\S+): (checked|assumed|external|rejected|error)", line)
        if m:
            rust[m.group(1)] = "accept" if m.group(2) == "checked" else m.group(2)
    obj = os.path.join(tmp, stem + ".o")
    ok = subprocess.run([CLANG, *CFLAGS, src, "-o", obj], capture_output=True).returncode == 0
    if not os.path.exists(exp_lean):
        return stem, {}, rust, None
    text = open(exp_lean, encoding="utf-8").read()
    fns = re.findall(r"/-- `([^`]+)`: section (\S+) offset (0x[0-9a-fA-F]+)", text)
    ns = re.search(r"^namespace (\S+)", text, re.M).group(1)
    lines = [text, "", f"open {ns}", "open NoCompiler NoCompiler.Typed", ""]
    for name, sec, off in fns:
        ident = re.sub(r"[^A-Za-z0-9_]", "_", name)
        words = section_words(obj, sec, tmp) if ok else None
        if words is None:
            lines.append(f'#eval IO.println "LEAN {name} no-object"')
            continue
        ws = ", ".join(f"0x{w:08x}#32" for w in words)
        lines.append(f"def code_{ident} : Code := ⟨0#64, #[{ws}]⟩")
        lines.append(f'#eval IO.println s!"LEAN {name} {{if fn_{ident}.check code_{ident} then "accept" else "reject"}}"')
        lines.append(f'#eval IO.println s!"WHY {name} struct={{fn_{ident}.structOk}} entry={{fn_{ident}.edge none fn_{ident}.initTy 0}} '
                     f'bad={{((List.range fn_{ident}.size).filter (fun k => !fn_{ident}.instr code_{ident} k)).map (fun k => (k, repr (code_{ident}.instr (fn_{ident}.pcOf k))))}}"')
    gen = os.path.join(keep or tmp, stem + ".lean")
    open(gen, "w", encoding="utf-8").write("\n".join(lines) + "\n")
    try:
        r = subprocess.run(["lake", "env", "lean", gen], cwd=os.path.join(ROOT, "lean"),
                           capture_output=True, text=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired as e:
        out = e.stdout.decode() if isinstance(e.stdout, bytes) else (e.stdout or "")
        r = subprocess.CompletedProcess([], 1, out + "\nTIMEOUT", "")
    lean = {}
    for line in r.stdout.splitlines():
        if line.startswith("WHY ") and why is not None:
            why.append(line)
        m = re.match(r"LEAN (\S+) (\S+)", line)
        if m:
            lean[m.group(1)] = m.group(2)
    if r.returncode != 0 and not lean:
        err = (r.stdout + r.stderr).strip().splitlines()
        lean = {"*": "timeout" if "TIMEOUT" in r.stdout else "lean-error: " + (err[0] if err else "?")}
    return stem, lean, rust, gen


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--checker", default=os.path.join(
        os.environ.get("CARGO_TARGET_DIR", os.path.join(ROOT, "target")), "release", "nocompiler-typed"))
    ap.add_argument("--keep", help="keep the generated Lean files here")
    ap.add_argument("--why", action="store_true", help="say where the Lean checker rejects")
    ap.add_argument("paths", nargs="*", default=[os.path.join(ROOT, "tests", "typed", "corpus")])
    a = ap.parse_args()
    if a.keep:
        os.makedirs(a.keep, exist_ok=True)
    stats = {}
    with tempfile.TemporaryDirectory() as tmp:
        for src in corpus_files(a.paths):
            exp = expectations(src)
            why = []
            stem, lean, rust, _ = run_file(src, a.checker, tmp, a.keep, why)
            names = sorted(set(exp) | set(rust) | set(k for k in lean if k != "*"))
            for n in names:
                rv = rust.get(n, "-")
                lv = lean.get(n, lean.get("*", "no-record"))
                ev = exp.get(n, "-")
                rel = os.path.relpath(src, ROOT)
                print(flush=True, end="")
                print(f"{rel} {n} expected={ev.split()[0] if ev != '-' else '-'} rust={rv} lean={lv}")
                if a.why and lv == "reject":
                    for w in why:
                        if w.startswith(f"WHY {n} "):
                            print("   " + w)
                key = (rv, lv)
                stats[key] = stats.get(key, 0) + 1
    print("summary (rust, lean): " + ", ".join(f"{k[0]}/{k[1]}: {v}" for k, v in sorted(stats.items())))


if __name__ == "__main__":
    main()

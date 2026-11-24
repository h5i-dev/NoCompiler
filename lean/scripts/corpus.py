#!/usr/bin/env python3
"""Run the Lean checker on the shared corpus (tests/typed/corpus/, TWO-AGENTS.md).

For each typed-assembly file: the Rust checker exports its record (`--export-lean`,
docs/typed/export.md); clang assembles the file; the Lean checker (`Fn.check`) runs on
the object's code words with that record. Prints one line per function:

    FILE NAME expected=<#! expect> rust=<accept|reject> lean=<accept|reject|no-record>

and a summary. The Lean verdict here is compiled evaluation (`#eval`), which is enough to
compare verdicts; a theorem needs the kernel (`decide`), as lean/TypedTests/Sum.lean does.

With --link the object is linked first (ld.lld, entry `_start` when the file has one; every
symbol the file leaves undefined, i.e. a callee declared here by its signature only, gets a
one-word `ret` stub so it has an address, and the callee's signature is assumed there), the record is exported against the linked image (`--image`,
export.md "Linked image": linked addresses, static data, call pairs), every function is
checked on the linked `.text` at its address, and `Prog.check` runs on `prog`
(callee-first): `PROG <file> accept|reject`.

Usage: lean/scripts/corpus.py [--checker PATH] [--keep DIR] [--link] [FILES or DIRS ...]
Environment: LEAN_TIMEOUT (seconds per file), CORPUS_MEM (e.g. 4G: each file's Lean process
in its own memory scope, so running out of memory is that file's verdict, `out-of-memory`).
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
LD = os.environ.get("LD_LLD", "ld.lld-20")
READELF = os.environ.get("READELF", "llvm-readelf")
NM = os.environ.get("NM", "llvm-nm")
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


def section_addr(elf, sec):
    """The address of section `sec` in a linked ELF (llvm-readelf -S)."""
    r = subprocess.run([READELF, "-S", "-W", elf], capture_output=True, text=True)
    for line in r.stdout.splitlines():
        f = line.replace("[", " ").replace("]", " ").split()
        if sec in f:
            i = f.index(sec)
            try:
                return int(f[i + 2], 16)
            except (IndexError, ValueError):
                return None
    return None


def link(src, obj, tmp, stem):
    """Link the object (entry `_start` if the file defines it) with a stub `ret` for every
    symbol it leaves undefined (functions declared here and checked elsewhere): each callee
    then has a real address, and the Lean checker checks the caller on the linked image with
    the callees' signatures assumed there. (elf, whether stubs were added); (None, False)
    when linking fails."""
    elf = os.path.join(tmp, stem + ".elf")
    text = open(src, encoding="utf-8").read()
    entry = ["-e", "_start"] if re.search(r"^_start:", text, re.M) else ["--entry=0"]
    undef = subprocess.run([NM, "-u", obj], capture_output=True, text=True).stdout.split()
    undef = [u for u in undef if u not in ("U", "w", "v") and not u.startswith(".")]
    objs = [obj]
    if undef:
        stub_s = os.path.join(tmp, stem + ".stubs.s")
        with open(stub_s, "w", encoding="utf-8") as fh:
            fh.write("    .text\n")
            for u in undef:
                fh.write(f"    .p2align 2\n    .globl {u}\n    .type {u},@function\n{u}:\n    ret\n")
        stub_o = os.path.join(tmp, stem + ".stubs.o")
        if subprocess.run([CLANG, *CFLAGS, stub_s, "-o", stub_o], capture_output=True).returncode == 0:
            objs.append(stub_o)
    r = subprocess.run([LD, *entry, "--unresolved-symbols=ignore-all", "-o", elf, *objs],
                       capture_output=True, text=True)
    return (elf, bool(undef)) if r.returncode == 0 and os.path.exists(elf) else (None, False)


def verdict(name, ident, code):
    """One `#eval`: the verdict, and on a reject the reason (structOk, the entry edge and the
    first instruction that fails, found by an early-stopping search: the check runs once)."""
    f = f"fn_{ident}"
    return (f'#eval do\n'
            f'  if {f}.check {code} then IO.println "LEAN {name} accept" else do\n'
            f'    IO.println "LEAN {name} reject"\n'
            f'    let bad := (List.range {f}.size).find? (fun k => !{f}.instr {code} k)\n'
            f'    IO.println s!"WHY {name} struct={{{f}.structOk}} entry={{{f}.edge none {f}.initTy 0}} '
            f'bad={{bad.map (fun k => (k, repr ({code}.instr ({f}.pcOf k))))}}"')


def run_file(src, checker, tmp, keep, why=None, linked=False):
    stem = re.sub(r"[^A-Za-z0-9_]", "_", os.path.splitext(os.path.basename(src))[0])
    exp_lean = os.path.join(tmp, stem + ".export.lean")
    obj = os.path.join(tmp, stem + ".o")
    ok = subprocess.run([CLANG, *CFLAGS, src, "-o", obj], capture_output=True).returncode == 0
    elf, stubbed = link(src, obj, tmp, stem) if (linked and ok) else (None, False)
    cmd = [checker, "check", src, "--export-lean", exp_lean] + (["--image", elf] if elf else [])
    r = subprocess.run(cmd, capture_output=True, text=True)
    rust_out = r.stdout + r.stderr
    rust = {}
    for line in rust_out.splitlines():
        m = re.match(r"(\S+): (checked|assumed|external|rejected|error)", line)
        if m:
            rust[m.group(1)] = "accept" if m.group(2) == "checked" else m.group(2)
    if not os.path.exists(exp_lean):
        return stem, {}, rust, None
    text = open(exp_lean, encoding="utf-8").read()
    fns = re.findall(r"/-- `([^`]+)`: section (\S+) offset (0x[0-9a-fA-F]+)", text)
    ns = re.search(r"^namespace (\S+)", text, re.M).group(1)
    lines = [text, "", f"open {ns}", "open NoCompiler NoCompiler.Typed", ""]
    if elf:
        # one image: the linked .text at its address; every function checked against it
        words = section_words(elf, ".text", tmp)
        base = section_addr(elf, ".text")
        if words is None or base is None:
            lines.append('#eval IO.println "LEAN * no-linked-text"')
        else:
            ws = ", ".join(f"0x{w:08x}#32" for w in words)
            lines.append(f"def code : Code := ⟨0x{base:x}#64, #[{ws}]⟩")
            for name, sec, off in fns:
                ident = re.sub(r"[^A-Za-z0-9_]", "_", name)
                lines.append(verdict(name, ident, "code"))
            if re.search(r"^def prog ", text, re.M):
                # theorem D needs every callee in `prog`; a file with stubbed callees (checked
                # elsewhere) has none to offer, so only its functions' verdicts count
                if stubbed:
                    lines.append(f'#eval IO.println "PROG {os.path.basename(src)} external-callees"')
                else:
                    lines.append(f'#eval IO.println s!"PROG {os.path.basename(src)} {{if Prog.check code [] prog then "accept" else "reject"}}"')
        fns = []
    for name, sec, off in fns:
        ident = re.sub(r"[^A-Za-z0-9_]", "_", name)
        words = section_words(obj, sec, tmp) if ok else None
        if words is None:
            lines.append(f'#eval IO.println "LEAN {name} no-object"')
            continue
        ws = ", ".join(f"0x{w:08x}#32" for w in words)
        lines.append(f"def code_{ident} : Code := ⟨0#64, #[{ws}]⟩")
        lines.append(verdict(name, ident, f"code_{ident}"))
    gen = os.path.join(keep or tmp, stem + ".lean")
    open(gen, "w", encoding="utf-8").write("\n".join(lines) + "\n")
    try:
        # `lake lean` (not `lake env lean`) loads the precompiled NoCompiler modules, so the
        # #eval of Fn.check runs native code instead of the interpreter (musl memcpy: 157 s -> 7 s)
        # CORPUS_MEM (e.g. 4G): each file's Lean process in its own memory scope, so running out
        # of memory loses that file's verdict only, not the whole run
        mem = os.environ.get("CORPUS_MEM")
        pre = (["systemd-run", "--user", "--scope", "--quiet", "-p", f"MemoryMax={mem}",
                "-p", "MemorySwapMax=0"] if mem else [])
        r = subprocess.run([*pre, "lake", "lean", gen], cwd=os.path.join(ROOT, "lean"),
                           capture_output=True, text=True, timeout=TIMEOUT)
        if r.returncode < 0 or r.returncode == 137:
            r = subprocess.CompletedProcess([], 1, r.stdout + "\nOUT-OF-MEMORY", "")
    except subprocess.TimeoutExpired as e:
        out = e.stdout.decode() if isinstance(e.stdout, bytes) else (e.stdout or "")
        r = subprocess.CompletedProcess([], 1, out + "\nTIMEOUT", "")
    lean = {}
    for line in r.stdout.splitlines():
        if line.startswith("WHY ") and why is not None:
            why.append(line)
        if line.startswith("PROG ") and why is not None:
            why.append(line)
        m = re.match(r"LEAN (\S+) (\S+)", line)
        if m:
            lean[m.group(1)] = m.group(2)
    if r.returncode != 0 and not lean:
        err = (r.stdout + r.stderr).strip().splitlines()
        lean = {"*": "timeout" if "TIMEOUT" in r.stdout else
                 "out-of-memory" if "OUT-OF-MEMORY" in r.stdout else
                 "lean-error: " + (err[0] if err else "?")}
    return stem, lean, rust, gen


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--checker", default=os.path.join(
        os.environ.get("CARGO_TARGET_DIR", os.path.join(ROOT, "target")), "release", "nocompiler-typed"))
    ap.add_argument("--keep", help="keep the generated Lean files here")
    ap.add_argument("--why", action="store_true", help="say where the Lean checker rejects")
    ap.add_argument("--link", action="store_true", help="check on the linked image (--image)")
    ap.add_argument("paths", nargs="*", default=[os.path.join(ROOT, "tests", "typed", "corpus")])
    a = ap.parse_args()
    if a.keep:
        os.makedirs(a.keep, exist_ok=True)
    stats = {}
    with tempfile.TemporaryDirectory() as tmp:
        for src in corpus_files(a.paths):
            exp = expectations(src)
            why = []
            stem, lean, rust, _ = run_file(src, a.checker, tmp, a.keep, why, a.link)
            for w in why:
                if w.startswith("PROG "):
                    print(w)
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

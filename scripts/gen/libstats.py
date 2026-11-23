#!/usr/bin/env python3
"""Library size for round 7's METRIC (2): per library directory under lean/, files, lines, theorems
(`theorem`/`lemma`, top-level, any modifiers) and definitions (`def`/`abbrev`/`structure`/`inductive`).

usage: libstats.py [LEAN_DIR] [--git REV]   (default: lean/ of the working tree; with --git, the tree at REV)
"""
import argparse, os, re, subprocess

DIRS = ["NoCompiler/Lib", "NoCompiler/Libc", "LPS/Common", "LPS/Bridge", "LPS/LinuxProcessSem", "LPS/EquivalenceDefinition",
        "LPS/Riscv", "LPS/OSSVerify", "Examples/Libc"]
THM = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*(?:theorem|lemma)\s", re.M)
DEF = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*(?:def|abbrev|structure|inductive)\s", re.M)


def files_fs(root, d):
    p = os.path.join(root, d)
    for r, _, fs in os.walk(p):
        for f in fs:
            if f.endswith(".lean"):
                yield os.path.join(r, f), open(os.path.join(r, f)).read()


def files_git(rev, d):
    ls = subprocess.run(["git", "ls-tree", "-r", "--name-only", rev, f"lean/{d}"], capture_output=True, text=True).stdout
    for f in ls.split():
        if f.endswith(".lean"):
            yield f, subprocess.run(["git", "show", f"{rev}:{f}"], capture_output=True, text=True).stdout


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("lean", nargs="?", default="lean"); ap.add_argument("--git")
    a = ap.parse_args()
    print("| library | files | lines | theorems | definitions |\n| --- | --- | --- | --- | --- |")
    tot = [0, 0, 0, 0]
    for d in DIRS:
        fs = list(files_git(a.git, d) if a.git else files_fs(a.lean, d))
        n, ln = len(fs), sum(s.count("\n") for _, s in fs)
        th, df = sum(len(THM.findall(s)) for _, s in fs), sum(len(DEF.findall(s)) for _, s in fs)
        tot = [tot[0] + n, tot[1] + ln, tot[2] + th, tot[3] + df]
        print(f"| {d} | {n} | {ln} | {th} | {df} |")
    print(f"| total | {tot[0]} | {tot[1]} | {tot[2]} | {tot[3]} |")


if __name__ == "__main__":
    main()

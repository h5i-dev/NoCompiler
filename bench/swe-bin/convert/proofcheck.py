"""check_proof: the patch-mode proof bonus (lead 00:49 UTC, user decision: option (b)).

  proofcheck.py check BASE_ELF SUB_ELF PROOF.lean WORK [--cache DIR]

For each function f the submission replaced (its symbol now in `.swb`, where `link` puts the
agent's code, and present in base), the bonus needs, in PROOF.lean (module SweBin.Proof):

  def pre_f_0 : α → State → Prop := ...      -- the precondition, one conjunct per def
  def pre_f_1 : α → State → Prop := ...
  def sp_f : Spec α := { pre := fun a s => pre_f_0 a s ∧ pre_f_1 a s, ... }
  theorem inhabited_f : ∃ a s, Entry SweBin.Base.f_dom SweBin.Base.f_entry s ∧ sp_f.pre a s
  theorem refines_f : Refines sp_f SweBin.Base.code SweBin.Base.f_dom SweBin.Base.f_entry
                                   SweBin.Patched.code SweBin.Patched.f_dom SweBin.Patched.f_entry

Refines carries ARuns (a whole proof that base's f runs from every entry sp_f allows; decision
2026-11-21 (3)). Checked, in a sandbox (env/sandbox.sh: no network; only the Lean toolchain,
NoCompiler's build and the work directory visible):
  1. the text (all of it, comments included): imports only SweBin.Base, SweBin.Patched,
     NoCompiler(.*); none of the words of the commands that run code or change the checker (#eval, run_cmd, elab, macro, syntax, initialize, axiom,
     unsafe, implemented_by, extern, debug.skipKernelTC, ...);
  2. SweBin.Proof compiles; a checker file (written here) restates both statements exactly and
     `#print axioms` them: only propext, Classical.choice, Quot.sound;
  3. non-vacuity (the spec-mutation check, kind `pre`): sp_f.pre is the conjunction of the
     pre_f_k (checked by `rfl`), and with each pre_f_k replaced by `fun _ _ => True` the module
     must FAIL to compile: every conjunct is used. With inhabited_f, the precondition holds of some
     entry state, so it is not False.
The bonus: all of that, for every replaced function. Also recorded, not scored (option (a)): how
many functions keep their bytes (Refines.refl applies to them as they are).

The images: `nocompiler export --format chunks` of base and of the submission's proof view
(swb-elf proofview: .text extended over .swb), each trimmed to the replaced functions' _dom (the
other function symbols demoted), since a whole-binary export does not fit the memory cap.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import struct
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
BENCH = os.path.dirname(HERE)
NC = os.environ.get("NOCOMPILER", "/mnt/scratch/ec2-user/target-nc-d/release/nocompiler")
SWB_ELF = os.environ.get("SWB_ELF", "/mnt/scratch/ec2-user/target-nc-d/release/swb-elf")
LEAN_TC = os.environ.get("LEAN_TC", "/mnt/scratch/ec2-user/elan/toolchains/leanprover--lean4---v4.35.0")
NC_LEAN = os.path.realpath(os.environ.get("NC_LEAN", os.path.join(BENCH, "..", "..", "lean", ".lake", "build")))
SANDBOX = os.path.join(BENCH, "env", "sandbox.sh")
MEM = os.environ.get("PROOF_MEM", "6G")
TIMEOUT = int(os.environ.get("PROOF_TIMEOUT", "1200"))

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = [r"#eval", r"#exit", r"\brun_cmd\b", r"\brun_elab\b", r"\brun_meta\b", r"\belab\b", r"\bmacro\b",
             r"\bmacro_rules\b", r"\bsyntax\b", r"\binitialize\b", r"\bbuiltin_initialize\b", r"\baxiom\b",
             r"\bunsafe\b", r"implemented_by", r"@\[extern", r"\bextern\b", r"skipKernelTC", r"\bnative_decide\b",
             r"Lean\.ofReduceBool", r"\bopaque\b", r"\bpartial\b", r"set_option\s+(?!maxRecDepth|maxHeartbeats)",
             r"\bIO\b", r"#print", r"\bnamespace\s+SweBin\.(Base|Patched)\b", r"\bimport\b(?!\s+(SweBin\.Base|SweBin\.Patched|NoCompiler[\w.]*)\s*$)"]


def symbols(path):
    """(name, value, size, is_func) per symbol; and the .swb section's [start, end)."""
    from elftools.elf.elffile import ELFFile
    with open(path, "rb") as fh:
        e = ELFFile(fh)
        swb = e.get_section_by_name(".swb")
        rng = (swb["sh_addr"], swb["sh_addr"] + swb["sh_size"]) if swb else None
        st = e.get_section_by_name(".symtab")
        syms = [(s.name, s["st_value"], s["st_size"], s["st_info"]["type"] == "STT_FUNC") for s in st.iter_symbols()] if st else []
    return syms, rng


def replaced(base, sub):
    """The base functions whose symbol the submission moved into .swb (what `link` replaced)."""
    bs, _ = symbols(base)
    ss, rng = symbols(sub)
    if rng is None:
        return []
    names = {n for n, _, _, f in bs if f and n}
    return sorted(n for n, v, _, f in ss if f and n in names and rng[0] <= v < rng[1])


def export(elf, ns, names, out):
    """`nocompiler export --format chunks` of ELF, trimmed to the union of NAMES' _dom."""
    full = out + ".full.lean"
    subprocess.run([NC, "export", "--format", "chunks", "--namespace", ns, "-o", full, elf], check=True,
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    text = open(full).read()
    starts = set()
    for n in names:
        m = re.search(r"^def %s_dom : Dom := \[(.*)\]$" % re.escape(n), text, re.M)
        if not m:
            raise RuntimeError(f"{ns}: no _dom for {n} (it or a function it calls does not pass the profile check)")
        starts |= {int(a, 16) for a in re.findall(r"\((0x[0-9a-f]+)#64, \d+\)", m.group(1))}
    if b".nocompiler.struct" in open(elf, "rb").read():
        # the metadata section names every function: keep them all (such binaries are small)
        os.replace(full, out)
        return
    os.unlink(full)
    d = bytearray(open(elf, "rb").read())
    shoff, = struct.unpack_from("<Q", d, 0x28)
    shentsize, shnum, _ = struct.unpack_from("<HHH", d, 0x3a)
    for i in range(shnum):
        t = struct.unpack_from("<IIQQQQIIQQ", d, shoff + i * shentsize)
        if t[1] != 2:  # SHT_SYMTAB
            continue
        for k in range(t[5] // t[9]):
            o = t[4] + k * t[9]
            val, = struct.unpack_from("<Q", d, o + 8)
            if d[o + 4] & 0xF == 2 and val not in starts:
                d[o + 4] &= 0xF0  # STT_FUNC -> STT_NOTYPE: not exported
    trimmed = out + ".trim.elf"
    open(trimmed, "wb").write(d)
    subprocess.run([NC, "export", "--format", "chunks", "--namespace", ns, "-o", out, trimmed], check=True,
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    os.unlink(trimmed)


def lean(work, src, mod):
    """Compile WORK/SRC as module MOD (olean under WORK/lp), sandboxed; (ok, output)."""
    rel = os.path.join("lp", *mod.split(".")) + ".olean"
    os.makedirs(os.path.dirname(os.path.join(work, rel)), exist_ok=True)
    lp = ":".join([os.path.join(NC_LEAN, "lib", "lean"), os.path.join(LEAN_TC, "lib", "lean"), os.path.join(work, "lp")])
    cmd = ["systemd-run", "--user", "--scope", "-q", "-p", f"MemoryMax={MEM}", "-p", "MemorySwapMax=0",
           SANDBOX, work, LEAN_TC, NC_LEAN, "--", "env", f"LEAN_PATH={lp}",
           "timeout", str(TIMEOUT), os.path.join(LEAN_TC, "bin", "lean"), "-o", rel, src]
    p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    return p.returncode == 0, p.stdout


def text_problems(src):
    out = []
    # the whole text, comments and strings included: a word in a comment costs a rewrite, but
    # nothing Lean reads as code can hide from the check
    for i, line in enumerate(src.splitlines(), 1):
        for pat in FORBIDDEN:
            if re.search(pat, line):
                out.append(f"line {i}: not allowed in a proof file, even in a comment ({pat}): {line.strip()[:120]}")
    return out


def check(base, sub, proof, work, cache=None):
    t0 = time.time()
    work = os.path.realpath(work)
    res = {"checked": False, "functions": {}, "reasons": []}
    fs = replaced(base, sub)
    res["replaced"] = fs
    bs, _ = symbols(base)
    ss, _ = symbols(sub)
    sv = {n: (v, z) for n, v, z, f in ss if f}
    with open(base, "rb") as b, open(sub, "rb") as s:
        bd, sd = b.read(), s.read()
    # option (a), recorded: functions whose bytes at the same address are unchanged
    from elftools.elf.elffile import ELFFile
    same = 0
    tot = 0
    eb = ELFFile(open(base, "rb"))
    for n, v, z, f in bs:
        if not f or not z or n in fs:
            continue
        tot += 1
        if sv.get(n, (None,))[0] == v:
            off = next((sg["p_offset"] + v - sg["p_vaddr"] for sg in eb.iter_segments()
                        if sg["p_type"] == "PT_LOAD" and sg["p_vaddr"] <= v < sg["p_vaddr"] + sg["p_filesz"]), None)
            if off is not None and bd[off:off + z] == sd[off:off + z]:
                same += 1
    res["unchanged_identical"] = f"{same} of {tot} other functions have their base bytes (Refines.refl); recorded, not scored"
    if not fs:
        res["reasons"].append("the submission replaces no function (nothing in .swb): no bonus goal")
        return res
    src = open(proof).read()
    probs = text_problems(src)
    if probs:
        res["reasons"] += probs
        return res
    os.makedirs(work, exist_ok=True)
    # the images (base cached per task)
    key = "-".join(fs)
    bl = os.path.join(cache or work, f"Base-{key}.lean")
    if not os.path.exists(bl):
        export(base, "SweBin.Base", fs, bl)
    view = os.path.join(work, "view.elf")
    subprocess.run([SWB_ELF, "proofview", sub, view], check=True, stdout=subprocess.DEVNULL)
    export(view, "SweBin.Patched", fs, os.path.join(work, "Patched.lean"))
    shutil.copy(bl, os.path.join(work, "Base.lean"))
    for mod, f in (("SweBin.Base", "Base.lean"), ("SweBin.Patched", "Patched.lean")):
        ok, out = lean(work, f, mod)
        if not ok:
            res["reasons"].append(f"{mod} did not compile (an environment problem): {out[-600:]}")
            return res
    shutil.copy(proof, os.path.join(work, "Proof.lean"))
    ok, out = lean(work, "Proof.lean", "SweBin.Proof")
    if not ok:
        res["reasons"].append("SweBin.Proof did not compile:\n" + out[-3000:])
        return res
    chk = ["import SweBin.Proof", "open NoCompiler SweBin.Proof"]
    for f in fs:
        parts = sorted(set(re.findall(r"^def (pre_%s_\d+)\b" % re.escape(f), src, re.M)), key=lambda x: int(x.rsplit("_", 1)[1]))
        res["functions"][f] = {"pre_conjuncts": parts}
        if not parts:
            res["reasons"].append(f"{f}: no pre_{f}_0 ...: the precondition must be one def per conjunct")
            return res
        conj = " ∧ ".join(f"{p} a s" for p in parts)
        chk += [f"example : Refines sp_{f} SweBin.Base.code SweBin.Base.{f}_dom SweBin.Base.{f}_entry "
                f"SweBin.Patched.code SweBin.Patched.{f}_dom SweBin.Patched.{f}_entry := refines_{f}",
                f"example : ∃ a s, Entry SweBin.Base.{f}_dom SweBin.Base.{f}_entry s ∧ (sp_{f}).pre a s := inhabited_{f}",
                f"example : (sp_{f}).pre = fun a s => {conj} := rfl",
                f"#print axioms refines_{f}", f"#print axioms inhabited_{f}"]
    open(os.path.join(work, "Check.lean"), "w").write("\n".join(chk) + "\n")
    ok, out = lean(work, "Check.lean", "SweBin.Check")
    if not ok:
        res["reasons"].append("the statements do not match (Check.lean):\n" + out[-3000:])
        return res
    axioms = set()
    for m in re.finditer(r"depends on axioms: \[([^\]]*)\]", out):
        axioms |= {a.strip() for a in m.group(1).split(",") if a.strip()}
    bad = axioms - ALLOWED_AXIOMS
    res["axioms"] = sorted(axioms)
    if bad or "sorryAx" in out:
        res["reasons"].append(f"axioms not allowed: {sorted(bad) or ['sorryAx']}")
        return res
    # non-vacuity: each conjunct of each precondition is needed
    for f in fs:
        survived = []
        for p in res["functions"][f]["pre_conjuncts"]:
            mw = os.path.join(work, "mut", p)
            os.makedirs(mw, exist_ok=True)
            for x in ("Base.lean", "Patched.lean"):
                shutil.copy(os.path.join(work, x), mw)
            shutil.copytree(os.path.join(work, "lp"), os.path.join(mw, "lp"), dirs_exist_ok=True)
            msrc, n = re.subn(r"^(def %s\s*:\s*[^:=]*?)\s*:=.*?(?=^\S)" % re.escape(p), r"\1 := fun _ _ => True\n\n",
                              src + "\n#\n", flags=re.M | re.S)
            if n != 1:
                res["reasons"].append(f"{p}: could not replace its body (one def, its body up to the next unindented line)")
                return res
            open(os.path.join(mw, "Proof.lean"), "w").write(msrc[:-2])
            ok, _ = lean(mw, "Proof.lean", "SweBin.Proof")
            if ok:
                survived.append(p)
            shutil.rmtree(mw)
        res["functions"][f]["survived_mutations"] = survived
        if survived:
            res["reasons"].append(f"{f}: the proof still holds with {', '.join(survived)} replaced by True: "
                                  "that conjunct is not needed (drop it and prove again)")
    res["checked"] = not res["reasons"]
    res["seconds"] = round(time.time() - t0, 1)
    return res


def main(argv):
    if len(argv) < 5 or argv[0] != "check":
        print(__doc__.strip(), file=sys.stderr)
        return 2
    cache = argv[argv.index("--cache") + 1] if "--cache" in argv else None
    print(json.dumps(check(argv[1], argv[2], argv[3], argv[4], cache)))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

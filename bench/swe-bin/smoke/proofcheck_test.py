"""QUEUE-D 2a: check_proof (convert/proofcheck.py) accepts a valid proof and rejects broken ones.

  proofcheck_test.py DIR

DIR holds base.elf, sub.elf (base with one function replaced through `swb-elf link`) and Proof.lean,
a valid proof of the bonus statement for that function. Each case below changes Proof.lean in one
way; the valid one must be checked, every other one rejected for the reason named.
The run used for the record: base = examples/elf/refine-sum-a.elf, sub = base with sum_b.s's
`sum` (the loop's add commuted) linked in, Proof.lean = the sum spec split into 5 conjuncts, the
`nocompiler refine --images` certificate, `nocompiler_auto` for A's run (as
lean/Examples/Refine/Diff.lean does), and an entry state for `inhabited_sum`.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PC = os.path.join(os.path.dirname(HERE), "convert", "proofcheck.py")
PY = os.environ.get("PY", "/mnt/scratch/ec2-user/swe-bin/venv/bin/python")


def cases(src):
    yield "valid", src, None
    yield "sorry", src.replace("  refines _ (ARuns.of_verified sum_a)", "  sorry"), "axioms"
    yield "wrong-statement", src.replace(
        "theorem refines_sum : Refines sp_sum SweBin.Base.code SweBin.Base.sum_dom SweBin.Base.sum_entry\n"
        "    SweBin.Patched.code SweBin.Patched.sum_dom SweBin.Patched.sum_entry :=\n"
        "  refines _ (ARuns.of_verified sum_a)",
        "theorem refines_sum : Refines sp_sum SweBin.Base.code SweBin.Base.sum_dom SweBin.Base.sum_entry\n"
        "    SweBin.Base.code SweBin.Base.sum_dom SweBin.Base.sum_entry :=\n"
        "  Refines.refl (ARuns.of_verified sum_a)"), "statements"
    yield "axiom", src.replace("theorem sum_a", "axiom cheat : False\n\ntheorem sum_a"), "not allowed"
    yield "eval", src.replace("theorem sum_a", "#eval 1\n\ntheorem sum_a"), "not allowed"
    yield "native_decide", src.replace("⟨rfl, rfl, by decide, by decide, by decide⟩",
                                       "⟨rfl, rfl, by native_decide, by decide, by decide⟩"), "not allowed"
    unused = src.replace(
        "def sp_sum : Spec Args where\n  pre := fun a s => pre_sum_0 a s ∧ pre_sum_1 a s ∧ pre_sum_2 a s ∧ pre_sum_3 a s ∧ pre_sum_4 a s",
        "def pre_sum_5 : Args → State → Prop := fun _ s => s.trace = []\n\n"
        "def sp_sum : Spec Args where\n  pre := fun a s => pre_sum_0 a s ∧ pre_sum_1 a s ∧ pre_sum_2 a s ∧ pre_sum_3 a s ∧ pre_sum_4 a s ∧ pre_sum_5 a s")
    unused = unused.replace("rintro ⟨a, xs⟩ s he ⟨ha0, ha1, hlen, hal, harr⟩\n  simp only [pre_sum_0, pre_sum_1, pre_sum_2, pre_sum_3, pre_sum_4] at ha0 ha1 hlen hal harr",
                            "rintro ⟨a, xs⟩ s he ⟨ha0, ha1, hlen, hal, harr, _⟩\n  simp only [pre_sum_0, pre_sum_1, pre_sum_2, pre_sum_3, pre_sum_4] at ha0 ha1 hlen hal harr")
    unused = unused.replace("pre_sum_3, pre_sum_4, State.reg, aligned, arr64]; decide⟩",
                            "pre_sum_3, pre_sum_4, pre_sum_5, State.reg, aligned, arr64]; decide⟩")
    yield "unused-conjunct", unused, "not needed"


def main(d):
    src = open(os.path.join(d, "Proof.lean")).read()
    ok_all = True
    for name, text, want in cases(src):
        if name != "valid" and text == src:
            print(f"{name}: the case did not change the file (test bug)")
            ok_all = False
            continue
        p = os.path.join(d, f"case-{name}.lean")
        open(p, "w").write(text)
        w = os.path.join(d, f"work-{name}")
        subprocess.run(["rm", "-rf", w], check=True)
        out = subprocess.run([PY, PC, "check", os.path.join(d, "base.elf"), os.path.join(d, "sub.elf"), p, w],
                             stdout=subprocess.PIPE, text=True).stdout
        r = json.loads(out.strip().splitlines()[-1])
        reasons = " | ".join(x.replace("\n", " ")[:160] for x in r["reasons"])
        good = r["checked"] if want is None else (not r["checked"] and want in " ".join(r["reasons"]))
        ok_all &= good
        print(f"{name}: checked={r['checked']} {'OK' if good else 'UNEXPECTED'} {reasons} ({r.get('seconds', '-')} s)")
    print("PROOFCHECK", "PASS" if ok_all else "FAIL")
    return 0 if ok_all else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))

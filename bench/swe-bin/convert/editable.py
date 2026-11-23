"""Backfill `editable_crates` for class-B records converted before RustTests.build recorded it.

  editable.py [TASK ...]     (default: every record with a deviation and no editable_crates)

The crates under test are the workspace's library and proc-macro crates at the base commit, as
RustTests.build computes them: `cargo metadata --no-deps` on a checkout of base (no build). Without
the list, harness.integrity rejects every changed function ("crate X is not under test"), so no
submission, the gold one included, could pass (the axum records, pilot 2026-11-21-r2).
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rusttc  # noqa: E402

SWB = os.environ.get("SWB", "/mnt/scratch/ec2-user/swe-bin")
TASKS = os.path.join(os.path.dirname(HERE), "tasks")


def crates_at(repo_git: str, commit: str) -> list[str]:
    with tempfile.TemporaryDirectory(dir=os.path.join(SWB, "work")) as tmp:
        wt = os.path.join(tmp, "src")
        subprocess.run(["git", "clone", "-q", "--no-checkout", repo_git, wt], check=True)
        subprocess.run(["git", "-C", wt, "checkout", "-q", commit], check=True)
        env = dict(os.environ, RUSTUP_HOME=rusttc.RUSTUP_HOME, CARGO_HOME=rusttc.CARGO_HOME)
        out = subprocess.run(["cargo", f"+{rusttc.LOCK_TOOLCHAIN}", "metadata", "--no-deps", "--format-version", "1"],
                             cwd=wt, env=env, check=True, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL).stdout
    crates = set()
    for pk in json.loads(out).get("packages", []):
        for tg in pk.get("targets", []):
            if "lib" in tg.get("kind", []) or "proc-macro" in tg.get("kind", []):
                crates.add(tg["name"].replace("-", "_"))
    return sorted(crates)


def main(argv):
    names = argv or sorted(f[:-5] for f in os.listdir(TASKS) if f.endswith(".json") and f != "notes.json")
    for n in names:
        p = os.path.join(TASKS, f"{n}.json")
        with open(p) as fh:
            tj = json.load(fh)
        if not tj.get("deviation") or tj.get("editable_crates") is not None:
            continue
        repo = os.path.join(SWB, "repos", tj["repo"].split("/")[1] + ".git")
        tj["editable_crates"] = crates_at(repo, tj["base_commit"])
        with open(p, "w") as fh:
            json.dump(tj, fh, indent=1)
            fh.write("\n")
        print(f"{n}: {len(tj['editable_crates'])} crates: {' '.join(tj['editable_crates'])}")


if __name__ == "__main__":
    main(sys.argv[1:])

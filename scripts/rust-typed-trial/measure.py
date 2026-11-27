#!/usr/bin/env python3
"""Measure a fixed coverage set using automatically generated contracts."""

import argparse
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
CHECK = ROOT / "tools/rust-annotate/cargo-nocompiler"
FIXTURES = ROOT / "examples/rust-typed/fixtures"


def vec(capacity, method):
    return (
        "heapless::vec::VecInner::<u64, usize, heapless::vec::storage::"
        f"VecStorageInner<[core::mem::MaybeUninit<u64>; {capacity}]>>::{method}"
    )


def targets(category, *names):
    return [(category, name) for name in names]


RUNS = [
    ("heapless", "heapless_probe",
     targets("upstream", vec(4, "as_slice"), vec(8, "as_slice"), vec(8, "push"),
             vec(8, "push_unchecked"), vec(8, "len"))
     + targets("wrapper", "heapless_probe::read::<4>", "heapless_probe::read::<8>",
               "heapless_probe::append", "heapless_probe::copy_first")),
    ("memchr-forward", "memchr_probe", targets("upstream", "memchr::memchr")
     + targets("wrapper", "memchr_probe::find")),
    ("memchr-reverse", "memchr_probe", targets("upstream", "memchr::memrchr")
     + targets("wrapper", "memchr_probe::find_last")),
    ("rust-alloc", "global_alloc_probe",
     targets("fixture", "global_alloc_probe::rust_alloc_round_trip", "global_alloc_probe::boxed_release")),
    ("box-transfer", "global_alloc_probe",
     targets("fixture", "global_alloc_probe::boxed_transfer")),
    ("buffers", "buffer_ops", targets("fixture", "buffer_ops::sum_after_prefix",
                                      "buffer_ops::scan_records", "buffer_ops::read_spilled")),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifacts", type=Path, default=None)
    args = parser.parse_args()
    root = args.artifacts.resolve() if args.artifacts else Path(tempfile.mkdtemp(prefix="nocompiler-coverage-"))
    root.mkdir(parents=True, exist_ok=True)
    def measure(run):
        label, binary, entries = run
        directory = root / label
        log = root / f"{label}.log"
        command = [CHECK, "check", "--manifest-path", FIXTURES / binary / "Cargo.toml",
                   "--bin", binary, "--artifacts", directory, "--allow-assumptions"]
        for _, name in entries:
            command.extend(["--function", name])
        with log.open("x") as output:
            subprocess.run(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT, check=False)
        report_path = directory / "report.json"
        report = json.loads(report_path.read_text()) if report_path.exists() else {}
        functions = report.get("functions", {})
        return [{"run": label, "category": category, "function": name,
                 "result": functions.get(name, {"status": "tool_error"})}
                for category, name in entries]

    with ThreadPoolExecutor(max_workers=2) as pool:
        rows = [row for group in pool.map(measure, RUNS) for row in group]
    counts = defaultdict(Counter)
    for row in rows:
        for group in ("all", row["category"], row["run"]):
            counts[group][row["result"]["status"]] += 1
    (root / "coverage.json").write_text(json.dumps({"counts": counts, "targets": rows}, indent=2) + "\n")
    for group, values in counts.items():
        total = sum(values.values())
        print(f"{group}: {values['proved']}/{total} proved ({values['proved'] / total:.1%}), {dict(values)}")
    print(f"Artifacts: {root}")
    return int(any(row["result"]["status"] == "tool_error" for row in rows))


if __name__ == "__main__":
    raise SystemExit(main())

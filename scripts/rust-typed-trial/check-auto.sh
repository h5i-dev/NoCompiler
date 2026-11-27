#!/bin/bash
# Exercise compiler-driven annotations on two independent Rust crates.
set -euo pipefail
cd "$(dirname "$0")/../.."
export PATH="$PWD/tools/rust-annotate:$PATH"
artifacts=$(mktemp -d)
echo "Integration artifacts: $artifacts"

cargo nocompiler check \
    --manifest-path examples/rust-typed/fixtures/buffer_ops/Cargo.toml --bin buffer_ops \
    --function buffer_ops::read_at --function buffer_ops::copy_byte \
    --artifacts "$artifacts/buffers"

cargo nocompiler check \
    --manifest-path examples/rust-typed/fixtures/word_ops/Cargo.toml --bin word_ops \
    --function word_ops::write_first --function word_ops::read_word \
    --artifacts "$artifacts/words"

status=0
cargo nocompiler check \
    --manifest-path examples/rust-typed/fixtures/buffer_ops/Cargo.toml --bin buffer_ops \
    --function buffer_ops::read_unchecked --function buffer_ops::unknown \
    --artifacts "$artifacts/rejected" || status=$?
if [ "$status" -ne 1 ]; then
    echo "Expected a verification failure, got status $status" >&2
    exit 1
fi

python3 - "$artifacts" <<'PY'
import json
from pathlib import Path
import sys

directory = Path(sys.argv[1])
buffers = (directory / "buffers/contracts.s").read_text().splitlines()
assert len(buffers) == 2
assert "bytes[8*n0] ro where 8 | p0" in buffers[0]
assert "bytes[1*n0] rw, p1 |-> bytes[1*n1] ro" in buffers[1]
assert "x1 <" not in buffers[0] and "x2 <" not in buffers[1]

report = json.loads((directory / "rejected/report.json").read_text())
unchecked = report["functions"]["buffer_ops::read_unchecked"]
assert unchecked["status"] == "rejected"
assert unchecked["error"]["rule"] == "mem-bounds"
assert report["functions"]["buffer_ops::unknown"]["status"] == "unsupported"
PY

#!/bin/bash
# Run CI's jobs on this machine. CI on GitHub runs only for pull requests;
# before that, a change is checked here.
#
#   scripts/ci/local.sh check   fmt + clippy (CI job `check`)
#   scripts/ci/local.sh core    Lean build, audit, controls, cost gate, core tests (CI job `core`)
#   scripts/ci/local.sh test    the whole cargo suite with the fixture corpus built, in a
#                               ubuntu:24.04 container like CI's runner (CI job `test`)
#   scripts/ci/local.sh all     the three above
#
# Which to run before landing: always `check`; `core` when lean/**, crates/nocompiler/**,
# crates/nocompiler-cli/** or examples/** change; `test` when any crate changes.
# Lean runs under a memory cap (MEMCAP, default 6G), as everywhere on the shared machine.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
MEMCAP=${MEMCAP:-6G}
cap() { systemd-run --user --scope -q -p MemoryMax="$MEMCAP" -p MemorySwapMax=0 "$@"; }

job_check() {
  cargo fmt --all --check
  cargo clippy --workspace --all-targets -- -D warnings
}

job_core() {
  (cd lean && cap lake build && cap lake exe nocompiler-audit)
  cap ./lean/AuditControls/run.sh
  # The cost gate's budgets come from CI's quiet runners; on this shared machine the
  # load makes every entry slow, so here it reports and the pull request's CI gates.
  python3 -I scripts/core/bench-gate.py || echo "local CI: bench-gate over budget (load $(cut -d' ' -f1 /proc/loadavg)); reported, not gated here; the PR's CI gates it"
  cargo test -p nocompiler --no-fail-fast
  cargo test -p nocompiler-cli --test core
  cargo build -p nocompiler-cli --bin nocompiler
  NOCOMPILER="$(cargo metadata --format-version 1 --no-deps | python3 -c 'import json,sys;print(json.load(sys.stdin)["target_directory"])')/debug/nocompiler" \
    ./scripts/core/check-proof-controls.sh
  ./scripts/core/check-audit-controls.sh
  python3 -I scripts/core/check-spec-references.py
  python3 -I scripts/core/check-spec-mutations.py --skip demo-cobs
}

# The fixture corpus needs CI's apt packages; a container keeps them off the host.
# Caches (cargo registry, rustup, target dir) live in CI_CACHE between runs.
job_test() {
  local cache=${CI_CACHE:-/mnt/scratch/$USER/ci-cache}
  local src; src=$(mktemp -d "${cache%/}-src.XXXXXX")
  mkdir -p "$cache"
  git archive HEAD | tar -x -C "$src"
  local rc=0
  docker run --rm -e HOST_UID="$(id -u)" -v "$src":/src -v "$cache":/ci -w /src ubuntu:24.04 bash -c '
    set -euo pipefail
    export DEBIAN_FRONTEND=noninteractive
    apt-get -o Acquire::Retries=2 update -qq
    apt-get install -y -qq clang llvm binutils qemu-user-static golang-go gcc-aarch64-linux-gnu \
      g++-aarch64-linux-gnu curl ca-certificates git build-essential >/dev/null
    export CARGO_HOME=/ci/cargo RUSTUP_HOME=/ci/cargo/rustup PATH=/ci/cargo/bin:$PATH
    command -v cargo >/dev/null || curl -sSf https://sh.rustup.rs | sh -s -- -y -q --profile minimal --default-toolchain stable
    ./scripts/toolkit/build-fixtures.sh > /ci/fixtures.log 2>&1
    export CARGO_TARGET_DIR=/ci/target CARGO_PROFILE_TEST_OPT_LEVEL=2
    rc=0; cargo test --workspace --no-fail-fast -j4 > /ci/test.log 2>&1 || rc=$?
    grep -E "^test result|FAILED|panicked" /ci/test.log || true
    chown -R "$HOST_UID" /src /ci 2>/dev/null || true  # the host can remove them
    exit $rc' || rc=$?
  rm -rf "$src"
  return $rc
}

case "${1:-}" in
  check) job_check ;;
  core) job_core ;;
  test) job_test ;;
  all) job_check && job_core && job_test ;;
  *) sed -n '2,13p' "$0"; exit 2 ;;
esac
echo "local CI: ${1} ok"

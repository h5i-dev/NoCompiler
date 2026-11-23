#!/usr/bin/env bash
# sandbox.sh WORKDIR KEEP... -- CMD...: run CMD (the Lean check of an agent's proof) with no
# network, and with /mnt/scratch, /home and /tmp replaced by empty tmpfs mounts except for
# WORKDIR (read-write) and each KEEP path (read-only): the Lean toolchain and NoCompiler's build.
# The tasks, the gold artifacts, the test names, the repositories, other episodes and every
# transcript are then not reachable from code the proof runs at elaboration time (#eval, tactics).
# Unprivileged: a user namespace (`unshare -rmn`), as systemd-run --user cannot hide paths.
set -euo pipefail
[ $# -ge 3 ] || { echo "usage: sandbox.sh WORKDIR KEEP... -- CMD..." >&2; exit 2; }
WORK=$(realpath "$1"); shift
KEEP=()
while [ $# -gt 0 ] && [ "$1" != "--" ]; do KEEP+=("$(realpath "$1")"); shift; done
[ "${1:-}" = "--" ] || { echo "sandbox.sh: missing --" >&2; exit 2; }
shift
for p in "$WORK" "${KEEP[@]}"; do
  case "$p" in /mnt/scratch/*|/home/*) ;; *) echo "sandbox.sh: $p is not under /mnt/scratch or /home" >&2; exit 2;; esac
done
export SBX_WORK="$WORK" SBX_KEEP="${KEEP[*]}"
exec unshare -rmn --propagation private bash -c '
  set -euo pipefail
  hold=$(mktemp -d /dev/shm/swbsbx.XXXXXX)
  i=0
  for p in $SBX_WORK $SBX_KEEP; do mkdir -p "$hold/$i"; mount --rbind "$p" "$hold/$i"; i=$((i+1)); done
  mount -t tmpfs -o size=16m none /mnt/scratch
  mount -t tmpfs -o size=16m none /home
  mount -t tmpfs -o size=64m none /tmp
  i=0
  for p in $SBX_WORK $SBX_KEEP; do
    mkdir -p "$p"; mount --move "$hold/$i" "$p"
    [ $i -gt 0 ] && mount -o remount,bind,ro "$p"
    i=$((i+1))
  done
  rm -rf "$hold"
  cd "$SBX_WORK"
  exec "$@"' sandbox "$@"

#!/usr/bin/env bash
# A minimal, portable semaphore for CPU-intensive Lean jobs.
#
#   tasks/campaign/lean_slot.sh acquire [timeout_seconds]   # prints the slot index
#   tasks/campaign/lean_slot.sh release <slot-index>
#   tasks/campaign/lean_slot.sh status
#
# The pool size is read from $CRNT_BUILD_SLOTS (default 4).  Slots are plain
# directories created with `mkdir`, which is atomic on POSIX, so no lock file or
# `flock` is needed -- macOS ships no `flock`.
#
# Each slot directory holds the PID of its owner.  A slot whose owner is no longer
# alive is stale (the holder was killed) and is reclaimed automatically, so a crashed
# worker cannot leak capacity for the rest of the campaign.
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
POOL="${CRNT_SLOT_DIR:-$ROOT/.campaign/slots}"
mkdir -p "$POOL"

slots="${CRNT_BUILD_SLOTS:-4}"
case "$slots" in (''|*[!0-9]*) slots=4 ;; esac
[ "$slots" -ge 1 ] 2>/dev/null || slots=1

alive() { kill -0 "$1" 2>/dev/null; }

reap() {  # remove slots whose owner died
  for d in "$POOL"/slot.*; do
    [ -d "$d" ] || continue
    pidfile="$d/pid"
    [ -f "$pidfile" ] || { rmdir "$d" 2>/dev/null || true; continue; }
    pid="$(cat "$pidfile" 2>/dev/null || true)"
    if [ -z "$pid" ] || ! alive "$pid"; then
      rm -f "$pidfile"
      rmdir "$d" 2>/dev/null || true
    fi
  done
}

case "${1:-}" in
  acquire)
    timeout="${2:-1800}"
    waited=0
    while : ; do
      reap
      i=1
      while [ "$i" -le "$slots" ]; do
        if mkdir "$POOL/slot.$i" 2>/dev/null; then
          echo "$$" >"$POOL/slot.$i/pid"
          echo "$i"
          exit 0
        fi
        i=$((i + 1))
      done
      [ "$waited" -ge "$timeout" ] && break
      sleep 3
      waited=$((waited + 3))
    done
    echo "lean_slot: timed out after ${timeout}s waiting for a slot (pool=$slots)" >&2
    exit 1
    ;;
  acquire-all)
    # Take every slot in the pool: used by the authoritative full build, which must
    # have exclusive access to the compilation budget.
    timeout="${2:-3600}"
    waited=0
    while : ; do
      reap
      i=1
      ok=1
      while [ "$i" -le "$slots" ]; do
        if mkdir "$POOL/slot.$i" 2>/dev/null; then
          echo "$$" >"$POOL/slot.$i/pid"
        else
          ok=0
        fi
        i=$((i + 1))
      done
      if [ "$ok" = "1" ]; then
        echo "$slots"
        exit 0
      fi
      # release what we took and retry
      i=1
      while [ "$i" -le "$slots" ]; do
        rm -f "$POOL/slot.$i/pid"
        rmdir "$POOL/slot.$i" 2>/dev/null || true
        i=$((i + 1))
      done
      [ "$waited" -ge "$timeout" ] && break
      sleep 3
      waited=$((waited + 3))
    done
    echo "lean_slot: timed out after ${timeout}s waiting for the whole pool" >&2
    exit 1
    ;;
  release-all)
    i=1
    while [ "$i" -le "$slots" ]; do
      rm -f "$POOL/slot.$i/pid"
      rmdir "$POOL/slot.$i" 2>/dev/null || true
      i=$((i + 1))
    done
    exit 0
    ;;
  release)
    i="${2:-}"
    if [ -n "$i" ]; then
      rm -f "$POOL/slot.$i/pid"
      rmdir "$POOL/slot.$i" 2>/dev/null || true
    fi
    exit 0
    ;;
  status)
    reap
    used=0
    for d in "$POOL"/slot.*; do
      [ -d "$d" ] && used=$((used + 1))
    done
    echo "lean_slot: $used/$slots in use"
    for d in "$POOL"/slot.*; do
      [ -d "$d" ] || continue
      echo "  $(basename "$d") pid=$(cat "$d/pid" 2>/dev/null || echo '?')"
    done
    exit 0
    ;;
  *)
    echo "usage: $0 {acquire [timeout]|release <slot>|status}" >&2
    exit 2
    ;;
esac

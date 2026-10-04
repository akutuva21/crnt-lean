#!/usr/bin/env bash
# checkmod.sh — the ONE sanctioned way an agent type-checks a module.
#
#   research/scripts/checkmod.sh CRNT/Dynamics/HighCodimensionSiphonFace.lean
#   research/scripts/checkmod.sh --quiet CRNT/Geometry/PolyhedralBarrier.lean
#
# Elaborates the given source file directly against the *shared* build cache
# ($CRNT_ROOT/.lake/build/lib/lean) so that every agent sees the same dependency
# oleans without each agent paying for a private full Lake build.  The produced
# olean is written into your own worktree's .lake/build tree, never the shared one.
#
# Exit code 0 = the file elaborates.  Non-zero = read the diagnostics.
set -uo pipefail

CRNT_ROOT="${CRNT_ROOT:-/Users/akutuva/Documents/Proofs/crnt-lean}"
QUIET=0
if [ "${1:-}" = "--quiet" ]; then QUIET=1; shift; fi

if [ $# -lt 1 ]; then echo "usage: checkmod.sh [--quiet] <path/to/Module.lean> [...]" >&2; exit 2; fi

rc=0
for f in "$@"; do
  [ -f "$f" ] || { echo "MISSING: $f" >&2; rc=2; continue; }
  mod="${f%.lean}"
  out="$PWD/.lake/build/lib/lean/${mod}.olean"
  mkdir -p "$(dirname "$out")"
  log=$(mktemp)
  # LEAN_PATH order is load-bearing, and `lake env` breaks it.
  #
  # `lake env` PREPENDS its own entries, so a preset LEAN_PATH ends up *after* the
  # workspace's.  This script's own `mkdir -p` above has just created a worktree-local
  # .lake/build/lib/lean/CRNT/, so Lean resolves the CRNT namespace to the worktree root,
  # fails on the missing submodule .olean, and never reaches the shared cache that has
  # it.  Every module importing a CRNT.* module therefore failed, silently, with an
  # error that names a file which really does exist.  (mathlib-only modules were
  # unaffected, which is what made it look intermittent.)
  #
  # The fix is to put the shared root FIRST and call `lean` directly, so nothing
  # reorders LEAN_PATH behind our back.  `$out` is absolute, so the .olean still lands
  # in this worktree's tree and never in the shared one.
  LEAN_PATH="$CRNT_ROOT/.lake/build/lib/lean:$(lake env printenv LEAN_PATH 2>/dev/null)" \
    lean -o "$out" "$f" >"$log" 2>&1
  status=$?
  if [ $status -ne 0 ]; then
    rc=$status
    echo "=== FAIL($status) $f ==="
    grep -E "error:" "$log" | head -40
    [ $QUIET -eq 1 ] || tail -20 "$log"
  elif [ $QUIET -eq 0 ]; then
    warns=$(grep -c "declaration uses \`sorry\`" "$log" || true)
    echo "=== OK $f (sorry-warnings: $warns) ==="
  fi
  rm -f "$log"
done
exit $rc
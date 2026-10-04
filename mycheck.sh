#!/usr/bin/env bash
# Local elaboration check resolving imports against the shared build cache, writing
# nothing into it.  Same contract as research/scripts/checkmod.sh (exit 0 = elaborates).
set -uo pipefail
ROOT=/Users/akutuva/Documents/Proofs/crnt-lean
ML=/Users/akutuva/lean/mathlib4/.lake/build/lib/lean
LEAN_PATH="$ROOT/.lake/build/lib/lean:$ML"
for pkg in Cli batteries Qq aesop importGraph LeanSearchClient plausible; do
  d="/Users/akutuva/lean/mathlib4/.lake/packages/$pkg/.lake/build/lib/lean"
  [ -d "$d" ] && LEAN_PATH="$LEAN_PATH:$d"
done
LEAN_PATH="$LEAN_PATH:$ROOT/.lake/packages/proofwidgets/.lake/build/lib/lean"
rc=0
for f in "$@"; do
  if [ ! -f "$f" ]; then echo "MISSING: $f" >&2; rc=2; continue; fi
  mod="${f%.lean}"
  out="$PWD/.lake/build/lib/lean/${mod}.olean"
  mkdir -p "$(dirname "$out")"
  log="$PWD/leanout.log"
  LEAN_PATH="$LEAN_PATH" lean -DmaxHeartbeats=800000 -o "$out" "$f" >"$log" 2>&1
  st=$?
  if [ $st -ne 0 ]; then
    rc=$st
    echo "=== FAIL($st) $f ==="
    grep -E "error:" "$log" | head -60
  else
    echo "=== OK $f ==="
  fi
done
exit $rc
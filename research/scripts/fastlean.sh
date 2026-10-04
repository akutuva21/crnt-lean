#!/usr/bin/env bash
# fastlean.sh — direct `lean` (no `lake env`), same search path checkmod uses plus
# the vendored Mathlib/Batteries oleans.  For fast iteration only; the sanctioned
# check is research/scripts/checkmod.sh.
set -uo pipefail
ROOT="${CRNT_ROOT:-/Users/akutuva/Documents/Proofs/crnt-lean}"
WT="$(pwd)"
LEAN=~/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean
PP="$ROOT/.lake/build/lib/lean:$WT/.lake/build/lib/lean"
for d in "$ROOT"/.lake/packages/*/.lake/build/lib/lean; do PP="$PP:$d"; done
export LEAN_PATH="$PP"
rc=0
for f in "$@"; do
  mod="${f%.lean}"
  out="$WT/.lake/build/lib/lean/${mod}.olean"
  mkdir -p "$(dirname "$out")"
  "$LEAN" -o "$out" "$f" >/tmp/fastlean.log 2>&1
  st=$?
  grep -E "error:" /tmp/fastlean.log | head -"${ERRLIMIT:-60}"
  if [ "$st" -ne 0 ]; then rc=1; else echo "=== OK $f ==="; fi
done
exit $rc

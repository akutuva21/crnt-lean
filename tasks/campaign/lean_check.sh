#!/usr/bin/env bash
# Elaborate one or more Lean files against the *already built* CRNT library,
# without touching the shared build directory.
#
#   tasks/campaign/lean_check.sh <file.lean> [<file.lean> ...]
#
# The library is used read-only through the recorded LEAN_PATH; nothing is written
# into `.lake/build`.  A CPU slot is held for the duration so that the number of
# simultaneous Lean elaborations stays inside the measured budget.
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
export PATH="$HOME/.elan/bin:$PATH"

LP="$ROOT/.campaign/leanpath.txt"
if [ ! -s "$LP" ]; then
  ( cd "$ROOT" && lake env printenv LEAN_PATH ) >"$LP" 2>/dev/null
fi
if [ ! -s "$LP" ]; then
  echo "lean_check: could not record LEAN_PATH" >&2
  exit 2
fi

if [ $# -eq 0 ]; then
  echo "usage: $0 <file.lean> [...]" >&2
  exit 2
fi

SLOT="$(tasks/campaign/lean_slot.sh acquire "${CRNT_SLOT_WAIT:-3600}")" || {
  echo "lean_check: no build slot available" >&2
  exit 3
}
trap 'tasks/campaign/lean_slot.sh release "$SLOT" >/dev/null 2>&1' EXIT

rc=0
for f in "$@"; do
  echo "=== lean $f ==="
  LEAN_PATH="$(cat "$LP")" lean "$f" || rc=1
done
exit $rc

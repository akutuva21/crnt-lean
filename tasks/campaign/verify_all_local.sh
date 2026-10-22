#!/usr/bin/env bash
# The authoritative local verification pipeline for the CRNT-Lean campaign.
#
#   tasks/campaign/verify_all_local.sh [--quick]
#
# Every gate below MUST succeed for the pipeline to report PASS.  A gate that cannot
# run counts as a failure: the pipeline never records PASS on the strength of a
# command it did not actually execute.
#
# Gates
#   1  build         the core library `lake build +CRNT`
#   2  pins          regenerate `test/FieldMapAudit.lean` from `docs/field-map.md`
#                    and check that it does not drift from the committed file
#   3  tests         build the `test` library (this elaborates every `#guard_msgs`
#                    in the test suite, including the field-map and axiom audits)
#   4  exclusions    `scripts/check_exclusions.py` (ledger invariants)
#   5  imports       `scripts/check_imports.py`
#   6  stubs         `scripts/check_stubs.py` (hollow definitions)
#   7  frontier      build `+CRNTFrontier`; this target is a *ledger* and is
#                    historically expected to fail, so it is REPORTED, not gated
#   8  record        write a JSON result with the exact commit hash
#
# `--quick` skips gate 7.
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"
# Bound each Lean's internal thread pool: the campaign's CPU budget is spent on
# *processes*, not on threads inside a process.
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"

QUICK=0
[ "${1:-}" = "--quick" ] && QUICK=1

RESULTS="$ROOT/.campaign/results"
mkdir -p "$RESULTS"
RESULT="$RESULTS/verify_all.json"
LOG="$ROOT/.campaign/verify_all.log"

: >"$LOG"
GATES=()
FAILED=0

gate() {  # gate <name> <ok|fail> <detail>
  GATES+=("$1:$2")
  if [ "$2" = "ok" ]; then
    printf '  [ ok ] %s\n' "$1" | tee -a "$LOG"
  else
    printf '  [FAIL] %s -- %s\n' "$1" "$3" | tee -a "$LOG"
    FAILED=1
  fi
}

run_gate() {  # run_gate <name> <command...>
  local name="$1"; shift
  printf '=== %s ===\n' "$name" | tee -a "$LOG"
  if "$@" >>"$LOG" 2>&1; then
    gate "$name" ok ""
  else
    gate "$name" fail "see $LOG"
  fi
}

COMMIT="$(git rev-parse HEAD 2>/dev/null || echo unknown)"
DIRTY="$(git status --porcelain | wc -l | tr -d ' ')"

printf 'CRNT-Lean authoritative verification\ncommit: %s\ndirty files: %s\n' \
  "$COMMIT" "$DIRTY" | tee -a "$LOG"

# The full build must have exclusive access to the compilation budget: take every
# slot in the pool for the duration, so no worker's Lean elaboration can run
# alongside it and push the machine past its measured capacity.
POOL_SLOTS="$(tasks/campaign/lean_slot.sh acquire-all "${CRNT_SLOT_WAIT:-3600}")" || {
  echo "could not acquire the whole build pool" >&2
  exit 1
}
trap 'tasks/campaign/lean_slot.sh release-all >/dev/null 2>&1' EXIT
printf 'build pool: %s slot(s) held exclusively\n' "$POOL_SLOTS" | tee -a "$LOG"

run_gate build lake build +CRNT

# Regenerate the field-map pins and require that the committed audit file was in
# sync with `docs/field-map.md`.  A stale audit silently pins declarations that no
# longer exist, so this is a hard gate: if the regeneration changes the file, the
# audit was out of date, the file has now been regenerated, and it must be
# committed before the pipeline passes again.
mkdir -p .campaign
cp test/FieldMapAudit.lean .campaign/fieldmap_pins.before 2>/dev/null || true
if lake env python3 scripts/field_map_pins.py >>"$LOG" 2>&1; then
  if cmp -s .campaign/fieldmap_pins.before test/FieldMapAudit.lean; then
    gate pins ok ""
  else
    gate pins fail "test/FieldMapAudit.lean was out of date w.r.t. docs/field-map.md; it has been regenerated and must be committed"
    git diff --stat -- test/FieldMapAudit.lean >>"$LOG" 2>&1
  fi
else
  gate pins fail "scripts/field_map_pins.py failed"
fi

run_gate tests lake build test
run_gate exclusions python3 scripts/check_exclusions.py
run_gate imports python3 scripts/check_imports.py
run_gate stubs python3 scripts/check_stubs.py

if [ "$QUICK" = "0" ]; then
  if lake build +CRNTFrontier >>"$LOG" 2>&1; then
    gate frontier ok ""
  else
    gate frontier fail "the frontier ledger target does not build (reported, not fatal)"
  fi
fi

STATUS="PASS"
[ "$FAILED" = "1" ] && STATUS="FAIL"

python3 - "$RESULT" "$STATUS" "$COMMIT" "$DIRTY" "${GATES[*]}" <<'PY'
import json, sys, time
path, status, commit, dirty, gates = sys.argv[1:6]
rec = {
    "status": status,
    "commit": commit,
    "dirty_files": int(dirty),
    "gates": gates.split(),
    "verified_at": time.strftime("%Y-%m-%dT%H:%M:%S"),
}
with open(path, "w") as fh:
    json.dump(rec, fh, indent=1)
PY

printf '\nRESULT: %s  (commit %s)\n' "$STATUS" "$COMMIT" | tee -a "$LOG"
cat "$RESULT"
exit $FAILED

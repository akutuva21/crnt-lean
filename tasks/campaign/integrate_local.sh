#!/usr/bin/env bash
# Orchestrator-side integration of one or more verified worker modules.
#
#   tasks/campaign/integrate_local.sh <module-path> [<module-path> ...]
#
# Steps (orchestrator only — workers never run this):
#   1. forbidden-construct check (check_module.py);
#   2. private compile of the candidate and an axiom audit of the FRESH artifact
#      (verify_module_local.sh) — never the stale prebuilt olean;
#   3. `import` insertion into CRNT.lean (idempotent);
#   4. the authoritative local pipeline (build + field-map pins + tests + gates);
#   5. `git add` of the EXPLICIT paths only — never `git add -A`, which is how the
#      previous campaign accidentally staged a worker's unfinished source.
#
# It does NOT commit; the orchestrator reviews and commits.
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"

if [ $# -eq 0 ]; then
  echo "usage: $0 <module-path> ..." >&2
  exit 2
fi

for mod in "$@"; do
  if [ ! -f "$mod" ]; then
    echo "missing module: $mod" >&2
    exit 1
  fi
done

echo "=== 1. forbidden constructs ==="
python3 tasks/campaign/check_module.py "$@" || exit 1

echo "=== 2. private compile + axiom audit of the fresh artifact ==="
for mod in "$@"; do
  label="$(basename "$mod" .lean)"
  if ! tasks/campaign/verify_module_local.sh "$mod" --label "$label" \
       >/dev/null 2>&1; then
    echo "verification FAILED for $mod" >&2
    cat ".campaign/results/$label.json" >&2
    exit 1
  fi
  cat ".campaign/results/$label.json"
done

echo "=== 3. imports ==="
for mod in "$@"; do
  modname="${mod%.lean}"
  modname="${modname//\//.}"
  imp="import $modname"
  if ! grep -qxF "$imp" CRNT.lean; then
    python3 - "$imp" <<'PY'
import sys
imp = sys.argv[1]
path = "CRNT.lean"
lines = open(path).read().split("\n")
last = max(i for i, l in enumerate(lines) if l.startswith("import "))
lines.insert(last + 1, imp)
open(path, "w").write("\n".join(lines))
print("added:", imp)
PY
  else
    echo "already imported: $imp"
  fi
done

echo "=== 4. authoritative pipeline ==="
tasks/campaign/verify_all_local.sh || {
  echo "the authoritative pipeline FAILED; not staging anything" >&2
  exit 1
}

echo "=== 5. staging (explicit paths only) ==="
git add -- "$@" CRNT.lean test/FieldMapAudit.lean
git status --short
echo
echo "review the staged diff with: git diff --cached --stat"

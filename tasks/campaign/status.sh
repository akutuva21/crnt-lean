#!/usr/bin/env bash
# A one-shot status report for the campaign.
#
#   tasks/campaign/status.sh
#
# Reports the numbers the campaign has to keep accurate: active agents, active Lean
# compilations, the verification queue, the free build slots, the CPU and memory
# pressure, the swap usage, and the number of completed integrations.
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"

echo "=== CRNT-Lean campaign status ==="
echo "branch:  $(git rev-parse --abbrev-ref HEAD)  $(git rev-parse --short HEAD)"
echo "origin:  $(git log --oneline -1 origin/$(git rev-parse --abbrev-ref HEAD) 2>/dev/null | cut -c1-60)"
echo "dirty:   $(git status --porcelain | wc -l | tr -d ' ') file(s)"
echo

echo "-- agents --"
echo "opencode processes: $(ps aux | grep -c '[o]pencode')"
echo

echo "-- lean compilations --"
echo "running lean processes: $(ps aux | grep -c '[l]ean ')"
tasks/campaign/lean_slot.sh status 2>/dev/null | sed 's/^/  /'
echo

echo "-- verification results --"
if [ -d .campaign/results ]; then
  python3 - <<'PY'
import json, os
d = ".campaign/results"
rows = []
for f in sorted(os.listdir(d)):
    if not f.endswith(".json"): continue
    try:
        r = json.load(open(os.path.join(d, f), encoding="utf-8"))
    except Exception:
        continue
    rows.append((r.get("status", "?"), r.get("module", f), r.get("verified_at", "")))
for s, m, t in sorted(rows):
    print(f"  {s:5s} {m}")
print(f"  ({sum(1 for r in rows if r[0]=='PASS')} PASS, {sum(1 for r in rows if r[0]!='PASS')} not PASS, {len(rows)} total)")
PY
fi
echo

echo "-- machine --"
uptime
sysctl -n vm.swapusage
memory_pressure 2>&1 | tail -2
echo "top CPU consumers:"
ps aux | sort -k3 -rn | head -5 | awk '{printf "  %s%%  %s\n", $3, $12}'

#!/bin/zsh
# Integrate the modules produced by parallel agents into the main repository.
#
# Usage:
#   scripts/integrate_worktrees.sh <worktree>:<module-path> ...
#
# For each argument the module is copied from the worktree into the main
# repository and an `import` line for it is appended to `CRNT.lean` (if it is
# not already there).  The script then builds the library, so that a failure is
# reported immediately and no half-integrated state is left behind.
#
# Example:
#   scripts/integrate_worktrees.sh \
#     /tmp/crnt-wt-foo:CRNT/Dynamics/Foo.lean \
#     /tmp/crnt-wt-bar:CRNT/Algebra/Bar.lean
set -e

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

if [ $# -eq 0 ]; then
  echo "usage: $0 <worktree>:<module-path> ..." >&2
  exit 2
fi

added=()
for spec in "$@"; do
  wt="${spec%%:*}"
  mod="${spec#*:}"
  if [ ! -f "$wt/$mod" ]; then
    echo "missing: $wt/$mod" >&2
    exit 1
  fi
  cp "$wt/$mod" "$mod"
  imp="import $mod"
  if ! grep -qxF "$imp" CRNT.lean; then
    printf '%s\n' "$imp" >> CRNT.lean
  fi
  added+=("$mod")
done

echo "integrated ${#added[@]} module(s):"
printf '  %s\n' "${added[@]}"

lake build +CRNT

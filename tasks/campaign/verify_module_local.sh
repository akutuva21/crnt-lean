#!/usr/bin/env bash
# Local (no cluster) verification of a single CRNT module.
#
#   tasks/campaign/verify_module_local.sh <module-path> [--commit <sha>] [--label <id>]
#   tasks/campaign/verify_module_local.sh --self-test
#
# This is the local replacement for the cluster's `verify_module.sbatch`.  It keeps
# everything that was useful in the Slurm version -- private output directory, an
# axiom audit of every declaration, a JSON result record -- and removes everything
# that required Slurm, /scr, or a cluster home directory.
#
# It fixes the audit weakness of the cluster version.  The Slurm script compiled the
# candidate into `$WORKDIR/out/module.olean` and then audited `import $modname`,
# which resolved through the shared `LEAN_PATH` to the *stale* prebuilt `.olean` of
# the same module -- so a candidate carrying `sorry` could be audited against the
# clean previous build and pass.  Here the candidate is compiled to
# `$OUT/<module>.olean` and `$OUT` is placed *first* on `LEAN_PATH` for every
# subsequent `lean` invocation, so `import Foo` provably resolves to the freshly
# compiled artifact.  `--self-test` exercises exactly that failure mode with a module
# containing `sorry`: the audit must reject it.
#
# Exit status is 0 only when every gate passed: forbidden-construct check, compilation
# of the candidate, the audit of the fresh artifact, and the axiom-set test.
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"

MODULE=""
COMMIT=""
LABEL=""
SELF_TEST=0
while [ $# -gt 0 ]; do
  case "$1" in
    --commit) COMMIT="$2"; shift 2 ;;
    --label) LABEL="$2"; shift 2 ;;
    --self-test) SELF_TEST=1; shift ;;
    *) MODULE="$1"; shift ;;
  esac
done

RESULTS="$ROOT/.campaign/results"
mkdir -p "$RESULTS"

status="FAIL"
detail=""
declare -a GATES=()

gate() {  # gate <name> <ok|fail>
  if [ "$2" = "ok" ]; then GATES+=("$1:PASS"); else GATES+=("$1:FAIL"); fi
}

if [ -z "$MODULE" ] && [ "$SELF_TEST" != "1" ]; then
  echo "usage: $0 <module-path> [--commit sha] [--label id] | --self-test" >&2
  exit 2
fi

LABEL="${LABEL:-${MODULE##*/}}"
LABEL="${LABEL%.lean}"
WORK="$ROOT/.campaign/work/$LABEL"
RESULT="$RESULTS/$LABEL.json"
mkdir -p "$WORK"
build_log="$WORK/build.log"
axioms_out="$WORK/axioms.txt"
: >"$build_log"

finish() {
  local g=""
  for x in ${GATES[@]+"${GATES[@]}"}; do g="$g $x"; done
  python3 - "$RESULT" "$LABEL" "$MODULE" "$COMMIT" "$status" "$detail" "$g" <<'PY'
import json, os, sys, time
path, tid, module, commit, status, detail, gates = sys.argv[1:8]
rec = {
    "task_id": tid,
    "module": module,
    "commit": commit,
    "status": status,
    "detail": detail[:4000],
    "gates": gates.split(),
    "verified_at": time.strftime("%Y-%m-%dT%H:%M:%S"),
    "host": os.uname().nodename,
}
with open(path, "w") as fh:
    json.dump(rec, fh, indent=1)
PY
}
trap finish EXIT

if [ "$SELF_TEST" = "1" ]; then
  # The self-test module lives outside CRNT/ so it never enters the build glob.
  SRCROOT="$ROOT/.campaign/selftest"
  MODULE="Campaign/SelfTest/LocalVerifySelfTest.lean"
  LABEL="LocalVerifySelfTest"
  RESULT="$RESULTS/$LABEL.json"
  WORK="$ROOT/.campaign/work/$LABEL"
  mkdir -p "$WORK" "$SRCROOT/Campaign/SelfTest"
  build_log="$WORK/build.log"
  axioms_out="$WORK/axioms.txt"
  : >"$build_log"
  cat > "$SRCROOT/$MODULE" <<'EOF'
import Mathlib.Tactic
namespace Campaign.SelfTest
theorem selfTest_withSorry : True := by sorry
end Campaign.SelfTest
EOF
  detail="self-test: a module containing a sorry must be rejected"
  SRC_SHA="n/a"
else
  SRCROOT="$ROOT"
fi

# ---------------------------------------------------------------- source identity
if [ -f "$SRCROOT/$MODULE" ]; then
  SRC_SHA="$(shasum -a 256 "$SRCROOT/$MODULE" | awk '{print $1}')"
else
  detail="module not found: $MODULE"
  gate source FAIL
  exit 1
fi
gate source ok
if [ -z "$COMMIT" ]; then
  COMMIT="$(git rev-parse HEAD 2>/dev/null || echo unknown)"
fi
DIRTY=0
if [ "$SELF_TEST" != "1" ] && ! git diff --quiet -- "$MODULE" 2>/dev/null; then
  DIRTY=1
  detail="$detail [worktree differs from $COMMIT for $MODULE; sha256=$SRC_SHA]"
fi

# ------------------------------------------------------- forbidden construct check
if [ "${CRNT_SKIP_STATIC_CHECK:-0}" != "1" ] && \
   ! ( cd "$SRCROOT" && python3 "$ROOT/tasks/campaign/check_module.py" "$MODULE" ) >>"$build_log" 2>&1; then
  gate static-check FAIL
  if [ "$SELF_TEST" = "1" ]; then
    status="PASS"
    detail="self-test OK: the forbidden-construct check rejected the sorry-module"
    exit 0
  fi
  detail="forbidden construct: $(tail -c 1200 "$build_log")"
  exit 1
fi
gate static-check ok

# ------------------------------------------------------------------- compile slot
SLOT="$(tasks/campaign/lean_slot.sh acquire 3600)" || {
  detail="could not acquire a build slot"
  gate slot FAIL
  exit 1
}
gate slot ok
trap 'tasks/campaign/lean_slot.sh release "$SLOT" >/dev/null 2>&1; finish' EXIT

# --------------------------------------------------------------- shared LEAN_PATH
if [ ! -s "$WORK/leanpath.txt" ]; then
  ( cd "$ROOT" && lake env printenv LEAN_PATH ) >"$WORK/leanpath.txt" 2>/dev/null
fi
if [ ! -s "$WORK/leanpath.txt" ]; then
  detail="could not export LEAN_PATH (is the library built?)"
  gate lean-path FAIL
  exit 1
fi
DEPS="$(cat "$WORK/leanpath.txt")"
gate lean-path ok

modname="${MODULE%.lean}"
modname="${modname//\//.}"

# --------------------------------------------------- compile the candidate alone
# Compile into a scratch directory that is NOT on LEAN_PATH yet.
TMPOUT="$WORK/compiled"
rm -rf "$TMPOUT"
mkdir -p "$TMPOUT/$(dirname "$MODULE")"
OLEANTARGET="$TMPOUT/${MODULE%.lean}.olean"
if ! ( cd "$SRCROOT" && LEAN_PATH="$DEPS" lean -o "$OLEANTARGET" "$MODULE" ) >>"$build_log" 2>&1; then
  gate compile FAIL
  if [ "$SELF_TEST" = "1" ]; then
    status="PASS"
    detail="self-test OK: the sorry-module failed to compile as required"
    exit 0
  fi
  detail="compile failed: $(tail -c 2500 "$build_log")"
  exit 1
fi
if [ ! -f "$OLEANTARGET" ]; then
  gate compile FAIL
  detail="compile produced no artifact at $OLEANTARGET"
  exit 1
fi
OLEAN_SHA="$(shasum -a 256 "$OLEANTARGET" | awk '{print $1}')"
gate compile ok

# ----------------------------------------------------------------- axiom audit
# Lean's module resolution (Lean.Util.Path.findWithExt) picks the *first* search-path
# entry that contains a directory named after the module's ROOT package (`CRNT`), and
# then resolves *every* `CRNT.*` module under that entry.  A private output directory
# that merely contains `CRNT/` would therefore shadow the whole package and the
# dependency oleans would "not exist".  So the audit root is a mirror of the built
# package in which the candidate's artifact replaces the stale one; the mirror is
# symlinks, so the shared build directory is never written to.
PKGROOT=""
ROOTNAME="${MODULE%%/*}"
IFS=':' read -r -a _departs <<<"$DEPS"
for d in "${_departs[@]}"; do
  if [ -d "$d/$ROOTNAME" ]; then PKGROOT="$d"; break; fi
done
if [ -z "$PKGROOT" ]; then
  # The module's root package is not in the build (a brand-new package, or the
  # self-test module).  The audit root then holds just the candidate, and its
  # dependencies resolve from the ordinary search path.
  PKGROOT="$WORK/absent-package"
  mkdir -p "$PKGROOT"
fi
OUT="$WORK/auditroot"
rm -rf "$OUT"
mkdir -p "$OUT/$ROOTNAME"
( cd "$PKGROOT/$ROOTNAME" && find . -name '*.olean' -print0 ) | while IFS= read -r -d '' f; do
  mkdir -p "$OUT/$ROOTNAME/$(dirname "$f")"
  ln -sf "$PKGROOT/$ROOTNAME/$f" "$OUT/$ROOTNAME/$f"
done
RELPATH="${MODULE#"$ROOTNAME/"}"
RELPATH="${RELPATH%.lean}.olean"
rm -f "$OUT/$ROOTNAME/$RELPATH"
mkdir -p "$OUT/$ROOTNAME/$(dirname "$RELPATH")"
cp "$OLEANTARGET" "$OUT/$ROOTNAME/$RELPATH"
if [ ! -f "$OUT/$ROOTNAME/$RELPATH" ]; then
  gate axiom-audit FAIL
  detail="the fresh artifact was not installed in the audit root at $OUT/$ROOTNAME/$RELPATH"
  exit 1
fi
if ! python3 "$ROOT/tasks/campaign/audit_module.py" "$SRCROOT/$MODULE" "$OLEANTARGET" "$OUT" "$DEPS" "$modname" \
      >"$axioms_out" 2>"$WORK/audit.err"; then
  gate axiom-audit FAIL
  if [ "$SELF_TEST" = "1" ]; then
    status="PASS"
    detail="self-test OK: the axiom audit rejected the sorry-module ($(tail -c 200 "$WORK/audit.err" | tr '\n' ' '))"
    exit 0
  fi
  detail="axiom audit failed: $(tail -c 1500 "$WORK/audit.err")"
  exit 1
fi
gate axiom-audit ok

detail="$(cat "$axioms_out"); src_sha256=$SRC_SHA; olean_sha256=$OLEAN_SHA"
if [ "$DIRTY" = "1" ]; then
  detail="$detail; [uncommitted source]"
fi
status="PASS"
exit 0

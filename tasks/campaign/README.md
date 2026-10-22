# The CRNT-Lean 12-hour formalization campaign (2026-10-21)

This directory holds the orchestrator's infrastructure for the 12-hour campaign that formalized
as much of chemical reaction network theory as possible into the `crnt-lean` library.

## Starting point

| | |
|---|---|
| start commit | `3065e963124a04e0e4830ac2f320df8c16909ba8` |
| leaves | 90 (70 proved, 20 partial) |
| pinned declarations | 1020 |
| Lean / Mathlib | 4.34.0 / v4.34.0 (`lean-toolchain`, `lake-manifest.json` unchanged) |

## Files

| file | purpose |
|---|---|
| `WORKER_PROTOCOL.md` | the rules every theorem-proving worker follows |
| `registry.py` / `registry.json` | the machine-readable task registry (the orchestrator is the only writer) |
| `check_module.py` | rejects a candidate module that uses `sorry`, `admit`, a new `axiom`, `native_decide`, `unsafe` or `@[implemented_by]` (comments and strings are stripped first) |
| `integrate.sh` | the orchestrator's integration path: forbidden-token check, `import` insertion into `CRNT.lean`, re-elaboration, static gates, field-map pins |
| `update_field_map.py`, `update_field_map2.py` | fold the campaign's declarations into `docs/field-map.md` |
| `add_leaves.py` | add the new leaves (F16–F18, S22–S23, D21–D22) |
| `base_build.sbatch` | the one-time base build of the library on the cluster |
| `sync_build.sbatch` | the authoritative independent build + axiom audit on the cluster |
| `verify_module.sbatch`, `submit.sh` | per-module isolated verification jobs |
| `diag.sbatch` | the diagnostic used to find the cluster's `--mem`/address-space interaction |

---

# The 2026-10-22 campaign (local Mac)

The second campaign runs **entirely on one Mac** — no Slurm, no `/scr`, no cluster home, no SSH.
The starting point is the end of the first campaign, `298b1bb2df21577affc35ec14eb9378007f82540`
(99 leaves: 79 proved, 20 partial; 1245 pinned declarations; 59 new modules).

## Hardware profile and concurrency

| | |
|---|---|
| machine | Apple M5 Pro (15 logical / 15 physical cores, 24 GiB RAM) |
| swap | 3 GiB total; ~1.9 GiB in use at the start (stable) |
| load average | 2.15 at the start |
| disk free | 79 GiB |

The conservative starting limits are

```
R = max(4 GiB, 0.25 × M) = 6 GiB
B = min(6, max(1,P-2)=13, max(1,floor(0.6·L)=9), max(1,floor((M-R)/4)=4)) = 4   # Lean jobs
A = min(16, L=15, 2B+2=10, max(2,floor(0.4·M)=9)) = 9                          # MiniMax agents
```

`B` bounds *simultaneous CPU-intensive Lean processes*; `A` bounds *active MiniMax agents*.
The two are independent: model inference is remote, so an agent waiting for a build slot keeps
working (reading references, planning, searching the library) instead of burning CPU.

## The local verification infrastructure

| file | purpose |
|---|---|
| `lean_slot.sh` | a portable CPU semaphore.  Slots are plain directories created with `mkdir` (atomic on POSIX); each holds the owner's PID, so a slot whose owner died is reclaimed automatically.  macOS ships no `flock`, which is why this is not a lock file. |
| `lean_check.sh` | elaborate a file against the **already built** library, read-only, holding a slot.  This is what workers use; they never run `lake build`. |
| `verify_module_local.sh` | the local replacement for `verify_module.sbatch`.  Compiles the candidate into a private output directory and audits *that* artifact.  `--self-test` proves the audit is sound. |
| `audit_module.py` | discovers a module's **own** declarations from its own compiled `.olean` (`Lean.ModuleData.constNames`), then audits their axiom sets.  No source parsing, so namespaces, `instance`s and `private` declarations are handled exactly. |
| `verify_all_local.sh` | the authoritative pipeline: build → field-map pin regeneration and drift check → test library → exclusion/import/stub gates → frontier ledger → JSON record with the exact commit hash.  A gate that cannot run counts as a failure. |
| `registry2.json` | this campaign's machine-readable task registry. |

### The audit bug this campaign fixes

The cluster's `verify_module.sbatch` compiled the candidate into `$WORKDIR/out/module.olean` and
then audited `import $modname` **through the shared `LEAN_PATH`**, which resolved to the *stale*
prebuilt `.olean` of the same module.  A candidate carrying `sorry` could therefore be audited
against the clean previous build and *pass*.  The local script puts the private output directory
**first** on `LEAN_PATH` for every subsequent `lean` invocation, so `import Foo` provably
resolves to the artifact that was just built, and `--self-test` exercises exactly that failure
mode:

```
$ CRNT_SKIP_STATIC_CHECK=1 tasks/campaign/verify_module_local.sh --self-test
  → FORBIDDEN: Campaign.SelfTest.selfTest_withSorry depends on ['sorryAx']
  → status PASS  (the self-test's expectation was met)
```

### The field-map audit bug this campaign fixes

`scripts/field_map_pins.py` joined the quoted declaration name and the axiom clause without a
space, so every generated `#guard_msgs` docstring read

```
/-- info: 'CRNT.Network.source_mem_complexes'depends on axioms: [...] -/
```

and Lean's `#guard_msgs` rejected **all 1245 pins** with *"Docstring on `#guard_msgs` does not
match generated message"*.  The `test` library therefore **did not build** at the head commit.
The generator is fixed, the audit regenerated, and `lake build test` now succeeds.

## The cluster scripts

`verify_module.sbatch`, `submit.sh`, `base_build.sbatch` and `sync_build.sbatch` are **kept** for
the historical record.  They are not usable on this Mac (they need Slurm, `/scr` and a cluster
home directory) and the local campaign does not invoke them.  The useful parts — source
checking, integration, the task registry — are preserved in the local scripts above.

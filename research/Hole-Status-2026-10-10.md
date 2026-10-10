# Hole status — consolidated, evidence-backed

**Date:** 2026-10-10 · **Branch:** `resolve-holes` · **Worktree:** `tmp/holes-resolve`
**Supersedes for planning purposes:** `CURRENT_PROOF_HOLES.md` (stale — lists 7 holes that are
now down to 2) and the scattered route notes. This document states, for each hole, what is
machine-checked today, what is missing, and what is *known dead*.

## 0. Ground truth (reproduced in this worktree)

```
python3 research/scripts/measure.py
  holes = 2      hole_sites:
                  CRNT/Dynamics/HighCodimensionSiphonFace.lean:147
                  CRNT/Multistationarity/TrueChemistrySRCriterion.lean:9435
  frontier_mods = 868   scaffold_mods = 24   lean_lines = 142480   declared_axioms = 0
  gates: check_imports / check_stubs / check_undefined_names / check_exclusions  — all pass
  score = -1292
```

Both hole modules verified to compile in this worktree with **exactly one** `sorry` each:

| module | `checkmod.sh` result | time |
|---|---|---|
| `CRNT/Dynamics/HighCodimensionSiphonFace.lean` | `=== OK (sorry-warnings: 1)` | 65 s |
| `CRNT/Multistationarity/TrueChemistrySRCriterion.lean` | `=== OK (sorry-warnings: 1)` | 232 s |

### 0.1 Operational note — the worktree build fix (cost real time; worth recording)

`research/scripts/newagent.sh:26-29` symlinks `$WT/.lake/packages` → `$ROOT/.lake/packages`.
That step must happen **before** anything runs `lake env`. If `lake env` runs first it *creates a
fresh, unbuilt* `.lake/packages` in the worktree, `checkmod.sh` then resolves that instead of the
shared cache, and every module fails with

```
error: unknown module prefix 'Mathlib'
```

with `No directory 'Mathlib' in the search path entries: …`. This is not a source error and it is
not a broken toolchain. Fix:

```sh
rm -rf .lake/packages && ln -s /Users/akutuva/Documents/Proofs/crnt-lean/.lake/packages .lake/packages
```

## 1. Audit verdict — both holes are faithful and non-vacuous

Independently audited (read-only, source-traced). Both statements survive scrutiny:

**Hole A — FAITHFUL, NOT VACUOUS.** Reached from exactly one call site,
`GlobalAttractorTheorem.lean:1555-1557` inside `complexBalanced_genuinePermanent` (:1490). All 18
hypotheses are supplied with identical mathematical content at every step. The single
`False.elim` at :1521 sits in the *facet* branch and does not feed the hole; the hole is reached
only in the `negbranch` where `hfacet : ¬(…)`. Non-vacuity is machine-checked:
`CRNT/Examples/CodimTwoFaceModel.lean:337` (`codimTwoModel_all_but_hsol`) satisfies **17 of the 18**
hypotheses jointly with the conclusion FALSE, and `codimTwoModel_not_derivable_without_hsol` proves
`hsol` is the only load-bearing hypothesis. So the theorem is genuinely hard, not vacuously true.

**Hole B — FAITHFUL, NOT VACUOUS.** Three consumers (`:9444`, `:9452`, `:9460`) pass
`hsep`/`hflow`/`hSR` through verbatim, bridged via the hole-free
`StrongConcordance.lean:277`. Caveat: the hypothesis class `hsep ∧ hflow ∧ hSR` is non-empty but
**degenerate** — a network whose channels are all canonical inflows satisfies all three with `hSR`
vacuous. (DEAD-ENDS B-26 is a search result, not a refutation.)

**Correction to a widely-repeated claim.** The round-1 refutation (`refutation-report-A.md` V1)
shows `_of_upperRegion` and its whole family are inconsistent with boundary-ω-point data. That
inconsistency **does not touch the hole**: `UpperRegionFloorRefutation.lean:107` needs **seven**
hypotheses the hole does not have (`hε hopenLow hopenUp hdisj hsplit hx₀Z hfloor`). The
inconsistency belongs to the dead criteria only.

## 2. Hole B — residue reduced to ONE named proposition

The `sorry` is **already discharged** by a proved, axiom-clean theorem that cannot be reached:

`CRNT/Multistationarity/TrueSRCycleSpeciesDegree.lean:239` `no_escape_from_cycleSpecies` — its
hypotheses match the residue context at the `inl s0` branch exactly.

Hence **Hole B ⟺ `no_offCycle_negFlux`** (`TrueSRCycleSpeciesDegree.lean:202`):

```lean
def no_offCycle_negFlux (α : N.fullyOpen.R → ℝ) (σ : S → ℝ) (C : N.TrueSRCycle n) : Prop :=
  ∀ (b : Fin n) (ρ : N.TrueReaction), ¬ C.HasReaction ρ →
    0 ≤ N.trueInternalClassFlux α ρ (C.species b) * σ (C.species b)
```

> no off-cycle reaction class drains any cycle species

with the negation extracted by a proved theorem (:287):

```lean
theorem exists_offCycle_negFlux_class (hoff_neg : ¬ no_offCycle_negFlux α σ C) :
    ∃ (b : Fin n) (ρ : N.TrueReaction), ¬ C.HasReaction ρ ∧
      N.trueInternalClassFlux α ρ (C.species b) * σ (C.species b) < 0
```

This is precisely the "off-cycle species/class with negative flux at a cycle species" that
`holeB-steering.md` and `BRIEF-B.md` §B.2 named as the A.6 Case-2 source-block datum — now a
single machine-checked `Prop` with a proved decomposer rather than prose.

### Two separable obstacles

| # | obstacle | nature |
|---|---|---|
| **1** | **Import cycle.** `TrueSRCycleSpeciesDegree.lean:1` imports `TrueChemistrySRCriterion`, but the `sorry` is *inside* that file, so the discharger cannot be applied. It needs `trueInternalClassFlux`, `nonAdjacent_cycleClassFlux_eq_zero`, `TrueInternalAggregateCausalEdge`, `ActiveAggregateTrueReaction`, all currently `private` to TSC. | **mechanical Lean work** — lift those into a module TSC itself imports, inverting the cycle |
| **2** | **Proving `no_offCycle_negFlux`** from `hsep` + `hSR` + `C.Even` + `hcausal`. | **the open mathematics** |

Obstacle 1 alone reduces the hole to a single proposition; it does **not** close it.
Obstacle 2 is the genuine frontier: it is the Shinar–Feinberg §5.5/§A.3 source-block analysis.
`TrueSRCycleSpeciesDegree.lean:200` records that the analogous `hrest` "cannot be discharged (its
natural instance is refuted by `hattachment`)".

### Orphaned A.6 machinery (changes what a next attempt should build on)

* `CRNT/Multistationarity/TrueSREarCase1.lean` and `TrueSREarCase2.lean` **are in `master`**, and
  `TrueSREarCase2.lean` mentions `SignDirected` 19 times — i.e. blocker 1 of `holeB-steering.md` §9
  looks already addressed there.
* But **nothing imports `TrueSREarCase2`**, and `TrueChemistrySRCriterion.lean` imports neither.
  The A.6 Case-1/Case-2 ear modules are **orphaned** — they cannot reach the residue.
* `CRNT/Graph/EarNonseparability.lean` (828 lines) and `CRNT/Graph/RelPathAppend.lean` (186 lines)
  exist only on the diverged `backup-fig8` branch and are **absent from `master`**.
  `backup-fig8` is 75 commits ahead / 7 behind `master` (merge-base `ef8048c`) and is an *older*
  overall state (4 sorries in `HighCodimensionSiphonFace.lean` there vs 1 in `master`) — so it is a
  source of specific files, not a branch to merge.

## 3. Hole A — the missing object is now precisely located

Hole A is Craciun v3 Thm B: build an exhaustive family of zero-separating hypersurfaces over a
complete pointed fan. Prior framing ("Mathlib has no polytope/face-lattice/normal-fan API, so this
is hopeless") is **out of date**. Mathlib and this repo now provide much of it:

| capability | where | status |
|---|---|---|
| dual cone, bipolar involution | `PointedCone.dual`, `dual_dual_flip_dual` (Mathlib `Geometry/Convex/Cone/Dual.lean`) | EXISTS |
| cone duality is a lattice antitone | `dual_anti`, `dual_hull`, `DualFG` (Mathlib `Cone/DualFinite.lean`) | EXISTS |
| cone faces | `PointedCone.IsFaceOf`, `Face C` lattice (Mathlib) | EXISTS |
| repo dual cone + bipolar | `CRNT/Geometry/PolyhedralFan.lean` — `coneDual`, `cone_dual_dual`, Farkas `exists_mem_coneDual_of_notMem`, Newton polytope | EXISTS |
| exposed-face antitone under domination | `CRNT/Geometry/ConeFaceIncidence.lean:110` `exposedFace_antitone` | EXISTS |
| dually-finite cells on a fan | `CRNT/Geometry/FanRefinement.lean:981` `HasDualFGCells`, `properExposedFace_hasDualFG`, `coneDual_intersection_decomp_of_dualFG` | EXISTS |
| well-founded §7 face-dependency induction | `FanRefinement.lean` — `ProperExposedFaceDependency`, `oneBitFanFaceDependency_wellFounded`, `oneBitFanFaceDependency_induction` | EXISTS |
| forward-invariance engine | `CRNT/Geometry/PolyhedralBarrier.lean:317` `forwardInvariant_barrierSublevel` | EXISTS |

### 3.1 The `backup-fig8` port

| file | source | result |
|---|---|---|
| `research/drafts/portfig8/RelPathAppend.lean` (186 ln) | `backup-fig8:CRNT/Graph/RelPathAppend.lean` | **ports CLEAN** against master's API — `=== OK (sorry-warnings: 0)` in 48 s |
| `research/drafts/portfig8/EarNonseparability.lean` (828 ln) | `backup-fig8:CRNT/Graph/EarNonseparability.lean` | **does NOT port** — 11 errors, all one shape (below) |

`RelPathAppend.lean` is a clean win: `appendPath` plus its `start`/`end`/`noRepeat` lemmas, built on
`CRNT.RelPath`, which `TrueChemistrySRCriterion.lean` already imports.

`EarNonseparability.lean` fails on **walk-support API drift**: master's `CRNT.RelPath` walk
membership no longer matches what the branch expects. Every error has the same shape —

```
hblk (…) has type (∀ x ∈ (…).support, x ∈ C) → v ∈ (…).support
but is expected to have type v ∈ (…).support
```

i.e. a support-containment hypothesis is now a function of the vertex rather than applied
positionally. It is a mechanical repair (10 sites, lines 523–826), not a mathematical gap — but it
is real work, and note the file imports `TrueChemistrySRCriterion`, so it carries the **same import
cycle** as `TrueSRCycleSpeciesDegree.lean` and is equally unusable at the residue until §2 obstacle 1
is resolved.

### 3.2 The one hypothesis that is the whole of Hole A

The cone-wide dominance relation Hole A needs —

> a family `n C` indexed by the cones, with `⟪n C, x⟫ ≥ ⟪n C', x⟫` for all `x ∈ C`

— appears in the tree **exactly once**, as an *unused hypothesis* of
`ConeFaceIncidence.exposedFace_antitone:110`. It has never been packaged as a family over cones and
never proved. That packaging plus its existence theorem is the whole of Hole A's residue.

Two cautions:

* `CRNT/Geometry/CraciunV3BlueprintScales.lean` is **nearly empty** — exactly two theorems, both
  pure real-order list-splitting, importing only `Mathlib.Basic.Real.Basic` /
  `Data.Fintype.Basic` / `Tactic.Linarith`, and connected to **no other CRNT module**. Despite its
  name it contains **no δ-slack and no scale-hierarchy object**. Do not assume the §7 scales exist.
* `Fan E := Finset (ProperCone ℝ E)` (`ToricFan.lean:50`). There is **no** `Pointed`/`Complete`/
  `Rational` cone structure and **no lattice structure on a fan**. Completeness is derived in
  `FanFaceLattice.lean` from `IsPolyhedralFan`, not native.
* Every *geometric datum* the barrier engine consumes — normals `n`, levels `b`, `R`, `R'`,
  `hstart`, `hm`, `hregime` — is an unbuilt assumption, and `hsep` in that family is machine-refuted
  inconsistent. The descent/trapping half is fully built; the feeding half is not.

## 4. Known dead — do not re-walk

* **`_of_upperRegion` and the whole packaged family** (`blueprintData`, `selfConsistent_normals`,
  `convex_tiles`, `tiled_faceCores`, `faceRelevantCore`, `toric_blueprint`, `toric_halfspace`, and
  everything routing through `_of_coordinate_floors` with `T = S`). Supplying their inputs buys
  `False`. `CRNT/Geometry/ConvexBarrierObstruction.lean` independently kills the convex single-barrier
  route in dim ≥ 3.
* **`hfloor` on a region.** Machine-checked inconsistent (`UpperRegionFloorRefutation.lean:107`).
* **SS-parity steering (Route D).** Refuted and landed: `TrueSREdge.Connects` forces orientation,
  so the edge `endpoint` is a function of the vertex pair
  (`aggregateAdj_edge_endpoint_forced`, `:8322`), and `ssNumCPairs P % 2` is determined, not free.
* **`hSR.2` for species→species overlaps.** No `False`-producer in `CRNT/` derives `False` from two
  even `TrueSRCycle`s sharing only a species→species path; the SS layer never reaches `hSR.2`.
* **Removing `hsep` from Hole B.** Provably false; `CRNT/Examples/TrueSRNetCoeffCounterexample.lean`.

## 5. Honest status

Neither hole was closed. Both were **faithful and non-vacuous**, so neither was closable by a tactic
or a statement weakening — which is also why no such shortcut was taken.

What was achieved:

* ground truth reproduced and both baselines verified compiling in a fresh worktree;
* the `.lake/packages` worktree build failure diagnosed and documented (§0.1) — it silently blocks
  all work in any new worktree;
* Hole B reduced from a 200-line in-file residue to **one named proposition** with a proved
  decomposer, and its remaining work split into a mechanical half and a mathematical half;
* Hole A's residue localised from "we need polytope theory" to **one unused hypothesis at
  `ConeFaceIncidence.lean:110` that needs packaging as a family**;
* `CRNT/Graph/RelPathAppend.lean` ported from `backup-fig8`: compiles clean against `master`, 0 sorries.

In-flight work in `research/drafts/`: the cycle-inversion feasibility analysis, an exact-arithmetic
search for a counterexample to `no_offCycle_negFlux`, the deferred block/end-block/ear-decomposition
theory from `SourceBlocks.lean`, and the polar/face-duality layer for Hole A.

**The honest bottom line.** Both holes bottom out in mathematics that has not been written yet —
the Shinar–Feinberg source-block analysis (Hole B) and the Craciun v3 toric hypersurface
construction (Hole A). The infrastructure around both is in better shape than the older route docs
suggest. Neither is a "missing lemma" problem.
# Cross-branch status — 2026-09-19

For the parallel branch. Everything below was confirmed by elaborating against
`leanprover/lean4:v4.31.0` with the supplied `mathlib4-4.31.0` and the prebuilt cache.
Nothing here is an estimate.

## Current state

| metric | value |
|---|---|
| `sorry`/`admit` lines | **286** across 98 modules |
| frontier ledger | **185** (was 201) |
| verified core (`import CRNT`) | **520 modules**, elaborates with zero diagnostics |
| four gates | all PASS |
| theorems/lemmas | 4687 — PROVED 3514, UNCHECKED 895, SORRY 278 |

Your 290 and our 286 agree closely; the residue is line-vs-declaration counting.

## Read this first: `UNCHECKED` is the number nobody was tracking

**895 theorems/lemmas have no `sorry` but sit in modules that have never elaborated, so Lean
has never seen their proofs.** Treat them as unproved. This matters concretely:

* `shinarFeinberg_pinnedRatioAt_via_linkageScalars` (`Design/ShinarFeinbergCrossClass`) reads
  `H.toShinarFeinbergHypotheses`, `H.deficiencyOneHypotheses`, `H.c_nonterminal`,
  `H.d_nonterminal` — **none of those fields exist**. `StandardShinarFeinbergHypotheses`
  (`Design/ACRStandard.lean:61`) is a standalone struct with `nonTerminalC`/`nonTerminalD` and
  no `extends`. We cleared four blockers to get that file to elaborate, and it failed on the
  missing fields. Fixing the struct is mechanical and is the real prerequisite.
* `nonterminal_complex_detects_deficiency_coordinate`
  (`Deficiency/DeficiencyOneLinkageScalars`) was **vacuous**: its conclusion was
  `∃ α, α ≠ 0 ∧ v = α * d + (v - α * d)`, an instance of `a = b + (a - b)`, true for every
  `α`. Proved with `α := 1` and `ring`; none of its hypotheses were used, so nonterminality
  played no role despite the name. Do not rely on that name for mathematical content.

Generated index: `docs/theorem-index.md` (`scripts/decl_index.py --build`).

## Merge protocol — please use it

`scripts/compare_tree.py` diffs two trees and **elaborates both versions of every differing
file** under an identical `LEAN_PATH` and identical dependency `.olean`s, adopting only where
the other side is strictly better on `(errors, holes)`. Testing a file inside its own tree is
not comparable.

```
python3 scripts/compare_tree.py --other /path/to/tree --verify          # measure
python3 scripts/compare_tree.py --other /path/to/tree --verify --port   # adopt
```

**Known flaw, guard against it:** a module failing at *import* time reports only 1 error while
hiding everything behind it. That caused us to adopt `PlanarSectionCoordinates` on a measured
`1` that was really `12`. Do not adopt when diagnostics contain
`object file ... does not exist`; build deps and re-measure.

### Results of merging your branch (736 files: 681 identical, 45 differing)

**Adopted from you — 7, all verified.** Thank you, these were real unblocks:

| module | ours was | yours |
|---|---|---|
| `Deficiency.ExactSequence` | 18 err, 1 hole | **0, 0** |
| `Design.Localization` | 5 err, 1 hole | 0, 0 |
| `Kinetics.GeneralizedNondegeneracy` | 4 err, 1 hole | 0, 0 |
| `Design.EmergentCycles` | 4 err, 1 hole | 0, 0 |
| `Equilibria.TreeConstantKernelBasis` | 3 err, 1 hole | 0, 0 |
| `Equilibria.TreeConstantBinomials` | 2 err, 1 hole | 0, 0 |
| `Subnetwork.EmbeddedNetwork` | 0 err, 1 hole | 0, 0 |

`ExactSequence` and `TreeConstantBinomials` were the two highest-leverage one-hole roots
(~20 downstream modules each).

**Please re-pull before touching these — ours currently measures better:**

| module | ours | yours |
|---|---|---|
| `Oscillation.VassenaContinuation` | **30 err** | 38 |
| `Oscillation.VassenaCriteria` | **0** | 4 |
| `Flux.Elementary` | **0** | 3 |
| `Reduction.Intermediates` | **0** | 2 |
| `Flux.Cone` | **0** | 1 |
| `Reduction.SingleIntermediateElimination` | **6** | 8 |
| `Translation.LinearConjugacy` | **3** | 5 |
| `Translation.SourceComplexes` | **13** | 16 |
| `Kinetics.GeneralizedNetwork` | **4** | 5 |
| `Geometry.ConservativeCompatibility` | **4** | 5 |
| `Deficiency.TerminalKernelFaces` | **1** | 2 |
| `Equilibria.DetailedBalanceToric` | **5** | 6 |
| `LinearAlgebra.OrientedMatroidNondegeneracy` | **2** | 3 |

`VassenaContinuation` and `VassenaCriteria` are the ones to note — both were reported as
compiling cleanly but measure worse here. Most of the rest are cases where our automated
auto-fix pass overtook hand repairs, which is why re-pulling first saves you effort.

## Findings that will save you time

**`section` as a struct field — root cause of a large "invalid field" cluster.** FOUR
structures declared a field literally named `section`: `ReturnMapFamilyPersistence:34`,
`ScalarReturnMapFamilyPersistence:27`, `FloquetPersistenceGeneral:34`,
`PlanarReturnOrdering:30`. `section` is a Lean *command* keyword, so the parser reads the
field declaration as a `section` command and the whole structure is never created — the error
then surfaces far away as "invalid field" on unrelated names. Renaming the field to
`xsection` (declarations, instance assignments, unqualified in-struct uses, and every
`.section` projection) took `ReturnMapFamilyPersistence` from **28 errors to 0**.
`Dynamics/HopfRealizes` uses a distinct `.section'` that builds — leave it alone.

**`Phase2` was the wrong type.** `abbrev Phase2 := Fin 2 → ℝ` cannot work: `TransversalSection`
is stated over `InnerProductSpace ℝ E` and uses the inner product essentially, but the pi type
carries the sup norm, which is not induced by any inner product — so the "missing
`InnerProductSpace ℝ Phase2` instance" can never exist. Now
`abbrev Phase2 := EuclideanSpace ℝ (Fin 2)`. Ripple is mechanical: vector literals need
`WithLp.toLp 2 ![...]` (Lean inserts the `ofLp` coercion but cannot wrap the result back).
This unblocked four consecutive Planar gates.

**Consequence of that retype:** on `EuclideanSpace`, `⟪x, y⟫_ℝ` needs **`PiLp.inner_apply`** in
the simp set, not `RCLike.inner_apply` alone — the inner product routes through the `PiLp`
layer first.

**Notation scope.** `⟪x, y⟫_ℝ` lives in the **`InnerProductSpace`** scope, not
`RealInnerProductSpace` (which gives the unsuffixed `⟪x, y⟫`). Without the open the bracket is
not a valid token, so it appears as a bare `expected token` **parse** error that hides every
later defect in the file. 36 files use it; 8 were missing the open.

**Stale mathlib paths / near-misses in 4.31:**
* `Mathlib.Data.Matrix.Notation` → `Mathlib.LinearAlgebra.Matrix.Notation`
* `Finset.eq_empty_iff_forall_not_mem` → `Finset.eq_empty_iff_forall_notMem`
* `map_cluster_pt_iff` → `mapClusterPt_iff_frequently`
* `IsClosed.isCompact_of_isBounded` does not exist → `Metric.isCompact_of_isClosed_isBounded`
  (takes both facts explicitly, lives in the `Metric` namespace)
* `nonneg_of_mul_nonneg_right` → `mul_nonneg_iff_of_pos_right`
* `Quotient.mk''` takes the setoid as an **instance**; `stronglyLinkedSetoid` is a plain `def`,
  so write `Quotient.mk N.stronglyLinkedSetoid c`, and `Quotient.sound (s := ...)`
* `congrField` is `subst`-defined, so `change` cannot see through it — use
  `congrField_orbit` etc.
* `noncomputable theorem` is always an error (theorems emit no code)
* `∑ x in s` → `∑ x ∈ s`
* HANDOFF §2.2 is **wrong**: a `.olean`-only cache imports fine.

## Statements that are FALSE or vacuous as written

These need restating, not proving. We agree with you on the first two.

1. **`OrientedMatroidNondegeneracy`** — not true under its current witness definition: a
   nonzero witness with no positive coordinates makes the positive-block covering condition
   vacuous. Fix: require nonempty positive support. **We independently reached your
   conclusion.** Ours is at 2 errors, yours 3; neither compiles. Worth one of us finishing —
   say which.
2. **`Translation/SourceComplexes`** — targets the obsolete `N.ReactionTranslation`; needs an
   API migration, not a proof. Agreed.
3. **`complexBalanced_iff_toricLeaf`** (`Equilibria/GeneralizedComplexBalanceToric`) — false
   as written. The forward direction needs `x.Positive`, but `IsComplexBalanced` is
   `∀ c, inflow c = outflow c`, carrying no positivity (the zero state satisfies it
   vacuously). That `sorry` was unfillable. Now takes `(hx : x.Positive)` explicitly.
4. **`Dynamics.TierStrictUpwardPartner`** — goal false under its own hypotheses.

## Shinar–Feinberg: the chain is fully mapped, one theorem open

`shinarFeinberg_pinnedRatioAt` ← `standardShinarFeinberg_crossClassRatioPinned`
← `logMonomialRatio_eq_of_nonterminal_SF_pair` ← `nonterminal_linkageScalars_eq`.

Verified progress inside `nonterminal_linkageScalars_eq`:
* **same linkage class — DISCHARGED.** `by_cases hcls : N.classOf c = N.classOf d` then
  `rw [hcls]`, since the goal is an equality of *class* scalars and
  `logMonomialRatio_eqOn_linkageClass` already gives constancy of `Φ` on a class.
* **distinct classes — open**, and now reduced to `x s = y s`.

The reduction is an **iff** (`crossClassRatio_eq_iff_robust`, `Design/ACRCrossClass.lean:118`,
which we deduplicated down to `Deficiency/LogMonomialRatio.lean` so the `Deficiency/*` side
can reach it without importing `Design/*`). So the cross-class coupling lemma and ACR at `s`
are **the same statement** — meaning any route through `CrossClassRatioPinned`
(`ACRUnconditional`, `ACRCrossClass`, `shinarFeinberg_ACRAt`) is **circular by construction**.
That is very likely why this chain has stalled.

Everything proved gives `Φ` constant *within* a class only:
`logMonomialRatio_const_of_deficiencyZeroClass`, `logMonomialRatio_eqOn_deficientClass`,
`logMonomialRatio_eqOn_linked`, and `proportional_of_restrictedKineticImage`
(`MultiClass.lean:114` — sorry-free and building, but concluding `Ψx = K·Ψy` on the deficient
class θ **only**). The viable route is deficiency-one structure theory: `h.oneTerminal`,
nonterminality of both complexes, uniqueness of the deficient class
(`deficientLinkageClass`, `linkageDeficiency_eq_zero_of_ne_deficientClass`, both proved).
The step to find is one that crosses from a deficiency-**zero** class to the deficient class.

## Suggested split so we don't collide

Ours next:
* `canonicalSectionPoint_scalar` (`Oscillation/PlanarSectionCoordinates`) — 4 errors, one
  theorem, the surjectivity direction; last thing gating the Planar chain.
* `Design/ShinarFeinbergTreeFormula` — five of the 22 missing-API names live here
  (`CrossLinkageTreeRatioPinned`, `robustExponent`, `sameLinkageACRValue`,
  `sameLinkage_ACR_treeConstant_equation`, `weaklyReversible_of_complexBalanced`); one
  coherent design job.

Good for you, non-overlapping:
* Extending `StandardShinarFeinbergHypotheses` to carry a `ShinarFeinbergHypotheses` plus the
  deficiency-one hypotheses (mechanical, unblocks `ShinarFeinbergCrossClass`).
* `Oscillation.FloquetOrbitalStability` (30 errors) and `Deficiency.DeficiencyOneMonotonicity`
  (missing `DeficiencyOneBranchStrictlyMonotone`, `DeficiencyOneScalarBranch`).
* `OrientedMatroidNondegeneracy`, if you want it — you were already mid-correction.

Please don't count a module as done until its `.olean` exists; `UNCHECKED` is how 895
statements got into this state.

## The 22 names declared nowhere in the tree

Checked every unresolved name against a map of all declarations: **all 22 are invented — zero
are missing imports.** So `invalid-field` / `unknown-ident` is entirely
"written against an API that does not exist", not an import problem.

`BranchPeriodicTrajectory` (now built), `CrossLinkageTreeRatioPinned`, `robustExponent`,
`sameLinkageACRValue`, `sameLinkage_ACR_treeConstant_equation`,
`weaklyReversible_of_complexBalanced`, `DeficiencyOneBranchStrictlyMonotone`,
`DeficiencyOneScalarBranch`, `DifferentiablyMonotonicAt`, `LocalC1SensitivityBranch`,
`TransverseFloquetSectionData`, `ReactionTranslation`, `toShinarFeinbergHypotheses`,
`conservationCoordinates_eq_of_stoichCompatible`,
`stoichCompatible_iff_conservationCoordinates_eq`,
`concordanceKineticsRealization_noninjective`,
`exists_positive_kineticKernel_of_weaklyReversible`, `returnMap_eq`,
`eventually_field_ne_zero`, `section`, `R`, `isCompact_of_isBounded`.

## Scripts (all in `scripts/`)

| script | purpose |
|---|---|
| `decl_index.py` | generated declaration index; `--like` duplicate check, `--dups`, `--open` |
| `triage.py` | classify failures by defect class; `--apply` batch-fixes the safe ones |
| `batch_build.py` | resumable budgeted build driver (a command caps at ~300 s here) |
| `promote.py` | atomic ledger promotion with all four gates and **rollback** |
| `compare_tree.py` | cross-tree merge, Lean-verified |
| `dump_sorries.py` | every `sorry` with its real statement |
| `find_transferable.py` | normalized-statement match for sorried-with-a-proved-twin |
| `promotable.py`, `rank_targets.py` | eligibility and leverage ranking |
| `zdec.py` (repo root) | ctypes zstd streaming — `zstd` is absent, network off |

Standing pipeline:
`triage --apply` → `batch_build --retry-all` → `promote --all` → `decl_index --build`.

Full detail in `docs/CHECKLIST.md` and `docs/session-addendum.md`.

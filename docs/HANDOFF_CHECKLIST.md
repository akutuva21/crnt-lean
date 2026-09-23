# CRNT-Lean Handoff Checklist

Snapshot: 2026-09-20. Read `../README_PROGRESS.md` first for the mathematical overview.

## Mission

The long-term goal is to formalize essentially all of Chemical Reaction Network Theory in Lean 4, while keeping three categories distinct:

1. **Established CRNT mathematics that is not yet formalized** — formalization debt.
2. **Lean/API/build debt** — the mathematics is already encoded or understood, but source does not currently elaborate or has not been freshly promoted.
3. **Research-frontier mathematics** — genuinely open statements or new deductions exposed by the formalization program.

Do not turn category 3 into an axiom or placeholder just to make the library green.

## Current trust boundary

- [x] Lean 4.31.0 / Mathlib 4.31.0 environment supplied.
- [x] Stable `import CRNT` is statically isolated from all known hollow definitions.
- [x] `scripts/check_imports.py` passes.
- [x] `scripts/check_stubs.py` passes against the current baseline.
- [x] `scripts/check_undefined_names.py` passes.
- [x] `scripts/check_exclusions.py` passes.
- [x] 548 CRNT modules are reachable from the stable umbrella.
- [ ] Full fresh 549-module umbrella rebuild completed in this packaging session. It did **not** finish within the execution window.
- [ ] Frontier is empty. It is not: 160 modules remain in `scripts/unverified_modules.txt`.
- [ ] Repository has zero proof holes. It does not: 163 `sorry`/`admit` occurrences remain across 61 modules; the stricter stub checker reports 63 hollow declarations.

## Recently completed / promoted work

- [x] Decomposition rank independence and rank-additivity equivalences.
- [x] Deficiency additivity consequences.
- [x] Cycle exact sequence.
- [x] Wegscheider generators and deficiency quotient layer.
- [x] Deterministic MaxRPA charge identity.
- [x] MaxRPA integrator results.
- [x] Stochastic MaxRPA counterparts.
- [x] Canonical Shinar--Feinberg pinned-ratio / ACR kernel.
- [x] Conservative compatibility-class compactness machinery.
- [x] Generalized cycle exact sequence and generalized deficiency comparison.
- [x] Stochastic absorbing/conservative-class infrastructure.
- [x] Static frontier/trust-boundary gates.

## Repaired but still requiring fresh promotion/verification

These have no explicit `sorry` in source but must not be called verified until their exact dependency closure and an immediate dependent compile:

- `CRNT.Algebra.SteadyStateIdeal`
- `CRNT.Algebra.DeficiencyIdeal`
- `CRNT.Algebra.PositiveTorusIdeals`
- `CRNT.Deficiency.TerminalKernelDimension`
- `CRNT.Deficiency.TerminalKernelCone`
- `CRNT.Deficiency.TerminalKernelFaces`
- `CRNT.Equilibria.BoundarySiphon`
- `CRNT.Equilibria.GeneralizedTreeConstantCriterion`
- `CRNT.Equilibria.GeneralizedComplexBalanceToric`
- `CRNT.Equilibria.TreePotentialIntegration`
- `CRNT.Kinetics.GeneralizedDeficiencyZeroProof`
- `CRNT.Stability.RobustLyapunov`
- `CRNT.Theorems.DeficiencyZero.Characterization`
- `CRNT.Theorems.DeficiencyZero.TreeConstantConstruction`
- `CRNT.Theorems.DeficiencyZero.TreeConstantProofComplete`

The complete source-hole-free frontier list is `SOURCE_HOLE_FREE_FRONTIER.md` (99 modules).

## Highest-priority next proofs

### P0 — Directed Matrix--Tree / tree constants

- [ ] Prove and integrate `CRNT.Equilibria.TreeConstants.treeConstant_kineticKernel`.
- [ ] Compile `TreeConstants.lean` from source.
- [ ] Compile an immediate tree-constant/deficiency-zero consumer.
- [ ] Promote the affected dependency cone only after both succeed.

Why first: one classical combinatorial theorem unlocks much of the deficiency-zero/complex-balance branch.

The intended proof is a weight-preserving root-rotation bijection between decorated arborescences. Earlier sessions had scratch-level progress on forward/inverse surgery and weight matching, but that proof is **not present in this checkout**.

### P0 — Cheap frontier promotion

- [ ] Work bottom-up through the 99 source-hole-free frontier modules.
- [ ] Fix API/universe/elaboration errors only where compiler output requires it.
- [ ] Promote each module after compiling it and a downstream consumer.

Immediate known blocker: `CRNT.Oscillation.VassenaContinuation` currently fails at the two diagonal-scaling witness lemmas with universe/type mismatches.

### P1 — Classical deficiency-one chain

- [ ] `CRNT.Deficiency.DeficiencyOneLinkageScalars`
- [ ] `CRNT.Deficiency.DeficiencyOneMonotonicity`
- [ ] `CRNT.Theorems.DeficiencyOne.DegreeExistence`
- [ ] `CRNT.Theorems.DeficiencyOne.WeaklyReversibleExistence`
- [ ] `CRNT.Theorems.DeficiencyOne.Theorem`

The Shinar--Feinberg pinned-ratio kernel is already repaired; finish the surrounding classical theory rather than inventing parallel APIs.

### P1 — Complex/detailed balance

- [ ] Matrix--Tree cofactor and directed Matrix--Tree proof files.
- [ ] Complex-balance geometry.
- [ ] Complex-balance linear stability.
- [ ] Detailed-balance entropy, toric, and linear-stability files.
- [ ] Generalized complex-balance geometry and deficiency-zero existence/obstruction.

### P1 — Persistence/permanence and global asymptotics

- [ ] Kernel-check the strongly-endotactic tier/permanence chain.
- [ ] Formalize established weakly-reversible persistence subclasses.
- [ ] Keep the unrestricted weakly-reversible Persistence Conjecture explicitly isolated as open.
- [ ] Complete `CRNT.Dynamics.GlobalAttractorTheorem` (4 current proof holes) using the established literature proof architecture.

Important distinction: the complex-balanced Global Attractor Conjecture was proved in the literature; here it is a deep **formalization task**, not an open conjecture. General weakly-reversible persistence remains a research frontier.

### P2 — Oscillation/global Hopf

Bottom-up order only:

- [ ] low-level spectral/matrix lemmas
- [ ] `VassenaContinuation`
- [ ] `DHopf`
- [ ] `ChildSelectionReactivity`
- [ ] `GlobalHopfContinuation`
- [ ] `SpectralOpenness`
- [ ] `GlobalHopfSpectralCrossing`
- [ ] `GlobalHopfIndex`
- [ ] global Hopf theorem / continuation capstones
- [ ] Floquet and orbital stability

Do not begin from the top-level global-Hopf theorem and fabricate missing interfaces.

### P2 — Dense independent clusters

- [ ] Flux: circulation -> conformal decomposition -> extreme rays -> circuits -> integer T-invariants.
- [ ] Multistationarity: concordance/discordance, normality, strong concordance, influence/SR graph criteria.
- [ ] Translation: source coefficients, parallel aggregation, improper translations, linear conjugacy.
- [ ] Stochastic: product-form converse, Foster criteria, exhaustive birth-death results.
- [ ] Reduction: intermediate Schur-complement exactness.

## Remaining proof-hole counts

See `CURRENT_PROOF_HOLES.md` for exact files.

- Equilibria: 39
- Multistationarity: 27
- Translation: 23
- Flux: 17
- Kinetics: 13
- Stochastic: 9
- Design: 7
- Theorems: 7
- Deficiency: 5
- Graph: 5
- Stability: 5
- Dynamics: 4
- Reduction: 2
- **Total: 163 `sorry`/`admit` occurrences across 61 modules**

## Verification protocol for every theorem

- [ ] Read exact declaration and definitions.
- [ ] Search current file, project, and local Mathlib before proving.
- [ ] Reduce the mathematics to a short dependency chain.
- [ ] Test uncertain pieces in a small scratch theorem.
- [ ] Integrate the proof into the real declaration.
- [ ] Compile the actual module from source.
- [ ] Compile at least one immediate downstream dependent.
- [ ] Confirm no new `sorry`, `admit`, custom axiom, or unchecked assumption.
- [ ] Confirm theorem statement was not weakened or assumptions strengthened.
- [ ] Only then remove/promote the module from `scripts/unverified_modules.txt`.
- [ ] Run all four project gates after a promotion batch.

## Commands

Use the supplied environment; do not reinstall or update dependencies.

```bash
export PATH=/path/to/lean431-mini/bin:$PATH
export CRNT_CACHE=/path/to/crnt-compiled-cache
python3 scripts/offline_build.py CRNT.Some.Module
python3 scripts/offline_build.py --plan CRNT.Some.Module
```

Trust-boundary gates:

```bash
python3 scripts/check_imports.py
python3 scripts/check_stubs.py
python3 scripts/check_undefined_names.py
python3 scripts/check_exclusions.py
```

## Definition of project success

The near-term success criterion is not merely “zero `sorry`.” It is:

1. every intended CRNT theorem has its exact mathematical statement represented faithfully;
2. every established theorem is kernel-checked in its real module;
3. dependency modules compile from source, not stale objects;
4. no custom axiom or hidden assumption substitutes for proof;
5. computational decision procedures are connected to proved specifications;
6. open conjectures are visibly separated from established mathematics;
7. the dependency graph itself makes clear which new mathematical results would advance the frontier.

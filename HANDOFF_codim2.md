# Hole A — codimension-two route (session 2026-10-10, continued)

Hole A (`exists_positive_omegaPoint_of_highCodimension_siphonFace_nonVertex`) is **still open**.
Everything below compiles and audits to `[propext, Classical.choice, Quot.sound]`
(pins in `test/AxiomAudit.lean`).

## New modules

| Module | Content |
|---|---|
| `CRNT/Geometry/PlanarZSH.lean` | Planar zero-separating polygon in log coordinates (Craciun v3 §5). `Rays.exists_polygon`, `Rays.eventually_bandGood`. |
| `CRNT/Geometry/PlanarZSHTrap.lean` | Finite-horizon band fencing; `Rays.exists_trapping_polygon` (forward invariance of the shrunk region on `[0,T]` while in the box). |
| `CRNT/Geometry/PlanarFanSlopes.lean` | `Rays.ofSlopes`; compatibility of comparison vectors; margin bound `Rays.pair_ge_of_good`. |
| `CRNT/Dynamics/SourceOrderDescent.lean` | `inner_nonneg_of_sourceOrder`: exact pointwise descent from the order of source log-rates. |
| `CRNT/Dynamics/TransversalPlanarDescent.lean` | `transversal_descent` (aligned codim-2 face ⇒ planar descent), `local_codimTwo_trap` (trajectory segments near an aligned codim-2 face stay above the polygon). |

"Aligned": the two extreme rays of the transversal cone `projOn P (S) ∩ ℝ^P_{≥0}` have disjoint
species supports `P1`, `P2`; then on the whole class `x s = c s · ∑_{P1} x` (`s ∈ P1`) and
`x s = c s · ∑_{P2} x` (`s ∈ P2`).

## Remaining obligations for Hole A

1. **Global codim-2 argument (aligned).** Localization (`hzcard` + compactness: near the face the
   other species are bounded below) is routine. The open step is re-entry into the box near the
   two adjacent facets, where species outside `Pmax` can also be small. What the trap does prove:
   if the orbit accumulates on the face, then for every small `ε` the ω-limit set contains a point
   with transversal coordinates `(ε, 0)` or `(0, ε)` and the other species bounded below, i.e. a
   point in the relative interior of an adjacent facet. Excluding those is a facet statement
   *without* the maximality hypothesis that closed the existing facet case.
2. **Non-aligned codim-2 faces**: two charts (sectors `U₁ ≤ U₂`, `U₁ ≥ U₂`), edge normals
   `Mρ` different from the log rays.
3. **Codimension ≥ 3** (rank ≥ 4): higher-dimensional zero-separating construction (Craciun §6–§8);
   the planar module is the base case.

## Basic CRNT additions (same session)

| Module | Theorem |
|---|---|
| `CRNT/Theorems/DeficiencyZero/HornCharacterization.lean` | `forall_complexBalanced_iff`: a positive complex-balanced state exists for **every** rate vector ⟺ weakly reversible ∧ deficiency zero (Horn 1972). The converse direction `weaklyReversible_and_deficiencyZero_of_forall_complexBalanced` is new; it uses circulation-weighted rates `κ r = c r · exp(-d (source r))` for `d` in the deficiency subspace. Also `exists_positive_circulation`. |
| `CRNT/Deficiency/KineticSubspace.lean` | `kineticSubspace` (span of mass-action velocities at positive states); `kineticSubspace_le_stoichSubspace`; `span_complexMonomialVector_eq_top` (monomial vectors span the complex space, via `MvPolynomial.funext_set`); `range_kineticMap_eq_range_incidenceMap_of_numTerminalSLC`; `kineticSubspace_eq_stoichSubspace_of_numTerminalSLC` (Feinberg–Horn 1977, `t = ℓ`) and the weakly reversible corollary. |

Coverage notes: deficiency zero and one theorems, Birch, Horn–Jackson (toric structure, every
positive equilibrium complex balanced, uniqueness per class), detailed balance / Wegscheider,
injectivity and concordance, SR graph, siphon persistence (no critical siphon ⇒ positive
ω-limits), single-linkage-class GAC, ACR (Shinar–Feinberg), linear conjugacy and dynamical
equivalence were already present.

## Basic CRNT additions (third round)

| Module | Theorem |
|---|---|
| `CRNT/Theorems/DeficiencyZero/GeneralKinetics.lean` | Deficiency Zero Theorem part (i) for **arbitrary kinetics**: `deficiencyZero_not_weaklyReversible_no_positive_steadyState_or_cycle` (no steady state with all rates positive, no cyclic trajectory along which all rates are positive); `weaklyReversible_of_deficiencyZero_of_cyclic_trajectory` (integrate the rates over one period to get a positive stoichiometric cycle, which at δ = 0 is a positive graph circulation). |
| `CRNT/Equilibria/QuasiThermostatic.lean` | Horn–Jackson: `isComplexBalanced_of_positive_steadyState`; `positiveSteadyState_iff_logRatio_mem_orthStoich` (quasi-thermostatic property); `positiveSteadyState_iff_complexBalanced`. |
| `CRNT/Dynamics/SiphonLinkage.lean` | Shiu–Sturmfels: `isSiphon_iff_of_weaklyReversible` (in a WR network, `P` is a siphon iff every reaction's source meets `P` exactly when its target does); `meets_iff_of_linked` (complexes meeting a siphon form a union of linkage classes). |
| `CRNT/Theorems/DeficiencyZero/NoPeriodicOrbitComplexBalanced.lean` | `eq_of_periodic_solution_of_complexBalanced`: no non-constant positive periodic orbit in any complex-balanced mass-action system, at any deficiency. |

## Fourth round

| Module | Theorem |
|---|---|
| `CRNT/Dynamics/FirstOrderGAC.lean` | `hasNoCriticalSiphon_of_firstOrder` (weakly reversible first-order networks have no critical siphon: by Shiu–Sturmfels, the indicator of a siphon is a conservation law at molecularity ≤ 1); `gac_of_firstOrder` (global attractor property for every complex-balanced first-order system, via the Hole-A-free `gac_of_hasNoCriticalSiphon`). Uses the existing `Network.IsFirstOrder`. |
| `CRNT/Dynamics/GACLowRank.lean` | The reduction chain of `complexBalanced_genuinePermanent` repeated under `N.stoichRank ≤ 2`, with the non-vertex residual branch refuted by `three_le_stoichRank_of_nonVertex` instead of calling the `sorry`: `complexBalanced_genuinePermanent_of_stoichRank_le_two` and `complexBalanced_trajectory_converges_of_stoichRank_le_two` — the **Global Attractor Theorem in stoichiometric rank ≤ 2, axiom-clean**. |

Hole A status unchanged: the general theorem still depends on `sorryAx` through
`exists_positive_omegaPoint_of_highCodimension_siphonFace_nonVertex` (rank ≥ 3).

## Fifth round

**Correction to the fourth round.** `CRNT.Dynamics.GACLowRank` was not imported from `CRNT.lean`
and the pins for `gac_of_firstOrder` / `..._of_stoichRank_le_two` were not added (a guarded
`grep && sed` chain skipped them). Both are fixed in this round; every module of the session is
now imported and every main theorem pinned (checked by script).

| Module | Theorem |
|---|---|
| `CRNT/Dynamics/GACVertexFacet.lean` | `CodimTwoCriticalSiphonsAreVertices` (every critical siphon of codimension ≥ 2 is a vertex zero set); `complexBalanced_genuinePermanent_of_codimTwoCriticalSiphonsAreVertices` and `complexBalanced_trajectory_converges_of_codimTwoCriticalSiphonsAreVertices` — the **Anderson–Shiu / CDSS form of the GAC (critical siphons are vertices or facets), axiom-clean**. Generalizes `GACLowRank` (`codimTwoCriticalSiphonsAreVertices_of_stoichRank_le_two`) and covers networks with no critical siphon. In the residual, `Pmax` is shown to be a critical siphon (`isSiphon_zeroSet_of_mem_omegaLimit`, `criticalSiphon_of_compatibilityFace_nonempty`). |
| `CRNT/Kinetics/HungarianLemma.lean` | `exists_massAction_realization_iff` (Hárs–Tóth 1979): a polynomial field `∑ c i m x^m` is a mass-action field iff every negative monomial in coordinate `i` contains `x_i`. Explicit realizing network `hungarianNetwork` with rates `|c i m|`. |

Hole A, precisely: the GAC remains open (in this tree) exactly for networks having a critical
siphon whose face has codimension ≥ 2 and is not a vertex.

## Sixth round

* `CRNT/Examples/CatalyticChainGAC.lean`: `CatalyticChain.globalAttractor` — the global
  attractor property of `A + C ⇌ 2C ⇌ B + C` (the network of `CodimTwoFaceModel`, codimension-two
  critical siphon `{B, C}`), axiom-clean via the rank ≤ 2 theorem.
* **Gate fix.** Importing `GACLowRank` from `CRNT.lean` (done in round five) pulled the
  hole-bearing `GlobalAttractorTheorem`/`HighCodimensionSiphonFace` into the verified core and
  made `research/Audit/ledger_coverage.py` fail C3. `GACLowRank`, `GACVertexFacet` and
  `CatalyticChainGAC` now live in the frontier target (`scripts/frontier_history.txt` →
  `CRNTFrontier.lean`), are imported directly by `test/AxiomAudit.lean`, and the orphan baseline
  records the decision (126 → 129). All gates pass: `ledger_coverage.py`, `check_stubs.py`,
  `check_imports.py`, `test/AxiomAudit.lean`.
* Coverage check this round: Boros's existence theorem
  (`exists_positiveSteadyState_of_weaklyReversible`) and linkage-deficiency additivity
  (`sum_linkageDeficiency_eq_deficiencyInt_iff_independent`) were already present.

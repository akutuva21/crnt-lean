# Persistence and the global attractor conjecture

This area concerns the behavior of mass-action trajectories *in the large*: whether species avoid
extinction (**persistence**) and whether every positive trajectory of a complex-balanced network
converges to its unique positive equilibrium (the **global attractor conjecture**, Horn 1974). It
builds directly on the relative-entropy Lyapunov function and the forward semiflow described in
[`dynamics.md`](dynamics.md), and on the complex-balanced equilibrium theory in
[`deficiency.md`](deficiency.md).

The global attractor conjecture is open in general. This document records what is **proven here** and
states honestly where the formalization stops.

## The reduction: GAC ⟺ persistence

For a complex-balanced (toric) mass-action system, the relative entropy `relEntropy x* ·` is a strict
Lyapunov function whose dissipation vanishes exactly at complex-balanced equilibria (Horn & Jackson,
*General mass action kinetics*, 1972). LaSalle's invariance principle then forces convergence to the
equilibrium `{x*}` **unless** the ω-limit set of the trajectory touches the boundary of the
nonnegative orthant. So for complex-balanced systems, the global attractor conjecture is equivalent
to **persistence**: no positive trajectory has an ω-limit point on the boundary.

This reduction is fully formalized:

- `omegaLimit_eq_singleton_of_persistent` (`Dynamics/GlobalStability.lean`): given a compact
  absorbing set inside the open orthant, the ω-limit set is `{x*}`.
- `gac_of_genuine_persistence` / `gac_of_persistent` (`Dynamics/PersistenceGAC.lean`,
  `Dynamics/SingleLinkageGAC.lean`): the same from a genuine-field / bundled persistence certificate.
- `omegaLimit_eq_singleton_of_mem_positive` (`Dynamics/GACOmegaPositive.lean`), the sharp form: if
  the ω-limit set contains **even one** strictly positive point, it equals `{x*}`. Persistence is
  therefore needed only to place a single ω-point in the interior.

## Siphons and the boundary (Angeli–De Leenheer–Sontag)

The combinatorial control on boundary ω-limit points is the **Petri-net siphon**. Following Angeli,
De Leenheer & Sontag (*A Petri-net approach to persistence analysis*, 2007), the zero set of a
boundary ω-limit point is a siphon, and a network with no *critical* (drainable) siphon is
persistent. This chain is proven:

- `omegaLimit_negInvariant` (`Dynamics/NegativeInvariance.lean`): backward (negative) invariance of
  the ω-limit set of a precompact `Flow ℝ≥0` orbit. This is general dynamical-systems content absent
  from Mathlib, and a prerequisite for the boundary analysis.
- `massActionVectorField_pos_of_not_isSiphon` (`Dynamics/StrictInflow.lean`): at a nonnegative point
  whose zero set is **not** a siphon, the field has strictly positive inflow at a depleted species.
- `isSiphon_zeroSet_of_mem_omegaLimit` (`Dynamics/BoundaryOmegaSiphon.lean`): the zero set of a
  boundary ω-limit point is a siphon.
- `isCriticalSiphon_zeroSet_of_mem_omegaLimit` (`Dynamics/CriticalSiphonOmega.lean`): for a positive
  start it is moreover a *critical* siphon (by the mass-conservation argument).
- `omegaLimit_positive_of_hasNoCriticalSiphon` (`Dynamics/NoCriticalSiphonPersistence.lean`): under
  `HasNoCriticalSiphon`, every ω-limit point is strictly positive.
- **`gac_of_hasNoCriticalSiphon`** (`Dynamics/GACNoCriticalSiphon.lean`): **unconditional global
  attractor convergence for the no-critical-siphon class of complex-balanced networks**, with no
  persistence hypothesis. This is the headline global-convergence theorem currently proven.

Siphons themselves (`IsSiphon`, `IsCriticalSiphon`, `HasNoCriticalSiphon`) are defined in
`Dynamics/Siphon.lean`; `IsSiphon` is decidable. Forward-invariance of siphon faces and the supporting
confinement/descent results are in `Dynamics/{Persistence,PersistenceTheorem,PersistenceConfined,
ConfinedInvariance,BoundaryDescent,ConservationLaw,SiphonConservation}.lean`.

## Toric differential inclusions (Craciun)

A second, geometric approach to persistence, independent of siphons, embeds the toric dynamical
system into a **toric differential inclusion** `ẋ ∈ F_{F,δ}(log x)`, whose right-hand side is read
off the polyhedral fan of the reaction vectors, and constructs **zero-separating surfaces** bounding
an invariant region that stays a fixed distance from the boundary. This is the approach of Craciun,
*Toric differential inclusions and a proof of the global attractor conjecture*. The general proof is
an unrefereed preprint; the formalization here machine-checks its architecture, and is candid about
which steps are theorems and which are interfaces awaiting a construction.

Built and proven:

- **Differential inclusions** (`Dynamics/DifferentialInclusion.lean`): `Field`, inclusion solutions,
  the embedding of an ODE solution into any inclusion that selects it, and forward-invariant regions.
- **The polyhedral-fan field** (`Geometry/{PolyhedralFan,ToricFan}.lean`): the polar cone
  (`coneDual`) with bipolar and Farkas duality; the δ-uncertainty field `F_{F,δ}(X)` (`toricField`,
  monotone in δ) and the inclusion `ẋ ∈ F_{F,δ}(logCoords x)`. The full fan axioms (covering, closure
  under faces) are not imposed; `Geometry/ConeFace.lean` has the exposed-face and lattice fragments.
- **The embedding** (`Dynamics/{ToricEmbedding,ToricEmbeddingOrder,ToricEmbeddingWR}.lean`): a single
  cycle's velocity lies in the polar cone, by ordering complexes along an interior direction and
  summing consecutive differences (Abel summation). The assembly over a weakly-reversible network is
  conditional on a cycle cover (`NetworkCycleDecomposition`), which is taken as a graph-theoretic
  hypothesis: weak reversibility is defined through `Relation.ReflTransGen`, and no cycle-extraction
  lemma derives the cover from it.
- **Zero-separating surfaces** (`Dynamics/ZeroSeparating.lean`, `Geometry/{ZeroSeparatingCurve2D,
  ZeroSeparatingSurface,FaithfulCurve,FaithfulCurve2D,FaithfulCurve2DFan,FaithfulCurveExistence,
  FaithfulCurveGeneral}.lean`, `Dynamics/{PolyRegionInvariant,PolyRegionStrictInvariant,
  SupportDiniBridge,ZeroSeparatingInduction,FanRefinement,ThmBGenuine}.lean`):
  - the one-dimensional case is proven outright (`zeroSeparatingRegion_Ici`);
  - the invariance engine for a polygonal region is `polyRegion_invariant_of_strictSupport`: forward
    invariance from *boundary-local* strict subtangency, checked only at the active faces at a curve's
    actual position, so genuinely distinct (even conflicting) edge normals are handled;
  - in two dimensions the faithful curve is constructed by **angular chaining**: edge normals are
    unit vectors at the fan-wall angles and rotate monotonically, so within a sector of width less
    than π one direction lies strictly inside every face at once (`exists_strict_interior`), giving a
    nonempty zero-separating region that excludes a ball about the origin
    (`exists_faithful_separating_region`), and these normals are genuine attracting directions of an
    actual fan (`toricField_subset_wall_halfPlane`);
  - the higher-dimensional induction sweeps a lower-dimensional surface along a ruling direction
    (`ruledSet`), with separation and subtangency transferring to the sweep; a surface normal on a
    ruled patch must be orthogonal to its active directions, which is feasible below the ambient
    dimension and over-determined once those directions span. This is the elementary linear-algebra fact
    behind the difficulty in dimension four. Refining the fan keeps each patch below that threshold
    and transfers admissibility to the coarser fan (`FanRefinement`), so the dimension-four
    over-determination is a feature of the naive construction, not an obstruction.
- **Viability** (`Dynamics/{Viability,FirstExit,SublevelInvariant,SublevelNagumo,ClosedSetNagumo}.lean`,
  `Dynamics/ThmBGenuine.lean`): for the genuine (Lipschitz) dynamics, solution existence is free
  (Picard–Lindelöf), so only invariance must be shown. The single-valued Nagumo step is proven: given a
  sublevel surface with a neighborhood-descent band and ball-separation, the genuine trajectory stays a
  fixed distance from the origin (`genuine_away_from_origin`, `massAction_genuine_away_from_origin`).
  That surface is supplied as input. The set-valued Nagumo theorem (subtangency implies invariance for a
  set-valued field) is itself taken as a hypothesis.

What is **not** verified are the analytic and geometric steps the proof rests on. Each is carried as an
explicit hypothesis (a `Prop`, a structure, or a supplied argument), never a `sorry`:

1. **Set-valued viability / Nagumo.** Subtangency implies forward invariance for a set-valued field.
   `Dynamics/Viability.lean` defines the subtangency predicates (`Subtangent`, `PosSubtangent`) and
   proves the easy direction; the converse enters as a solution-existence argument, and the general
   theorem is absent from Mathlib.
2. **The n-dimensional surface construction.** The decomposition of a neighborhood into ruled patches
   and the simplicial gluing is the predicate `InductionStepHypothesis`; `inductionStep_of_ruledBuild`
   returns its assumed witness unchanged. The descent band and ball-separation feeding
   `genuine_away_from_origin` are likewise supplied.
3. **The weak-reversibility cycle cover.** `NetworkCycleDecomposition` packages the cycle-cover data
   and is assumed; no lemma extracts a cover from `WeaklyReversible`.
4. **The polyhedral-fan axioms.** `IsPolyhedralFan` (closure under exposed faces, pairwise intersection
   a common face, covering) is a hypothesis; `Fan` is bare cone data.
5. **Arbitrary-fan faithful-curve existence.** The global slope-interval chaining is the `ChainingData`
   interface; the two-dimensional results assume a sector bound and strict subtangency
   (`IsStrictSupportField`), discharged only for worked instances such as the first-quadrant `crossFan`.
6. **The support-to-`infDist` bridge.** For a Lipschitz polygonal boundary, the step from edgewise
   support to a nonincreasing distance to the region is supplied as a hypothesis (`hanti`).

No theorem assembles these into a conclusion of persistence or the global attractor conjecture for the
toric-inclusion approach. Its persistence-style results are the one-dimensional base case
(unconditional) and genuine-flow distance bounds conditional on a supplied surface. The architecture is
machine-checked and the dimension-four over-determination is understood, but the conjecture is not
closed here.

## What is complete, and what is open

- **Complete:** the Lyapunov/LaSalle reduction; GAC ⟺ persistence; unconditional global convergence
  for the no-critical-siphon class; the sharp "one positive ω-point ⇒ convergence" reduction; the
  siphon → critical-siphon → ω-positivity chain; backward invariance of ω-limit sets; the
  differential-inclusion, polar-cone, embedding, one- and two-dimensional zero-separating, and
  single-valued-Nagumo machinery above.
- **Open:** persistence in general (the remaining gap: interior orbits repelled from critical-siphon
  faces), which needs the analytic boundary-repulsion estimates (Anderson & Shiu near-facet dynamics;
  Anderson's single-linkage tier argument) and the feasibility test for critical siphons; and, in the
  toric-inclusion approach, the six explicit hypotheses enumerated above, none of which is assembled
  into a persistence or GAC conclusion.

## Modules

`Dynamics/`: `Siphon`, `SiphonConservation`, `ConservationLaw`, `Persistence`, `PersistenceTheorem`,
`PersistenceConfined`, `ConfinedInvariance`, `BoundaryDescent`, `GlobalStability`, `PersistenceGAC`,
`ForwardInvariance`, `StrictInflow`, `NegativeInvariance`, `BoundaryOmegaSiphon`, `CriticalSiphonOmega`,
`NoCriticalSiphonPersistence`, `GACNoCriticalSiphon`, `GACOmegaPositive`, `SingleLinkageGAC`,
`IsolatedInvariant`, `ButlerMcGehee`, `FacetRepulsion`, `DifferentialInclusion`, `ToricInclusion`,
`ToricEmbedding`, `ToricEmbeddingOrder`, `ToricEmbeddingWR`, `ZeroSeparating`, `Viability`,
`FirstExit`, `SublevelInvariant`, `SublevelNagumo`, `ClosedSetNagumo`, `SupportDiniBridge`,
`PolyRegionInvariant`, `PolyRegionStrictInvariant`, `ZeroSeparatingInduction`, `FanRefinement`,
`ThmBGenuine`, `EndotacticPermanence`, `DissipationBound`.
`Geometry/`: `PolyhedralFan`, `Endotactic`, `ToricFan`, `ConeFace`, `ZeroSeparatingSurface`,
`ZeroSeparatingCurve2D`, `ToricFieldPolar`, `ToricFieldPolarMulti`, `FaithfulCurve`,
`FaithfulCurveExistence`, `FaithfulCurveGeneral`, `FaithfulCurve2D`, `FaithfulCurve2DFan`.

Related: [`architecture.md`](architecture.md), [`dynamics.md`](dynamics.md),
[`deficiency.md`](deficiency.md).

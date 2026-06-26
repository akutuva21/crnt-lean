# Persistence and the global attractor conjecture

This area concerns the behavior of mass-action trajectories *in the large*: whether species avoid
extinction (**persistence**) and whether every positive trajectory of a complex-balanced network
converges to its unique positive equilibrium (the **global attractor conjecture**, Horn 1974). It
builds on the relative-entropy Lyapunov function and the forward semiflow described in
[`dynamics.md`](dynamics.md), and on the complex-balanced equilibrium theory in
[`deficiency.md`](deficiency.md).

The global attractor conjecture is open in general. This document records what is **proven here**,
what is **gated on explicit hypotheses**, and where the formalization stops. Every result discussed
is `sorry`-free; the conjecture is not closed, and where a step is missing it enters as a named
hypothesis (a `Prop`, a structure, or a supplied argument), never as a `sorry`.

## The reduction: GAC ⟺ persistence

For a complex-balanced (toric) mass-action system, the relative entropy `relEntropy x* ·` is a
strict Lyapunov function whose dissipation vanishes exactly at complex-balanced equilibria (Horn &
Jackson, *General mass action kinetics*, 1972). LaSalle's invariance principle then forces
convergence to the equilibrium `{x*}` **unless** the ω-limit set of the trajectory touches the
boundary of the nonnegative orthant. So for complex-balanced systems, the global attractor
conjecture is equivalent to **persistence**: no positive trajectory has an ω-limit point on the
boundary.

This reduction is fully formalized:

- `omegaLimit_eq_singleton_of_persistent` (`Dynamics/GlobalStability.lean`): for a weakly reversible
  network with positive complex-balanced reference `x*`, given a compact set `K₀` in the open
  orthant that absorbs the cutoff orbit, the ω-limit set is `{x*}`. The persistence content enters as
  the absorbing-set hypothesis.
- `gac_of_genuine_persistence` (`Dynamics/PersistenceGAC.lean`): the same conclusion from a
  genuine-field persistence certificate `hgen` — every genuine integral curve from `x₀` stays in a
  fixed compact `K₀ ⊆` the open orthant.
- `gac_of_persistent` (`Dynamics/SingleLinkageGAC.lean`): the conjecture's conclusion against the
  bundled certificate `Network.PersistentFrom κ x₀`, which packages exactly the compact positive
  absorbing set `gac_of_genuine_persistence` consumes.
- `omegaLimit_eq_singleton_of_mem_positive` (`Dynamics/GACOmegaPositive.lean`), the sharp form: if
  the ω-limit set contains **even one** strictly positive point, it equals `{x*}`. Persistence is
  therefore needed only to place a single ω-point in the interior. The LaSalle facts the proof uses
  (ω-orbits solve the genuine field, the relative entropy is constant on the ω-limit set, ω-points
  are nonnegative and affinely invariant) are supplied as arguments and discharged inside the
  no-critical-siphon assembly below.

## Siphons and the boundary (Angeli–De Leenheer–Sontag)

The combinatorial control on boundary ω-limit points is the **Petri-net siphon**. Following Angeli,
De Leenheer & Sontag (*A Petri-net approach to persistence analysis*, 2007), the zero set of a
boundary ω-limit point is a siphon, and a network with no *critical* (drainable) siphon is
persistent. This chain is proven:

- `omegaLimit_negInvariant` (`Dynamics/NegativeInvariance.lean`): backward (negative) invariance of
  the ω-limit set of a precompact `Flow ℝ≥0` orbit in a Hausdorff space. This is general
  dynamical-systems content absent from Mathlib, and a prerequisite for the boundary analysis.
- `massActionVectorField_pos_of_not_isSiphon` (`Dynamics/StrictInflow.lean`): at a nonnegative point
  whose zero set is **not** a siphon, the field has strictly positive inflow at a depleted species.
- `isSiphon_zeroSet_of_mem_omegaLimit` (`Dynamics/BoundaryOmegaSiphon.lean`): the zero set of a
  boundary ω-limit point is a siphon.
- `isCriticalSiphon_zeroSet_of_mem_omegaLimit` (`Dynamics/CriticalSiphonOmega.lean`): for a positive
  start it is moreover a *critical* siphon, by the mass-conservation argument (affine invariance of
  the ω-limit set).
- `omegaLimit_positive_of_hasNoCriticalSiphon` (`Dynamics/NoCriticalSiphonPersistence.lean`): under
  `HasNoCriticalSiphon`, every ω-limit point is strictly positive.
- **`gac_of_hasNoCriticalSiphon`** (`Dynamics/GACNoCriticalSiphon.lean`): **unconditional global
  attractor convergence for the no-critical-siphon class of complex-balanced networks**, with no
  persistence or closeness hypothesis — `HasNoCriticalSiphon` supplies it. This is the headline
  global-convergence theorem proven here. Its arguments are weak reversibility, a positive
  complex-balanced reference, and a positive start in that reference's compatibility class.

Siphons themselves are defined in `Dynamics/Siphon.lean`: `IsSiphon` (every reaction producing a
species in the set also consumes one), `IsCriticalSiphon` (a nonempty siphon whose face carries no
conserved positive vector), and `HasNoCriticalSiphon`. `IsSiphon` is decidable (`decidableIsSiphon`,
checkable by `decide`); `IsCriticalSiphon` and `HasNoCriticalSiphon` are not, since deciding
criticality is a sign-restricted kernel-feasibility question. Forward invariance of siphon faces and
the supporting confinement, conservation, and descent results are in `Dynamics/{Persistence,
PersistenceTheorem,PersistenceConfined,ConfinedInvariance,BoundaryDescent,ConservationLaw,
SiphonConservation}.lean`.

The general dynamical-systems scaffolding for boundary-repulsion arguments is also formalized,
independent of reaction networks: the **Butler–McGehee escape principle** (`Dynamics/ButlerMcGehee.lean`,
after Butler & Waltman and Hale, *Asymptotic Behavior of Dissipative Systems*) — two-sided
invariance of the ω-limit set and the escaping-point geometry for an isolated invariant set;
**isolated invariant sets and isolating neighborhoods** (`Dynamics/IsolatedInvariant.lean`); and
**minimal compact invariant sets** by a Zorn descent (`exists_minimal_compact_invariant_subset`,
`Dynamics/MinimalInvariant.lean`). `Dynamics/EscapeSiphonFace.lean` fuses these: for a precompact
positive trajectory the forward limit of an escaping ω-point carries a critical siphon on its zero
set, so under `HasNoCriticalSiphon` no isolated boundary set can trap the ω-limit set.

## Toric differential inclusions (Craciun)

A second, geometric approach to persistence, independent of siphons, embeds the toric dynamical
system into a **toric differential inclusion** `ẋ ∈ F_{F,δ}(log x)`, whose right-hand side is read
off the polyhedral fan of the reaction vectors, and constructs **zero-separating surfaces** bounding
an invariant region that stays a fixed distance from the boundary. This is the approach of Craciun,
*Toric differential inclusions and a proof of the global attractor conjecture*. The general proof is
an unrefereed preprint; the formalization here machine-checks its architecture, and is candid about
which steps are theorems and which are interfaces awaiting a construction.

Built and proven:

- **Differential inclusions** (`Dynamics/DifferentialInclusion.lean`): the set-valued `Field`,
  inclusion solutions, the embedding of an ODE solution into any inclusion that selects it, and
  forward-invariant regions. `Dynamics/ToricInclusion.lean` shows the mass-action velocity lies in
  the constant reaction-cone inclusion, so a nonnegative mass-action curve solves it.
- **The polyhedral-fan field** (`Geometry/{PolyhedralFan,ToricFan,ConeFace}.lean`): the polar cone
  (`coneDual`) with the bipolar theorem (`cone_dual_dual`) and Farkas separation
  (`exists_mem_coneDual_of_notMem`); the δ-uncertainty field `F_{F,δ}(X)` (`toricField`, monotone in
  δ by `toricField_mono_delta`) and the inclusion `ẋ ∈ F_{F,δ}(logCoords x)`. A `Fan` is bare cone
  data (`Finset (ProperCone ℝ E)`); the full fan axioms are the separate hypothesis
  `IsPolyhedralFan` (closure under exposed faces, pairwise intersection a common face, covering), and
  `Geometry/ConeFace.lean` supplies the exposed-face and supporting-hyperplane fragments
  (`exposedFace`, `IsExposedFaceOf`).
- **The embedding** (`Dynamics/{ToricEmbedding,ToricEmbeddingOrder,ToricEmbeddingWR}.lean`): a single
  cycle's velocity lies in the polar cone (`cycle_velocity_mem_polarCone`), by ordering complexes
  along an interior direction and summing consecutive differences (Abel summation) against
  `C`-minimality. The assembly over a weakly-reversible network is conditional on a cycle cover:
  `NetworkCycleDecomposition` packages the per-cycle reaction sequences and the ordering data
  (`mono`, `cmin`), and `velocity_mem_polarCone` derives the total-velocity membership from it.
- **The cycle-cover boundary** (`Graph/CycleCover.lean`): weak reversibility is defined through
  `Relation.ReflTransGen` reachability (`Graph/{Reachability,WeakReversibility}.lean`). At that
  reachability level the cover *is* proven: `WeaklyReversible.onDirectedCycle` shows every reaction
  lies on a directed cycle, and `WeaklyReversible.reaches_comm` gives strong connectivity of each
  component. What is **not** constructed is extracting a concrete closed walk (a `List N.R`) from the
  propositional reachability witness and assembling the full `NetworkCycleDecomposition` with its
  `mono`/`cmin` projection-ordering data; that structure is consumed as input by the multi-cycle
  embedding rather than derived from `WeaklyReversible`.
- **Zero-separating surfaces** (`Dynamics/ZeroSeparating.lean`,
  `Geometry/{ZeroSeparatingCurve2D,ZeroSeparatingSurface,ZeroSeparatingInduction,FaithfulCurve,
  FaithfulCurve2D,FaithfulCurve2DFan,FaithfulCurveExistence,FaithfulCurveGeneral,FanRefinement,
  ToricFieldPolar,ToricFieldPolarMulti}.lean`,
  `Dynamics/{PolyRegionInvariant,PolyRegionStrictInvariant,SupportDiniBridge,ThmBGenuine}.lean`):
  - the one-dimensional case is proven outright (`zeroSeparatingRegion_Ici`);
  - the invariance engine for a polygonal region is `polyRegion_invariant_of_strictSupport`: forward
    invariance from *boundary-local* strict subtangency (`IsStrictSupportField`), checked only at the
    active faces at a curve's actual position, so genuinely distinct (even conflicting) edge normals
    are handled;
  - in two dimensions the faithful curve is constructed by **angular chaining**: edge normals are
    unit vectors at the fan-wall angles and rotate monotonically, so within a sector of width less
    than π one direction lies strictly inside every face at once (`exists_strict_interior`), giving a
    nonempty zero-separating region that excludes a ball about the origin
    (`exists_faithful_separating_region`), and these normals are genuine attracting directions of an
    actual fan (`toricField_subset_wall_halfPlane`);
  - the higher-dimensional induction sweeps a lower-dimensional surface along a ruling direction
    (`ruledSet`), with separation and subtangency transferring to the sweep; a surface normal on a
    ruled patch must be orthogonal to its active directions, which is feasible below the ambient
    dimension and over-determined once those directions span. This is the elementary linear-algebra
    fact behind the difficulty in dimension four. Refining the fan keeps each patch below that
    threshold and transfers admissibility to the coarser fan (`Geometry/FanRefinement.lean`), so the
    dimension-four over-determination is a feature of the naive construction, not an obstruction.
- **Viability** (`Dynamics/{Viability,FirstExit,SublevelInvariant,SublevelNagumo,ClosedSetNagumo,
  ThmBGenuine}.lean`): for the genuine (Lipschitz) dynamics, solution existence is free
  (Picard–Lindelöf), so only invariance must be shown. The single-valued Nagumo step is proven: given
  a sublevel surface with a neighborhood-descent band and ball-separation, the genuine trajectory
  stays a fixed distance from the origin (`genuine_away_from_origin`,
  `massAction_genuine_away_from_origin`). That surface is supplied as input. The set-valued Nagumo
  theorem (subtangency implies invariance for a set-valued field) is itself taken as a hypothesis.

What is **not** verified are the analytic and geometric steps the proof rests on. Each is carried as
an explicit hypothesis, never a `sorry`:

1. **Set-valued viability / Nagumo.** Subtangency implies forward invariance for a set-valued field.
   `Dynamics/Viability.lean` defines the subtangency predicates (`Subtangent`, `PosSubtangent`) and
   proves the easy direction (invariance ⇒ subtangency along a solution); the general converse needs
   Filippov selection and Peano existence on a moving constraint, which Mathlib lacks, so it is not
   attempted.
2. **The n-dimensional surface construction.** The decomposition of a neighborhood into ruled patches
   and the simplicial gluing is the predicate `InductionStepHypothesis`
   (`Geometry/ZeroSeparatingSurface.lean`); `inductionStep_of_ruledBuild`
   (`Geometry/ZeroSeparatingInduction.lean`) returns its assumed witness unchanged. The descent band
   and ball-separation feeding `genuine_away_from_origin` are likewise supplied.
3. **The weak-reversibility cycle cover.** `NetworkCycleDecomposition` packages the concrete
   cycle-cover data (path lists with their ordering fields) and is assumed; the reachability-level
   cover is proven (`WeaklyReversible.onDirectedCycle`), but no lemma turns it into the concrete
   decomposition the embedding consumes.
4. **The polyhedral-fan axioms.** `IsPolyhedralFan` (closure under exposed faces, pairwise
   intersection a common face, covering) is a hypothesis; `Fan` is bare cone data.
5. **Arbitrary-fan faithful-curve existence.** The global slope-interval chaining is the
   `ChainingData` interface (`Geometry/FaithfulCurveGeneral.lean`); the two-dimensional results assume
   a sector bound and strict subtangency (`IsStrictSupportField`), discharged only for worked
   instances such as the first-quadrant `crossFan`.
6. **The support-to-`infDist` bridge.** For a Lipschitz polygonal boundary the per-half-plane Dini
   monotonicity is proven (`infDist_halfPlane_antitoneOn_of_support`, `Dynamics/SupportDiniBridge.lean`),
   and the per-face slack lower-bounds the region distance. The matching upper control — the
   convex-intersection projection identity that turns per-face support into antitonicity of the
   *region* distance — enters as the hypothesis `hanti`.

No theorem assembles these into a conclusion of persistence or the global attractor conjecture for
the toric-inclusion approach. Its persistence-style results are the one-dimensional base case
(unconditional) and genuine-flow distance bounds conditional on a supplied surface. The architecture
is machine-checked and the dimension-four over-determination is understood, but the conjecture is not
closed here.

## The permanence route (Gopalkrishnan–Miller–Shiu)

A third route to the conjecture runs through **permanence**: `StronglyEndotactic ⇒ permanent ⇒ GAC`,
the geometric approach of Gopalkrishnan, Miller & Shiu (*A geometric approach to the global attractor
conjecture*, 2014), with low-dimensional predecessors in Craciun, Nazarov & Pantea (2013) and Pantea
(2012). `Endotactic` and `StronglyEndotactic` are defined in `Geometry/Endotactic.lean`. The
**permanence ⇒ convergence** bridge is constructed (`Dynamics/EndotacticPermanence.lean`):
`Permanent` is the eventual-confinement predicate (the forward orbit is eventually inside a fixed
compact set of strictly positive concentrations), `omegaLimit_meets_positive_of_permanent` places an
ω-point in the interior, and `gac_of_permanent` then yields `ω = {x*}` via the sharp positive-ω-point
form. The sign content of strong endotacticity along the relative-entropy dissipation is proven
(`stronglyEndotactic_strict_dissipation_direction`). What this route does **not** supply is the step
`StronglyEndotactic ⇒ permanent`, which is the unproven analytic core.

## What is complete, and what is open

- **Complete:** the Lyapunov/LaSalle reduction; GAC ⟺ persistence; unconditional global convergence
  for the no-critical-siphon class; the sharp "one positive ω-point ⇒ convergence" reduction; the
  siphon → critical-siphon → ω-positivity chain; backward invariance of ω-limit sets; the
  Butler–McGehee escape geometry, isolated and minimal invariant sets; the reachability-level cycle
  cover of a weakly-reversible network; the differential-inclusion, polar-cone, embedding, one- and
  two-dimensional zero-separating, and single-valued-Nagumo machinery above; the permanence ⇒
  convergence bridge.
- **Open:** persistence in general — the remaining gap is that interior orbits must be repelled from
  *critical*-siphon faces. The codimension-1 non-siphon facet case is proven
  (`Dynamics/FacetRepulsion.lean`, via `massActionVectorField_pos_of_not_isSiphon` and Butler–McGehee:
  a non-siphon facet is strictly repelling and traps no ω-point). The critical-siphon facet is taken
  as a hypothesis: there the field is tangent, so first-order repulsion gives nothing, and the
  near-facet quantitative estimate of Anderson & Shiu (*The dynamics of weakly reversible population
  processes near facets*, 2010) — together with Anderson's single-linkage tier argument — is not
  formalized; it needs a near-facet differential inequality absent from this layer. Also open: the
  feasibility test for critical siphons; in the toric-inclusion approach, the six explicit hypotheses
  enumerated above, none assembled into a persistence or GAC conclusion; and, in the permanence route,
  `StronglyEndotactic ⇒ permanent`.

## Modules

`Dynamics/`: `Siphon`, `SiphonConservation`, `ConservationLaw`, `Persistence`, `PersistenceTheorem`,
`PersistenceConfined`, `ConfinedInvariance`, `BoundaryDescent`, `GlobalStability`, `PersistenceGAC`,
`ForwardInvariance`, `StrictInflow`, `NegativeInvariance`, `BoundaryOmegaSiphon`, `CriticalSiphonOmega`,
`NoCriticalSiphonPersistence`, `GACNoCriticalSiphon`, `GACOmegaPositive`, `SingleLinkageGAC`,
`IsolatedInvariant`, `MinimalInvariant`, `ButlerMcGehee`, `EscapeSiphonFace`, `FacetRepulsion`,
`EndotacticPermanence`, `DifferentialInclusion`, `ToricInclusion`, `ToricEmbedding`,
`ToricEmbeddingOrder`, `ToricEmbeddingWR`, `ZeroSeparating`, `Viability`, `FirstExit`,
`SublevelInvariant`, `SublevelNagumo`, `ClosedSetNagumo`, `SupportDiniBridge`, `PolyRegionInvariant`,
`PolyRegionStrictInvariant`, `ThmBGenuine`, `DissipationBound`.
`Geometry/`: `PolyhedralFan`, `Endotactic`, `ToricFan`, `ConeFace`, `ZeroSeparatingSurface`,
`ZeroSeparatingCurve2D`, `ZeroSeparatingInduction`, `FanRefinement`, `ToricFieldPolar`,
`ToricFieldPolarMulti`, `FaithfulCurve`, `FaithfulCurveExistence`, `FaithfulCurveGeneral`,
`FaithfulCurve2D`, `FaithfulCurve2DFan`.
`Graph/`: `Reachability`, `WeakReversibility`, `CycleCover`.

Related: [`architecture.md`](architecture.md), [`dynamics.md`](dynamics.md),
[`deficiency.md`](deficiency.md).

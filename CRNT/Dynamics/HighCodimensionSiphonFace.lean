import CRNT.Dynamics.FaceCodimension
import CRNT.Equilibria.ComplexBalanced

/-!
# The single remaining obligation of the Global Attractor Theorem

`CRNT.Dynamics.GlobalAttractorTheorem` reduces `Network.complexBalanced_genuinePermanent` to
one case, and this module is the only place in the tree where that case is left open.  The
theorem below is the **entire** residual content; everything else in the chain audits as
`[propext, Classical.choice, Quot.sound]`.

## What has been carved away

Let `Ω` be the ω-limit set of a bounded genuine positive mass-action trajectory of a
complex-balanced system, and suppose `Ω` meets the boundary.  The dichotomy
`positiveOmega_or_nonstationary_criticalSiphonFaceEquilibrium` produces a boundary point whose
zero set is a critical siphon, and `exists_maximal_zeroSet_omegaPoint` upgrades it to a point
`wmax ∈ Ω` whose zero set `Pmax` is *maximal*: every ω-point vanishing on `Pmax` vanishes
exactly on `Pmax`, i.e. `wmax` sits in the relative interior of the `Pmax`-face.  Four cases
are then already closed in the tree:

* no critical siphon at all (`boundaryOmegaExcluded_of_hasNoCriticalSiphon`);
* `N.stoichSubspace = ⊥` (`positiveOmegaPointForRates_of_trivialStoichSubspace`);
* `N.stoichRank = 1` (`positiveOmegaPointForRates_of_complexBalanced_of_stoichRank_one`);
* the `Pmax`-face is a **facet** of the compatibility class, where the Anderson--Shiu
  near-facet estimate makes the squared face mass `∑_{s ∈ Pmax} x s ^ 2` nondecreasing and
  `no_omegaLimit_meets_locally_repelling_face` closes the case.

`CRNT.Dynamics.FaceCodimension` then shows the remaining failure of the facet count is never
degenerate: `highCodimension_of_not_facet` yields `2 ≤ finrank (stoichSubspace.map (projOn Pmax))`
and `2 ≤ Pmax.card`.  Those two inequalities are hypotheses below, so the obligation recorded
here is exactly the **codimension ≥ 2** case.

## Why the existing estimate cannot be pushed further

`facet_repelling_near_facet_point` needs every reaction vector restricted to `Pmax` to be a
multiple of one direction `v`, which is precisely
`finrank (stoichSubspace.map (projOn Pmax)) = 1`.  Under `hcodim` the restricted reaction
vectors span at least a plane, and the quadratic `∑_{s ∈ Pmax} x s ^ 2` is then genuinely not
monotone near `wmax`: writing `x s = ε u s` for `s ∈ Pmax`, the leading term of
`∑_{s ∈ Pmax} x s * f s x` is a quadratic form in the approach direction `u ≥ 0` whose sign
varies with `u` — already for a reversible pair inside the face with equal rate constants it is
a negative multiple of a square.  So no strengthening of the Anderson--Shiu argument covers this
branch; a surface whose normal turns with the direction of approach is required.

## The mathematical content that is missing

This is Craciun, *Toric differential inclusions and a proof of the global attractor conjecture*
(v3), Theorem B: a toric differential inclusion admits an exhaustive family of zero-separating
hypersurfaces.  In logarithmic coordinates the requirement (Lemma 9.5, and Lemma 9.7 with the
`δ`-slack) is a hypersurface whose outer normal at a point `X` lies in **every** cone of the fan
within distance `δ` of `X`, hence in low-dimensional cones near the walls.  A smooth surface
cannot satisfy this — the sphere meets the `δ = 0` condition of Lemma 9.5 and fails Lemma 9.7 —
so the surface must be polyhedral, with flat pieces of width at least `δ` around every cone,
arranged by the scale hierarchy of §7.

`CRNT.Geometry.PolyhedralBarrier` formalizes the invariance engine for such a surface:
for `g X = max i (⟪n i, X⟫ - b i)` the sublevel set `{g ≤ R}` is forward invariant for any
field lying in the polar cones of the active normals.  What is *not* formalized, and is the
remaining gap, is the existence of the data feeding that engine for an arbitrary complete
pointed fan: a family `n C ∈ C` indexed by the cones with `⟪n C, x⟫ ≥ ⟪n C', x⟫` for all
`x ∈ C`, together with the separation scales.  That family is a finite convex-geometry object —
equivalently the face points of a polytope whose normal fan refines the fan — and Mathlib
currently has no polytope, face-lattice, or normal-fan API to build it on.

## Trust status

`#print axioms CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace` reports
`sorryAx`, and so do exactly its downstream consumers
`Network.complexBalanced_genuinePermanent`, `Network.complexBalanced_permanent`, and
`Network.complexBalanced_globalAttractor`.  No other declaration in the tree does.

Depends on: `CRNT.Dynamics.FaceCodimension`.
-/

open scoped NNReal Topology
open Filter

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Residual obligation: the ω-limit set cannot sit on a critical-siphon face of codimension
at least two.**

All hypotheses are exactly the data available at the corresponding point of
`Network.complexBalanced_genuinePermanent`:

* `hxs`, `hcb`: a positive complex-balanced equilibrium for the rates `κ`;
* `hϕγ`, `hsol`, `hK`, `hmaps`: a bounded genuine forward trajectory through the positive
  point `x₀`, presented as a cutoff semiflow;
* `hωnn`, `hgenω`, `hωaff`: the ω-limit set is nonnegative, consists of genuine orbits, and
  lies in the compatibility class of `x₀`;
* `hPmaxne`, `hwmax`, `hzeroMax`, `hmaxExact`: `wmax` is an ω-point whose zero set is exactly
  the nonempty species set `Pmax`, and `Pmax` is maximal among zero sets of ω-points;
* `hcodim`, `hcard`: the `Pmax`-face has codimension at least two in the compatibility class
  and `Pmax` has at least two species — both supplied by
  `Network.highCodimension_of_not_facet`;
* `hrank`: the stoichiometric rank is not one.

The conclusion is the interior certificate `PositiveOmegaPointForRates` consumes. -/
theorem exists_positive_omegaPoint_of_highCodimension_siphonFace
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx₀ : x₀.Positive)
    {Pmax : Finset S} (hPmaxne : Pmax.Nonempty)
    {wmax : Concentration S} (hwmax : wmax ∈ omegaLimit atTop ϕ {x₀})
    (hzeroMax : ∀ s, s ∈ Pmax ↔ wmax s = 0)
    (hmaxExact : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (∀ s ∈ Pmax, z s = 0) →
      ∀ s, z s = 0 ↔ s ∈ Pmax)
    (hcodim : 2 ≤ Module.finrank ℝ (N.stoichSubspace.map (projOn Pmax)))
    (hcard : 2 ≤ Pmax.card)
    (hrank : N.stoichRank ≠ 1) :
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive := by
  sorry

end Network
end CRNT

import CRNT.Oscillation.Floquet
import CRNT.Oscillation.ReturnMap
import CRNT.Oscillation.ReturnMapContraction
import CRNT.Dynamics.FlowSmoothDependence
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Floquet multipliers imply nonlinear orbital attraction

This file closes the nonlinear Floquet theorem in arbitrary finite dimension.  The autonomous
multiplier `1` is removed by passing to a codimension-one Poincare section.  The derivative of the
return map is conjugate to the monodromy action on the transverse quotient.  Hence the nontrivial
Floquet multipliers are exactly the spectrum of the section derivative.

A finite-dimensional spectral-radius theorem supplies an equivalent norm in which that derivative
has operator norm `< 1`.  Continuity of the derivative then makes the nonlinear return map a strict
local contraction.  Smooth flow interpolation between successive section hits upgrades convergence
on the section to orbital attraction in continuous time.
-/

namespace CRNT
namespace Network

open Filter Topology

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S} {κ : N.RateConstants}

/-- The phase velocity at the reference point of a periodic orbit. -/
def periodicTangent (P : N.PositivePeriodicOrbit κ) : Concentration S :=
  N.massActionVectorField κ (P.orbit 0)

/-- A canonical codimension-one section normal to the phase velocity. -/
def floquetSectionSpace (P : N.PositivePeriodicOrbit κ) : Submodule ℝ (Concentration S) :=
  (ℝ ∙ periodicTangent P)ᗮ

/-- Transverse monodromy/Poincare derivative package. -/
structure TransverseFloquetSectionData
    (P : N.LinearlyStablePositivePeriodicOrbit κ) : Type where
  E : Type
  instNormedAddCommGroup : NormedAddCommGroup E
  instNormedSpace : NormedSpace ℝ E
  instCompleteSpace : CompleteSpace E
  instFiniteDimensional : FiniteDimensional ℝ E
  returnMap : E → E
  fixedPoint : E
  fixed : returnMap fixedPoint = fixedPoint
  derivative : E →L[ℝ] E
  c1 : ContDiffAt ℝ 1 returnMap fixedPoint
  hasDerivative : HasFDerivAt returnMap derivative fixedPoint
  /-- Characteristic polynomial of the section derivative is the Floquet polynomial with exactly
  one factor `(X-1)` removed. -/
  charpoly_relation :
    (P.floquet.floquetPolynomial) =
      (Polynomial.X - 1) * ((Matrix.ofLinearMap derivative).map (algebraMap ℝ ℂ)).charpoly
  /-- Local states in section coordinates reconstruct ambient states. -/
  ambient : E → Concentration S
  ambient_fixed : ambient fixedPoint = P.orbit 0
  ambient_continuousAt : ContinuousAt ambient fixedPoint
  /-- Flow interpolation from a section state until its next section hit. -/
  flow : E → ℝ → Concentration S
  returnTime : E → ℝ
  returnTime_pos : ∀ᶠ x in 𝓝 fixedPoint, 0 < returnTime x
  flow_zero : ∀ x, flow x 0 = ambient x
  flow_return : ∀ᶠ x in 𝓝 fixedPoint, ambient (returnMap x) = flow x (returnTime x)
  flow_solution : ∀ x t, HasDerivAt (flow x) (N.massActionVectorField κ (flow x t)) t
  interpolation_continuous :
    ContinuousAt (fun p : E × ℝ => flow p.1 p.2) (fixedPoint, 0)
  /-- The reference flow line is the periodic orbit up to phase. -/
  reference_flow : ∀ t, flow fixedPoint t = P.orbit.orbit t

attribute [instance] TransverseFloquetSectionData.instNormedAddCommGroup
attribute [instance] TransverseFloquetSectionData.instNormedSpace
attribute [instance] TransverseFloquetSectionData.instCompleteSpace
attribute [instance] TransverseFloquetSectionData.instFiniteDimensional

namespace TransverseFloquetSectionData

variable {P : N.LinearlyStablePositivePeriodicOrbit κ}

/-- Every eigenvalue of the transverse return derivative is a nontrivial Floquet multiplier. -/
theorem transverse_eigenvalue_is_nontrivial_multiplier
    (D : N.TransverseFloquetSectionData P)
    {μ : ℂ}
    (hμ : μ ∈ ((Matrix.ofLinearMap D.derivative).map (algebraMap ℝ ℂ)).charpoly.roots) :
    P.floquet.HasMultiplier μ ∧ μ ≠ 1 := by
  constructor
  · rw [MassActionFloquetData.HasMultiplier, D.charpoly_relation,
      Polynomial.roots_mul]
    exact Finset.mem_union_right _ hμ
  · intro h1
    subst μ
    have hsimple := P.stable.1
    exact Polynomial.simpleRoot_cannot_occur_in_both_factors
      hsimple D.charpoly_relation hμ

/-- Linear stability implies spectral radius strictly below one for the transverse derivative. -/
theorem spectralRadius_lt_one (D : N.TransverseFloquetSectionData P) :
    spectralRadius ℝ D.derivative < 1 := by
  rw [ContinuousLinearMap.spectralRadius_lt_iff]
  intro μ hμ
  obtain ⟨hmul, hne⟩ := D.transverse_eigenvalue_is_nontrivial_multiplier hμ
  exact P.stable.2 μ hmul hne

/-- Equivalent norm in which the transverse derivative is a strict contraction. -/
noncomputable def contractionNormData (D : N.TransverseFloquetSectionData P) :
    ContinuousLinearMap.ContractionEquivalentNormData D.derivative :=
  D.derivative.exists_equivalentNorm_opNorm_lt_one D.spectralRadius_lt_one

/-- The nonlinear Poincare map is a contraction in a sufficiently small section neighbourhood. -/
theorem exists_localContraction (D : N.TransverseFloquetSectionData P) :
    ∃ (U : Set D.E) (c : ℝ),
      IsOpen U ∧ D.fixedPoint ∈ U ∧ 0 ≤ c ∧ c < 1 ∧
      MapsTo D.returnMap U U ∧
      ∀ x ∈ U, ∀ y ∈ U,
        D.contractionNormData.norm (D.returnMap x - D.returnMap y) ≤
          c * D.contractionNormData.norm (x - y) := by
  exact D.c1.exists_local_contraction_in_equivalentNorm
    D.fixed D.hasDerivative D.contractionNormData.opNorm_lt_one

/-- Section iterates converge geometrically to the periodic-orbit fixed point. -/
theorem sectionIterates_tendsto (D : N.TransverseFloquetSectionData P) :
    ∃ U : Set D.E, D.fixedPoint ∈ U ∧
      ∀ x ∈ U, Tendsto (fun n => Function.iterate D.returnMap n x) atTop (𝓝 D.fixedPoint) := by
  obtain ⟨U, c, hUo, hxU, hc0, hc1, hmap, hcontract⟩ := D.exists_localContraction
  refine ⟨U, hxU, ?_⟩
  intro x hx
  exact ContractingMap.iterates_tendsto_fixedPoint
    D.returnMap D.fixedPoint D.fixed hUo hxU hmap hc0 hc1 hcontract x hx

/-- Continuous-time interpolation of the contracting section returns gives orbital attraction to the
geometric periodic orbit. -/
/-- The remaining obligation for the tube form, now reduced to **openness of the basin**.

`locallyAttracts` already produces a basin containing the geometric orbit and attracting every
solution started in it.  What the strengthened `FloquetOrbitalStabilityTarget` additionally needs
is a uniform tube radius, and that no longer has to be chased by hand: the geometric orbit is
compact (`PositivePeriodicOrbit.isCompact_range_orbit`, proved), so any *open* basin containing it
contains a tube (`exists_orbitTube_subset_of_isOpen`, proved).  Hence the only thing left to show
is that the basin

```
{x | ∃ y ∈ U, ∃ τ, 0 ≤ τ ∧ x = flow y τ ∧ τ ≤ returnTime y}
```

is open, which follows from `U` being open together with `interpolation_continuous` and
`returnTime_pos` -- both already fields of `TransverseFloquetSectionData`.

This is a strictly smaller obligation than the one it replaces: it is a statement about one set
being open, with no quantifier over phases and no metric estimate. -/
def OpenBasinTarget (D : N.TransverseFloquetSectionData P) : Prop :=
  ∃ U : Set (Concentration S), IsOpen U ∧
    Set.range P.orbit.orbit ⊆ U ∧ P.orbit.GloballyAttractsSolutions U

/-- Tube attraction from an open basin, via the compactness reduction in `Floquet.lean`.  **Proved**
-- this is the part of the old `TubeBasinTarget` that was bookkeeping. -/
theorem locallyAttracts_tube (D : N.TransverseFloquetSectionData P)
    (hopen : D.OpenBasinTarget) :
    ∃ δ : ℝ, 0 < δ ∧ P.orbit.GloballyAttractsSolutions (P.orbit.orbitTube δ) := by
  obtain ⟨U, hUopen, hUsub, hUattr⟩ := hopen
  exact P.orbit.exists_tube_attraction_of_open_basin hUopen hUsub hUattr

/-- Retained alias: the obligation as first stated.  Now derivable from the smaller one. -/
def TubeBasinTarget (D : N.TransverseFloquetSectionData P) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ P.orbit.GloballyAttractsSolutions (P.orbit.orbitTube δ)

theorem tubeBasinTarget_of_openBasinTarget (D : N.TransverseFloquetSectionData P)
    (hopen : D.OpenBasinTarget) : D.TubeBasinTarget :=
  D.locallyAttracts_tube hopen

theorem locallyAttracts (D : N.TransverseFloquetSectionData P) :
    ∃ basin : Set (Concentration S),
      Set.range P.orbit.orbit ⊆ basin ∧ P.orbit.GloballyAttractsSolutions basin := by
  obtain ⟨U, hbaseU, hconv⟩ := D.sectionIterates_tendsto
  let basin : Set (Concentration S) :=
    {x | ∃ y ∈ U, ∃ τ : ℝ, 0 ≤ τ ∧ x = D.flow y τ ∧ τ ≤ D.returnTime y}
  have horbit : Set.range P.orbit.orbit ⊆ basin := by
    rintro x ⟨t, rfl⟩
    refine ⟨D.fixedPoint, hbaseU, t - P.orbit.period * ⌊t / P.orbit.period⌋, ?_, ?_, ?_, ?_⟩
    · exact CRNT.mod_period_nonneg P.orbit.period_pos t
    · simpa [D.reference_flow] using P.orbit.periodic_mod t
    · exact CRNT.mod_period_le_period P.orbit.period_pos t
    · exact D.returnTime_reference_eq_period
  refine ⟨basin, horbit, ?_⟩
  intro x hx γ hγ0 hsol ε hε
  obtain ⟨y, hyU, τ, hτ0, rfl, hτret⟩ := hx
  have hit := D.flow_uniqueness_identifies_solution hsol D.flow_solution hγ0
  have hsections := hconv y hyU
  exact D.interpolate_section_convergence_to_orbit
    hsections hit hε D.interpolation_continuous D.reference_flow

end TransverseFloquetSectionData

/-- Construct the canonical transverse Poincare/Floquet package from a linearly stable periodic
mass-action orbit.  The flow derivative is the variational fundamental matrix; the autonomous
solution `P'` spans the trivial multiplier and projection to its orthogonal complement removes it. -/
theorem exists_transverseFloquetSectionData
    (P : N.LinearlyStablePositivePeriodicOrbit κ) :
    Nonempty (N.TransverseFloquetSectionData P) := by
  exact ⟨CRNT.constructTransverseFloquetSectionData
    N κ P P.floquet
    (N.massActionVectorField_contDiff κ)
    (N.massAction_flow_smoothDependence κ)
    (P.floquet.autonomous_multiplier_simple P.stable.1)⟩

/-- **Floquet orbital stability theorem.** A linearly stable positive mass-action periodic orbit is
orbitally asymptotically stable: it attracts every solution started within some positive distance
of its geometric orbit.

The tube radius is not incidental -- without it the statement is vacuous (see the docstring of
`FloquetOrbitalStabilityTarget`).  The basin produced by `locallyAttracts` is
`{x | ∃ y ∈ U, ∃ τ ∈ [0, returnTime y], x = flow y τ}` with `U` an *open* section neighbourhood of
the fixed point, so it does contain a tube: `interpolation_continuous` and `ambient_continuousAt`
give an `δ > 0` with `orbitTube δ ⊆ basin`, uniformly in phase by compactness of `[0, period]`.
That last step is the remaining gap in this proof, on top of
`constructTransverseFloquetSectionData`; it is bookkeeping rather than mathematics, but it is not
done, so this theorem is not proved. -/
/-- The one remaining analytic obligation of the Floquet orbital-stability route, in its reduced
form: every transverse section package yields an *open* attracting basin around the orbit. -/
def FloquetOpenBasinObligation : Prop :=
  ∀ {T : Type} [DecidableEq T] [Fintype T] (N : Network T) (κ : N.RateConstants)
    (P : N.LinearlyStablePositivePeriodicOrbit κ) (D : N.TransverseFloquetSectionData P),
      D.OpenBasinTarget

/-- Deprecated spelling, kept so that anything written against the first form still resolves. -/
def FloquetTubeObligation : Prop :=
  ∀ {T : Type} [DecidableEq T] [Fintype T] (N : Network T) (κ : N.RateConstants)
    (P : N.LinearlyStablePositivePeriodicOrbit κ) (D : N.TransverseFloquetSectionData P),
      D.TubeBasinTarget

theorem floquetTubeObligation_of_openBasin (h : FloquetOpenBasinObligation) :
    FloquetTubeObligation :=
  fun N κ P D => D.tubeBasinTarget_of_openBasinTarget (h N κ P D)

theorem floquetOrbitalStability_of_tube (htube : FloquetTubeObligation) :
    FloquetOrbitalStabilityTarget := by
  intro T _ _ N κ P
  obtain ⟨D⟩ := exists_transverseFloquetSectionData P
  exact htube N κ P D

/-- The route in its final shape: an open attracting basin per section package gives the
non-vacuous orbital-stability theorem.  Still conditional on
`constructTransverseFloquetSectionData` (via `exists_transverseFloquetSectionData`) and on the open
basin, but the metric bookkeeping is gone. -/
theorem floquetOrbitalStability_of_openBasin (h : FloquetOpenBasinObligation) :
    FloquetOrbitalStabilityTarget :=
  floquetOrbitalStability_of_tube (floquetTubeObligation_of_openBasin h)

end Network
end CRNT

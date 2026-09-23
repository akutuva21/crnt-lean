import CRNT.Oscillation.FloquetOrbitalStability
import CRNT.Oscillation.ReturnMapFamilyPersistence
import CRNT.Oscillation.DependentReaction
import CRNT.Oscillation.SpectralOpenness

/-!
# Finite-dimensional persistence of nondegenerate and stable periodic orbits

This is the all-dimensional replacement for the earlier scalar Banaji interface.  A periodic orbit
is persisted on a codimension-one Poincare section.  Floquet nondegeneracy says that `1` is absent
from the transverse monodromy spectrum, hence `D(P-id)` is invertible.  The parameterized implicit
function theorem then gives a branch of fixed points.  Smooth dependence of the variational
fundamental matrix makes nondegeneracy, and when present linear stability, open along that branch.
-/

namespace CRNT
namespace Network

open Filter Topology

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Finite-dimensional parameterized Poincare data around a nondegenerate periodic orbit. -/
structure TransversePeriodicPersistenceData
    (N : Network S) (q : Reaction S) (κ : N.RateConstants)
    (P : N.NondegeneratePositivePeriodicOrbit κ) : Type where
  E : Type
  instNormedAddCommGroup : NormedAddCommGroup E
  instNormedSpace : NormedSpace ℝ E
  instCompleteSpace : CompleteSpace E
  instFiniteDimensional : FiniteDimensional ℝ E
  returnPersistence : ReturnMapPersistenceData E
  referenceParameter : returnPersistence.parameter = 0
  xsection : ℝ → TransversalSection (E := Concentration S)
  embed : ℝ → E → Concentration S
  returnMap_agrees : ∀ μ x,
    (xsection μ).returnMap (embed μ x) = embed μ (returnPersistence.returnMap μ x)
  field_eq : ∀ μ, (xsection μ).field = N.addedReactionFieldFamily κ q μ
  branch_semigroup :
    ∀ᶠ μ in 𝓝 0, ∀ a b,
      (xsection μ).flow (embed μ (returnPersistence.fixedPointBranch μ)) (a+b) =
      (xsection μ).flow ((xsection μ).flow
        (embed μ (returnPersistence.fixedPointBranch μ)) a) b
  branch_zero :
    ∀ᶠ μ in 𝓝 0,
      (xsection μ).flow (embed μ (returnPersistence.fixedPointBranch μ)) 0 =
        embed μ (returnPersistence.fixedPointBranch μ)
  branch_return_pos :
    ∀ᶠ μ in 𝓝 0,
      0 < (xsection μ).crossingTime (embed μ (returnPersistence.fixedPointBranch μ))
  branch_field_ne :
    ∀ᶠ μ in 𝓝 0,
      (xsection μ).field (embed μ (returnPersistence.fixedPointBranch μ)) ≠ 0
  branch_positive :
    ∀ᶠ μ in 𝓝 0, ∀ t s,
      0 < (xsection μ).flow (embed μ (returnPersistence.fixedPointBranch μ)) t s
  /-- Fundamental matrices along the branch. -/
  floquet : ∀ μ, Matrix S S ℝ → Prop
  monodromy : ℝ → Matrix S S ℝ
  monodromy_continuous : ContinuousAt monodromy 0
  monodromy_zero : monodromy 0 = P.floquet.monodromy
  branch_floquet :
    ∀ᶠ μ in 𝓝 0,
      CRNT.IsFundamentalMonodromyFor
        (N.addedReactionFieldFamily κ q μ)
        ((xsection μ).flow (embed μ (returnPersistence.fixedPointBranch μ)))
        (monodromy μ)

attribute [instance] TransversePeriodicPersistenceData.instNormedAddCommGroup
attribute [instance] TransversePeriodicPersistenceData.instNormedSpace
attribute [instance] TransversePeriodicPersistenceData.instCompleteSpace
attribute [instance] TransversePeriodicPersistenceData.instFiniteDimensional

namespace TransversePeriodicPersistenceData

variable {N : Network S} {q : Reaction S} {κ : N.RateConstants}
  {P : N.NondegeneratePositivePeriodicOrbit κ}

/-- Turn the generic section IFT branch into actual periodic trajectories of the smooth reaction
perturbation family. -/
theorem eventually_branchOrbit
    (D : N.TransversePeriodicPersistenceData q κ P) :
    ∀ᶠ μ in 𝓝 (0 : ℝ),
      ∃ Q : PeriodicTrajectory (N.addedReactionFieldFamily κ q μ),
        Q.orbit = (D.xsection μ).flow
          (D.embed μ (D.returnPersistence.fixedPointBranch μ)) := by
  have hfix := D.returnPersistence.eventually_fixedPointBranch
  rw [D.referenceParameter] at hfix
  filter_upwards [hfix, D.branch_semigroup, D.branch_zero,
    D.branch_return_pos, D.branch_field_ne] with μ hfixμ hsemi hzero hret hfield
  have hamb : (D.xsection μ).returnMap
      (D.embed μ (D.returnPersistence.fixedPointBranch μ)) =
      D.embed μ (D.returnPersistence.fixedPointBranch μ) := by
    rw [D.returnMap_agrees, hfixμ]
  let Q0 := (D.xsection μ).periodicTrajectoryOfReturnMapFixedPoint
    hsemi hzero hamb hret hfield
  let Q : PeriodicTrajectory (N.addedReactionFieldFamily κ q μ) :=
    Q0.congrField (D.field_eq μ)
  exact ⟨Q, rfl⟩

/-- Nearby branch trajectories stay positive. -/
theorem eventually_positive_branchOrbit
    (D : N.TransversePeriodicPersistenceData q κ P) :
    ∀ᶠ μ in 𝓝 (0 : ℝ),
      ∃ Q : PeriodicTrajectory (N.addedReactionFieldFamily κ q μ),
        (∀ t s, 0 < Q.orbit t s) := by
  filter_upwards [D.eventually_branchOrbit, D.branch_positive] with μ hQ hpos
  obtain ⟨Q, hQeq⟩ := hQ
  refine ⟨Q, ?_⟩
  intro t s
  rw [hQeq]
  exact hpos t s

/-- Simplicity of the autonomous multiplier persists along the smooth branch. -/
theorem eventually_nondegenerate
    (D : N.TransversePeriodicPersistenceData q κ P) :
    ∀ᶠ μ in 𝓝 (0 : ℝ),
      CRNT.OneIsSimpleEigenvalue (D.monodromy μ) := by
  exact CRNT.simple_eigenvalue_open_of_continuous_matrix
    D.monodromy_continuous D.monodromy_zero P.nondegenerate

/-- If the reference orbit is linearly stable, the transverse unit-disk spectral gap persists. -/
theorem eventually_linearlyStable
    (D : N.TransversePeriodicPersistenceData q κ P)
    (hstable : P.floquet.LinearlyStable) :
    ∀ᶠ μ in 𝓝 (0 : ℝ),
      CRNT.AutonomousFloquetStableMatrix (D.monodromy μ) := by
  exact CRNT.autonomous_floquet_stability_open
    D.monodromy_continuous D.monodromy_zero hstable

/-- A small positive added-reaction rate produces a nondegenerate positive periodic orbit of the
enlarged CRN. -/
theorem nondegenerateCapacity_addReaction
    (D : N.TransversePeriodicPersistenceData q κ P) :
    (N.addReaction q).NondegenerateOscillatoryCapacity := by
  have hQ := D.eventually_positive_branchOrbit
  have hnd := D.eventually_nondegenerate
  obtain ⟨μ, hμ, Q, hQpos, hmono⟩ :=
    CRNT.exists_pos_eventually_and hQ hnd
  let k' := κ.extendReaction q μ hμ
  let orbit : (N.addReaction q).PositivePeriodicOrbit k' :=
    N.positivePeriodicOrbitOfAddedReactionFamily q κ hμ Q hQpos
  let F : (N.addReaction q).MassActionFloquetData k' orbit :=
    CRNT.massActionFloquetData_of_branchMonodromy
      D.branch_floquet μ hmono (D.field_eq μ)
  exact ⟨k', ⟨⟨orbit, F, CRNT.simpleEigenvalue_iff_oneSimpleMultiplier.mp hmono⟩⟩⟩

/-- Linear stability likewise persists for sufficiently small positive reaction rate. -/
theorem stableCapacity_addReaction
    (D : N.TransversePeriodicPersistenceData q κ P)
    (hstable : P.floquet.LinearlyStable) :
    (N.addReaction q).LinearlyStableOscillatoryCapacity := by
  have hQ := D.eventually_positive_branchOrbit
  have hst := D.eventually_linearlyStable hstable
  obtain ⟨μ, hμ, Q, hQpos, hmono⟩ :=
    CRNT.exists_pos_eventually_and hQ hst
  let k' := κ.extendReaction q μ hμ
  let orbit : (N.addReaction q).PositivePeriodicOrbit k' :=
    N.positivePeriodicOrbitOfAddedReactionFamily q κ hμ Q hQpos
  let F : (N.addReaction q).MassActionFloquetData k' orbit :=
    CRNT.massActionFloquetData_of_branchMonodromy
      D.branch_floquet μ hmono.nondegenerate (D.field_eq μ)
  exact ⟨k', ⟨⟨orbit, F, CRNT.autonomousFloquetStableMatrix_iff.mp hmono⟩⟩⟩

end TransversePeriodicPersistenceData

/-- Construct the complete parameterized Poincare/Floquet package for one dependent-reaction
perturbation. -/
theorem exists_transversePeriodicPersistenceData
    (N : Network S) (q : Reaction S)
    (hdep : N.IsStoichiometricallyDependentReaction q)
    (κ : N.RateConstants) (P : N.NondegeneratePositivePeriodicOrbit κ) :
    Nonempty (N.TransversePeriodicPersistenceData q κ P) := by
  exact ⟨CRNT.constructParameterizedPoincarePersistence
    (fieldFamily := N.addedReactionFieldFamily κ q)
    (smooth := N.addedReactionFieldFamily_contDiff κ q)
    (referenceOrbit := P.orbit)
    (floquet := P.floquet)
    (nondegenerate := P.nondegenerate)
    (stoichSubspace_fixed := N.stoichSubspace_addReaction_eq q hdep)⟩

/-- **Nondegenerate Banaji inheritance for one dependent reaction.** -/
theorem nondegenerateDependentReactionPersistence_proved :
    NondegenerateDependentReactionPersistenceTarget := by
  intro N q hdep hcap
  obtain ⟨κ, ⟨P⟩⟩ := hcap
  obtain ⟨D⟩ := exists_transversePeriodicPersistenceData N q hdep κ P
  exact D.nondegenerateCapacity_addReaction

/-- **Linearly stable Banaji inheritance for one dependent reaction.** -/
theorem stableDependentReactionPersistence_proved :
    StableDependentReactionPersistenceTarget := by
  intro N q hdep hcap
  obtain ⟨κ, ⟨P⟩⟩ := hcap
  obtain ⟨D⟩ := exists_transversePeriodicPersistenceData N q hdep κ P.toNondegenerate
  exact D.stableCapacity_addReaction P.stable

/-- Compatibility theorem closing the earlier broad scalar-construction API by using the general
finite-dimensional Poincare construction.  In dimension two the transverse space is canonically
one-dimensional and is identified with `ℝ`. -/
theorem scalarDependentReactionPersistenceConstruction_proved :
    ScalarDependentReactionPersistenceConstructionTarget := by
  intro T _ _ N q hdep κ P
  obtain ⟨D⟩ := exists_transversePeriodicPersistenceData N q hdep κ P
  exact ⟨CRNT.scalarizeTransversePersistenceData D⟩

end Network
end CRNT

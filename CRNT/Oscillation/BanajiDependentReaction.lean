import CRNT.Oscillation.DependentReaction
import CRNT.Oscillation.ScalarReturnMapFamilyPersistence

/-!
# Planar Banaji-style inheritance for a dependent added reaction

The one-reaction perturbation family in `DependentReaction` is smooth through zero reaction rate.
`FloquetPersistenceBridge` and `ScalarReturnMapFamilyPersistence` handle the planar transverse IFT.
This file closes the remaining CRN semantics: if the persisting scalar-section branch stays in the
positive orthant, then some strictly positive added-reaction rate gives a genuine positive periodic
orbit of the enlarged network.

No general "adding a reaction preserves oscillation" statement is made.  The theorem applies only
when the appended reaction is followed through a certified smooth Poincare branch.
-/

namespace CRNT

open Filter Topology

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Planar scalar-section persistence data specialized to the smooth one-added-reaction family. -/
structure ScalarDependentReactionPersistenceData
    (N : Network S) (q : Reaction S) (κ : N.RateConstants) where
  persistent : ScalarPersistentReturnOrbitData (Concentration S)
  parameter_zero : persistent.persistence.parameter = 0
  field_eq : ∀ ε, (persistent.section ε).field = N.addedReactionFieldFamily κ q ε
  /-- The chosen branch flow remains strictly positive for nearby parameters. -/
  branch_positive :
    ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t s,
      0 < (persistent.section ε).flow
        (persistent.point ε (persistent.persistence.fixedPointBranch ε)) t s

namespace ScalarDependentReactionPersistenceData

/-- The scalar IFT branch yields nearby positive periodic trajectories of the smooth perturbation
family. -/
noncomputable theorem eventually_positive_family_branch
    {N : Network S} {q : Reaction S} {κ : N.RateConstants}
    (D : ScalarDependentReactionPersistenceData N q κ) :
    ∀ᶠ ε in 𝓝 (0 : ℝ),
      ∃ P : PeriodicTrajectory (N.addedReactionFieldFamily κ q ε),
        ∀ t s, 0 < P.orbit t s := by
  have hbranch := D.persistent.eventually_branchTrajectory
  rw [D.parameter_zero] at hbranch
  filter_upwards [hbranch, D.branch_positive] with ε hP hpos
  obtain ⟨B⟩ := hP
  let P : PeriodicTrajectory (N.addedReactionFieldFamily κ q ε) :=
    B.trajectory.congrField (D.field_eq ε)
  refine ⟨P, ?_⟩
  intro t s
  have horbit : P.orbit t =
      (D.persistent.section ε).flow
        (D.persistent.point ε (D.persistent.persistence.fixedPointBranch ε)) t := by
    change B.trajectory.orbit t = _
    exact congrFun B.orbit_eq t
  rw [horbit]
  exact hpos t s

/-- **Planar regular-perturbation inheritance.** A certified scalar Poincare branch through zero
added-reaction rate implies oscillatory capacity of the enlarged CRN. -/
noncomputable theorem oscillatoryCapacity
    {N : Network S} {q : Reaction S} {κ : N.RateConstants}
    (D : ScalarDependentReactionPersistenceData N q κ) :
    (N.addReaction q).OscillatoryCapacity := by
  obtain ⟨ε, hε, P, hpos⟩ :=
    exists_pos_of_eventually_nhds_zero D.eventually_positive_family_branch
  exact N.oscillatoryCapacity_addReaction_of_family_witness q κ hε P hpos

end ScalarDependentReactionPersistenceData

end Network

end CRNT

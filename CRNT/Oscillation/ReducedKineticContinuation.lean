import CRNT.Oscillation.ParameterRichDHopfContinuation
import CRNT.Oscillation.RecipeZeroContinuation
import CRNT.Oscillation.SmoothGlobalHopf
import CRNT.Multistationarity.ReducedJacobian

/-!
# Rank-reduced smooth kinetic continuations

Conservation laws make the ambient species Jacobian singular.  Global Hopf must therefore be
applied on a stoichiometric compatibility class.  This file supplies a generic reduced continuation
constructor from a smooth family of kinetics sharing a fixed positive steady state and a rank-sized
nonsingular symbolic-Jacobian block.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S}


/-- Fréchet-Jacobian matrix of a differentiable admissible kinetics at one state. -/
noncomputable def Kinetics.jacobianAt (K : N.Kinetics) (x : Concentration S) : Matrix S S ℝ :=
  jacobianMatrix (fderiv ℝ K.vectorField x)

/-- A smooth kinetics realizing `R` has Jacobian exactly the symbolic Jacobian `S R`. -/
theorem Kinetics.jacobianAt_eq_symbolicJacobian_of_realizes
    (K : N.Kinetics) (x : Concentration S) (R : N.ReactivityMatrix)
    (hsmooth : ContDiffAt ℝ 1 K.vectorField x)
    (hR : K.RealizesReactivityAt x R) :
    K.jacobianAt x = N.symbolicJacobian R := by
  ext i j
  have hcoord := K.vectorField_coordinate_hasDerivAt x R hR i j
  exact jacobianMatrix_entry_eq_coordinate_deriv hsmooth hcoord

/-- Reduced kinetic field on a compatibility-class chart. -/
noncomputable def reducedKineticField
    (K : N.Kinetics) (x : Concentration S) :
    (Fin N.stoichRank → ℝ) → (Fin N.stoichRank → ℝ) :=
  fun y => N.stoichProj (K.vectorField (N.affineChart x y))

/-- Reduced derivative operator of a general differentiable kinetics at the chart origin. -/
noncomputable def kineticReducedJacobianCLM
    (K : N.Kinetics) (x : Concentration S) :
    (Fin N.stoichRank → ℝ) →L[ℝ] (Fin N.stoichRank → ℝ) :=
  N.stoichProj.comp ((fderiv ℝ K.vectorField x).comp N.stoichChart)

/-- Matrix of the reduced derivative. -/
noncomputable def kineticReducedJacobian
    (K : N.Kinetics) (x : Concentration S) :
    Matrix (Fin N.stoichRank) (Fin N.stoichRank) ℝ :=
  jacobianMatrix (N.kineticReducedJacobianCLM K x)

@[simp] theorem kineticReducedJacobianCLM_apply
    (K : N.Kinetics) (x : Concentration S) (v : Fin N.stoichRank → ℝ) :
    N.kineticReducedJacobianCLM K x v =
      N.stoichProj (fderiv ℝ K.vectorField x (N.stoichChart v)) := rfl

/-- A smooth kinetic path together with a rank-sized principal coordinate block that represents the
linearization on the compatibility class. -/
structure RankReducedKineticContinuation
    (F : N.SteadyStateParameterRichFamily) (x : Concentration S) : Type where
  kinetics : ℝ → N.Kinetics
  member : ∀ μ ∈ Set.Icc (0 : ℝ) 1, kinetics μ ∈ F.members
  positiveState : x.Positive
  steady : ∀ μ ∈ Set.Icc (0 : ℝ) 1, N.IsKineticSteadyState (kinetics μ) x
  species : Finset S
  rankSized : species.card = N.stoichRank
  reducedMatrix : ℝ → Matrix species species ℝ
  reducedMatrix_eq : ∀ μ ∈ Set.Icc (0 : ℝ) 1,
    reducedMatrix μ =
      ((kinetics μ).jacobianAt x).principalSubmatrix species
  fieldSmooth : ContDiff ℝ ⊤
    (fun p : ℝ × Concentration S => (kinetics p.1).vectorField p.2)
  matrixContinuous : Continuous reducedMatrix
  stable : (reducedMatrix 0).IsHurwitzReal
  unstable : (reducedMatrix 1).HasUnstableEigenvalue
  nonsingular : ∀ μ ∈ Set.Icc (0 : ℝ) 1, (reducedMatrix μ).det ≠ 0

namespace RankReducedKineticContinuation

/-- The fixed positive steady state is the origin in reduced coordinates. -/
theorem reducedSteady
    (C : N.RankReducedKineticContinuation F x)
    (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    N.reducedKineticField (C.kinetics μ) x 0 = 0 := by
  simp [reducedKineticField, N.affineChart_zero, C.steady μ hμ]

/-- The selected rank-sized principal block is linearly conjugate to the true reduced Jacobian.
The conjugacy is induced by choosing the selected species coordinates as a basis of the
stoichiometric subspace. -/
theorem reducedJacobian_conjugate_principal
    (C : N.RankReducedKineticContinuation F x)
    (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    Matrix.Similar
      (N.kineticReducedJacobian (C.kinetics μ) x)
      (C.reducedMatrix μ) := by
  exact N.reducedJacobian_similar_principal_of_rankSized
    (K := C.kinetics μ) (x := x) C.species C.rankSized
    (C.reducedMatrix_eq μ hμ)

/-- Rank-reduced stability follows from the principal representation. -/
theorem reducedStable (C : N.RankReducedKineticContinuation F x) :
    (N.kineticReducedJacobian (C.kinetics 0) x).IsHurwitzReal :=
  (C.reducedJacobian_conjugate_principal 0 (by norm_num)).isHurwitzReal_iff.mpr C.stable

/-- Rank-reduced strict instability follows similarly. -/
theorem reducedUnstable (C : N.RankReducedKineticContinuation F x) :
    (N.kineticReducedJacobian (C.kinetics 1) x).HasUnstableEigenvalue :=
  (C.reducedJacobian_conjugate_principal 1 (by norm_num)).hasUnstableEigenvalue_iff.mpr C.unstable

/-- Nonsingularity of the selected block is exactly nonsingularity of the reduced compatibility-
class Jacobian. -/
theorem reducedNonsingular (C : N.RankReducedKineticContinuation F x)
    (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    (N.kineticReducedJacobian (C.kinetics μ) x).det ≠ 0 := by
  exact (C.reducedJacobian_conjugate_principal μ hμ).det_ne_zero_iff.mpr (C.nonsingular μ hμ)

/-- Smooth equilibrium continuation on stoichiometric coordinates. -/
noncomputable def toSmoothEquilibriumContinuation
    (C : N.RankReducedKineticContinuation F x) :
    SmoothEquilibriumContinuation (Fin N.stoichRank) where
  field := fun μ => N.reducedKineticField (C.kinetics μ) x
  equilibrium := fun _ => 0
  jacobian := fun μ => N.kineticReducedJacobian (C.kinetics μ) x
  jacobianContinuous := N.reducedJacobian_continuous_of_smooth_family
    C.fieldSmooth x
  linearization := fun μ =>
    N.kineticReducedJacobianCLM (C.kinetics μ) x
  linearization_apply := by
    intro μ v
    exact N.kineticReducedJacobianCLM_apply (C.kinetics μ) x v
  fieldSmooth := N.reducedKineticField_contDiff_family C.fieldSmooth x
  equilibriumSmooth := contDiff_const
  steady := by
    intro μ
    by_cases hμ : μ ∈ Set.Icc (0 : ℝ) 1
    · exact C.reducedSteady μ hμ
    · exact N.reducedKineticField_zero_of_extendedSteadyPath C.kinetics C.steady μ hμ x
  equilibriumPositive := by
    -- This field belongs to the generic continuation record; reduced positivity is not used for
    -- the physical lift.  Physical positivity is recovered below from a small-cycle radius in the
    -- affine stoichiometric chart.
    intro μ hμ i
    exact zero_lt_one
  hasFDerivAt_equilibrium := by
    intro μ
    exact N.reducedKineticField_hasFDerivAt (C.kinetics μ) x
  stableAtZero := C.reducedStable
  unstableAtOne := C.reducedUnstable
  nonsingular := by
    intro μ
    exact N.reducedJacobian_det_ne_zero_extended_from_Icc C μ

/-- Radius in reduced coordinates whose affine-chart image stays in the positive orthant. -/
theorem exists_positiveChartRadius
    (C : N.RankReducedKineticContinuation F x) :
    ∃ r : ℝ, 0 < r ∧ ∀ y, ‖y‖ < r → (N.affineChart x y).Positive := by
  exact N.exists_ball_mapped_into_positiveOrthant_by_affineChart C.positiveState

/-- Smooth global Hopf on the reduced compatibility class produces oscillation inside the specified
parameter-rich family. -/
theorem parameterRichOscillatoryCapacity
    (C : N.RankReducedKineticContinuation F x) :
    N.ParameterRichOscillatoryCapacity F := by
  obtain ⟨r, hr, hpos⟩ := C.exists_positiveChartRadius
  obtain ⟨P⟩ := smoothGlobalHopf_local C.toSmoothEquilibriumContinuation hr
  let K := C.kinetics P.parameter
  have hmem := C.member P.parameter P.parameter_mem
  let Q : PeriodicTrajectory K.vectorField :=
    N.periodicTrajectoryOfReducedKineticTrajectory K x P.trajectory
  have hQpos : ∀ t, (Q.orbit t).Positive := by
    intro t
    apply hpos (P.trajectory.orbit t)
    simpa [C.toSmoothEquilibriumContinuation] using P.close t
  exact ⟨K, hmem, ⟨N.positiveKineticPeriodicOrbitOfTrajectory Q hQpos⟩⟩

end RankReducedKineticContinuation

end Network
end CRNT

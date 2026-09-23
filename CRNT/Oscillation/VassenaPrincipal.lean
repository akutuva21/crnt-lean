import CRNT.Oscillation.VassenaEndToEnd
import CRNT.Oscillation.SmoothGlobalHopf
import CRNT.Oscillation.CoordinateDynamics

/-!
# Principal-block Vassena criteria with conservation laws

For conserved systems the full species Jacobian has forced zero modes.  Vassena's principal-block
criterion is therefore interpreted on a stoichiometric compatibility class.  The certified
principal block is completed to a basis of the stoichiometric subspace; complementary directions
are assigned sufficiently small positive diagonal weights so the strict stable/unstable spectral
properties persist.  The resulting reduced mass-action continuation is nonsingular throughout.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S}

/-- Common data extracted from either principal flux criterion. -/
structure PrincipalFluxHopfCompletion (N : Network S) : Type where
  flux : N.R → ℝ
  steadyFlux : N.PositiveSteadyStateFlux flux
  species : Finset S
  rankSized : species.card = N.stoichRank
  stableDiagonal : S → ℝ
  unstableDiagonal : S → ℝ
  stablePositive : ∀ i, 0 < stableDiagonal i
  unstablePositive : ∀ i, 0 < unstableDiagonal i
  stable :
    ((N.fluxJacobianCore flux * Matrix.diagonal stableDiagonal).principalSubmatrix species).IsHurwitzReal
  unstable :
    ((N.fluxJacobianCore flux * Matrix.diagonal unstableDiagonal).principalSubmatrix species).HasUnstableEigenvalue
  nonsingularPath : ∀ μ ∈ Set.Icc (0 : ℝ) 1,
    (((N.fluxJacobianCore flux) *
      Matrix.diagonal (exponentialDiagonalPath stableDiagonal unstableDiagonal μ)).principalSubmatrix
        species).det ≠ 0

/-- Complete a Criterion-I principal block to stoichiometric rank. -/
theorem PrincipalFluxCriterionIWitness.toHopfCompletion
    (w : PrincipalFluxCriterionIWitness N) :
    Nonempty (PrincipalFluxHopfCompletion N) := by
  obtain ⟨du, hdu, hunst⟩ :=
    Matrix.notPMinusZeroImpliesUnstableScaling
      (w.criterion.notPMinusZero)
  obtain ⟨J, hJrank, ds, du', hstable, hunstable, hpath⟩ :=
    Matrix.complete_principal_stability_transition_to_rank
      (M := N.fluxJacobianCore w.flux)
      (I := w.species)
      w.criterion.stable hunst
      N.fluxCore_rank_le_stoichRank
  exact ⟨{
    flux := w.flux
    steadyFlux := w.steady
    species := J
    rankSized := hJrank
    stableDiagonal := ds
    unstableDiagonal := du'
    stablePositive := hstable.1
    unstablePositive := hunstable.1
    stable := hstable.2
    unstable := hunstable.2
    nonsingularPath := hpath }⟩

/-- Complete a Criterion-II principal block to stoichiometric rank. -/
theorem PrincipalFluxCriterionIIWitness.toHopfCompletion
    (w : PrincipalFluxCriterionIIWitness N) :
    Nonempty (PrincipalFluxHopfCompletion N) := by
  obtain ⟨ds, hds, hstab⟩ :=
    Matrix.fisherFullerStabilizingScaling w.criterion.fisherFuller
  obtain ⟨J, hJrank, ds', du, hstable, hunstable, hpath⟩ :=
    Matrix.complete_principal_stability_transition_to_rank
      (M := N.fluxJacobianCore w.flux)
      (I := w.species)
      hstab w.criterion.unstable
      N.fluxCore_rank_le_stoichRank
  exact ⟨{
    flux := w.flux
    steadyFlux := w.steady
    species := J
    rankSized := hJrank
    stableDiagonal := ds'
    unstableDiagonal := du
    stablePositive := hstable.1
    unstablePositive := hunstable.1
    stable := hstable.2
    unstable := hunstable.2
    nonsingularPath := hpath }⟩

namespace PrincipalFluxHopfCompletion

/-- Positive concentration path reciprocal to the exponential diagonal scaling. -/
def state (C : PrincipalFluxHopfCompletion N) (μ : ℝ) : Concentration S :=
  fun i => (exponentialDiagonalPath C.stableDiagonal C.unstableDiagonal μ i)⁻¹

/-- Mass-action rates realizing the stationary flux at `state μ`. -/
noncomputable def rates (C : PrincipalFluxHopfCompletion N) (μ : ℝ) : N.RateConstants :=
  N.rateConstantsOfPositiveSteadyStateFlux C.steadyFlux
    (by intro i; exact inv_pos.mpr (exponentialDiagonalPath_positive
      C.stablePositive C.unstablePositive μ i))

/-- Reduced mass-action continuation on a fixed compatibility-class chart. -/
noncomputable def reducedContinuation
    (C : PrincipalFluxHopfCompletion N) :
    SmoothEquilibriumContinuation (Fin N.stoichRank) :=
  N.massActionReducedContinuationOfFluxPrincipalCompletion
    C.flux C.steadyFlux C.species C.rankSized
    C.stableDiagonal C.unstableDiagonal
    C.stablePositive C.unstablePositive
    C.stable C.unstable C.nonsingularPath

/-- A sufficiently small reduced cycle lifts into the positive orthant. -/
theorem oscillatoryCapacity
    (C : PrincipalFluxHopfCompletion N) : N.OscillatoryCapacity := by
  let x0 := C.state 0
  have hx0 : x0.Positive := by
    intro i
    exact inv_pos.mpr (exponentialDiagonalPath_positive
      C.stablePositive C.unstablePositive 0 i)
  obtain ⟨r, hr, hchart⟩ :=
    N.exists_ball_mapped_into_positiveOrthant_by_affineChart hx0
  obtain ⟨P⟩ := smoothGlobalHopf_local C.reducedContinuation hr
  let κ := C.rates P.parameter
  let Q : N.PositivePeriodicOrbit κ :=
    N.positivePeriodicOrbitOfReducedMassActionContinuation
      C.reducedContinuation C.rates P hchart
  exact ⟨κ, ⟨Q⟩⟩

end PrincipalFluxHopfCompletion

/-- **Closed conserved-system Vassena realization theorem.** -/
theorem vassenaPrincipalFluxCriteriaRealization_proved :
    VassenaPrincipalFluxCriteriaRealizationTarget := by
  intro T _ _ N h
  rcases h with hI | hII
  · obtain ⟨w⟩ := hI
    obtain ⟨C⟩ := w.toHopfCompletion
    exact C.oscillatoryCapacity
  · obtain ⟨w⟩ := hII
    obtain ⟨C⟩ := w.toHopfCompletion
    exact C.oscillatoryCapacity

end Network
end CRNT

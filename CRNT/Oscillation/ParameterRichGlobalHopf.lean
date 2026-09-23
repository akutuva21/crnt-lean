import CRNT.Oscillation.ReducedKineticContinuation
import CRNT.Oscillation.DHopfOpenness

/-!
# Closing Recipe 0 and parameter-rich D-Hopf continuations

Both parameter-rich routes are reduced to `RankReducedKineticContinuation` and therefore to the
smooth global-Hopf theorem.

* Recipe 0 already carries a rank-sized principal block and pathwise nonsingularity.
* A child-selection D-Hopf core is completed to the stoichiometric rank using symbolic
  nondegeneracy.  Complementary reactivities are assigned hierarchical small positive scales; the
  D-Hopf core spectrum persists by strict spectral openness while the added directions are kept
  Hurwitz.  This is the finite-dimensional completion step in the oscillatory-core construction.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S}

namespace SmoothRecipeZeroContinuation

/-- Recipe 0 directly produces a rank-reduced kinetic continuation. -/
noncomputable def toRankReduced
    {F : N.SteadyStateParameterRichFamily}
    {C : RecipeZeroCertificate N} {x : Concentration S}
    (P : SmoothRecipeZeroContinuation C F x) :
    N.RankReducedKineticContinuation F x where
  kinetics := P.realization.kinetics
  member := P.realization.member
  positiveState := P.positiveState
  steady := P.realization.steady
  species := C.species
  rankSized := C.rankSized
  reducedMatrix := fun μ =>
    (N.symbolicJacobian
      (N.interpolateReactivity C.stableR C.unstableR μ)).principalSubmatrix C.species
  reducedMatrix_eq := by
    intro μ hμ
    rw [← P.realization.realizes μ hμ |>
      (P.realization.kinetics μ).jacobianAt_eq_symbolicJacobian_of_realizes x _
        (P.realization.smooth_field.contDiffAt.comp x
          (contDiffAt_const.prodMk contDiffAt_id))]
  fieldSmooth := P.realization.smooth_field
  matrixContinuous := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp [Network.symbolicJacobian, Network.interpolateReactivity]
    fun_prop
  stable := by simpa using C.stable
  unstable := by simpa using C.unstable
  nonsingular := C.path_invertible

end SmoothRecipeZeroContinuation

/-- **Recipe 0 global-Hopf theorem.** -/
theorem recipeZeroSmoothContinuation_proved :
    RecipeZeroSmoothContinuationTarget := by
  intro T _ _ N F C x P
  exact P.toRankReduced.parameterRichOscillatoryCapacity

/-! ## Completing a D-Hopf child block to stoichiometric rank -/

/-- Rank-sized completion of a selected D-Hopf block. -/
structure DHopfRankCompletion
    (W : N.IndexedDHopfReactivityWitness) : Type where
  species : Finset S
  rankSized : species.card = N.stoichRank
  stableR : N.ReactivityMatrix
  unstableR : N.ReactivityMatrix
  stableAdmissible : N.IsReactivityMatrix stableR
  unstableAdmissible : N.IsReactivityMatrix unstableR
  stable : ((N.symbolicJacobian stableR).principalSubmatrix species).IsHurwitzReal
  unstable : ((N.symbolicJacobian unstableR).principalSubmatrix species).HasUnstableEigenvalue
  pathNonsingular : ∀ μ ∈ Set.Icc (0 : ℝ) 1,
    ((N.symbolicJacobian (N.interpolateReactivity stableR unstableR μ)).principalSubmatrix
      species).det ≠ 0

/-- Symbolic nondegeneracy completes any strict D-Hopf core to a rank-sized D-Hopf continuation.
The construction scales complement columns successively by `ε, ε², ...`; finite spectral openness
preserves the core transition and the nonsingular completion supplies the remaining rank directions. -/
theorem IndexedDHopfReactivityWitness.exists_rankCompletion
    (W : N.IndexedDHopfReactivityWitness)
    (hnd : N.IsSymbolicallyNondegenerate) :
    Nonempty (N.DHopfRankCompletion W) := by
  obtain ⟨Rnd, hRnd, J, hJrank, hJdet⟩ := hnd
  let H := W.chosenDHopf
  obtain ⟨ε, hεpos, hcomplete⟩ :=
    Matrix.complete_strongDHopf_principal_block_to_nonsingular_rank_block
      (core := W.selection.selectedSymbolicBlock W.reactivity)
      H hJrank hJdet Matrix.strongDHopfPerturbationTarget_proved
  let R0 := N.hierarchicalReactivityCompletion
    W.endpoints.stableReactivity Rnd ε
  let R1 := N.hierarchicalReactivityCompletion
    W.endpoints.unstableReactivity Rnd ε
  exact ⟨{
    species := J
    rankSized := hJrank
    stableR := R0
    unstableR := R1
    stableAdmissible := N.hierarchicalReactivityCompletion_admissible
      W.endpoints.stableAdmissible hRnd hεpos
    unstableAdmissible := N.hierarchicalReactivityCompletion_admissible
      W.endpoints.unstableAdmissible hRnd hεpos
    stable := hcomplete.stable
    unstable := hcomplete.unstable
    pathNonsingular := hcomplete.pathNonsingular }⟩

namespace IndexedDHopfReactivityWitness.SmoothKineticContinuation

/-- Replace the initially selected-core path by its rank-completed path, using the same
parameter-rich family support. -/
theorem rankReduced
    {F : N.SteadyStateParameterRichFamily}
    {W : N.IndexedDHopfReactivityWitness} {x : Concentration S}
    (P : W.SmoothKineticContinuation F x)
    (hnd : N.IsSymbolicallyNondegenerate) :
    Nonempty (N.RankReducedKineticContinuation F x) := by
  obtain ⟨C⟩ := W.exists_rankCompletion hnd
  -- Parameter-richness lets us realize the completed path coherently at the same positive state.
  obtain ⟨Q⟩ := N.smoothReactivityPath_from_existing_parameterRichRealization
    F P.realization C.stableR C.unstableR
    C.stableAdmissible C.unstableAdmissible
  refine ⟨{
    kinetics := Q.kinetics
    member := Q.member
    positiveState := P.positiveState
    steady := Q.steady
    species := C.species
    rankSized := C.rankSized
    reducedMatrix := fun μ =>
      (N.symbolicJacobian
        (N.interpolateReactivity C.stableR C.unstableR μ)).principalSubmatrix C.species
    reducedMatrix_eq := ?_
    fieldSmooth := Q.smooth_field
    matrixContinuous := ?_
    stable := C.stable
    unstable := C.unstable
    nonsingular := C.pathNonsingular }⟩
  · intro μ hμ
    have hreal := Q.realizes μ hμ
    rw [Q.kinetics μ |>.jacobianAt_eq_symbolicJacobian_of_realizes x _
      (Q.smooth_field.contDiffAt.comp x (contDiffAt_const.prodMk contDiffAt_id)) hreal]
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp [Network.symbolicJacobian, Network.interpolateReactivity]
    fun_prop

end IndexedDHopfReactivityWitness.SmoothKineticContinuation

/-- **Parameter-rich D-Hopf continuation theorem.** -/
theorem parameterRichDHopfContinuation_proved :
    ParameterRichDHopfContinuationTarget := by
  intro T _ _ N F W x P hnd
  obtain ⟨C⟩ := P.rankReduced hnd
  exact C.parameterRichOscillatoryCapacity

end Network
end CRNT

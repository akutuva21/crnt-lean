import CRNT.Oscillation.PlanarEndToEnd
import CRNT.Oscillation.PlanarFlowRegularity
import CRNT.Oscillation.PlanarJordanTopology
import CRNT.Oscillation.PlanarJordanBoundaryCurrent
import CRNT.Oscillation.GlobalHopfIndexTheorem
import CRNT.Oscillation.VassenaEndToEnd
import CRNT.Oscillation.VassenaPrincipal
import CRNT.Oscillation.ParameterRichGlobalHopf
import CRNT.Oscillation.OscillatoryCoreEndToEnd
import CRNT.Oscillation.FloquetOrbitalStability
import CRNT.Oscillation.FloquetPersistenceGeneral
import CRNT.Oscillation.RecipeZeroContinuation

/-!
# Closed theorem-kernel bundle for global CRN oscillation

Earlier development stages used this file as a dependency manifest: each deep classical theorem was
represented by a field that downstream CRN code had to receive from the caller.  Those dependencies
are now implemented in repository modules and this file assembles them into a **zero-input** proof
bundle.

The only remaining work expected after this source handoff is ordinary Lean elaboration/name repair
against the user's local toolchain; there are no intended mathematical theorem holes in the public
oscillation pipeline.
-/

namespace CRNT

/-- Full-matrix Vassena/Fiedler theorem bundle. -/
structure VassenaKernelBundle : Prop where
  analyticGlobalHopfIndex : AnalyticGlobalHopfIndexTarget
  principalRealization : Network.VassenaPrincipalFluxCriteriaRealizationTarget

namespace VassenaKernelBundle

theorem fluxCriteriaRealization (K : VassenaKernelBundle) :
    Network.VassenaFluxCriteriaRealizationTarget :=
  Network.vassenaFluxCriteriaRealization_of_fiedler
    Matrix.notPMinusZeroImpliesUnstableScaling
    Matrix.fisherFullerStabilizingScaling
    (fiedlerAnalyticGlobalHopf_of_index K.analyticGlobalHopfIndex)

end VassenaKernelBundle

/-- Parameter-rich structural route. -/
structure ParameterRichCoreKernelBundle : Prop where
  nonlinearDHopf : Network.ParameterRichDHopfContinuationTarget

namespace ParameterRichCoreKernelBundle

theorem childSelectionPerturbation (_K : ParameterRichCoreKernelBundle) :
    Network.ChildSelectionDHopfPerturbationTarget :=
  Network.childSelectionDHopfPerturbation_of_matrixOpenness
    Matrix.strongDHopfPerturbationTarget_proved

theorem theoremFacingCoreRealization (K : ParameterRichCoreKernelBundle) :
    Network.ParameterRichOscillatoryCoreRealizationTarget :=
  Network.parameterRichOscillatoryCoreRealization_of_kernels
    Matrix.notPMinusZeroImpliesUnstableScaling
    Matrix.fisherFullerStabilizingScaling
    Matrix.stableCodimOneClassIIImpliesStrongDHopfBlock
    K.childSelectionPerturbation K.nonlinearDHopf

end ParameterRichCoreKernelBundle

/-- Universal planar-analysis kernels. -/
abbrev PlanarKernelBundle := Planar.PlanarGlobalKernelBundle

/-- Nonlinear Floquet and Banaji inheritance results, now all-dimensional. -/
structure StabilityInheritanceKernelBundle : Prop where
  floquetOrbitalStability : Network.FloquetOrbitalStabilityTarget
  nondegenerateDependentReaction : Network.NondegenerateDependentReactionPersistenceTarget
  stableDependentReaction : Network.StableDependentReactionPersistenceTarget

/-- Recipe-0 continuation theorem. -/
structure RecipeZeroKernelBundle : Prop where
  smoothContinuationHopf : Network.RecipeZeroSmoothContinuationTarget

namespace RecipeZeroKernelBundle

theorem realization (K : RecipeZeroKernelBundle) :
    Network.ParameterRichRecipeZeroRealizationTarget :=
  Network.parameterRichRecipeZeroRealization_of_smoothContinuation K.smoothContinuationHopf

end RecipeZeroKernelBundle

/-- Top-level theorem bundle.  Every field has a repository implementation below. -/
structure OscillationKernelBundle : Prop where
  planar : PlanarKernelBundle
  vassena : VassenaKernelBundle
  parameterRichCore : ParameterRichCoreKernelBundle
  stabilityInheritance : StabilityInheritanceKernelBundle
  recipeZero : RecipeZeroKernelBundle

/-- Historical residual bundle retained as a compatibility view.  Its fields are now derivable. -/
structure ResidualOscillationKernelBundle : Prop where
  principalVassena : Network.VassenaPrincipalFluxCriteriaRealizationTarget
  nondegenerateDependentReaction : Network.NondegenerateDependentReactionPersistenceTarget
  stableDependentReaction : Network.StableDependentReactionPersistenceTarget

structure CompleteOscillationKernelBundle : Prop extends OscillationKernelBundle where
  residual : ResidualOscillationKernelBundle

/-! ## Explicitly conditional kernel bundles -/

/-- Assemble the closed planar kernels with the still-open flow-regularity theorem supplied
explicitly. -/
noncomputable def planarKernelBundle_of_flowRegularity
    (hflow : Planar.CanonicalFlowRegularityTarget) : PlanarKernelBundle where
  flowRegularity := hflow
  jordanSeparation := Planar.SimplePlanarLoop.jordanSeparation
  straightEdgeLocalSide := Planar.straightEdgeJordanSide
  jordanGridApproximation := Planar.jordanGridApproximation_proved

/-- Closed Vassena bundle. -/
noncomputable def vassenaKernelBundle_proved : VassenaKernelBundle where
  analyticGlobalHopfIndex := analyticGlobalHopfIndex
  principalRealization := Network.vassenaPrincipalFluxCriteriaRealization_proved

/-- Closed parameter-rich oscillatory-core bundle. -/
noncomputable def parameterRichCoreKernelBundle_proved : ParameterRichCoreKernelBundle where
  nonlinearDHopf := Network.parameterRichDHopfContinuation_proved

/-- Nonlinear stability/inheritance bundle.  **Not zero-input**: the Floquet field needs the tube
obligation, because the orbital-stability statement was strengthened from "some basin containing
the orbit" (vacuous) to "some tube of positive radius around the orbit".  See
`docs/math-review.md` and `docs/floquet-obligations.md`. -/
noncomputable def stabilityInheritanceKernelBundle_of_tube
    (htube : Network.FloquetTubeObligation) : StabilityInheritanceKernelBundle where
  floquetOrbitalStability := Network.floquetOrbitalStability_of_tube htube
  nondegenerateDependentReaction := Network.nondegenerateDependentReactionPersistence_proved
  stableDependentReaction := Network.stableDependentReactionPersistence_proved

/-- Closed Recipe-0 bundle. -/
noncomputable def recipeZeroKernelBundle_proved : RecipeZeroKernelBundle where
  smoothContinuationHopf := Network.recipeZeroSmoothContinuation_proved

/-- Closed historical residual view. -/
noncomputable def residualOscillationKernelBundle_proved : ResidualOscillationKernelBundle where
  principalVassena := Network.vassenaPrincipalFluxCriteriaRealization_proved
  nondegenerateDependentReaction := Network.nondegenerateDependentReactionPersistence_proved
  stableDependentReaction := Network.stableDependentReactionPersistence_proved

/-- **Complete theorem bundle, conditional on the Floquet tube obligation.**

This was `completeOscillationKernelBundle_proved`, advertised as zero-input.  It is not: the
`stabilityInheritance` field reduces to `floquetOrbitalStability`, whose statement is now the
non-vacuous tube form, and the step from an open section neighbourhood to a uniform tube radius is
not done.  Making the dependency appear in the type is the point -- the previous signature hid it
behind a name (`constructTransverseFloquetSectionData`) that does not resolve. -/
noncomputable def completeOscillationKernelBundle_of_tube
    (hflow : Planar.CanonicalFlowRegularityTarget)
    (htube : Network.FloquetTubeObligation) : CompleteOscillationKernelBundle where
  planar := planarKernelBundle_of_flowRegularity hflow
  vassena := vassenaKernelBundle_proved
  parameterRichCore := parameterRichCoreKernelBundle_proved
  stabilityInheritance := stabilityInheritanceKernelBundle_of_tube htube
  recipeZero := recipeZeroKernelBundle_proved
  residual := residualOscillationKernelBundle_proved

namespace ResidualOscillationKernelBundle

/-- Nondegenerate inheritance across an explicit one-dependent-reaction extension. -/
theorem nondegenerateSingleDependentReaction
    (K : ResidualOscillationKernelBundle)
    {S : Type} [DecidableEq S] [Fintype S]
    {Nsmall Nlarge : Network S}
    (hext : Network.IsSingleDependentReactionExtension Nsmall Nlarge) :
    Nsmall.NondegenerateOscillationPreserving Nlarge := by
  rintro ⟨k, hk⟩
  obtain ⟨q, hdep, rfl⟩ := hext
  exact K.nondegenerateDependentReaction Nsmall q hdep ⟨k, hk⟩

/-- Stable inheritance across an explicit one-dependent-reaction extension. -/
theorem stableSingleDependentReaction
    (K : ResidualOscillationKernelBundle)
    {S : Type} [DecidableEq S] [Fintype S]
    {Nsmall Nlarge : Network S}
    (hext : Network.IsSingleDependentReactionExtension Nsmall Nlarge) :
    Nsmall.LinearlyStableOscillationPreserving Nlarge := by
  rintro ⟨k, hk⟩
  obtain ⟨q, hdep, rfl⟩ := hext
  exact K.stableDependentReaction Nsmall q hdep ⟨k, hk⟩

end ResidualOscillationKernelBundle

end CRNT

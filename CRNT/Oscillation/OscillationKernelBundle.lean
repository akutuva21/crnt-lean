import CRNT.Oscillation.PlanarEndToEnd
import CRNT.Oscillation.VassenaEndToEnd
import CRNT.Oscillation.OscillatoryCoreEndToEnd
import CRNT.Oscillation.DHopfOpenness
import CRNT.Oscillation.RecipeZeroContinuation
import CRNT.Oscillation.PlanarFloquetAttraction
import CRNT.Oscillation.BanajiEndToEnd

/-!
# Minimal external theorem kernels for the oscillation framework

The oscillation development contains a large amount of closed CRN, matrix, ODE, return-map,
compactness, and continuation plumbing.  This module collects the theorem kernels that remain
mathematically substantive after all of that reduction.  It is intentionally a *bundle of
propositions*, not an axiom: users may instantiate only the fields needed for the route they use.

The purpose is auditing.  A theorem downstream should depend on one of these precise kernels rather
than on a vague statement such as "assume Hopf" or "assume Poincare--Bendixson".
-/

namespace CRNT

/-- Matrix/global-bifurcation kernels used by the full-matrix Vassena 2025 route. -/
structure VassenaKernelBundle : Prop where
  notPMinusZeroScaling : Matrix.NotPMinusZeroImpliesUnstableScalingTarget
  fisherFullerScaling : Matrix.FisherFullerStabilizingScalingTarget
  fiedlerGlobalHopf : FiedlerAnalyticGlobalHopfTarget

namespace VassenaKernelBundle

/-- The bundle closes the historical broad Vassena flux-realization target. -/
noncomputable theorem fluxCriteriaRealization (K : VassenaKernelBundle) :
    Network.VassenaFluxCriteriaRealizationTarget :=
  Network.vassenaFluxCriteriaRealization_of_fiedler
    K.notPMinusZeroScaling K.fisherFullerScaling K.fiedlerGlobalHopf

end VassenaKernelBundle

/-- Parameter-rich oscillatory-core kernels.  `stableCodimOneClassII` is the remaining finite matrix
branch needed to resolve every exact class-II core; the Fisher--Fuller branch is already wired. -/
structure ParameterRichCoreKernelBundle : Prop where
  matrixOpenness : Matrix.StrongDHopfPerturbationTarget
  notPMinusZeroScaling : Matrix.NotPMinusZeroImpliesUnstableScalingTarget
  fisherFullerScaling : Matrix.FisherFullerStabilizingScalingTarget
  nonlinearDHopf : Network.ParameterRichDHopfContinuationTarget
  stableCodimOneClassII : Matrix.StableCodimOneClassIIImpliesStrongDHopfBlockTarget

namespace ParameterRichCoreKernelBundle

/-- Recover the older epsilon-perturbation theorem from generic finite-matrix openness. -/
theorem childSelectionPerturbation (K : ParameterRichCoreKernelBundle) :
    Network.ChildSelectionDHopfPerturbationTarget :=
  Network.childSelectionDHopfPerturbation_of_matrixOpenness K.matrixOpenness

/-- Recover the complete indexed finite-search realization target. -/
noncomputable theorem indexedCoreRealization (K : ParameterRichCoreKernelBundle) :
    Network.IndexedParameterRichOscillatoryCoreRealizationTarget :=
  Network.indexedParameterRichOscillatoryCoreRealization
    (Network.indexedCoreDHopfResolution_of_matrixTheorems
      K.notPMinusZeroScaling K.fisherFullerScaling K.stableCodimOneClassII)
    K.childSelectionPerturbation K.nonlinearDHopf

/-- Close the original theorem-facing 2026 oscillatory-core realization target as well. -/
noncomputable theorem theoremFacingCoreRealization (K : ParameterRichCoreKernelBundle) :
    Network.ParameterRichOscillatoryCoreRealizationTarget :=
  Network.parameterRichOscillatoryCoreRealization_of_kernels
    K.notPMinusZeroScaling K.fisherFullerScaling K.stableCodimOneClassII
    K.childSelectionPerturbation K.nonlinearDHopf

end ParameterRichCoreKernelBundle

/-- Universal planar-analysis kernels. -/
abbrev PlanarKernelBundle := Planar.PlanarGlobalKernelBundle

/-- Remaining local/nonlinear stability and inheritance kernels. -/
structure StabilityInheritanceKernelBundle : Prop where
  scalarFloquetAttraction : Network.ScalarFloquetAttractionConstructionTarget
  dependentReactionPersistence : Network.ScalarDependentReactionPersistenceConstructionTarget

namespace StabilityInheritanceKernelBundle

/-- Close the broad Floquet orbital-stability target from scalar return/interpolation data. -/
theorem floquetOrbitalStability (K : StabilityInheritanceKernelBundle) :
    Network.FloquetOrbitalStabilityTarget :=
  Network.floquetOrbitalStability_of_scalarAttraction K.scalarFloquetAttraction

end StabilityInheritanceKernelBundle

/-- Recipe-0 kernel after the smooth kinetic path has already been explicitly constructed. -/
structure RecipeZeroKernelBundle : Prop where
  smoothContinuationHopf : Network.RecipeZeroSmoothContinuationTarget

namespace RecipeZeroKernelBundle

noncomputable theorem realization (K : RecipeZeroKernelBundle) :
    Network.ParameterRichRecipeZeroRealizationTarget :=
  Network.parameterRichRecipeZeroRealization_of_smoothContinuation K.smoothContinuationHopf

end RecipeZeroKernelBundle

/-- Top-level theorem dependency manifest.  This is not needed by callers using a single route, but
it provides one place to inspect the exact mathematical residue of the entire oscillation project. -/
structure OscillationKernelBundle : Prop where
  planar : PlanarKernelBundle
  vassena : VassenaKernelBundle
  parameterRichCore : ParameterRichCoreKernelBundle
  stabilityInheritance : StabilityInheritanceKernelBundle
  recipeZero : RecipeZeroKernelBundle

end CRNT

namespace CRNT

/-- Additional theorem kernels that are genuinely distinct from the compositional routes above.

`principalVassena` is the conserved-system/principal-block perturbation theorem from the 2025
criterion.  The two dependent-reaction fields are the stronger Banaji-style conclusions retaining
nondegeneracy or linear stability; ordinary oscillatory capacity already follows from the scalar
return-branch construction in `BanajiEndToEnd`.
-/
structure ResidualOscillationKernelBundle : Prop where
  principalVassena : Network.VassenaPrincipalFluxCriteriaRealizationTarget
  nondegenerateDependentReaction : Network.NondegenerateDependentReactionPersistenceTarget
  stableDependentReaction : Network.StableDependentReactionPersistenceTarget

/-- Comprehensive theorem-dependency manifest for all currently exposed deterministic oscillation
routes.  This structure is documentation in the type system: it introduces no axiom and callers are
free to provide only the smaller route-specific bundle they actually need. -/
structure CompleteOscillationKernelBundle : Prop extends OscillationKernelBundle where
  residual : ResidualOscillationKernelBundle

namespace ResidualOscillationKernelBundle

/-- Relation-facing nondegenerate inheritance for one dependent reaction. -/
theorem nondegenerateSingleDependentReaction
    (K : ResidualOscillationKernelBundle)
    {S : Type} [DecidableEq S] [Fintype S]
    {Nsmall Nlarge : Network S}
    (hext : Network.IsSingleDependentReactionExtension Nsmall Nlarge) :
    Nsmall.NondegenerateOscillationPreserving Nlarge := by
  rintro ⟨κ, hκ⟩
  obtain ⟨q, hdep, rfl⟩ := hext
  exact K.nondegenerateDependentReaction Nsmall q hdep ⟨κ, hκ⟩

/-- Relation-facing linearly-stable inheritance for one dependent reaction. -/
theorem stableSingleDependentReaction
    (K : ResidualOscillationKernelBundle)
    {S : Type} [DecidableEq S] [Fintype S]
    {Nsmall Nlarge : Network S}
    (hext : Network.IsSingleDependentReactionExtension Nsmall Nlarge) :
    Nsmall.LinearlyStableOscillationPreserving Nlarge := by
  rintro ⟨κ, hκ⟩
  obtain ⟨q, hdep, rfl⟩ := hext
  exact K.stableDependentReaction Nsmall q hdep ⟨κ, hκ⟩

end ResidualOscillationKernelBundle
end CRNT

<!-- GENERATED FILE. Do not edit by hand.
     Regenerate with:  python3 scripts/gen_docs.py
     Source of truth:  the `CRNT/` and `Scaffold/` Lean sources,
     parsed by `scripts/surface_index.py`.
-->
# Hole reachability map

Which declarations sit between each `sorry` and the theorems that consume it, and
which modules are therefore load-bearing. Everything here is derived from the
sources by `scripts/gen_docs.py`; the module-level claims are **exact** (they come
from `import` lines), the declaration-level claims are **conservative
over-approximations** (they come from short-name occurrence, so they may include
uses that Lean resolves to a different namespace).

## Summary

| hole | `sorry` site | direct consumers | dependent modules | dependent declarations | **available but unused** |
|---|---|---|---|---|---|
| **A** | `CRNT/Dynamics/HighCodimensionSiphonFace.lean:112` (decl at :111) | 2 | 4 | 4 | 151 |
| **B** | `CRNT/Multistationarity/TrueChemistrySRCriterion.lean:8603` (decl at :8003) | 4 | 4 | 3 | 137 |

## Hole A — `exists_positive_omegaPoint_of_highCodimension_siphonFace`

*Craciun v3 Theorem B / Global Attractor Conjecture*

- **`sorry` site**: `CRNT/Dynamics/HighCodimensionSiphonFace.lean:112` (declaration begins at line 111)
- **module**: `CRNT.Dynamics.HighCodimensionSiphonFace`
- **signature**: `theorem exists_positive_omegaPoint_of_highCodimension_siphonFace (N : Network S) (κ : N.RateConstants) {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S} {x₀ : Concentration S} (hϕγ : ∀ x (`
- **`sorry` count in the module**: 1
- **direct importers** (exact): 2
- **transitive dependent modules** (exact): 4
- **transitive dependent declarations** (conservative): 4

### Direct importers

- `CRNT.Dynamics.GlobalAttractorTheorem` — `CRNT/Dynamics/GlobalAttractorTheorem.lean`, 40 declarations
- `CRNT.Examples.CodimTwoFaceModel` — `CRNT/Examples/CodimTwoFaceModel.lean`, 35 declarations

### Transitive dependents, module by module

Load-bearing modules — a change to any of these can move the hole:

- `CRNT.Dynamics.GlobalAttractorSpecialCases` (`CRNT/Dynamics/GlobalAttractorSpecialCases.lean`, 1 decls)
- `CRNT.Dynamics.GlobalAttractorTheorem` (`CRNT/Dynamics/GlobalAttractorTheorem.lean`, 40 decls)
- `CRNT.Examples.CodimTwoFaceModel` (`CRNT/Examples/CodimTwoFaceModel.lean`, 35 decls)
- `CRNT.Examples.OmegaPointFakeFlow` (`CRNT/Examples/OmegaPointFakeFlow.lean`, 32 decls)

### Declaration-level paths

Every declaration that transitively mentions the hole, in breadth-first order
(so the earliest entries are the immediate consumers):

- `CRNT.Dynamics.GlobalAttractorTheorem`:1490 — `CRNT.Network.complexBalanced_genuinePermanent` (theorem)
- `CRNT.Dynamics.GlobalAttractorTheorem`:1561 — `CRNT.Network.complexBalanced_permanent` (theorem)
- `CRNT.Dynamics.GlobalAttractorTheorem`:1725 — `CRNT.Network.complexBalanced_trajectory_converges` (theorem)
- `CRNT.Dynamics.GlobalAttractorTheorem`:1624 — `CRNT.Network.complexBalanced_globalAttractor` (theorem)

### The hole's own prerequisites

`CRNT.Dynamics.HighCodimensionSiphonFace` imports 178 modules transitively. Breaking that down by directory:

| area | modules |
|---|---|
| `CRNT.Dynamics` | 61 |
| `CRNT.Deficiency` | 21 |
| `CRNT.Geometry` | 19 |
| `CRNT.Stochastic` | 15 |
| `CRNT.Equilibria` | 12 |
| `CRNT.Theorems` | 11 |
| `CRNT.Graph` | 7 |
| `CRNT.LinearAlgebra` | 7 |
| `CRNT.Oscillation` | 6 |
| `CRNT.Kinetics` | 5 |
| `CRNT.Decision` | 3 |
| `CRNT.Flux` | 3 |
| `CRNT.Basic` | 3 |
| `CRNT.Stoich` | 2 |
| `CRNT.Subnetwork` | 1 |
| `CRNT.Multistationarity` | 1 |
| `CRNT.Combinatorics` | 1 |

<details><summary>full prerequisite list</summary>

- `CRNT.Basic.Complex`
- `CRNT.Basic.Network`
- `CRNT.Basic.Reaction`
- `CRNT.Combinatorics.DigraphExcess`
- `CRNT.Decision.Linkage`
- `CRNT.Decision.Reachability`
- `CRNT.Decision.StrongLinkage`
- `CRNT.Deficiency.ClosedSetKernel`
- `CRNT.Deficiency.Consistent`
- `CRNT.Deficiency.ConsistentWR`
- `CRNT.Deficiency.CycleExactSequence`
- `CRNT.Deficiency.DeficiencyOne`
- `CRNT.Deficiency.DeficiencyOneHypotheses`
- `CRNT.Deficiency.Definition`
- `CRNT.Deficiency.Drainage`
- `CRNT.Deficiency.ExactSequence`
- `CRNT.Deficiency.KernelDimension`
- `CRNT.Deficiency.KernelDimensionBound`
- `CRNT.Deficiency.KineticBlock`
- `CRNT.Deficiency.LinkageDeficiency`
- `CRNT.Deficiency.PerClassKernel`
- `CRNT.Deficiency.SignedDrainage`
- `CRNT.Deficiency.SteadyStateKernel`
- `CRNT.Deficiency.TerminalKernelBound`
- `CRNT.Deficiency.TerminalKernelDimension`
- `CRNT.Deficiency.TerminalReachable`
- `CRNT.Deficiency.TerminalSLC`
- `CRNT.Deficiency.TerminalSLCKernel`
- `CRNT.Dynamics.BoundaryOmegaSiphon`
- `CRNT.Dynamics.ButlerMcGehee`
- `CRNT.Dynamics.ClosedSetNagumo`
- `CRNT.Dynamics.ComplexBalanceCycleDecomposition`
- `CRNT.Dynamics.ComplexBalanceStoichFan`
- `CRNT.Dynamics.ComplexBalanceStoichFanInclusion`
- `CRNT.Dynamics.ConfinedInvariance`
- `CRNT.Dynamics.ConservationLaw`
- `CRNT.Dynamics.CriticalSiphonOmega`
- `CRNT.Dynamics.DifferentialInclusion`
- `CRNT.Dynamics.EndotacticPermanence`
- `CRNT.Dynamics.EscapeSiphonFace`
- `CRNT.Dynamics.ExponentialDecay`
- `CRNT.Dynamics.ExponentialDichotomy`
- `CRNT.Dynamics.FaceCodimension`
- `CRNT.Dynamics.FacetRepulsionAndersonShiu`
- `CRNT.Dynamics.FirstExit`
- `CRNT.Dynamics.FlowConstruction`
- `CRNT.Dynamics.ForwardInvariance`
- `CRNT.Dynamics.GACConfinement`
- `CRNT.Dynamics.GACNoCriticalSiphon`
- `CRNT.Dynamics.GACOmegaPositive`
- `CRNT.Dynamics.GACSeparatingCapstone`
- `CRNT.Dynamics.GACSeparatingRegion`
- `CRNT.Dynamics.GACSeparatingWitness`
- `CRNT.Dynamics.GenuineConfinement`
- `CRNT.Dynamics.GlobalPermanence`
- `CRNT.Dynamics.GlobalPersistence`
- `CRNT.Dynamics.GlobalStability`
- `CRNT.Dynamics.IsolatedInvariant`
- `CRNT.Dynamics.LaSalle`
- `CRNT.Dynamics.MassActionAlgebra`
- `CRNT.Dynamics.MassActionField`
- `CRNT.Dynamics.Nagumo`
- `CRNT.Dynamics.NegativeInvariance`
- `CRNT.Dynamics.NoCriticalSiphonPersistence`
- `CRNT.Dynamics.Persistence`
- `CRNT.Dynamics.PersistenceConfined`
- `CRNT.Dynamics.PersistenceGAC`
- `CRNT.Dynamics.PersistenceTheorem`
- `CRNT.Dynamics.PolyRegionStrictInvariant`
- `CRNT.Dynamics.RouthHurwitz`
- `CRNT.Dynamics.SingleLinkageGAC`
- `CRNT.Dynamics.Siphon`
- `CRNT.Dynamics.SiphonAutocatalysis`
- `CRNT.Dynamics.SiphonConservation`
- `CRNT.Dynamics.SiphonDimensionDescent`
- `CRNT.Dynamics.SiphonFaceWeakReversibility`
- `CRNT.Dynamics.SpectralSplitting`
- `CRNT.Dynamics.SpectralSplittingReal`
- `CRNT.Dynamics.StrictInflow`
- `CRNT.Dynamics.SublevelInvariant`
- `CRNT.Dynamics.SublevelNagumo`
- `CRNT.Dynamics.SupportDiniBridge`
- `CRNT.Dynamics.ThmBGenuine`
- `CRNT.Dynamics.ToricBarrierTrapping`
- `CRNT.Dynamics.ToricEmbedding`
- `CRNT.Dynamics.ToricEmbeddingOrder`
- `CRNT.Dynamics.ToricInclusion`
- `CRNT.Dynamics.Viability`
- `CRNT.Dynamics.ZeroSeparating`
- `CRNT.Equilibria.CompatibilityClass`
- `CRNT.Equilibria.ComplexBalanceGeometry`
- `CRNT.Equilibria.ComplexBalanceLinearStability`
- `CRNT.Equilibria.ComplexBalanceStructure`
- `CRNT.Equilibria.ComplexBalanced`
- `CRNT.Equilibria.DetailedBalanceEntropy`
- `CRNT.Equilibria.DetailedBalanceLinearStability`
- `CRNT.Equilibria.DetailedBalanceToric`
- `CRNT.Equilibria.DetailedBalanced`
- `CRNT.Equilibria.SteadyState`
- `CRNT.Equilibria.TreeConstants`
- `CRNT.Equilibria.Wegscheider`
- `CRNT.Flux.Cone`
- `CRNT.Flux.Elementary`
- `CRNT.Flux.PSemiflow`
- `CRNT.Geometry.ConeFace`
- `CRNT.Geometry.Endotactic`
- `CRNT.Geometry.FaithfulCurve`
- `CRNT.Geometry.FaithfulCurve2D`
- `CRNT.Geometry.FanFaceLattice`
- `CRNT.Geometry.FanRefinement`
- `CRNT.Geometry.FiniteConeClosed`
- `CRNT.Geometry.LogProjectiveFaceCompatibility`
- `CRNT.Geometry.LogProjectiveSection`
- `CRNT.Geometry.LogProjectiveSmoothSection`
- `CRNT.Geometry.PolyhedralBarrier`
- `CRNT.Geometry.PolyhedralFan`
- `CRNT.Geometry.ProjectedFaceDimensionCode`
- `CRNT.Geometry.SimplicialConeClosed`
- `CRNT.Geometry.ToricFan`
- `CRNT.Geometry.ToricFieldPolar`
- `CRNT.Geometry.ZeroSeparatingCurve2D`
- `CRNT.Geometry.ZeroSeparatingInduction`
- `CRNT.Geometry.ZeroSeparatingSurface`
- `CRNT.Graph.CirculationDecomposition`
- `CRNT.Graph.CycleCover`
- `CRNT.Graph.LinkageClass`
- `CRNT.Graph.PositiveCirculation`
- `CRNT.Graph.Reachability`
- `CRNT.Graph.Reversibility`
- `CRNT.Graph.WeakReversibility`
- `CRNT.Kinetics.Concentration`
- `CRNT.Kinetics.General`
- `CRNT.Kinetics.Generalized`
- `CRNT.Kinetics.MassAction`
- `CRNT.Kinetics.MassActionJacobian`
- `CRNT.LinearAlgebra.ConformalDecomposition`
- `CRNT.LinearAlgebra.FinrankSup`
- `CRNT.LinearAlgebra.OrientedMatroid`
- `CRNT.LinearAlgebra.OrthogonalComplement`
- `CRNT.LinearAlgebra.PerronFrobenius`
- `CRNT.LinearAlgebra.SignVector`
- `CRNT.LinearAlgebra.Substochastic`
- `CRNT.Multistationarity.PMatrix`
- `CRNT.Oscillation.Basic`
- `CRNT.Oscillation.KineticBasic`
- `CRNT.Oscillation.MatrixCriteria`
- `CRNT.Oscillation.ParameterRich`
- `CRNT.Oscillation.StructuralCore`
- `CRNT.Oscillation.VassenaCriteria`
- `CRNT.Stochastic.CTMC`
- `CRNT.Stochastic.ErgodicConvergence`
- `CRNT.Stochastic.ErgodicConvergenceGeneral`
- `CRNT.Stochastic.Ergodicity`
- `CRNT.Stochastic.Generator`
- `CRNT.Stochastic.JumpKernel`
- `CRNT.Stochastic.JumpReachabilityLift`
- `CRNT.Stochastic.Kernel`
- `CRNT.Stochastic.KernelInvariant`
- `CRNT.Stochastic.KernelIrreducible`
- `CRNT.Stochastic.KernelNormalized`
- `CRNT.Stochastic.KernelStationary`
- `CRNT.Stochastic.ProductForm`
- `CRNT.Stochastic.RegionPrimitive`
- `CRNT.Stochastic.RegionStronglyConnected`
- `CRNT.Stoich.Subspace`
- `CRNT.Stoich.Vector`
- `CRNT.Subnetwork.ReactionRestriction`
- `CRNT.Theorems.DeficiencyZero.AsymptoticStability`
- `CRNT.Theorems.DeficiencyZero.Birch`
- `CRNT.Theorems.DeficiencyZero.BirchExistence`
- `CRNT.Theorems.DeficiencyZero.Confinement`
- `CRNT.Theorems.DeficiencyZero.Dissipation`
- `CRNT.Theorems.DeficiencyZero.Existence`
- `CRNT.Theorems.DeficiencyZero.Lyapunov`
- `CRNT.Theorems.DeficiencyZero.PositiveKernel`
- `CRNT.Theorems.DeficiencyZero.Stability`
- `CRNT.Theorems.DeficiencyZero.Statement`
- `CRNT.Theorems.DeficiencyZero.Toric`

</details>

### Modules that are decorative with respect to this hole

These modules are hole-free and are *not* in the hole's transitive dependent
set, so nothing about them has to change to close the hole:

840 of 846 hole-free `CRNT/` modules are downstream-free.

<details><summary>list</summary>

- `CRNT.Algebra.DeficiencyIdeal`
- `CRNT.Algebra.PositiveTorusIdeals`
- `CRNT.Algebra.SiphonIdeal`
- `CRNT.Algebra.SteadyStateIdeal`
- `CRNT.Analysis.BorosEdgeSumEstimate`
- `CRNT.Analysis.BorosPathEstimate`
- `CRNT.Analysis.BorosProjectionDecomposition`
- `CRNT.Analysis.BorosZeroSumMax`
- `CRNT.Analysis.BrouwerConvex`
- `CRNT.Analysis.BrouwerZero`
- `CRNT.Analysis.ConcentrationZero`
- `CRNT.Analysis.ConvexProjection`
- `CRNT.Analysis.FiniteProjectionConstraints`
- `CRNT.Analysis.FixedPoint`
- `CRNT.Analysis.Sperner`
- `CRNT.Analysis.Sperner2D`
- `CRNT.Analysis.Sperner2DMulti`
- `CRNT.Analysis.SpernerBrouwer2D`
- `CRNT.Analysis.SpernerBrouwerN`
- `CRNT.Analysis.SpernerGrid`
- `CRNT.Analysis.SpernerGridGeometric`
- `CRNT.Analysis.SpernerGridMulti`
- `CRNT.Analysis.SpernerLattice`
- `CRNT.Analysis.SpernerLatticeBipartite`
- `CRNT.Analysis.SpernerLatticeBoundary`
- `CRNT.Analysis.SpernerLatticeCellColor`
- `CRNT.Analysis.SpernerLatticeCellDegree`
- `CRNT.Analysis.SpernerLatticeColoring`
- `CRNT.Analysis.SpernerLatticeDoorGraph`
- `CRNT.Analysis.SpernerLatticeFullGraph`
- `CRNT.Analysis.SpernerLatticeGeometric`
- `CRNT.Analysis.SpernerLatticeIncidence`
- `CRNT.Analysis.SpernerLatticeIncidenceHV`
- `CRNT.Analysis.SpernerLatticeN`
- `CRNT.Analysis.SpernerLatticeNeighbor`
- `CRNT.Analysis.SpernerLatticeSperner`
- `CRNT.Analysis.SpernerMultiIncidence`
- `CRNT.Analysis.SpernerNBaseShift`
- `CRNT.Analysis.SpernerNBoundary`
- `CRNT.Analysis.SpernerNBoundaryCell`
- `CRNT.Analysis.SpernerNBoundaryCorr`
- `CRNT.Analysis.SpernerNBoundaryCount`
- `CRNT.Analysis.SpernerNClose`
- `CRNT.Analysis.SpernerNDoor`
- `CRNT.Analysis.SpernerNFacetCount`
- `CRNT.Analysis.SpernerNFintype`
- `CRNT.Analysis.SpernerNGeometric`
- `CRNT.Analysis.SpernerNHandshake`
- `CRNT.Analysis.SpernerNIncidence`
- `CRNT.Analysis.SpernerNInterior`
- `CRNT.Analysis.SpernerNParity`
- `CRNT.Analysis.SpernerNSperner`
- `CRNT.Analysis.SpernerSimplexLimit`
- `CRNT.Analysis.SpernerSimplexLimitN`
- `CRNT.Analysis.SpernerTriangulation`
- `CRNT.Basic.Complex`
- `CRNT.Basic.Isomorphism`
- `CRNT.Basic.IsomorphismKinetics`
- `CRNT.Basic.IsomorphismStructural`
- `CRNT.Basic.Network`
- `CRNT.Basic.Reaction`
- `CRNT.Combinatorics.DecidableCycle`
- `CRNT.Combinatorics.DigraphExcess`
- `CRNT.Compose.Interconnect`
- `CRNT.Compose.InterconnectKinetics`
- `CRNT.Compose.InterconnectMonostationary`
- `CRNT.Compose.InterconnectSiphon`
- `CRNT.Compose.StoichIndependent`
- `CRNT.Decision.ACRCheck`
- `CRNT.Decision.ComputableDeficiency`
- `CRNT.Decision.ComputableTerminalSLC`
- `CRNT.Decision.ConservationConeStrict`
- `CRNT.Decision.CriticalSiphonDecide`
- `CRNT.Decision.DeficiencyOneConditionsDecide`
- `CRNT.Decision.DeficiencyZeroTactic`
- `CRNT.Decision.DirectedReachability`
- `CRNT.Decision.ExactDeficiency`
- `CRNT.Decision.GaussianRank`
- `CRNT.Decision.InjectivityMargin`
- `CRNT.Decision.IsCriticalSiphonDecidable`
- `CRNT.Decision.Linkage`
- `CRNT.Decision.LinkageDeficiencyExact`
- `CRNT.Decision.MinorSearch`
- `CRNT.Decision.PersistenceCertified`
- `CRNT.Decision.PersistenceSingleLinkage`
- `CRNT.Decision.PersistenceVerdict`
- `CRNT.Decision.Rank`
- `CRNT.Decision.RankExact`
- `CRNT.Decision.RationalFarkas`
- `CRNT.Decision.RationalFarkasDecide`
- `CRNT.Decision.RationalFarkasStrict`
- `CRNT.Decision.Reachability`
- `CRNT.Decision.StoichBasisQ`
- `CRNT.Decision.StrictConeRealization`
- `CRNT.Decision.StrongLinkage`
- `CRNT.Decision.Tactic`
- `CRNT.Decomposition.BlockDeficiency`
- `CRNT.Decomposition.Deficiency`
- `CRNT.Decomposition.Rank`
- `CRNT.Decomposition.ReactionPartition`
- `CRNT.Deficiency.AdvancedDeficiencyAlgorithm`
- `CRNT.Deficiency.BirchClassScaleTransport`
- `CRNT.Deficiency.BorosActiveInwardEstimate`
- `CRNT.Deficiency.BorosBirchGraph`
- `CRNT.Deficiency.BorosDeficiencyOneReduction`
- `CRNT.Deficiency.BorosLinkageProjection`
- `CRNT.Deficiency.BorosSingleLinkageEstimate`
- `CRNT.Deficiency.ClassConservation`
- `CRNT.Deficiency.ClassScaleSynchronization`
- `CRNT.Deficiency.ClosedSetKernel`
- `CRNT.Deficiency.Colinearity`
- `CRNT.Deficiency.ColinearityClasses`
- `CRNT.Deficiency.ComplexBalancedRatio`
- `CRNT.Deficiency.Confluence`
- `CRNT.Deficiency.Consistent`
- `CRNT.Deficiency.ConsistentWR`
- `CRNT.Deficiency.CutPair`
- `CRNT.Deficiency.CycleExactSequence`
- `CRNT.Deficiency.CycleSplitting`
- `CRNT.Deficiency.DOACapacityConstruction`
- `CRNT.Deficiency.DOAForward`
- `CRNT.Deficiency.DeficiencyOne`
- `CRNT.Deficiency.DeficiencyOneAlgorithm`
- `CRNT.Deficiency.DeficiencyOneDecide`
- `CRNT.Deficiency.DeficiencyOneDecomp`
- `CRNT.Deficiency.DeficiencyOneHypotheses`
- `CRNT.Deficiency.DeficiencyOneLine`
- `CRNT.Deficiency.DeficiencyOneLinkageScalars`
- `CRNT.Deficiency.DeficiencyOneLocalize`
- `CRNT.Deficiency.DeficiencyOneMonotonicity`
- `CRNT.Deficiency.DeficiencyOneRowDefect`
- `CRNT.Deficiency.DeficiencyOneScalarReduction`
- `CRNT.Deficiency.DeficiencyOneStructure`
- `CRNT.Deficiency.DeficiencyZeroConsistency`
- `CRNT.Deficiency.DeficientClassKernel`
- `CRNT.Deficiency.Definition`
- `CRNT.Deficiency.Drainage`
- `CRNT.Deficiency.ExactSequence`
- `CRNT.Deficiency.ExcessPositivity`
- `CRNT.Deficiency.HigherDeficiency`
- `CRNT.Deficiency.IncidenceBlock`
- `CRNT.Deficiency.KernelDimension`
- `CRNT.Deficiency.KernelDimensionBound`
- `CRNT.Deficiency.KernelDimensionWR`
- `CRNT.Deficiency.KineticBlock`
- `CRNT.Deficiency.KineticExcess`
- `CRNT.Deficiency.LevelSetSign`
- `CRNT.Deficiency.LinkageCoupling`
- `CRNT.Deficiency.LinkageCouplingLine`
- `CRNT.Deficiency.LinkageDeficiency`
- `CRNT.Deficiency.LogMonomialRatio`
- `CRNT.Deficiency.LogObstructionClassScaling`
- `CRNT.Deficiency.PerClassKernel`
- `CRNT.Deficiency.PerClassKernelPos`
- `CRNT.Deficiency.PerClassKernelUnique`
- `CRNT.Deficiency.PositiveKineticDomain`
- `CRNT.Deficiency.PositiveKineticFamily`
- `CRNT.Deficiency.PositiveKineticObstructionIVT`
- `CRNT.Deficiency.PositiveKineticPreimageWR`
- `CRNT.Deficiency.PositiveKineticSection`
- `CRNT.Deficiency.RangeKineticWR`
- `CRNT.Deficiency.Regular`
- `CRNT.Deficiency.Shelf`
- `CRNT.Deficiency.Signature`
- `CRNT.Deficiency.SignedDrainage`
- `CRNT.Deficiency.SteadyStateKernel`
- `CRNT.Deficiency.StrictKineticDissipation`
- `CRNT.Deficiency.StructuredPreimage`
- `CRNT.Deficiency.TerminalKernelBound`
- `CRNT.Deficiency.TerminalKernelCone`
- `CRNT.Deficiency.TerminalKernelDimension`
- `CRNT.Deficiency.TerminalKernelFaces`
- `CRNT.Deficiency.TerminalReachable`
- `CRNT.Deficiency.TerminalSLC`
- `CRNT.Deficiency.TerminalSLCKernel`
- `CRNT.Deficiency.WeaklyReversibleSteadyState`
- `CRNT.Design.ACR`
- `CRNT.Design.ACRCrossClass`
- `CRNT.Design.ACRStandard`
- `CRNT.Design.ACRUnconditional`
- `CRNT.Design.Adaptation`
- `CRNT.Design.BufferingStructure`
- `CRNT.Design.EmergentConservation`
- `CRNT.Design.EmergentCycles`
- `CRNT.Design.GeneratedClosure`
- `CRNT.Design.LabeledBufferingRPA`
- `CRNT.Design.LabeledBufferingStructure`
- `CRNT.Design.Localization`
- `CRNT.Design.LocalizationDifferential`
- `CRNT.Design.MaxRPA`
- `CRNT.Design.MaxRPAIntegrator`
- `CRNT.Design.MaxRPAStochastic`
- `CRNT.Design.MinimalForm`
- `CRNT.Design.OutputCompleteClosure`
- `CRNT.Design.ShinarFeinbergCrossClass`
- `CRNT.Design.ShinarFeinbergTheorem`
- `CRNT.Design.ShinarFeinbergTreeFormula`
- `CRNT.Design.StrongBufferingFluxRPA`
- `CRNT.Dynamics.BoundaryDescent`
- `CRNT.Dynamics.BoundaryOmegaSiphon`
- `CRNT.Dynamics.ButlerMcGehee`
- `CRNT.Dynamics.CenterManifold`
- `CRNT.Dynamics.CenterManifoldReduction`
- `CRNT.Dynamics.CertifiedReduction`
- `CRNT.Dynamics.ClosedSetNagumo`
- `CRNT.Dynamics.ComplexBalanceCycleDecomposition`
- `CRNT.Dynamics.ComplexBalanceStoichFan`
- `CRNT.Dynamics.ComplexBalanceStoichFanInclusion`
- `CRNT.Dynamics.ConfinedInvariance`
- `CRNT.Dynamics.ConservationLaw`
- `CRNT.Dynamics.CriticalSiphonDissipationRepulsion`
- `CRNT.Dynamics.CriticalSiphonNearFacetInflux`
- `CRNT.Dynamics.CriticalSiphonOmega`
- `CRNT.Dynamics.DifferentialInclusion`
- `CRNT.Dynamics.DissipationBound`
- `CRNT.Dynamics.DissipativeTracking`
- `CRNT.Dynamics.EndotacticPermanence`
- `CRNT.Dynamics.EscapeSiphonFace`
- `CRNT.Dynamics.ExponentialDecay`
- `CRNT.Dynamics.ExponentialDichotomy`
- `CRNT.Dynamics.FaceCodimension`
- `CRNT.Dynamics.FaceDirectionCone`
- `CRNT.Dynamics.FacetRepulsion`
- `CRNT.Dynamics.FacetRepulsionAndersonShiu`
- `CRNT.Dynamics.Fenichel`
- `CRNT.Dynamics.FenichelC1Manifold`
- `CRNT.Dynamics.FenichelComovingManifold`
- `CRNT.Dynamics.FenichelContinuousMovingTarget`
- `CRNT.Dynamics.FenichelCoupledBase`
- `CRNT.Dynamics.FenichelGeneralDrift`
- `CRNT.Dynamics.FenichelLogisticInstance`
- `CRNT.Dynamics.FenichelManifold`
- `CRNT.Dynamics.FenichelMovingGeneralDrift`
- `CRNT.Dynamics.FenichelPersistence`
- `CRNT.Dynamics.FenichelPersistenceConcrete`
- `CRNT.Dynamics.FenichelPersistenceContracting`
- `CRNT.Dynamics.FenichelReductionPrinciple`
- `CRNT.Dynamics.FenichelSlowDrift`
- `CRNT.Dynamics.FenichelStabilityTransfer`
- `CRNT.Dynamics.FiniteNegativeBudget`
- `CRNT.Dynamics.FirstExit`
- `CRNT.Dynamics.FlowConstruction`
- `CRNT.Dynamics.FlowDifferentiable`
- `CRNT.Dynamics.FlowSmoothDependence`
- `CRNT.Dynamics.ForwardInvariance`
- `CRNT.Dynamics.GACCertificate`
- `CRNT.Dynamics.GACConfinement`
- `CRNT.Dynamics.GACNoCriticalSiphon`
- `CRNT.Dynamics.GACOmegaPositive`
- `CRNT.Dynamics.GACSeparatingCapstone`
- `CRNT.Dynamics.GACSeparatingRegion`
- `CRNT.Dynamics.GACSeparatingRegionNagumo`
- `CRNT.Dynamics.GACSeparatingWitness`
- `CRNT.Dynamics.GenuineConfinement`
- `CRNT.Dynamics.GershgorinColumnMarginQ`
- `CRNT.Dynamics.GershgorinMarginQ`
- `CRNT.Dynamics.GlobalPermanence`
- `CRNT.Dynamics.GlobalPersistence`
- `CRNT.Dynamics.GlobalPersistenceCertificates`
- `CRNT.Dynamics.GlobalPersistenceFrontier`
- `CRNT.Dynamics.GlobalStability`
- `CRNT.Dynamics.GraphTransform`
- `CRNT.Dynamics.HopfAdmissible`
- `CRNT.Dynamics.HopfBoundaryQ`
- `CRNT.Dynamics.HopfGate`
- `CRNT.Dynamics.HopfGate3Matrix`
- `CRNT.Dynamics.HopfGate4`
- `CRNT.Dynamics.HopfLimitCycle`
- `CRNT.Dynamics.HopfNormalForm`
- `CRNT.Dynamics.HopfPersistentOrbit`
- `CRNT.Dynamics.HopfRealizes`
- `CRNT.Dynamics.HopfTransversality3`
- `CRNT.Dynamics.Hurwitz`
- `CRNT.Dynamics.Hurwitz2Matrix`
- `CRNT.Dynamics.Hurwitz3Matrix`
- `CRNT.Dynamics.HurwitzGershgorin`
- `CRNT.Dynamics.HurwitzGershgorinColumn`
- `CRNT.Dynamics.IsolatedInvariant`
- `CRNT.Dynamics.KnownGlobalPersistenceClasses`
- `CRNT.Dynamics.LaSalle`
- `CRNT.Dynamics.MassActionAlgebra`
- `CRNT.Dynamics.MassActionField`
- `CRNT.Dynamics.MichaelisMenten`
- `CRNT.Dynamics.MichaelisMentenC1`
- `CRNT.Dynamics.MichaelisMentenCertified`
- `CRNT.Dynamics.MichaelisMentenCertifiedUniform`
- `CRNT.Dynamics.MichaelisMentenCoupledContraction`
- `CRNT.Dynamics.MichaelisMentenDepletion`
- `CRNT.Dynamics.MichaelisMentenFenichel`
- `CRNT.Dynamics.MichaelisMentenFenichelAllTime`
- `CRNT.Dynamics.MichaelisMentenLipschitz`
- `CRNT.Dynamics.MichaelisMentenManifold`
- `CRNT.Dynamics.MichaelisMentenReduced`
- `CRNT.Dynamics.MichaelisMentenRegularized`
- `CRNT.Dynamics.MichaelisMentenSlowDrift`
- `CRNT.Dynamics.MichaelisMentenSlowDriftSpeed`
- `CRNT.Dynamics.MinimalInvariant`
- `CRNT.Dynamics.Monotone`
- `CRNT.Dynamics.Nagumo`
- `CRNT.Dynamics.NegativeInvariance`
- `CRNT.Dynamics.NoCriticalSiphonPersistence`
- `CRNT.Dynamics.NoDrainableSiphonPersistence`
- `CRNT.Dynamics.OrbitRegularity`
- `CRNT.Dynamics.PermanenceAssembly`
- `CRNT.Dynamics.Persistence`
- `CRNT.Dynamics.PersistenceConfined`
- `CRNT.Dynamics.PersistenceGAC`
- `CRNT.Dynamics.PersistenceTheorem`
- `CRNT.Dynamics.PoincareReturnMap`
- `CRNT.Dynamics.PolyRegionInvariant`
- `CRNT.Dynamics.PolyRegionStrictInvariant`
- `CRNT.Dynamics.ProperTierTransversal`
- `CRNT.Dynamics.QSSA`
- `CRNT.Dynamics.ReactionConeDisplacement`
- `CRNT.Dynamics.ReactionConeWeakReversibility`
- `CRNT.Dynamics.ReturnMapPeriodicOrbit`
- `CRNT.Dynamics.RouthHurwitz`
- `CRNT.Dynamics.RouthHurwitz4`
- `CRNT.Dynamics.RouthHurwitz4Suff`
- `CRNT.Dynamics.SingleLinkageGAC`
- `CRNT.Dynamics.SingleLinkageStructure`
- `CRNT.Dynamics.SingletonFacetEscape`
- `CRNT.Dynamics.Siphon`
- `CRNT.Dynamics.SiphonAutocatalysis`
- `CRNT.Dynamics.SiphonConservation`
- `CRNT.Dynamics.SiphonDimensionDescent`
- `CRNT.Dynamics.SiphonFaceWeakReversibility`
- `CRNT.Dynamics.SiphonFacetEscape`
- `CRNT.Dynamics.SpectralSplitting`
- `CRNT.Dynamics.SpectralSplittingReal`
- `CRNT.Dynamics.StrictInflow`
- `CRNT.Dynamics.SublevelInvariant`
- `CRNT.Dynamics.SublevelNagumo`
- `CRNT.Dynamics.SupportDiniBridge`
- `CRNT.Dynamics.ThmBGenuine`
- `CRNT.Dynamics.TierCompactNegativity`
- `CRNT.Dynamics.TierDirectionFeasibility`
- `CRNT.Dynamics.TierDirectionProjection`
- `CRNT.Dynamics.TierDissipationAsymptotics`
- `CRNT.Dynamics.TierExtraction`
- `CRNT.Dynamics.TierExtractionCompleted`
- `CRNT.Dynamics.TierLyapunov`
- `CRNT.Dynamics.TierOrderAlgebra`
- `CRNT.Dynamics.TierOriginGeometry`
- `CRNT.Dynamics.TierPersistence`
- `CRNT.Dynamics.TierScaleDecomposition`
- `CRNT.Dynamics.TierScaleExtractionLemma44`
- `CRNT.Dynamics.TierScaleMagnitude`
- `CRNT.Dynamics.TierScaleTruncation`
- `CRNT.Dynamics.TierSequentialReduction`
- `CRNT.Dynamics.TierStrictUpwardPartner`
- `CRNT.Dynamics.TierSubsequenceExtraction`
- `CRNT.Dynamics.Tikhonov`
- `CRNT.Dynamics.ToricBarrierExplicit`
- `CRNT.Dynamics.ToricBarrierTrapping`
- `CRNT.Dynamics.ToricCycleOrderLimits`
- `CRNT.Dynamics.ToricCycleSortedBase`
- `CRNT.Dynamics.ToricEmbedding`
- `CRNT.Dynamics.ToricEmbeddingOrder`
- `CRNT.Dynamics.ToricEmbeddingWR`
- `CRNT.Dynamics.ToricInclusion`
- `CRNT.Dynamics.TransversalCrossingTime`
- `CRNT.Dynamics.Trap`
- `CRNT.Dynamics.VariableTierLyapunov`
- `CRNT.Dynamics.VariationalEquation`
- `CRNT.Dynamics.Viability`
- `CRNT.Dynamics.ZeroSeparating`
- `CRNT.Equilibria.BoundarySiphon`
- `CRNT.Equilibria.BrouwerNormalCone`
- `CRNT.Equilibria.BrouwerSteadyState`
- `CRNT.Equilibria.CompatibilityClass`
- `CRNT.Equilibria.ComplexBalanceGeometry`
- `CRNT.Equilibria.ComplexBalanceLinearStability`
- `CRNT.Equilibria.ComplexBalanceObstruction`
- `CRNT.Equilibria.ComplexBalanceStructure`
- `CRNT.Equilibria.ComplexBalanced`
- `CRNT.Equilibria.ConservationCoordinates`
- `CRNT.Equilibria.DetailedBalanceEntropy`
- `CRNT.Equilibria.DetailedBalanceLinearStability`
- `CRNT.Equilibria.DetailedBalanceToric`
- `CRNT.Equilibria.DetailedBalanced`
- `CRNT.Equilibria.DirectedMatrixTreeProof`
- `CRNT.Equilibria.GeneralizedComplexBalanceGeometry`
- `CRNT.Equilibria.GeneralizedComplexBalanceToric`
- `CRNT.Equilibria.GeneralizedTreeConstantCriterion`
- `CRNT.Equilibria.LinkageComplexBalance`
- `CRNT.Equilibria.MatrixTreeCofactor`
- `CRNT.Equilibria.MatrixTreeCofactorDefs`
- `CRNT.Equilibria.SteadyState`
- `CRNT.Equilibria.SteadyStateFlux`
- `CRNT.Equilibria.TreeConstantBinomials`
- `CRNT.Equilibria.TreeConstantCriterion`
- `CRNT.Equilibria.TreeConstantKernelBasis`
- `CRNT.Equilibria.TreeConstants`
- `CRNT.Equilibria.TreePotentialIntegration`
- `CRNT.Equilibria.Wegscheider`
- `CRNT.Equilibria.WegscheiderConverse`
- `CRNT.Equilibria.WegscheiderDeficiency`
- `CRNT.Equilibria.WegscheiderDeficiencyOne`
- `CRNT.Equilibria.WegscheiderGenerators`
- `CRNT.Equilibria.WegscheiderInteger`
- `CRNT.Examples.CatalyticChain`
- `CRNT.Examples.ComplexBalancedBoundaryEquilibrium`
- `CRNT.Examples.CrntCheck`
- `CRNT.Examples.CycleRateNonMonotone`
- `CRNT.Examples.DecideDirectedReachability`
- `CRNT.Examples.DecideLinkage`
- `CRNT.Examples.DecideRank`
- `CRNT.Examples.DecideReachability`
- `CRNT.Examples.DecideStrongLinkage`
- `CRNT.Examples.DeficiencyBookkeeping`
- `CRNT.Examples.DeficiencyOneStatementExample`
- `CRNT.Examples.Enzyme`
- `CRNT.Examples.GACBlueprintPremiseCounterexamples`
- `CRNT.Examples.GACReversiblePair`
- `CRNT.Examples.GeneExpression`
- `CRNT.Examples.GeneralKinetics`
- `CRNT.Examples.HopfNetwork3`
- `CRNT.Examples.HopfNetwork3Branches`
- `CRNT.Examples.HopfOscillator3`
- `CRNT.Examples.IrreversibleChain`
- `CRNT.Examples.LinkageDeficiencyExample`
- `CRNT.Examples.Lotka`
- `CRNT.Examples.Minimal`
- `CRNT.Examples.OpenSystem`
- `CRNT.Examples.ReversiblePair`
- `CRNT.Examples.StochasticConvergenceExample`
- `CRNT.Examples.TrueSRCounterexample`
- `CRNT.Examples.TrueSRNetCoeffCounterexample`
- `CRNT.Flux.CircuitTheory`
- `CRNT.Flux.Cone`
- `CRNT.Flux.ConformalDecomposition`
- `CRNT.Flux.Elementary`
- `CRNT.Flux.ExtremeRay`
- `CRNT.Flux.IntegerTInvariant`
- `CRNT.Flux.PSemiflow`
- `CRNT.Geometry.CompatibilityFaces`
- `CRNT.Geometry.ConeFace`
- `CRNT.Geometry.ConservativeCompatibility`
- `CRNT.Geometry.ConvexBarrierObstruction`
- `CRNT.Geometry.CraciunV3BlueprintScales`
- `CRNT.Geometry.CraciunZSH`
- `CRNT.Geometry.Endotactic`
- `CRNT.Geometry.EndotacticGlobal`
- `CRNT.Geometry.FaithfulCurve`
- `CRNT.Geometry.FaithfulCurve2D`
- `CRNT.Geometry.FaithfulCurve2DFan`
- `CRNT.Geometry.FaithfulCurveExistence`
- `CRNT.Geometry.FaithfulCurveGeneral`
- `CRNT.Geometry.FanActiveWalls`
- `CRNT.Geometry.FanFaceLattice`
- `CRNT.Geometry.FanFaceProperness`
- `CRNT.Geometry.FanRefinement`
- `CRNT.Geometry.FanSeparationWitness`
- `CRNT.Geometry.FanWallActivityDecide`
- `CRNT.Geometry.FanWallsCrossed`
- `CRNT.Geometry.FiniteConeClosed`
- `CRNT.Geometry.HalfPlaneSeparatingSurface`
- `CRNT.Geometry.LogProjectiveFaceCompatibility`
- `CRNT.Geometry.LogProjectiveSection`
- `CRNT.Geometry.LogProjectiveSmoothSection`
- `CRNT.Geometry.PolyRegionSeparating`
- `CRNT.Geometry.PolyhedralBarrier`
- `CRNT.Geometry.PolyhedralFan`
- `CRNT.Geometry.ProjectedFaceDimensionCode`
- `CRNT.Geometry.ReactionFanGeneration`
- `CRNT.Geometry.ReactionHullCone`
- `CRNT.Geometry.SimplicialConeClosed`
- `CRNT.Geometry.SmoothBarrierGluing`
- `CRNT.Geometry.SourceOrderReactionFan`
- `CRNT.Geometry.SpeciesProjection`
- `CRNT.Geometry.ToricFan`
- `CRNT.Geometry.ToricFieldPolar`
- `CRNT.Geometry.ToricFieldPolarMulti`
- `CRNT.Geometry.ToricStrictSupport`
- `CRNT.Geometry.ToricUniformWallMargin`
- `CRNT.Geometry.ToricWRStrictInward`
- `CRNT.Geometry.WeakReversibleWallObstruction`
- `CRNT.Geometry.ZeroSeparatingCurve2D`
- `CRNT.Geometry.ZeroSeparatingInduction`
- `CRNT.Geometry.ZeroSeparatingSurface`
- `CRNT.Graph.CirculationDecomposition`
- `CRNT.Graph.Condensation`
- `CRNT.Graph.Crossing`
- `CRNT.Graph.CycleCover`
- `CRNT.Graph.FiniteSource`
- `CRNT.Graph.LinkageClass`
- `CRNT.Graph.PositiveCirculation`
- `CRNT.Graph.Reachability`
- `CRNT.Graph.RelPath`
- `CRNT.Graph.Reversibility`
- `CRNT.Graph.SourceBlocks`
- `CRNT.Graph.WeakReversibility`
- `CRNT.Interop.Analysis`
- `CRNT.Interop.Certificates`
- `CRNT.Interop.CodegenExamples`
- `CRNT.Interop.NetworkData`
- `CRNT.Kinetics.CatalystFace`
- `CRNT.Kinetics.Concentration`
- `CRNT.Kinetics.General`
- `CRNT.Kinetics.Generalized`
- `CRNT.Kinetics.GeneralizedBirchExistence`
- `CRNT.Kinetics.GeneralizedBirchLocal`
- `CRNT.Kinetics.GeneralizedBirchSelector`
- `CRNT.Kinetics.GeneralizedComplexBalanceObstruction`
- `CRNT.Kinetics.GeneralizedConditions`
- `CRNT.Kinetics.GeneralizedCycleExactSequence`
- `CRNT.Kinetics.GeneralizedDeficiencyComparison`
- `CRNT.Kinetics.GeneralizedDeficiencyZero`
- `CRNT.Kinetics.GeneralizedDeficiencyZeroCRNT`
- `CRNT.Kinetics.GeneralizedDeficiencyZeroExistence`
- `CRNT.Kinetics.GeneralizedDeficiencyZeroProof`
- `CRNT.Kinetics.GeneralizedNetwork`
- `CRNT.Kinetics.GeneralizedNondegeneracy`
- `CRNT.Kinetics.MassAction`
- `CRNT.Kinetics.MassActionJacobian`
- `CRNT.Kinetics.SpeciesProjectionMassAction`
- `CRNT.Kinetics.VariableMassAction`
- `CRNT.LinearAlgebra.CauchyBinet`
- `CRNT.LinearAlgebra.ConformalDecomposition`
- `CRNT.LinearAlgebra.DetCycleCover`
- `CRNT.LinearAlgebra.FinrankSup`
- `CRNT.LinearAlgebra.LogSumInj`
- `CRNT.LinearAlgebra.OrientedMatroid`
- `CRNT.LinearAlgebra.OrientedMatroidConditions`
- `CRNT.LinearAlgebra.OrientedMatroidNondegeneracy`
- `CRNT.LinearAlgebra.OrthogonalComplement`
- `CRNT.LinearAlgebra.PerronFrobenius`
- `CRNT.LinearAlgebra.PowerProductMono`
- `CRNT.LinearAlgebra.PowerProductMonoFinset`
- `CRNT.LinearAlgebra.RationalDenominator`
- `CRNT.LinearAlgebra.SignVector`
- `CRNT.LinearAlgebra.Substochastic`
- `CRNT.Multistationarity.Capacity`
- `CRNT.Multistationarity.Concordance`
- `CRNT.Multistationarity.ConcordanceConverse`
- `CRNT.Multistationarity.DeficiencyObstruction`
- `CRNT.Multistationarity.DegreeAdditivity`
- `CRNT.Multistationarity.DegreeHomotopyInvariant`
- `CRNT.Multistationarity.DegreeLocallyConstant`
- `CRNT.Multistationarity.DegreeProperConstant`
- `CRNT.Multistationarity.DegreeStability`
- `CRNT.Multistationarity.Discordance`
- `CRNT.Multistationarity.FullyOpenConcordanceSpectral`
- `CRNT.Multistationarity.GainPotential`
- `CRNT.Multistationarity.GaleNikaido`
- `CRNT.Multistationarity.GaleNikaidoBox`
- `CRNT.Multistationarity.GaleNikaidoUniv`
- `CRNT.Multistationarity.InfluenceConcordance`
- `CRNT.Multistationarity.Injectivity`
- `CRNT.Multistationarity.JacobianCycleSelection`
- `CRNT.Multistationarity.JacobianCycleSign`
- `CRNT.Multistationarity.JacobianDeterminantSign`
- `CRNT.Multistationarity.JacobianInjectivity`
- `CRNT.Multistationarity.LinearDegree`
- `CRNT.Multistationarity.LocalDegreeOn`
- `CRNT.Multistationarity.Normality`
- `CRNT.Multistationarity.NormalityTerminal`
- `CRNT.Multistationarity.PMatrix`
- `CRNT.Multistationarity.PMatrixSchur`
- `CRNT.Multistationarity.PMatrixSignature`
- `CRNT.Multistationarity.PMatrixUnivalence`
- `CRNT.Multistationarity.ParametrizedLocalDegree`
- `CRNT.Multistationarity.PivotChartInjectivity`
- `CRNT.Multistationarity.PivotReducedInjectivity`
- `CRNT.Multistationarity.PointIndepDecidable`
- `CRNT.Multistationarity.ReducedCoverSign`
- `CRNT.Multistationarity.ReducedJacobian`
- `CRNT.Multistationarity.ReducedJacobianSign`
- `CRNT.Multistationarity.ReducedPMatrixDecide`
- `CRNT.Multistationarity.ReducedSRGraph`
- `CRNT.Multistationarity.ReducedSRGraphBridge`
- `CRNT.Multistationarity.RegularValueDegree`
- `CRNT.Multistationarity.SRCoverPointIndependence`
- `CRNT.Multistationarity.SRCycleInjectivity`
- `CRNT.Multistationarity.SRGraph`
- `CRNT.Multistationarity.SRGraphCriterion`
- `CRNT.Multistationarity.SRGraphCycleDict`
- `CRNT.Multistationarity.SRInjectivityClass`
- `CRNT.Multistationarity.SRSignDecidable`
- `CRNT.Multistationarity.Sard`
- `CRNT.Multistationarity.SignConstruction`
- `CRNT.Multistationarity.SignedSRGraph`
- `CRNT.Multistationarity.SourceWeightPairing`
- `CRNT.Multistationarity.SteadyStateDegree`
- `CRNT.Multistationarity.StoichChart`
- `CRNT.Multistationarity.StrongConcordance`
- `CRNT.Multistationarity.StrongConcordanceStability`
- `CRNT.Multistationarity.Toric`
- `CRNT.Multistationarity.TrueChemistrySRGraph`
- `CRNT.Multistationarity.TrueChemistrySRGraphSpecialCases`
- `CRNT.Multistationarity.TrueSRArc`
- `CRNT.Multistationarity.TrueSRCPairThirdEdge`
- `CRNT.Multistationarity.TrueSRCausalCycleFacts`
- `CRNT.Multistationarity.TrueSRChordExtraction`
- `CRNT.Multistationarity.TrueSRChordParity`
- `CRNT.Multistationarity.TrueSRClosedWalk`
- `CRNT.Multistationarity.TrueSRCycleChord`
- `CRNT.Multistationarity.TrueSRCycleReverse`
- `CRNT.Multistationarity.TrueSRCycleSplit`
- `CRNT.Multistationarity.TrueSRDegreeTwoNoSToR`
- `CRNT.Multistationarity.TrueSREdgePath`
- `CRNT.Multistationarity.TrueSRGlueBlocks`
- `CRNT.Multistationarity.TrueSRGlueCPairs`
- `CRNT.Multistationarity.TrueSRGlueCount`
- `CRNT.Multistationarity.TrueSRGlueIndex`
- `CRNT.Multistationarity.TrueSRGlueInterface`
- `CRNT.Multistationarity.TrueSRGlueMaps`
- `CRNT.Multistationarity.TrueSRGlueSeams`
- `CRNT.Multistationarity.TrueSRLinearWalk`
- `CRNT.Multistationarity.TrueSRMidSegment`
- `CRNT.Multistationarity.TrueSRMinimalChord`
- `CRNT.Multistationarity.TrueSRNoArcChord`
- `CRNT.Multistationarity.TrueSRParityCount`
- `CRNT.Multistationarity.TrueSRParityLemma`
- `CRNT.Multistationarity.TrueSRParityRR`
- `CRNT.Multistationarity.TrueSRPath`
- `CRNT.Multistationarity.TrueSRPathAccessors`
- `CRNT.Multistationarity.TrueSRPathCPairs`
- `CRNT.Multistationarity.TrueSRPathSegment`
- `CRNT.Multistationarity.TrueSRPathTerminalSegment`
- `CRNT.Multistationarity.TrueSRReactionInteriorPath`
- `CRNT.Multistationarity.TrueSRRotate`
- `CRNT.Multistationarity.TrueSRSSGlueCPairs`
- `CRNT.Multistationarity.TrueSRSeamParity`
- `CRNT.Multistationarity.TrueSRSegmentEndpoints`
- `CRNT.Multistationarity.TrueSRSingleSharedEdge`
- `CRNT.Multistationarity.TrueSRSpeciesPath`
- `CRNT.Multistationarity.TrueSRTwoGluedCycles`
- `CRNT.Multistationarity.TrueSRTwoWeightGain`
- `CRNT.Multistationarity.TrueSRWalkEdges`
- `CRNT.Multistationarity.WeakNormality`
- `CRNT.Multistationarity.WeakNormalityCriterion`
- `CRNT.Open.Augmentation`
- `CRNT.Open.Boundary`
- `CRNT.Open.Deficiency`
- `CRNT.Open.PartialOpen`
- `CRNT.Oscillation`
- `CRNT.Oscillation.Analyze`
- `CRNT.Oscillation.BanajiDependentReaction`
- `CRNT.Oscillation.BanajiEndToEnd`
- `CRNT.Oscillation.Basic`
- `CRNT.Oscillation.Certificate`
- `CRNT.Oscillation.ChildSelectionReactivity`
- `CRNT.Oscillation.ChildSelectionSearch`
- `CRNT.Oscillation.CompatibilityAdapters`
- `CRNT.Oscillation.ConcentrationEuclidean`
- `CRNT.Oscillation.ContinuousTimeAttraction`
- `CRNT.Oscillation.CoordinateDynamics`
- `CRNT.Oscillation.DHopf`
- `CRNT.Oscillation.DHopfOpenness`
- `CRNT.Oscillation.DependentReaction`
- `CRNT.Oscillation.DependentReactionPersistence`
- `CRNT.Oscillation.DiagonalScaling`
- `CRNT.Oscillation.DulacAreaSign`
- `CRNT.Oscillation.DulacLineIntegral`
- `CRNT.Oscillation.Exclusion`
- `CRNT.Oscillation.FiedlerGlobalHopf`
- `CRNT.Oscillation.FisherFullerScaling`
- `CRNT.Oscillation.Floquet`
- `CRNT.Oscillation.FloquetOrbitalStability`
- `CRNT.Oscillation.FloquetPersistenceBridge`
- `CRNT.Oscillation.FloquetPersistenceGeneral`
- `CRNT.Oscillation.FloquetReturnBridge`
- `CRNT.Oscillation.GlobalAttraction`
- `CRNT.Oscillation.GlobalHopfContinuation`
- `CRNT.Oscillation.GlobalHopfIndex`
- `CRNT.Oscillation.GlobalHopfIndexTheorem`
- `CRNT.Oscillation.GlobalHopfSpectralCrossing`
- `CRNT.Oscillation.GreenJordanFoundations`
- `CRNT.Oscillation.GreenJordanReduction`
- `CRNT.Oscillation.HalfPlanePolynomial`
- `CRNT.Oscillation.HurwitzBordering`
- `CRNT.Oscillation.Inheritance`
- `CRNT.Oscillation.KineticBasic`
- `CRNT.Oscillation.LowRank`
- `CRNT.Oscillation.MatrixCriteria`
- `CRNT.Oscillation.OrbitTube`
- `CRNT.Oscillation.OscillationKernelBundle`
- `CRNT.Oscillation.OscillatoryCoreEndToEnd`
- `CRNT.Oscillation.ParameterRich`
- `CRNT.Oscillation.ParameterRichDHopfContinuation`
- `CRNT.Oscillation.ParameterRichGlobalHopf`
- `CRNT.Oscillation.PlanarAdjacentReturnLoop`
- `CRNT.Oscillation.PlanarCanonicalReturn`
- `CRNT.Oscillation.PlanarDivergenceRegularity`
- `CRNT.Oscillation.PlanarDulac`
- `CRNT.Oscillation.PlanarEndToEnd`
- `CRNT.Oscillation.PlanarFloquetAttraction`
- `CRNT.Oscillation.PlanarFlowBox`
- `CRNT.Oscillation.PlanarFlowRegularity`
- `CRNT.Oscillation.PlanarFrontier`
- `CRNT.Oscillation.PlanarGreenGrid`
- `CRNT.Oscillation.PlanarGreenJordanApproximation`
- `CRNT.Oscillation.PlanarGreenRectangle`
- `CRNT.Oscillation.PlanarJordanBoundaryCurrent`
- `CRNT.Oscillation.PlanarJordanCrossingOrder`
- `CRNT.Oscillation.PlanarJordanDyadic`
- `CRNT.Oscillation.PlanarJordanSeparation`
- `CRNT.Oscillation.PlanarJordanTopology`
- `CRNT.Oscillation.PlanarLateSectionReturn`
- `CRNT.Oscillation.PlanarLocalReturnLoops`
- `CRNT.Oscillation.PlanarLocalReturns`
- `CRNT.Oscillation.PlanarMinimalSet`
- `CRNT.Oscillation.PlanarNoCrossing`
- `CRNT.Oscillation.PlanarOmega`
- `CRNT.Oscillation.PlanarOneSidedReturns`
- `CRNT.Oscillation.PlanarPoincareBendixson`
- `CRNT.Oscillation.PlanarRecurrentSection`
- `CRNT.Oscillation.PlanarReturnMonotonicity`
- `CRNT.Oscillation.PlanarReturnOrdering`
- `CRNT.Oscillation.PlanarReturnSequence`
- `CRNT.Oscillation.PlanarSectionCoordinates`
- `CRNT.Oscillation.PlanarSectionHitIsolation`
- `CRNT.Oscillation.PlanarTransversalGeometry`
- `CRNT.Oscillation.RankTwoPlanar`
- `CRNT.Oscillation.ReactionRestriction`
- `CRNT.Oscillation.ReactivityScaling`
- `CRNT.Oscillation.RecipeZero`
- `CRNT.Oscillation.RecipeZeroContinuation`
- `CRNT.Oscillation.ReducedKineticContinuation`
- `CRNT.Oscillation.ReturnInterval`
- `CRNT.Oscillation.ReturnMap`
- `CRNT.Oscillation.ReturnMapAttraction`
- `CRNT.Oscillation.ReturnMapContraction`
- `CRNT.Oscillation.ReturnMapFamilyPersistence`
- `CRNT.Oscillation.ReturnMapPersistence`
- `CRNT.Oscillation.ScalarReturnMapFamilyPersistence`
- `CRNT.Oscillation.ScalarReturnStability`
- `CRNT.Oscillation.ScalarSectionInterpolation`
- `CRNT.Oscillation.SimpleCycle`
- `CRNT.Oscillation.SimpleNegativeSpectrum`
- `CRNT.Oscillation.SimpleRoot`
- `CRNT.Oscillation.SmoothGlobalHopf`
- `CRNT.Oscillation.SpectralOpenness`
- `CRNT.Oscillation.StableCodimOneDHopf`
- `CRNT.Oscillation.StructuralCore`
- `CRNT.Oscillation.VassenaAnalyticity`
- `CRNT.Oscillation.VassenaContinuation`
- `CRNT.Oscillation.VassenaCriteria`
- `CRNT.Oscillation.VassenaEndToEnd`
- `CRNT.Oscillation.VassenaFiniteDimHopf`
- `CRNT.Oscillation.VassenaPrincipal`
- `CRNT.Reduction.IntermediateSchurComplement`
- `CRNT.Reduction.Intermediates`
- `CRNT.Reduction.SingleIntermediateElimination`
- `CRNT.Stability.BDC`
- `CRNT.Stability.BDCCauchyBinetProof`
- `CRNT.Stability.BDCPrincipalMinors`
- `CRNT.Stability.BDCStructuralNonsingularity`
- `CRNT.Stability.RobustLyapunov`
- `CRNT.Stochastic.Absorbing`
- `CRNT.Stochastic.BirthDeathExhaustive`
- `CRNT.Stochastic.CTMC`
- `CRNT.Stochastic.ConservationClassRegion`
- `CRNT.Stochastic.ConservativeClasses`
- `CRNT.Stochastic.CountWitnessPath`
- `CRNT.Stochastic.DetailedBalance`
- `CRNT.Stochastic.ErgodicConvergence`
- `CRNT.Stochastic.ErgodicConvergenceGeneral`
- `CRNT.Stochastic.Ergodicity`
- `CRNT.Stochastic.FirstOrderFoster`
- `CRNT.Stochastic.FosterLyapunov`
- `CRNT.Stochastic.Generator`
- `CRNT.Stochastic.IntegerLattice`
- `CRNT.Stochastic.JumpKernel`
- `CRNT.Stochastic.JumpReachabilityLift`
- `CRNT.Stochastic.Kernel`
- `CRNT.Stochastic.KernelInvariant`
- `CRNT.Stochastic.KernelIrreducible`
- `CRNT.Stochastic.KernelMaximalRegion`
- `CRNT.Stochastic.KernelNormalized`
- `CRNT.Stochastic.KernelProductForm`
- `CRNT.Stochastic.KernelStationary`
- `CRNT.Stochastic.KernelSupport`
- `CRNT.Stochastic.KurtzFluidLimit`
- `CRNT.Stochastic.KurtzScaling`
- `CRNT.Stochastic.MultiPoissonFluctuation`
- `CRNT.Stochastic.PoissonClockFamily`
- `CRNT.Stochastic.PoissonFluctuation`
- `CRNT.Stochastic.ProductForm`
- `CRNT.Stochastic.ProductFormConverse`
- `CRNT.Stochastic.RegionPrimitive`
- `CRNT.Stochastic.RegionStronglyConnected`
- `CRNT.Stochastic.Semigroup`
- `CRNT.Stochastic.SemigroupComposition`
- `CRNT.Stochastic.SemigroupConvergence`
- `CRNT.Stochastic.TimeChangedFluctuation`
- `CRNT.Stochastic.UniformizedConvergence`
- `CRNT.Stoich.ConservationDimension`
- `CRNT.Stoich.RationalVector`
- `CRNT.Stoich.Subspace`
- `CRNT.Stoich.Transpose`
- `CRNT.Stoich.Vector`
- `CRNT.Subnetwork.EmbeddedNetwork`
- `CRNT.Subnetwork.ReactionRestriction`
- `CRNT.Theorems.DeficiencyOne.DegreeExistence`
- `CRNT.Theorems.DeficiencyOne.DegreeExistenceBridges`
- `CRNT.Theorems.DeficiencyOne.Existence`
- `CRNT.Theorems.DeficiencyOne.ExistenceDynamical`
- `CRNT.Theorems.DeficiencyOne.JacobianKernel`
- `CRNT.Theorems.DeficiencyOne.JacobianOnStoich`
- `CRNT.Theorems.DeficiencyOne.LogRatioUniqueness`
- `CRNT.Theorems.DeficiencyOne.MultiClass`
- `CRNT.Theorems.DeficiencyOne.Statement`
- `CRNT.Theorems.DeficiencyOne.Theorem`
- `CRNT.Theorems.DeficiencyOne.ToricReduction`
- `CRNT.Theorems.DeficiencyOne.Uniqueness`
- `CRNT.Theorems.DeficiencyOne.WeaklyReversibleExistence`
- `CRNT.Theorems.DeficiencyOne.WeaklyReversibleExistenceSpecialCases`
- `CRNT.Theorems.DeficiencyZero.AsymptoticStability`
- `CRNT.Theorems.DeficiencyZero.Birch`
- `CRNT.Theorems.DeficiencyZero.BirchExistence`
- `CRNT.Theorems.DeficiencyZero.Characterization`
- `CRNT.Theorems.DeficiencyZero.Confinement`
- `CRNT.Theorems.DeficiencyZero.Dissipation`
- `CRNT.Theorems.DeficiencyZero.Existence`
- `CRNT.Theorems.DeficiencyZero.Lyapunov`
- `CRNT.Theorems.DeficiencyZero.NoPeriodicOrbit`
- `CRNT.Theorems.DeficiencyZero.PositiveKernel`
- `CRNT.Theorems.DeficiencyZero.Stability`
- `CRNT.Theorems.DeficiencyZero.Statement`
- `CRNT.Theorems.DeficiencyZero.Toric`
- `CRNT.Theorems.DeficiencyZero.TreeConstantConstruction`
- `CRNT.Theorems.DeficiencyZero.TreeConstantProofComplete`
- `CRNT.Topology.ProperLocalHomeomorph`
- `CRNT.Translation.ComplexBalance`
- `CRNT.Translation.DeficiencyImprovement`
- `CRNT.Translation.DynamicalEquivalence`
- `CRNT.Translation.Improper`
- `CRNT.Translation.ImproperComplexBalance`
- `CRNT.Translation.LinearConjugacy`
- `CRNT.Translation.LinearConjugacySpectral`
- `CRNT.Translation.ParallelAggregation`
- `CRNT.Translation.ParallelStructural`
- `CRNT.Translation.ReactionTranslation`
- `CRNT.Translation.ResolvedComplexBalance`
- `CRNT.Translation.SourceCoefficientEquivalence`
- `CRNT.Translation.SourceComplexes`
- `CRNT.Translation.StructuralInvariants`

</details>

## Hole B — `stronglyConcordant_fullyOpen_of_trueSRCriterion`

*Shinar–Feinberg strong concordance*

- **`sorry` site**: `CRNT/Multistationarity/TrueChemistrySRCriterion.lean:8603` (declaration begins at line 8003)
- **module**: `CRNT.Multistationarity.TrueChemistrySRCriterion`
- **signature**: `theorem stronglyConcordant_fullyOpen_of_trueSRCriterion (N : Network S) (hsep : N.ReactantProductSeparated) (hflow : N.ZeroComplexReactionsAreFlows) (hSR : N.TrueSRStrongCriterion) : N.fullyOpen.StronglyConcordant`
- **`sorry` count in the module**: 1
- **direct importers** (exact): 4
- **transitive dependent modules** (exact): 4
- **transitive dependent declarations** (conservative): 3

### Direct importers

- `CRNT.Examples.TrueSRCounterexample` — `CRNT/Examples/TrueSRCounterexample.lean`, 26 declarations
- `CRNT.Examples.TrueSRNetCoeffCounterexample` — `CRNT/Examples/TrueSRNetCoeffCounterexample.lean`, 91 declarations
- `CRNT.Multistationarity.TrueChemistrySRGraphSpecialCases` — `CRNT/Multistationarity/TrueChemistrySRGraphSpecialCases.lean`, 1 declarations
- `CRNT.Multistationarity.TrueSRCausalCycleFacts` — `CRNT/Multistationarity/TrueSRCausalCycleFacts.lean`, 13 declarations

### Transitive dependents, module by module

Load-bearing modules — a change to any of these can move the hole:

- `CRNT.Examples.TrueSRCounterexample` (`CRNT/Examples/TrueSRCounterexample.lean`, 26 decls)
- `CRNT.Examples.TrueSRNetCoeffCounterexample` (`CRNT/Examples/TrueSRNetCoeffCounterexample.lean`, 91 decls)
- `CRNT.Multistationarity.TrueChemistrySRGraphSpecialCases` (`CRNT/Multistationarity/TrueChemistrySRGraphSpecialCases.lean`, 1 decls)
- `CRNT.Multistationarity.TrueSRCausalCycleFacts` (`CRNT/Multistationarity/TrueSRCausalCycleFacts.lean`, 13 decls)

### Declaration-level paths

Every declaration that transitively mentions the hole, in breadth-first order
(so the earliest entries are the immediate consumers):

- `CRNT.Multistationarity.TrueChemistrySRCriterion`:8616 — `CRNT.Network.stronglyConcordant_of_trueSRCriterion_of_weaklyNormal` (theorem)
- `CRNT.Multistationarity.TrueChemistrySRCriterion`:8624 — `CRNT.Network.stronglyConcordant_of_trueSRCriterion_of_weaklyReversible` (theorem)
- `CRNT.Multistationarity.TrueChemistrySRCriterion`:8632 — `CRNT.Network.injective_of_trueSRCriterion` (theorem)

### The hole's own prerequisites

`CRNT.Multistationarity.TrueChemistrySRCriterion` imports 172 modules transitively. Breaking that down by directory:

| area | modules |
|---|---|
| `CRNT.Multistationarity` | 51 |
| `CRNT.Dynamics` | 35 |
| `CRNT.Deficiency` | 20 |
| `CRNT.Stochastic` | 15 |
| `CRNT.Theorems` | 11 |
| `CRNT.Graph` | 7 |
| `CRNT.Oscillation` | 6 |
| `CRNT.LinearAlgebra` | 5 |
| `CRNT.Kinetics` | 4 |
| `CRNT.Equilibria` | 4 |
| `CRNT.Decision` | 3 |
| `CRNT.Basic` | 3 |
| `CRNT.Geometry` | 2 |
| `CRNT.Stoich` | 2 |
| `CRNT.Subnetwork` | 1 |
| `CRNT.Flux` | 1 |
| `CRNT.Open` | 1 |
| `CRNT.Combinatorics` | 1 |

<details><summary>full prerequisite list</summary>

- `CRNT.Basic.Complex`
- `CRNT.Basic.Network`
- `CRNT.Basic.Reaction`
- `CRNT.Combinatorics.DigraphExcess`
- `CRNT.Decision.Linkage`
- `CRNT.Decision.Reachability`
- `CRNT.Decision.StrongLinkage`
- `CRNT.Deficiency.ClosedSetKernel`
- `CRNT.Deficiency.Consistent`
- `CRNT.Deficiency.ConsistentWR`
- `CRNT.Deficiency.CycleExactSequence`
- `CRNT.Deficiency.DeficiencyOne`
- `CRNT.Deficiency.DeficiencyOneHypotheses`
- `CRNT.Deficiency.Definition`
- `CRNT.Deficiency.Drainage`
- `CRNT.Deficiency.ExactSequence`
- `CRNT.Deficiency.KernelDimension`
- `CRNT.Deficiency.KernelDimensionBound`
- `CRNT.Deficiency.KineticBlock`
- `CRNT.Deficiency.LinkageDeficiency`
- `CRNT.Deficiency.PerClassKernel`
- `CRNT.Deficiency.SignedDrainage`
- `CRNT.Deficiency.TerminalKernelBound`
- `CRNT.Deficiency.TerminalKernelDimension`
- `CRNT.Deficiency.TerminalReachable`
- `CRNT.Deficiency.TerminalSLC`
- `CRNT.Deficiency.TerminalSLCKernel`
- `CRNT.Dynamics.BoundaryOmegaSiphon`
- `CRNT.Dynamics.ConfinedInvariance`
- `CRNT.Dynamics.ConservationLaw`
- `CRNT.Dynamics.CriticalSiphonOmega`
- `CRNT.Dynamics.EndotacticPermanence`
- `CRNT.Dynamics.FlowConstruction`
- `CRNT.Dynamics.ForwardInvariance`
- `CRNT.Dynamics.GACConfinement`
- `CRNT.Dynamics.GACNoCriticalSiphon`
- `CRNT.Dynamics.GACOmegaPositive`
- `CRNT.Dynamics.GACSeparatingCapstone`
- `CRNT.Dynamics.GACSeparatingRegion`
- `CRNT.Dynamics.GACSeparatingWitness`
- `CRNT.Dynamics.GenuineConfinement`
- `CRNT.Dynamics.GlobalPermanence`
- `CRNT.Dynamics.GlobalPersistence`
- `CRNT.Dynamics.GlobalStability`
- `CRNT.Dynamics.LaSalle`
- `CRNT.Dynamics.MassActionAlgebra`
- `CRNT.Dynamics.MassActionField`
- `CRNT.Dynamics.Nagumo`
- `CRNT.Dynamics.NegativeInvariance`
- `CRNT.Dynamics.NoCriticalSiphonPersistence`
- `CRNT.Dynamics.Persistence`
- `CRNT.Dynamics.PersistenceConfined`
- `CRNT.Dynamics.PersistenceGAC`
- `CRNT.Dynamics.PersistenceTheorem`
- `CRNT.Dynamics.RouthHurwitz`
- `CRNT.Dynamics.SingleLinkageGAC`
- `CRNT.Dynamics.Siphon`
- `CRNT.Dynamics.SiphonAutocatalysis`
- `CRNT.Dynamics.SiphonConservation`
- `CRNT.Dynamics.SiphonFaceWeakReversibility`
- `CRNT.Dynamics.StrictInflow`
- `CRNT.Dynamics.SublevelInvariant`
- `CRNT.Equilibria.CompatibilityClass`
- `CRNT.Equilibria.ComplexBalanced`
- `CRNT.Equilibria.SteadyState`
- `CRNT.Equilibria.TreeConstants`
- `CRNT.Flux.Cone`
- `CRNT.Geometry.Endotactic`
- `CRNT.Geometry.PolyhedralFan`
- `CRNT.Graph.FiniteSource`
- `CRNT.Graph.LinkageClass`
- `CRNT.Graph.PositiveCirculation`
- `CRNT.Graph.Reachability`
- `CRNT.Graph.RelPath`
- `CRNT.Graph.Reversibility`
- `CRNT.Graph.WeakReversibility`
- `CRNT.Kinetics.Concentration`
- `CRNT.Kinetics.General`
- `CRNT.Kinetics.MassAction`
- `CRNT.Kinetics.MassActionJacobian`
- `CRNT.LinearAlgebra.FinrankSup`
- `CRNT.LinearAlgebra.OrthogonalComplement`
- `CRNT.LinearAlgebra.PerronFrobenius`
- `CRNT.LinearAlgebra.SignVector`
- `CRNT.LinearAlgebra.Substochastic`
- `CRNT.Multistationarity.Concordance`
- `CRNT.Multistationarity.ConcordanceConverse`
- `CRNT.Multistationarity.Discordance`
- `CRNT.Multistationarity.FullyOpenConcordanceSpectral`
- `CRNT.Multistationarity.GainPotential`
- `CRNT.Multistationarity.Injectivity`
- `CRNT.Multistationarity.Normality`
- `CRNT.Multistationarity.PMatrix`
- `CRNT.Multistationarity.SRGraph`
- `CRNT.Multistationarity.SourceWeightPairing`
- `CRNT.Multistationarity.StrongConcordance`
- `CRNT.Multistationarity.TrueChemistrySRGraph`
- `CRNT.Multistationarity.TrueSRArc`
- `CRNT.Multistationarity.TrueSRCPairThirdEdge`
- `CRNT.Multistationarity.TrueSRChordExtraction`
- `CRNT.Multistationarity.TrueSRChordParity`
- `CRNT.Multistationarity.TrueSRClosedWalk`
- `CRNT.Multistationarity.TrueSRCycleChord`
- `CRNT.Multistationarity.TrueSRCycleReverse`
- `CRNT.Multistationarity.TrueSRCycleSplit`
- `CRNT.Multistationarity.TrueSRDegreeTwoNoSToR`
- `CRNT.Multistationarity.TrueSREdgePath`
- `CRNT.Multistationarity.TrueSRGlueBlocks`
- `CRNT.Multistationarity.TrueSRGlueCPairs`
- `CRNT.Multistationarity.TrueSRGlueCount`
- `CRNT.Multistationarity.TrueSRGlueIndex`
- `CRNT.Multistationarity.TrueSRGlueInterface`
- `CRNT.Multistationarity.TrueSRGlueMaps`
- `CRNT.Multistationarity.TrueSRGlueSeams`
- `CRNT.Multistationarity.TrueSRMidSegment`
- `CRNT.Multistationarity.TrueSRMinimalChord`
- `CRNT.Multistationarity.TrueSRNoArcChord`
- `CRNT.Multistationarity.TrueSRParityCount`
- `CRNT.Multistationarity.TrueSRParityLemma`
- `CRNT.Multistationarity.TrueSRParityRR`
- `CRNT.Multistationarity.TrueSRPath`
- `CRNT.Multistationarity.TrueSRPathAccessors`
- `CRNT.Multistationarity.TrueSRPathCPairs`
- `CRNT.Multistationarity.TrueSRPathSegment`
- `CRNT.Multistationarity.TrueSRPathTerminalSegment`
- `CRNT.Multistationarity.TrueSRReactionInteriorPath`
- `CRNT.Multistationarity.TrueSRRotate`
- `CRNT.Multistationarity.TrueSRSSGlueCPairs`
- `CRNT.Multistationarity.TrueSRSeamParity`
- `CRNT.Multistationarity.TrueSRSegmentEndpoints`
- `CRNT.Multistationarity.TrueSRSingleSharedEdge`
- `CRNT.Multistationarity.TrueSRSpeciesPath`
- `CRNT.Multistationarity.TrueSRTwoGluedCycles`
- `CRNT.Multistationarity.TrueSRTwoWeightGain`
- `CRNT.Multistationarity.TrueSRWalkEdges`
- `CRNT.Multistationarity.WeakNormality`
- `CRNT.Open.Augmentation`
- `CRNT.Oscillation.Basic`
- `CRNT.Oscillation.KineticBasic`
- `CRNT.Oscillation.MatrixCriteria`
- `CRNT.Oscillation.ParameterRich`
- `CRNT.Oscillation.StructuralCore`
- `CRNT.Oscillation.VassenaCriteria`
- `CRNT.Stochastic.CTMC`
- `CRNT.Stochastic.ErgodicConvergence`
- `CRNT.Stochastic.ErgodicConvergenceGeneral`
- `CRNT.Stochastic.Ergodicity`
- `CRNT.Stochastic.Generator`
- `CRNT.Stochastic.JumpKernel`
- `CRNT.Stochastic.JumpReachabilityLift`
- `CRNT.Stochastic.Kernel`
- `CRNT.Stochastic.KernelInvariant`
- `CRNT.Stochastic.KernelIrreducible`
- `CRNT.Stochastic.KernelNormalized`
- `CRNT.Stochastic.KernelStationary`
- `CRNT.Stochastic.ProductForm`
- `CRNT.Stochastic.RegionPrimitive`
- `CRNT.Stochastic.RegionStronglyConnected`
- `CRNT.Stoich.Subspace`
- `CRNT.Stoich.Vector`
- `CRNT.Subnetwork.ReactionRestriction`
- `CRNT.Theorems.DeficiencyZero.AsymptoticStability`
- `CRNT.Theorems.DeficiencyZero.Birch`
- `CRNT.Theorems.DeficiencyZero.BirchExistence`
- `CRNT.Theorems.DeficiencyZero.Confinement`
- `CRNT.Theorems.DeficiencyZero.Dissipation`
- `CRNT.Theorems.DeficiencyZero.Existence`
- `CRNT.Theorems.DeficiencyZero.Lyapunov`
- `CRNT.Theorems.DeficiencyZero.PositiveKernel`
- `CRNT.Theorems.DeficiencyZero.Stability`
- `CRNT.Theorems.DeficiencyZero.Statement`
- `CRNT.Theorems.DeficiencyZero.Toric`

</details>

### Modules that are decorative with respect to this hole

These modules are hole-free and are *not* in the hole's transitive dependent
set, so nothing about them has to change to close the hole:

840 of 846 hole-free `CRNT/` modules are downstream-free.

<details><summary>list</summary>

- `CRNT.Algebra.DeficiencyIdeal`
- `CRNT.Algebra.PositiveTorusIdeals`
- `CRNT.Algebra.SiphonIdeal`
- `CRNT.Algebra.SteadyStateIdeal`
- `CRNT.Analysis.BorosEdgeSumEstimate`
- `CRNT.Analysis.BorosPathEstimate`
- `CRNT.Analysis.BorosProjectionDecomposition`
- `CRNT.Analysis.BorosZeroSumMax`
- `CRNT.Analysis.BrouwerConvex`
- `CRNT.Analysis.BrouwerZero`
- `CRNT.Analysis.ConcentrationZero`
- `CRNT.Analysis.ConvexProjection`
- `CRNT.Analysis.FiniteProjectionConstraints`
- `CRNT.Analysis.FixedPoint`
- `CRNT.Analysis.Sperner`
- `CRNT.Analysis.Sperner2D`
- `CRNT.Analysis.Sperner2DMulti`
- `CRNT.Analysis.SpernerBrouwer2D`
- `CRNT.Analysis.SpernerBrouwerN`
- `CRNT.Analysis.SpernerGrid`
- `CRNT.Analysis.SpernerGridGeometric`
- `CRNT.Analysis.SpernerGridMulti`
- `CRNT.Analysis.SpernerLattice`
- `CRNT.Analysis.SpernerLatticeBipartite`
- `CRNT.Analysis.SpernerLatticeBoundary`
- `CRNT.Analysis.SpernerLatticeCellColor`
- `CRNT.Analysis.SpernerLatticeCellDegree`
- `CRNT.Analysis.SpernerLatticeColoring`
- `CRNT.Analysis.SpernerLatticeDoorGraph`
- `CRNT.Analysis.SpernerLatticeFullGraph`
- `CRNT.Analysis.SpernerLatticeGeometric`
- `CRNT.Analysis.SpernerLatticeIncidence`
- `CRNT.Analysis.SpernerLatticeIncidenceHV`
- `CRNT.Analysis.SpernerLatticeN`
- `CRNT.Analysis.SpernerLatticeNeighbor`
- `CRNT.Analysis.SpernerLatticeSperner`
- `CRNT.Analysis.SpernerMultiIncidence`
- `CRNT.Analysis.SpernerNBaseShift`
- `CRNT.Analysis.SpernerNBoundary`
- `CRNT.Analysis.SpernerNBoundaryCell`
- `CRNT.Analysis.SpernerNBoundaryCorr`
- `CRNT.Analysis.SpernerNBoundaryCount`
- `CRNT.Analysis.SpernerNClose`
- `CRNT.Analysis.SpernerNDoor`
- `CRNT.Analysis.SpernerNFacetCount`
- `CRNT.Analysis.SpernerNFintype`
- `CRNT.Analysis.SpernerNGeometric`
- `CRNT.Analysis.SpernerNHandshake`
- `CRNT.Analysis.SpernerNIncidence`
- `CRNT.Analysis.SpernerNInterior`
- `CRNT.Analysis.SpernerNParity`
- `CRNT.Analysis.SpernerNSperner`
- `CRNT.Analysis.SpernerSimplexLimit`
- `CRNT.Analysis.SpernerSimplexLimitN`
- `CRNT.Analysis.SpernerTriangulation`
- `CRNT.Basic.Complex`
- `CRNT.Basic.Isomorphism`
- `CRNT.Basic.IsomorphismKinetics`
- `CRNT.Basic.IsomorphismStructural`
- `CRNT.Basic.Network`
- `CRNT.Basic.Reaction`
- `CRNT.Combinatorics.DecidableCycle`
- `CRNT.Combinatorics.DigraphExcess`
- `CRNT.Compose.Interconnect`
- `CRNT.Compose.InterconnectKinetics`
- `CRNT.Compose.InterconnectMonostationary`
- `CRNT.Compose.InterconnectSiphon`
- `CRNT.Compose.StoichIndependent`
- `CRNT.Decision.ACRCheck`
- `CRNT.Decision.ComputableDeficiency`
- `CRNT.Decision.ComputableTerminalSLC`
- `CRNT.Decision.ConservationConeStrict`
- `CRNT.Decision.CriticalSiphonDecide`
- `CRNT.Decision.DeficiencyOneConditionsDecide`
- `CRNT.Decision.DeficiencyZeroTactic`
- `CRNT.Decision.DirectedReachability`
- `CRNT.Decision.ExactDeficiency`
- `CRNT.Decision.GaussianRank`
- `CRNT.Decision.InjectivityMargin`
- `CRNT.Decision.IsCriticalSiphonDecidable`
- `CRNT.Decision.Linkage`
- `CRNT.Decision.LinkageDeficiencyExact`
- `CRNT.Decision.MinorSearch`
- `CRNT.Decision.PersistenceCertified`
- `CRNT.Decision.PersistenceSingleLinkage`
- `CRNT.Decision.PersistenceVerdict`
- `CRNT.Decision.Rank`
- `CRNT.Decision.RankExact`
- `CRNT.Decision.RationalFarkas`
- `CRNT.Decision.RationalFarkasDecide`
- `CRNT.Decision.RationalFarkasStrict`
- `CRNT.Decision.Reachability`
- `CRNT.Decision.StoichBasisQ`
- `CRNT.Decision.StrictConeRealization`
- `CRNT.Decision.StrongLinkage`
- `CRNT.Decision.Tactic`
- `CRNT.Decomposition.BlockDeficiency`
- `CRNT.Decomposition.Deficiency`
- `CRNT.Decomposition.Rank`
- `CRNT.Decomposition.ReactionPartition`
- `CRNT.Deficiency.AdvancedDeficiencyAlgorithm`
- `CRNT.Deficiency.BirchClassScaleTransport`
- `CRNT.Deficiency.BorosActiveInwardEstimate`
- `CRNT.Deficiency.BorosBirchGraph`
- `CRNT.Deficiency.BorosDeficiencyOneReduction`
- `CRNT.Deficiency.BorosLinkageProjection`
- `CRNT.Deficiency.BorosSingleLinkageEstimate`
- `CRNT.Deficiency.ClassConservation`
- `CRNT.Deficiency.ClassScaleSynchronization`
- `CRNT.Deficiency.ClosedSetKernel`
- `CRNT.Deficiency.Colinearity`
- `CRNT.Deficiency.ColinearityClasses`
- `CRNT.Deficiency.ComplexBalancedRatio`
- `CRNT.Deficiency.Confluence`
- `CRNT.Deficiency.Consistent`
- `CRNT.Deficiency.ConsistentWR`
- `CRNT.Deficiency.CutPair`
- `CRNT.Deficiency.CycleExactSequence`
- `CRNT.Deficiency.CycleSplitting`
- `CRNT.Deficiency.DOACapacityConstruction`
- `CRNT.Deficiency.DOAForward`
- `CRNT.Deficiency.DeficiencyOne`
- `CRNT.Deficiency.DeficiencyOneAlgorithm`
- `CRNT.Deficiency.DeficiencyOneDecide`
- `CRNT.Deficiency.DeficiencyOneDecomp`
- `CRNT.Deficiency.DeficiencyOneHypotheses`
- `CRNT.Deficiency.DeficiencyOneLine`
- `CRNT.Deficiency.DeficiencyOneLinkageScalars`
- `CRNT.Deficiency.DeficiencyOneLocalize`
- `CRNT.Deficiency.DeficiencyOneMonotonicity`
- `CRNT.Deficiency.DeficiencyOneRowDefect`
- `CRNT.Deficiency.DeficiencyOneScalarReduction`
- `CRNT.Deficiency.DeficiencyOneStructure`
- `CRNT.Deficiency.DeficiencyZeroConsistency`
- `CRNT.Deficiency.DeficientClassKernel`
- `CRNT.Deficiency.Definition`
- `CRNT.Deficiency.Drainage`
- `CRNT.Deficiency.ExactSequence`
- `CRNT.Deficiency.ExcessPositivity`
- `CRNT.Deficiency.HigherDeficiency`
- `CRNT.Deficiency.IncidenceBlock`
- `CRNT.Deficiency.KernelDimension`
- `CRNT.Deficiency.KernelDimensionBound`
- `CRNT.Deficiency.KernelDimensionWR`
- `CRNT.Deficiency.KineticBlock`
- `CRNT.Deficiency.KineticExcess`
- `CRNT.Deficiency.LevelSetSign`
- `CRNT.Deficiency.LinkageCoupling`
- `CRNT.Deficiency.LinkageCouplingLine`
- `CRNT.Deficiency.LinkageDeficiency`
- `CRNT.Deficiency.LogMonomialRatio`
- `CRNT.Deficiency.LogObstructionClassScaling`
- `CRNT.Deficiency.PerClassKernel`
- `CRNT.Deficiency.PerClassKernelPos`
- `CRNT.Deficiency.PerClassKernelUnique`
- `CRNT.Deficiency.PositiveKineticDomain`
- `CRNT.Deficiency.PositiveKineticFamily`
- `CRNT.Deficiency.PositiveKineticObstructionIVT`
- `CRNT.Deficiency.PositiveKineticPreimageWR`
- `CRNT.Deficiency.PositiveKineticSection`
- `CRNT.Deficiency.RangeKineticWR`
- `CRNT.Deficiency.Regular`
- `CRNT.Deficiency.Shelf`
- `CRNT.Deficiency.Signature`
- `CRNT.Deficiency.SignedDrainage`
- `CRNT.Deficiency.SteadyStateKernel`
- `CRNT.Deficiency.StrictKineticDissipation`
- `CRNT.Deficiency.StructuredPreimage`
- `CRNT.Deficiency.TerminalKernelBound`
- `CRNT.Deficiency.TerminalKernelCone`
- `CRNT.Deficiency.TerminalKernelDimension`
- `CRNT.Deficiency.TerminalKernelFaces`
- `CRNT.Deficiency.TerminalReachable`
- `CRNT.Deficiency.TerminalSLC`
- `CRNT.Deficiency.TerminalSLCKernel`
- `CRNT.Deficiency.WeaklyReversibleSteadyState`
- `CRNT.Design.ACR`
- `CRNT.Design.ACRCrossClass`
- `CRNT.Design.ACRStandard`
- `CRNT.Design.ACRUnconditional`
- `CRNT.Design.Adaptation`
- `CRNT.Design.BufferingStructure`
- `CRNT.Design.EmergentConservation`
- `CRNT.Design.EmergentCycles`
- `CRNT.Design.GeneratedClosure`
- `CRNT.Design.LabeledBufferingRPA`
- `CRNT.Design.LabeledBufferingStructure`
- `CRNT.Design.Localization`
- `CRNT.Design.LocalizationDifferential`
- `CRNT.Design.MaxRPA`
- `CRNT.Design.MaxRPAIntegrator`
- `CRNT.Design.MaxRPAStochastic`
- `CRNT.Design.MinimalForm`
- `CRNT.Design.OutputCompleteClosure`
- `CRNT.Design.ShinarFeinbergCrossClass`
- `CRNT.Design.ShinarFeinbergTheorem`
- `CRNT.Design.ShinarFeinbergTreeFormula`
- `CRNT.Design.StrongBufferingFluxRPA`
- `CRNT.Dynamics.BoundaryDescent`
- `CRNT.Dynamics.BoundaryOmegaSiphon`
- `CRNT.Dynamics.ButlerMcGehee`
- `CRNT.Dynamics.CenterManifold`
- `CRNT.Dynamics.CenterManifoldReduction`
- `CRNT.Dynamics.CertifiedReduction`
- `CRNT.Dynamics.ClosedSetNagumo`
- `CRNT.Dynamics.ComplexBalanceCycleDecomposition`
- `CRNT.Dynamics.ComplexBalanceStoichFan`
- `CRNT.Dynamics.ComplexBalanceStoichFanInclusion`
- `CRNT.Dynamics.ConfinedInvariance`
- `CRNT.Dynamics.ConservationLaw`
- `CRNT.Dynamics.CriticalSiphonDissipationRepulsion`
- `CRNT.Dynamics.CriticalSiphonNearFacetInflux`
- `CRNT.Dynamics.CriticalSiphonOmega`
- `CRNT.Dynamics.DifferentialInclusion`
- `CRNT.Dynamics.DissipationBound`
- `CRNT.Dynamics.DissipativeTracking`
- `CRNT.Dynamics.EndotacticPermanence`
- `CRNT.Dynamics.EscapeSiphonFace`
- `CRNT.Dynamics.ExponentialDecay`
- `CRNT.Dynamics.ExponentialDichotomy`
- `CRNT.Dynamics.FaceCodimension`
- `CRNT.Dynamics.FaceDirectionCone`
- `CRNT.Dynamics.FacetRepulsion`
- `CRNT.Dynamics.FacetRepulsionAndersonShiu`
- `CRNT.Dynamics.Fenichel`
- `CRNT.Dynamics.FenichelC1Manifold`
- `CRNT.Dynamics.FenichelComovingManifold`
- `CRNT.Dynamics.FenichelContinuousMovingTarget`
- `CRNT.Dynamics.FenichelCoupledBase`
- `CRNT.Dynamics.FenichelGeneralDrift`
- `CRNT.Dynamics.FenichelLogisticInstance`
- `CRNT.Dynamics.FenichelManifold`
- `CRNT.Dynamics.FenichelMovingGeneralDrift`
- `CRNT.Dynamics.FenichelPersistence`
- `CRNT.Dynamics.FenichelPersistenceConcrete`
- `CRNT.Dynamics.FenichelPersistenceContracting`
- `CRNT.Dynamics.FenichelReductionPrinciple`
- `CRNT.Dynamics.FenichelSlowDrift`
- `CRNT.Dynamics.FenichelStabilityTransfer`
- `CRNT.Dynamics.FiniteNegativeBudget`
- `CRNT.Dynamics.FirstExit`
- `CRNT.Dynamics.FlowConstruction`
- `CRNT.Dynamics.FlowDifferentiable`
- `CRNT.Dynamics.FlowSmoothDependence`
- `CRNT.Dynamics.ForwardInvariance`
- `CRNT.Dynamics.GACCertificate`
- `CRNT.Dynamics.GACConfinement`
- `CRNT.Dynamics.GACNoCriticalSiphon`
- `CRNT.Dynamics.GACOmegaPositive`
- `CRNT.Dynamics.GACSeparatingCapstone`
- `CRNT.Dynamics.GACSeparatingRegion`
- `CRNT.Dynamics.GACSeparatingRegionNagumo`
- `CRNT.Dynamics.GACSeparatingWitness`
- `CRNT.Dynamics.GenuineConfinement`
- `CRNT.Dynamics.GershgorinColumnMarginQ`
- `CRNT.Dynamics.GershgorinMarginQ`
- `CRNT.Dynamics.GlobalAttractorSpecialCases`
- `CRNT.Dynamics.GlobalAttractorTheorem`
- `CRNT.Dynamics.GlobalPermanence`
- `CRNT.Dynamics.GlobalPersistence`
- `CRNT.Dynamics.GlobalPersistenceCertificates`
- `CRNT.Dynamics.GlobalPersistenceFrontier`
- `CRNT.Dynamics.GlobalStability`
- `CRNT.Dynamics.GraphTransform`
- `CRNT.Dynamics.HopfAdmissible`
- `CRNT.Dynamics.HopfBoundaryQ`
- `CRNT.Dynamics.HopfGate`
- `CRNT.Dynamics.HopfGate3Matrix`
- `CRNT.Dynamics.HopfGate4`
- `CRNT.Dynamics.HopfLimitCycle`
- `CRNT.Dynamics.HopfNormalForm`
- `CRNT.Dynamics.HopfPersistentOrbit`
- `CRNT.Dynamics.HopfRealizes`
- `CRNT.Dynamics.HopfTransversality3`
- `CRNT.Dynamics.Hurwitz`
- `CRNT.Dynamics.Hurwitz2Matrix`
- `CRNT.Dynamics.Hurwitz3Matrix`
- `CRNT.Dynamics.HurwitzGershgorin`
- `CRNT.Dynamics.HurwitzGershgorinColumn`
- `CRNT.Dynamics.IsolatedInvariant`
- `CRNT.Dynamics.KnownGlobalPersistenceClasses`
- `CRNT.Dynamics.LaSalle`
- `CRNT.Dynamics.MassActionAlgebra`
- `CRNT.Dynamics.MassActionField`
- `CRNT.Dynamics.MichaelisMenten`
- `CRNT.Dynamics.MichaelisMentenC1`
- `CRNT.Dynamics.MichaelisMentenCertified`
- `CRNT.Dynamics.MichaelisMentenCertifiedUniform`
- `CRNT.Dynamics.MichaelisMentenCoupledContraction`
- `CRNT.Dynamics.MichaelisMentenDepletion`
- `CRNT.Dynamics.MichaelisMentenFenichel`
- `CRNT.Dynamics.MichaelisMentenFenichelAllTime`
- `CRNT.Dynamics.MichaelisMentenLipschitz`
- `CRNT.Dynamics.MichaelisMentenManifold`
- `CRNT.Dynamics.MichaelisMentenReduced`
- `CRNT.Dynamics.MichaelisMentenRegularized`
- `CRNT.Dynamics.MichaelisMentenSlowDrift`
- `CRNT.Dynamics.MichaelisMentenSlowDriftSpeed`
- `CRNT.Dynamics.MinimalInvariant`
- `CRNT.Dynamics.Monotone`
- `CRNT.Dynamics.Nagumo`
- `CRNT.Dynamics.NegativeInvariance`
- `CRNT.Dynamics.NoCriticalSiphonPersistence`
- `CRNT.Dynamics.NoDrainableSiphonPersistence`
- `CRNT.Dynamics.OrbitRegularity`
- `CRNT.Dynamics.PermanenceAssembly`
- `CRNT.Dynamics.Persistence`
- `CRNT.Dynamics.PersistenceConfined`
- `CRNT.Dynamics.PersistenceGAC`
- `CRNT.Dynamics.PersistenceTheorem`
- `CRNT.Dynamics.PoincareReturnMap`
- `CRNT.Dynamics.PolyRegionInvariant`
- `CRNT.Dynamics.PolyRegionStrictInvariant`
- `CRNT.Dynamics.ProperTierTransversal`
- `CRNT.Dynamics.QSSA`
- `CRNT.Dynamics.ReactionConeDisplacement`
- `CRNT.Dynamics.ReactionConeWeakReversibility`
- `CRNT.Dynamics.ReturnMapPeriodicOrbit`
- `CRNT.Dynamics.RouthHurwitz`
- `CRNT.Dynamics.RouthHurwitz4`
- `CRNT.Dynamics.RouthHurwitz4Suff`
- `CRNT.Dynamics.SingleLinkageGAC`
- `CRNT.Dynamics.SingleLinkageStructure`
- `CRNT.Dynamics.SingletonFacetEscape`
- `CRNT.Dynamics.Siphon`
- `CRNT.Dynamics.SiphonAutocatalysis`
- `CRNT.Dynamics.SiphonConservation`
- `CRNT.Dynamics.SiphonDimensionDescent`
- `CRNT.Dynamics.SiphonFaceWeakReversibility`
- `CRNT.Dynamics.SiphonFacetEscape`
- `CRNT.Dynamics.SpectralSplitting`
- `CRNT.Dynamics.SpectralSplittingReal`
- `CRNT.Dynamics.StrictInflow`
- `CRNT.Dynamics.SublevelInvariant`
- `CRNT.Dynamics.SublevelNagumo`
- `CRNT.Dynamics.SupportDiniBridge`
- `CRNT.Dynamics.ThmBGenuine`
- `CRNT.Dynamics.TierCompactNegativity`
- `CRNT.Dynamics.TierDirectionFeasibility`
- `CRNT.Dynamics.TierDirectionProjection`
- `CRNT.Dynamics.TierDissipationAsymptotics`
- `CRNT.Dynamics.TierExtraction`
- `CRNT.Dynamics.TierExtractionCompleted`
- `CRNT.Dynamics.TierLyapunov`
- `CRNT.Dynamics.TierOrderAlgebra`
- `CRNT.Dynamics.TierOriginGeometry`
- `CRNT.Dynamics.TierPersistence`
- `CRNT.Dynamics.TierScaleDecomposition`
- `CRNT.Dynamics.TierScaleExtractionLemma44`
- `CRNT.Dynamics.TierScaleMagnitude`
- `CRNT.Dynamics.TierScaleTruncation`
- `CRNT.Dynamics.TierSequentialReduction`
- `CRNT.Dynamics.TierStrictUpwardPartner`
- `CRNT.Dynamics.TierSubsequenceExtraction`
- `CRNT.Dynamics.Tikhonov`
- `CRNT.Dynamics.ToricBarrierExplicit`
- `CRNT.Dynamics.ToricBarrierTrapping`
- `CRNT.Dynamics.ToricCycleOrderLimits`
- `CRNT.Dynamics.ToricCycleSortedBase`
- `CRNT.Dynamics.ToricEmbedding`
- `CRNT.Dynamics.ToricEmbeddingOrder`
- `CRNT.Dynamics.ToricEmbeddingWR`
- `CRNT.Dynamics.ToricInclusion`
- `CRNT.Dynamics.TransversalCrossingTime`
- `CRNT.Dynamics.Trap`
- `CRNT.Dynamics.VariableTierLyapunov`
- `CRNT.Dynamics.VariationalEquation`
- `CRNT.Dynamics.Viability`
- `CRNT.Dynamics.ZeroSeparating`
- `CRNT.Equilibria.BoundarySiphon`
- `CRNT.Equilibria.BrouwerNormalCone`
- `CRNT.Equilibria.BrouwerSteadyState`
- `CRNT.Equilibria.CompatibilityClass`
- `CRNT.Equilibria.ComplexBalanceGeometry`
- `CRNT.Equilibria.ComplexBalanceLinearStability`
- `CRNT.Equilibria.ComplexBalanceObstruction`
- `CRNT.Equilibria.ComplexBalanceStructure`
- `CRNT.Equilibria.ComplexBalanced`
- `CRNT.Equilibria.ConservationCoordinates`
- `CRNT.Equilibria.DetailedBalanceEntropy`
- `CRNT.Equilibria.DetailedBalanceLinearStability`
- `CRNT.Equilibria.DetailedBalanceToric`
- `CRNT.Equilibria.DetailedBalanced`
- `CRNT.Equilibria.DirectedMatrixTreeProof`
- `CRNT.Equilibria.GeneralizedComplexBalanceGeometry`
- `CRNT.Equilibria.GeneralizedComplexBalanceToric`
- `CRNT.Equilibria.GeneralizedTreeConstantCriterion`
- `CRNT.Equilibria.LinkageComplexBalance`
- `CRNT.Equilibria.MatrixTreeCofactor`
- `CRNT.Equilibria.MatrixTreeCofactorDefs`
- `CRNT.Equilibria.SteadyState`
- `CRNT.Equilibria.SteadyStateFlux`
- `CRNT.Equilibria.TreeConstantBinomials`
- `CRNT.Equilibria.TreeConstantCriterion`
- `CRNT.Equilibria.TreeConstantKernelBasis`
- `CRNT.Equilibria.TreeConstants`
- `CRNT.Equilibria.TreePotentialIntegration`
- `CRNT.Equilibria.Wegscheider`
- `CRNT.Equilibria.WegscheiderConverse`
- `CRNT.Equilibria.WegscheiderDeficiency`
- `CRNT.Equilibria.WegscheiderDeficiencyOne`
- `CRNT.Equilibria.WegscheiderGenerators`
- `CRNT.Equilibria.WegscheiderInteger`
- `CRNT.Examples.CatalyticChain`
- `CRNT.Examples.CodimTwoFaceModel`
- `CRNT.Examples.ComplexBalancedBoundaryEquilibrium`
- `CRNT.Examples.CrntCheck`
- `CRNT.Examples.CycleRateNonMonotone`
- `CRNT.Examples.DecideDirectedReachability`
- `CRNT.Examples.DecideLinkage`
- `CRNT.Examples.DecideRank`
- `CRNT.Examples.DecideReachability`
- `CRNT.Examples.DecideStrongLinkage`
- `CRNT.Examples.DeficiencyBookkeeping`
- `CRNT.Examples.DeficiencyOneStatementExample`
- `CRNT.Examples.Enzyme`
- `CRNT.Examples.GACBlueprintPremiseCounterexamples`
- `CRNT.Examples.GACReversiblePair`
- `CRNT.Examples.GeneExpression`
- `CRNT.Examples.GeneralKinetics`
- `CRNT.Examples.HopfNetwork3`
- `CRNT.Examples.HopfNetwork3Branches`
- `CRNT.Examples.HopfOscillator3`
- `CRNT.Examples.IrreversibleChain`
- `CRNT.Examples.LinkageDeficiencyExample`
- `CRNT.Examples.Lotka`
- `CRNT.Examples.Minimal`
- `CRNT.Examples.OmegaPointFakeFlow`
- `CRNT.Examples.OpenSystem`
- `CRNT.Examples.ReversiblePair`
- `CRNT.Examples.StochasticConvergenceExample`
- `CRNT.Flux.CircuitTheory`
- `CRNT.Flux.Cone`
- `CRNT.Flux.ConformalDecomposition`
- `CRNT.Flux.Elementary`
- `CRNT.Flux.ExtremeRay`
- `CRNT.Flux.IntegerTInvariant`
- `CRNT.Flux.PSemiflow`
- `CRNT.Geometry.CompatibilityFaces`
- `CRNT.Geometry.ConeFace`
- `CRNT.Geometry.ConservativeCompatibility`
- `CRNT.Geometry.ConvexBarrierObstruction`
- `CRNT.Geometry.CraciunV3BlueprintScales`
- `CRNT.Geometry.CraciunZSH`
- `CRNT.Geometry.Endotactic`
- `CRNT.Geometry.EndotacticGlobal`
- `CRNT.Geometry.FaithfulCurve`
- `CRNT.Geometry.FaithfulCurve2D`
- `CRNT.Geometry.FaithfulCurve2DFan`
- `CRNT.Geometry.FaithfulCurveExistence`
- `CRNT.Geometry.FaithfulCurveGeneral`
- `CRNT.Geometry.FanActiveWalls`
- `CRNT.Geometry.FanFaceLattice`
- `CRNT.Geometry.FanFaceProperness`
- `CRNT.Geometry.FanRefinement`
- `CRNT.Geometry.FanSeparationWitness`
- `CRNT.Geometry.FanWallActivityDecide`
- `CRNT.Geometry.FanWallsCrossed`
- `CRNT.Geometry.FiniteConeClosed`
- `CRNT.Geometry.HalfPlaneSeparatingSurface`
- `CRNT.Geometry.LogProjectiveFaceCompatibility`
- `CRNT.Geometry.LogProjectiveSection`
- `CRNT.Geometry.LogProjectiveSmoothSection`
- `CRNT.Geometry.PolyRegionSeparating`
- `CRNT.Geometry.PolyhedralBarrier`
- `CRNT.Geometry.PolyhedralFan`
- `CRNT.Geometry.ProjectedFaceDimensionCode`
- `CRNT.Geometry.ReactionFanGeneration`
- `CRNT.Geometry.ReactionHullCone`
- `CRNT.Geometry.SimplicialConeClosed`
- `CRNT.Geometry.SmoothBarrierGluing`
- `CRNT.Geometry.SourceOrderReactionFan`
- `CRNT.Geometry.SpeciesProjection`
- `CRNT.Geometry.ToricFan`
- `CRNT.Geometry.ToricFieldPolar`
- `CRNT.Geometry.ToricFieldPolarMulti`
- `CRNT.Geometry.ToricStrictSupport`
- `CRNT.Geometry.ToricUniformWallMargin`
- `CRNT.Geometry.ToricWRStrictInward`
- `CRNT.Geometry.WeakReversibleWallObstruction`
- `CRNT.Geometry.ZeroSeparatingCurve2D`
- `CRNT.Geometry.ZeroSeparatingInduction`
- `CRNT.Geometry.ZeroSeparatingSurface`
- `CRNT.Graph.CirculationDecomposition`
- `CRNT.Graph.Condensation`
- `CRNT.Graph.Crossing`
- `CRNT.Graph.CycleCover`
- `CRNT.Graph.FiniteSource`
- `CRNT.Graph.LinkageClass`
- `CRNT.Graph.PositiveCirculation`
- `CRNT.Graph.Reachability`
- `CRNT.Graph.RelPath`
- `CRNT.Graph.Reversibility`
- `CRNT.Graph.SourceBlocks`
- `CRNT.Graph.WeakReversibility`
- `CRNT.Interop.Analysis`
- `CRNT.Interop.Certificates`
- `CRNT.Interop.CodegenExamples`
- `CRNT.Interop.NetworkData`
- `CRNT.Kinetics.CatalystFace`
- `CRNT.Kinetics.Concentration`
- `CRNT.Kinetics.General`
- `CRNT.Kinetics.Generalized`
- `CRNT.Kinetics.GeneralizedBirchExistence`
- `CRNT.Kinetics.GeneralizedBirchLocal`
- `CRNT.Kinetics.GeneralizedBirchSelector`
- `CRNT.Kinetics.GeneralizedComplexBalanceObstruction`
- `CRNT.Kinetics.GeneralizedConditions`
- `CRNT.Kinetics.GeneralizedCycleExactSequence`
- `CRNT.Kinetics.GeneralizedDeficiencyComparison`
- `CRNT.Kinetics.GeneralizedDeficiencyZero`
- `CRNT.Kinetics.GeneralizedDeficiencyZeroCRNT`
- `CRNT.Kinetics.GeneralizedDeficiencyZeroExistence`
- `CRNT.Kinetics.GeneralizedDeficiencyZeroProof`
- `CRNT.Kinetics.GeneralizedNetwork`
- `CRNT.Kinetics.GeneralizedNondegeneracy`
- `CRNT.Kinetics.MassAction`
- `CRNT.Kinetics.MassActionJacobian`
- `CRNT.Kinetics.SpeciesProjectionMassAction`
- `CRNT.Kinetics.VariableMassAction`
- `CRNT.LinearAlgebra.CauchyBinet`
- `CRNT.LinearAlgebra.ConformalDecomposition`
- `CRNT.LinearAlgebra.DetCycleCover`
- `CRNT.LinearAlgebra.FinrankSup`
- `CRNT.LinearAlgebra.LogSumInj`
- `CRNT.LinearAlgebra.OrientedMatroid`
- `CRNT.LinearAlgebra.OrientedMatroidConditions`
- `CRNT.LinearAlgebra.OrientedMatroidNondegeneracy`
- `CRNT.LinearAlgebra.OrthogonalComplement`
- `CRNT.LinearAlgebra.PerronFrobenius`
- `CRNT.LinearAlgebra.PowerProductMono`
- `CRNT.LinearAlgebra.PowerProductMonoFinset`
- `CRNT.LinearAlgebra.RationalDenominator`
- `CRNT.LinearAlgebra.SignVector`
- `CRNT.LinearAlgebra.Substochastic`
- `CRNT.Multistationarity.Capacity`
- `CRNT.Multistationarity.Concordance`
- `CRNT.Multistationarity.ConcordanceConverse`
- `CRNT.Multistationarity.DeficiencyObstruction`
- `CRNT.Multistationarity.DegreeAdditivity`
- `CRNT.Multistationarity.DegreeHomotopyInvariant`
- `CRNT.Multistationarity.DegreeLocallyConstant`
- `CRNT.Multistationarity.DegreeProperConstant`
- `CRNT.Multistationarity.DegreeStability`
- `CRNT.Multistationarity.Discordance`
- `CRNT.Multistationarity.FullyOpenConcordanceSpectral`
- `CRNT.Multistationarity.GainPotential`
- `CRNT.Multistationarity.GaleNikaido`
- `CRNT.Multistationarity.GaleNikaidoBox`
- `CRNT.Multistationarity.GaleNikaidoUniv`
- `CRNT.Multistationarity.InfluenceConcordance`
- `CRNT.Multistationarity.Injectivity`
- `CRNT.Multistationarity.JacobianCycleSelection`
- `CRNT.Multistationarity.JacobianCycleSign`
- `CRNT.Multistationarity.JacobianDeterminantSign`
- `CRNT.Multistationarity.JacobianInjectivity`
- `CRNT.Multistationarity.LinearDegree`
- `CRNT.Multistationarity.LocalDegreeOn`
- `CRNT.Multistationarity.Normality`
- `CRNT.Multistationarity.NormalityTerminal`
- `CRNT.Multistationarity.PMatrix`
- `CRNT.Multistationarity.PMatrixSchur`
- `CRNT.Multistationarity.PMatrixSignature`
- `CRNT.Multistationarity.PMatrixUnivalence`
- `CRNT.Multistationarity.ParametrizedLocalDegree`
- `CRNT.Multistationarity.PivotChartInjectivity`
- `CRNT.Multistationarity.PivotReducedInjectivity`
- `CRNT.Multistationarity.PointIndepDecidable`
- `CRNT.Multistationarity.ReducedCoverSign`
- `CRNT.Multistationarity.ReducedJacobian`
- `CRNT.Multistationarity.ReducedJacobianSign`
- `CRNT.Multistationarity.ReducedPMatrixDecide`
- `CRNT.Multistationarity.ReducedSRGraph`
- `CRNT.Multistationarity.ReducedSRGraphBridge`
- `CRNT.Multistationarity.RegularValueDegree`
- `CRNT.Multistationarity.SRCoverPointIndependence`
- `CRNT.Multistationarity.SRCycleInjectivity`
- `CRNT.Multistationarity.SRGraph`
- `CRNT.Multistationarity.SRGraphCriterion`
- `CRNT.Multistationarity.SRGraphCycleDict`
- `CRNT.Multistationarity.SRInjectivityClass`
- `CRNT.Multistationarity.SRSignDecidable`
- `CRNT.Multistationarity.Sard`
- `CRNT.Multistationarity.SignConstruction`
- `CRNT.Multistationarity.SignedSRGraph`
- `CRNT.Multistationarity.SourceWeightPairing`
- `CRNT.Multistationarity.SteadyStateDegree`
- `CRNT.Multistationarity.StoichChart`
- `CRNT.Multistationarity.StrongConcordance`
- `CRNT.Multistationarity.StrongConcordanceStability`
- `CRNT.Multistationarity.Toric`
- `CRNT.Multistationarity.TrueChemistrySRGraph`
- `CRNT.Multistationarity.TrueSRArc`
- `CRNT.Multistationarity.TrueSRCPairThirdEdge`
- `CRNT.Multistationarity.TrueSRChordExtraction`
- `CRNT.Multistationarity.TrueSRChordParity`
- `CRNT.Multistationarity.TrueSRClosedWalk`
- `CRNT.Multistationarity.TrueSRCycleChord`
- `CRNT.Multistationarity.TrueSRCycleReverse`
- `CRNT.Multistationarity.TrueSRCycleSplit`
- `CRNT.Multistationarity.TrueSRDegreeTwoNoSToR`
- `CRNT.Multistationarity.TrueSREdgePath`
- `CRNT.Multistationarity.TrueSRGlueBlocks`
- `CRNT.Multistationarity.TrueSRGlueCPairs`
- `CRNT.Multistationarity.TrueSRGlueCount`
- `CRNT.Multistationarity.TrueSRGlueIndex`
- `CRNT.Multistationarity.TrueSRGlueInterface`
- `CRNT.Multistationarity.TrueSRGlueMaps`
- `CRNT.Multistationarity.TrueSRGlueSeams`
- `CRNT.Multistationarity.TrueSRLinearWalk`
- `CRNT.Multistationarity.TrueSRMidSegment`
- `CRNT.Multistationarity.TrueSRMinimalChord`
- `CRNT.Multistationarity.TrueSRNoArcChord`
- `CRNT.Multistationarity.TrueSRParityCount`
- `CRNT.Multistationarity.TrueSRParityLemma`
- `CRNT.Multistationarity.TrueSRParityRR`
- `CRNT.Multistationarity.TrueSRPath`
- `CRNT.Multistationarity.TrueSRPathAccessors`
- `CRNT.Multistationarity.TrueSRPathCPairs`
- `CRNT.Multistationarity.TrueSRPathSegment`
- `CRNT.Multistationarity.TrueSRPathTerminalSegment`
- `CRNT.Multistationarity.TrueSRReactionInteriorPath`
- `CRNT.Multistationarity.TrueSRRotate`
- `CRNT.Multistationarity.TrueSRSSGlueCPairs`
- `CRNT.Multistationarity.TrueSRSeamParity`
- `CRNT.Multistationarity.TrueSRSegmentEndpoints`
- `CRNT.Multistationarity.TrueSRSingleSharedEdge`
- `CRNT.Multistationarity.TrueSRSpeciesPath`
- `CRNT.Multistationarity.TrueSRTwoGluedCycles`
- `CRNT.Multistationarity.TrueSRTwoWeightGain`
- `CRNT.Multistationarity.TrueSRWalkEdges`
- `CRNT.Multistationarity.WeakNormality`
- `CRNT.Multistationarity.WeakNormalityCriterion`
- `CRNT.Open.Augmentation`
- `CRNT.Open.Boundary`
- `CRNT.Open.Deficiency`
- `CRNT.Open.PartialOpen`
- `CRNT.Oscillation`
- `CRNT.Oscillation.Analyze`
- `CRNT.Oscillation.BanajiDependentReaction`
- `CRNT.Oscillation.BanajiEndToEnd`
- `CRNT.Oscillation.Basic`
- `CRNT.Oscillation.Certificate`
- `CRNT.Oscillation.ChildSelectionReactivity`
- `CRNT.Oscillation.ChildSelectionSearch`
- `CRNT.Oscillation.CompatibilityAdapters`
- `CRNT.Oscillation.ConcentrationEuclidean`
- `CRNT.Oscillation.ContinuousTimeAttraction`
- `CRNT.Oscillation.CoordinateDynamics`
- `CRNT.Oscillation.DHopf`
- `CRNT.Oscillation.DHopfOpenness`
- `CRNT.Oscillation.DependentReaction`
- `CRNT.Oscillation.DependentReactionPersistence`
- `CRNT.Oscillation.DiagonalScaling`
- `CRNT.Oscillation.DulacAreaSign`
- `CRNT.Oscillation.DulacLineIntegral`
- `CRNT.Oscillation.Exclusion`
- `CRNT.Oscillation.FiedlerGlobalHopf`
- `CRNT.Oscillation.FisherFullerScaling`
- `CRNT.Oscillation.Floquet`
- `CRNT.Oscillation.FloquetOrbitalStability`
- `CRNT.Oscillation.FloquetPersistenceBridge`
- `CRNT.Oscillation.FloquetPersistenceGeneral`
- `CRNT.Oscillation.FloquetReturnBridge`
- `CRNT.Oscillation.GlobalAttraction`
- `CRNT.Oscillation.GlobalHopfContinuation`
- `CRNT.Oscillation.GlobalHopfIndex`
- `CRNT.Oscillation.GlobalHopfIndexTheorem`
- `CRNT.Oscillation.GlobalHopfSpectralCrossing`
- `CRNT.Oscillation.GreenJordanFoundations`
- `CRNT.Oscillation.GreenJordanReduction`
- `CRNT.Oscillation.HalfPlanePolynomial`
- `CRNT.Oscillation.HurwitzBordering`
- `CRNT.Oscillation.Inheritance`
- `CRNT.Oscillation.KineticBasic`
- `CRNT.Oscillation.LowRank`
- `CRNT.Oscillation.MatrixCriteria`
- `CRNT.Oscillation.OrbitTube`
- `CRNT.Oscillation.OscillationKernelBundle`
- `CRNT.Oscillation.OscillatoryCoreEndToEnd`
- `CRNT.Oscillation.ParameterRich`
- `CRNT.Oscillation.ParameterRichDHopfContinuation`
- `CRNT.Oscillation.ParameterRichGlobalHopf`
- `CRNT.Oscillation.PlanarAdjacentReturnLoop`
- `CRNT.Oscillation.PlanarCanonicalReturn`
- `CRNT.Oscillation.PlanarDivergenceRegularity`
- `CRNT.Oscillation.PlanarDulac`
- `CRNT.Oscillation.PlanarEndToEnd`
- `CRNT.Oscillation.PlanarFloquetAttraction`
- `CRNT.Oscillation.PlanarFlowBox`
- `CRNT.Oscillation.PlanarFlowRegularity`
- `CRNT.Oscillation.PlanarFrontier`
- `CRNT.Oscillation.PlanarGreenGrid`
- `CRNT.Oscillation.PlanarGreenJordanApproximation`
- `CRNT.Oscillation.PlanarGreenRectangle`
- `CRNT.Oscillation.PlanarJordanBoundaryCurrent`
- `CRNT.Oscillation.PlanarJordanCrossingOrder`
- `CRNT.Oscillation.PlanarJordanDyadic`
- `CRNT.Oscillation.PlanarJordanSeparation`
- `CRNT.Oscillation.PlanarJordanTopology`
- `CRNT.Oscillation.PlanarLateSectionReturn`
- `CRNT.Oscillation.PlanarLocalReturnLoops`
- `CRNT.Oscillation.PlanarLocalReturns`
- `CRNT.Oscillation.PlanarMinimalSet`
- `CRNT.Oscillation.PlanarNoCrossing`
- `CRNT.Oscillation.PlanarOmega`
- `CRNT.Oscillation.PlanarOneSidedReturns`
- `CRNT.Oscillation.PlanarPoincareBendixson`
- `CRNT.Oscillation.PlanarRecurrentSection`
- `CRNT.Oscillation.PlanarReturnMonotonicity`
- `CRNT.Oscillation.PlanarReturnOrdering`
- `CRNT.Oscillation.PlanarReturnSequence`
- `CRNT.Oscillation.PlanarSectionCoordinates`
- `CRNT.Oscillation.PlanarSectionHitIsolation`
- `CRNT.Oscillation.PlanarTransversalGeometry`
- `CRNT.Oscillation.RankTwoPlanar`
- `CRNT.Oscillation.ReactionRestriction`
- `CRNT.Oscillation.ReactivityScaling`
- `CRNT.Oscillation.RecipeZero`
- `CRNT.Oscillation.RecipeZeroContinuation`
- `CRNT.Oscillation.ReducedKineticContinuation`
- `CRNT.Oscillation.ReturnInterval`
- `CRNT.Oscillation.ReturnMap`
- `CRNT.Oscillation.ReturnMapAttraction`
- `CRNT.Oscillation.ReturnMapContraction`
- `CRNT.Oscillation.ReturnMapFamilyPersistence`
- `CRNT.Oscillation.ReturnMapPersistence`
- `CRNT.Oscillation.ScalarReturnMapFamilyPersistence`
- `CRNT.Oscillation.ScalarReturnStability`
- `CRNT.Oscillation.ScalarSectionInterpolation`
- `CRNT.Oscillation.SimpleCycle`
- `CRNT.Oscillation.SimpleNegativeSpectrum`
- `CRNT.Oscillation.SimpleRoot`
- `CRNT.Oscillation.SmoothGlobalHopf`
- `CRNT.Oscillation.SpectralOpenness`
- `CRNT.Oscillation.StableCodimOneDHopf`
- `CRNT.Oscillation.StructuralCore`
- `CRNT.Oscillation.VassenaAnalyticity`
- `CRNT.Oscillation.VassenaContinuation`
- `CRNT.Oscillation.VassenaCriteria`
- `CRNT.Oscillation.VassenaEndToEnd`
- `CRNT.Oscillation.VassenaFiniteDimHopf`
- `CRNT.Oscillation.VassenaPrincipal`
- `CRNT.Reduction.IntermediateSchurComplement`
- `CRNT.Reduction.Intermediates`
- `CRNT.Reduction.SingleIntermediateElimination`
- `CRNT.Stability.BDC`
- `CRNT.Stability.BDCCauchyBinetProof`
- `CRNT.Stability.BDCPrincipalMinors`
- `CRNT.Stability.BDCStructuralNonsingularity`
- `CRNT.Stability.RobustLyapunov`
- `CRNT.Stochastic.Absorbing`
- `CRNT.Stochastic.BirthDeathExhaustive`
- `CRNT.Stochastic.CTMC`
- `CRNT.Stochastic.ConservationClassRegion`
- `CRNT.Stochastic.ConservativeClasses`
- `CRNT.Stochastic.CountWitnessPath`
- `CRNT.Stochastic.DetailedBalance`
- `CRNT.Stochastic.ErgodicConvergence`
- `CRNT.Stochastic.ErgodicConvergenceGeneral`
- `CRNT.Stochastic.Ergodicity`
- `CRNT.Stochastic.FirstOrderFoster`
- `CRNT.Stochastic.FosterLyapunov`
- `CRNT.Stochastic.Generator`
- `CRNT.Stochastic.IntegerLattice`
- `CRNT.Stochastic.JumpKernel`
- `CRNT.Stochastic.JumpReachabilityLift`
- `CRNT.Stochastic.Kernel`
- `CRNT.Stochastic.KernelInvariant`
- `CRNT.Stochastic.KernelIrreducible`
- `CRNT.Stochastic.KernelMaximalRegion`
- `CRNT.Stochastic.KernelNormalized`
- `CRNT.Stochastic.KernelProductForm`
- `CRNT.Stochastic.KernelStationary`
- `CRNT.Stochastic.KernelSupport`
- `CRNT.Stochastic.KurtzFluidLimit`
- `CRNT.Stochastic.KurtzScaling`
- `CRNT.Stochastic.MultiPoissonFluctuation`
- `CRNT.Stochastic.PoissonClockFamily`
- `CRNT.Stochastic.PoissonFluctuation`
- `CRNT.Stochastic.ProductForm`
- `CRNT.Stochastic.ProductFormConverse`
- `CRNT.Stochastic.RegionPrimitive`
- `CRNT.Stochastic.RegionStronglyConnected`
- `CRNT.Stochastic.Semigroup`
- `CRNT.Stochastic.SemigroupComposition`
- `CRNT.Stochastic.SemigroupConvergence`
- `CRNT.Stochastic.TimeChangedFluctuation`
- `CRNT.Stochastic.UniformizedConvergence`
- `CRNT.Stoich.ConservationDimension`
- `CRNT.Stoich.RationalVector`
- `CRNT.Stoich.Subspace`
- `CRNT.Stoich.Transpose`
- `CRNT.Stoich.Vector`
- `CRNT.Subnetwork.EmbeddedNetwork`
- `CRNT.Subnetwork.ReactionRestriction`
- `CRNT.Theorems.DeficiencyOne.DegreeExistence`
- `CRNT.Theorems.DeficiencyOne.DegreeExistenceBridges`
- `CRNT.Theorems.DeficiencyOne.Existence`
- `CRNT.Theorems.DeficiencyOne.ExistenceDynamical`
- `CRNT.Theorems.DeficiencyOne.JacobianKernel`
- `CRNT.Theorems.DeficiencyOne.JacobianOnStoich`
- `CRNT.Theorems.DeficiencyOne.LogRatioUniqueness`
- `CRNT.Theorems.DeficiencyOne.MultiClass`
- `CRNT.Theorems.DeficiencyOne.Statement`
- `CRNT.Theorems.DeficiencyOne.Theorem`
- `CRNT.Theorems.DeficiencyOne.ToricReduction`
- `CRNT.Theorems.DeficiencyOne.Uniqueness`
- `CRNT.Theorems.DeficiencyOne.WeaklyReversibleExistence`
- `CRNT.Theorems.DeficiencyOne.WeaklyReversibleExistenceSpecialCases`
- `CRNT.Theorems.DeficiencyZero.AsymptoticStability`
- `CRNT.Theorems.DeficiencyZero.Birch`
- `CRNT.Theorems.DeficiencyZero.BirchExistence`
- `CRNT.Theorems.DeficiencyZero.Characterization`
- `CRNT.Theorems.DeficiencyZero.Confinement`
- `CRNT.Theorems.DeficiencyZero.Dissipation`
- `CRNT.Theorems.DeficiencyZero.Existence`
- `CRNT.Theorems.DeficiencyZero.Lyapunov`
- `CRNT.Theorems.DeficiencyZero.NoPeriodicOrbit`
- `CRNT.Theorems.DeficiencyZero.PositiveKernel`
- `CRNT.Theorems.DeficiencyZero.Stability`
- `CRNT.Theorems.DeficiencyZero.Statement`
- `CRNT.Theorems.DeficiencyZero.Toric`
- `CRNT.Theorems.DeficiencyZero.TreeConstantConstruction`
- `CRNT.Theorems.DeficiencyZero.TreeConstantProofComplete`
- `CRNT.Topology.ProperLocalHomeomorph`
- `CRNT.Translation.ComplexBalance`
- `CRNT.Translation.DeficiencyImprovement`
- `CRNT.Translation.DynamicalEquivalence`
- `CRNT.Translation.Improper`
- `CRNT.Translation.ImproperComplexBalance`
- `CRNT.Translation.LinearConjugacy`
- `CRNT.Translation.LinearConjugacySpectral`
- `CRNT.Translation.ParallelAggregation`
- `CRNT.Translation.ParallelStructural`
- `CRNT.Translation.ReactionTranslation`
- `CRNT.Translation.ResolvedComplexBalance`
- `CRNT.Translation.SourceCoefficientEquivalence`
- `CRNT.Translation.SourceComplexes`
- `CRNT.Translation.StructuralInvariants`

</details>

# Available-but-unused capabilities

A module that is **transitively imported by a hole's module but never mentioned in
it** is a capability that exists, elaborates, carries no `sorry`, and is already in
the hole's dependency cone — and which nobody finds by reading the hole's file.

This table is the reason this document exists. It is computed, not curated: a module
qualifies when it is in the hole's transitive import closure, is hole-free, and none
of its declarations' short names occurs anywhere in the hole's module.

Read it as: *everything listed here is proved, in scope, and not yet wired in.*

## Hole A: 151 modules in the import closure, never used

`CRNT.Dynamics.HighCodimensionSiphonFace` transitively imports 178 modules. 151 of them contribute **nothing** to any declaration in the file.

| module | path | decls | theorems | largest declarations |
|---|---|---|---|---|
| `CRNT.Geometry.ZeroSeparatingInduction` | `CRNT/Geometry/ZeroSeparatingInduction.lean` | 294 | 238 | `CompactZeroBitFiberPatchCover.exists_common_scale_and_oneBit_fills_for_craciun_words`, `CompactZeroBitFiberPatchCover.exists_common_scale_and_oneBit_fills_along_binary_chains`, `CompactZeroBitFiberPatchCover.exists_common_scale_and_oneBit_fills` |
| `CRNT.Geometry.FanRefinement` | `CRNT/Geometry/FanRefinement.lean` | 156 | 117 | `fanSmallProductTile_adjacentStrip_seam`, `craciunProjectiveArrangementRadialOverlap_commonFace`, `CompactSmallBaseTiling.boundary_overlap_patch_at` |
| `CRNT.Dynamics.SiphonAutocatalysis` | `CRNT/Dynamics/SiphonAutocatalysis.lean` | 69 | 47 | `hasNoCriticalSiphon_of_weaklyReversible_noDrainable_of_minimalCriticalDichotomy`, `hasNoCriticalSiphon_of_noDrainable_of_minimalCriticalDichotomy`, `IsMinimalCriticalSiphon.drainable_and_selfReplicable_of_weaklyReversible` |
| `CRNT.Oscillation.VassenaCriteria` | `CRNT/Oscillation/VassenaCriteria.lean` | 60 | 37 | `fluxJacobianCore_isDStable_iff_reciprocalRealizations_hurwitz`, `massActionJacobian_diagonalSegment`, `massActionJacobian_reciprocalDiagonalRealization` |
| `CRNT.Equilibria.TreeConstants` | `CRNT/Equilibria/TreeConstants.lean` | 56 | 39 | `IsRootedInArborescence.inverse_swap_isRooted`, `lastEnteringReaction_spec`, `IsRootedInArborescence.last_entering_reaction_unique` |
| `CRNT.Geometry.ProjectedFaceDimensionCode` | `CRNT/Geometry/ProjectedFaceDimensionCode.lean` | 46 | 26 | `CoordinateProjectedConeChain.ofFiniteGenerators_cone_eq_projection`, `CoordinateProjectedFaceChain.projectionEquiv_of_dimensionLetter_false_apply`, `CoordinateProjectedConeChain.dimension_eq_wordWeight` |
| `CRNT.Oscillation.MatrixCriteria` | `CRNT/Oscillation/MatrixCriteria.lean` | 45 | 22 | `submatrix_isPMinusMatrix`, `IsOscillatoryCoreClassII.fisherFuller_or_stableCodimOne`, `properPrincipal_not_unstable` |
| `CRNT.Dynamics.SpectralSplittingReal` | `CRNT/Dynamics/SpectralSplittingReal.lean` | 40 | 30 | `conjPi_sub_smul_pow`, `conjPi_sub_smul`, `realPoints_sup_eq_top` |
| `CRNT.Equilibria.ComplexBalanceLinearStability` | `CRNT/Equilibria/ComplexBalanceLinearStability.lean` | 39 | 30 | `complexBalanceJacobianQuadratic_eq_neg_sum_sq`, `hasDerivAt_quadraticLyapunov`, `complexBalanceJacobianQuadratic_eq_zero_iff_tangent` |
| `CRNT.Dynamics.ComplexBalanceStoichFanInclusion` | `CRNT/Dynamics/ComplexBalanceStoichFanInclusion.lean` | 38 | 35 | `massActionVectorField_inner_nonneg_on_compact_projectedLogPatch`, `massActionVectorField_inner_pos_of_mem_interior_sourceOrderNegativeCone`, `massActionVectorField_inner_nonneg_of_projectedLogBall` |
| `CRNT.Dynamics.GlobalPersistence` | `CRNT/Dynamics/GlobalPersistence.lean` | 32 | 14 | `gac_of_structurallyPersistent`, `persistentOrbit_of_persistentFrom`, `persistentOrbit_of_permanent` |
| `CRNT.Geometry.LogProjectiveFaceCompatibility` | `CRNT/Geometry/LogProjectiveFaceCompatibility.lean` | 29 | 19 | `pointwise_compatibility_does_not_imply_first_jet_compatibility`, `positiveSectionPoint_eq_of_projectiveFiberWeight_eq`, `exists_common_weightedExpLevel_derivative_of_fiber_first_moment` |
| `CRNT.Oscillation.StructuralCore` | `CRNT/Oscillation/StructuralCore.lean` | 29 | 8 | `OscillatoryCoreClassIICertificate.parameterRichOscillatoryCapacity`, `OscillatoryCoreClassICertificate.parameterRichOscillatoryCapacity`, `IsOscillatoryCoreClassII.isUnstableNegativeFeedback` |
| `CRNT.Deficiency.KernelDimension` | `CRNT/Deficiency/KernelDimension.lean` | 28 | 22 | `linked_imp_eq_of_edge_const`, `sum_mul_incidenceMap_single_eq_edgeIncrement`, `incidenceMap_apply` |
| `CRNT.Graph.CirculationDecomposition` | `CRNT/Graph/CirculationDecomposition.lean` | 27 | 21 | `IsDirectedCycleFlow.exists_closedWalk_flux_of_mem_support`, `graphCirculation_weighted_sum_eq_closedWalkSums`, `graphCirculation_decomposes_into_closedWalkFluxes` |
| `CRNT.LinearAlgebra.ConformalDecomposition` | `CRNT/LinearAlgebra/ConformalDecomposition.lean` | 27 | 23 | `NonnegElementary.eq_pos_smul_of_support_subset`, `nonnegElementary_of_min_confDom`, `exists_nonnegElementarySum` |
| `CRNT.Oscillation.Basic` | `CRNT/Oscillation/Basic.lean` | 27 | 12 | `HasGloballyAttractingPositivePeriodicOrbit.hasPositivePeriodicOrbit`, `oscillatoryCapacity_of_globallyAttractingPositivePeriodicOrbit`, `HasGlobalLimitCycleOnClass.hasPositivePeriodicOrbit` |
| `CRNT.Geometry.ConeFace` | `CRNT/Geometry/ConeFace.lean` | 26 | 20 | `isPolyhedralFan_empty_clauses`, `exposedFace_isFaceOf`, `inner_nonneg_of_mem_coneDual` |
| `CRNT.Geometry.ZeroSeparatingCurve2D` | `CRNT/Geometry/ZeroSeparatingCurve2D.lean` | 26 | 16 | `stays_away_from_zero_of_support`, `polyRegion_subset_compl_ball`, `ball_subset_compl_polyRegion` |
| `CRNT.Equilibria.Wegscheider` | `CRNT/Equilibria/Wegscheider.lean` | 25 | 18 | `exists_positive_reactionwiseDetailedBalanced_of_hasWegscheiderPotential`, `hasWegscheiderPotential_iff_exists_positive_reactionwiseDetailedBalanced`, `hasWegscheiderPotential_of_reactionwiseDetailedBalanced` |
| `CRNT.Geometry.FanFaceLattice` | `CRNT/Geometry/FanFaceLattice.lean` | 24 | 19 | `forwardInvariant_barrier_toricInclusion`, `Network.inner_euclideanMassActionField_nonneg_of_mem_deltaCore`, `Network.inner_euclideanMassActionField_nonneg` |
| `CRNT.Dynamics.ToricEmbeddingOrder` | `CRNT/Dynamics/ToricEmbeddingOrder.lean` | 23 | 20 | `cyclicProjectedVelocity_nonpos_of_permutedList_rateSeparation`, `cyclicProjectedVelocity_nonpos_of_permutedList_of_orderedCoefficients`, `cyclicProjectedVelocity_nonpos_of_rateSeparation` |
| `CRNT.Dynamics.SpectralSplitting` | `CRNT/Dynamics/SpectralSplitting.lean` | 22 | 17 | `isInternal_stable_center_unstable`, `specSubspace_eq_biSup_inter_spectrum`, `disjoint_specSubspace` |
| `CRNT.Dynamics.ComplexBalanceStoichFan` | `CRNT/Dynamics/ComplexBalanceStoichFan.lean` | 20 | 16 | `properMap_subtype_eq_pointedMap`, `relativeSourceOrderStoichFan_faces_mem`, `comap_inf_relativeSourceOrder` |
| `CRNT.Geometry.FaithfulCurve2D` | `CRNT/Geometry/FaithfulCurve2D.lean` | 20 | 16 | `faithful_region_persistent`, `apexField_region_persistent`, `exists_faithful_separating_region` |
| `CRNT.Theorems.DeficiencyZero.PositiveKernel` | `CRNT/Theorems/DeficiencyZero/PositiveKernel.lean` | 20 | 17 | `weaklyReversible_exists_positive_kernelVector`, `reaches_supportReaches`, `kmat_blockdiag` |
| `CRNT.Dynamics.ExponentialDecay` | `CRNT/Dynamics/ExponentialDecay.lean` | 18 | 12 | `le_mul_exp_of_deriv_le`, `hasDerivAt_lyapFun`, `norm_exp_smul_le` |
| `CRNT.Dynamics.SiphonFaceWeakReversibility` | `CRNT/Dynamics/SiphonFaceWeakReversibility.lean` | 18 | 14 | `complexBalanced_and_massActionVectorField_eq_zero_of_constantEntropy_siphonFaceOrbit`, `massActionVectorField_eq_zero_of_confined_constantEntropy_siphonFaceOrbit`, `massActionVectorField_eq_zero_of_constantEntropy_siphonFaceOrbit` |
| `CRNT.LinearAlgebra.OrientedMatroid` | `CRNT/LinearAlgebra/OrientedMatroid.lean` | 18 | 14 | `realizable_compose`, `thr_safe`, `exists_signVector_add_smul` |
| `CRNT.Deficiency.LinkageDeficiency` | `CRNT/Deficiency/LinkageDeficiency.lean` | 17 | 10 | `sum_linkageDeficiency_eq_deficiency_iff`, `reactionVector_mem_linkageStoichSubspace`, `linkageDeficiency_eq_zero_of_deficiencyZero` |
| `CRNT.Dynamics.MassActionAlgebra` | `CRNT/Dynamics/MassActionAlgebra.lean` | 17 | 11 | `kineticMap_apply`, `kineticMap_complexMonomial_apply`, `massActionVectorField_eq` |
| `CRNT.Geometry.FaithfulCurve` | `CRNT/Geometry/FaithfulCurve.lean` | 17 | 10 | `faithfulOfAttractsAll`, `isSupportFace_of_attractsAll`, `toricGenerators_subset_dualHalfPlane_of_attractsAll` |
| `CRNT.Deficiency.CycleExactSequence` | `CRNT/Deficiency/CycleExactSequence.lean` | 16 | 11 | `finrank_stoichCycleSpace_eq_graphCycles_add_deficiency`, `cycleQuotientEquivDeficiency`, `deficiency_finrank_eq_cycle_gap` |
| `CRNT.Geometry.PolyhedralFan` | `CRNT/Geometry/PolyhedralFan.lean` | 16 | 11 | `mem_generatedCone_iff`, `exponentVector_mem_newtonPolytope`, `exists_mem_coneDual_of_notMem` |
| `CRNT.Dynamics.GlobalPermanence` | `CRNT/Dynamics/GlobalPermanence.lean` | 15 | 7 | `StructurallyPermanent.permanent`, `StructurallyPermanent.onPositiveClass`, `StructurallyPermanent.permanent_selfClass` |
| `CRNT.Equilibria.ComplexBalanceGeometry` | `CRNT/Equilibria/ComplexBalanceGeometry.lean` | 15 | 10 | `mem_positiveComplexBalancedSet_iff_toric`, `complexBalanced_geometricInterpolate`, `toricParam_complexBalanced` |
| `CRNT.Equilibria.DetailedBalanced` | `CRNT/Equilibria/DetailedBalanced.lean` | 15 | 12 | `detailedBalance_pair_symm`, `positiveComplexBalanced_of_positiveDetailedBalanced`, `pairFlux_pos_of_reaction` |
| `CRNT.Geometry.LogProjectiveSmoothSection` | `CRNT/Geometry/LogProjectiveSmoothSection.lean` | 15 | 11 | `exists_contDiff_local_sectionScale`, `positiveSectionPoint_spec`, `positiveSectionPoint_unique` |
| `CRNT.Kinetics.Generalized` | `CRNT/Kinetics/Generalized.lean` | 15 | 13 | `gen_birch_uniqueness`, `gen_birch_existence`, `birch_uniqueness_of_self` |
| `CRNT.Oscillation.ParameterRich` | `CRNT/Oscillation/ParameterRich.lean` | 15 | 5 | `isSymbolicallyNondegenerate_of_witness`, `vectorField_coordinate_hasDerivAt`, `IsReactivityMatrix.interpolate` |
| `CRNT.Deficiency.TerminalKernelDimension` | `CRNT/Deficiency/TerminalKernelDimension.lean` | 14 | 12 | `restrictToStrongClass_kineticKernel`, `weaklyReversible_of_exists_positive_kineticKernel`, `terminalKernelMode_zero_off` |
| `CRNT.Dynamics.Viability` | `CRNT/Dynamics/Viability.lean` | 14 | 12 | `forwardInvariant_Ici_of_nagumo`, `inwardOnBoundary_iff_posSubtangent`, `subtangent_of_forwardInvariant` |
| `CRNT.Equilibria.DetailedBalanceLinearStability` | `CRNT/Equilibria/DetailedBalanceLinearStability.lean` | 14 | 9 | `detailedBalance_Jacobian_pair_formula`, `detailedBalanceJacobianQuadratic_eq_neg_sum_sq`, `detailedBalanceJacobianQuadratic_eq_zero_iff` |
| `CRNT.Geometry.ToricFan` | `CRNT/Geometry/ToricFan.lean` | 14 | 9 | `coneDual_subset_toricGenerators`, `coneDual_le_toricField`, `toricInclusionField_mono_delta` |
| `CRNT.Stochastic.ErgodicConvergence` | `CRNT/Stochastic/ErgodicConvergence.lean` | 14 | 12 | `regionMatrix_pow_mulVec_tendsto_stationaryVec`, `colStochastic_pow_mulVec_tendsto`, `pow_mulVec_l1_le_geometric` |
| `CRNT.Stochastic.Ergodicity` | `CRNT/Stochastic/Ergodicity.lean` | 14 | 10 | `invariant_probabilityMeasure_unique_on_region`, `stationaryProbabilityMeasure_isInvariant_isProbability`, `stationaryVec_mulVec_fixed` |
| `CRNT.Stochastic.KernelStationary` | `CRNT/Stochastic/KernelStationary.lean` | 14 | 13 | `tsum_reaction_term_eq_generatorInflow`, `predecessor_sum_eq`, `jumpKernel_invariant_jumpStationaryMeasure` |
| `CRNT.Dynamics.IsolatedInvariant` | `CRNT/Dynamics/IsolatedInvariant.lean` | 13 | 11 | `isIsolatedInvariant_of_maximalInvariantSubset_eq`, `IsIsolatedInvariant.mem_nhds`, `subset_maximalInvariantSubset_of_isInvariant` |
| `CRNT.Flux.Cone` | `CRNT/Flux/Cone.lean` | 13 | 9 | `positiveSteadyStateFlux_iff_positive_fluxCone`, `isStationaryFlux_iff_species_balance`, `positiveStationaryFlux_mem_fluxCone` |
| `CRNT.Flux.Elementary` | `CRNT/Flux/Elementary.lean` | 13 | 8 | `elementaryFluxMode_support_eq_of_subset`, `elementaryFluxMode_of_support_singleton`, `elementaryFluxMode_pos_smul` |
| `CRNT.Theorems.DeficiencyZero.Existence` | `CRNT/Theorems/DeficiencyZero/Existence.lean` | 13 | 11 | `kineticMap_scale_eq_zero`, `stoichTranspose_apply`, `exists_isComplexBalanced` |
| `CRNT.Deficiency.ExactSequence` | `CRNT/Deficiency/ExactSequence.lean` | 12 | 6 | `incidence_finrank_eq_deficiency_add_stoich`, `deficiencySubspace_eq_bot_iff_incidenceToStoich_injective`, `incidenceQuotientDeficiencyEquivStoich` |
| `CRNT.Dynamics.DifferentialInclusion` | `CRNT/Dynamics/DifferentialInclusion.lean` | 12 | 8 | `IsInclusionSolutionOn.of_ode`, `IsInclusionSolution.of_ode`, `IsInclusionSolutionOn.mono` |
| `CRNT.Dynamics.ZeroSeparating` | `CRNT/Dynamics/ZeroSeparating.lean` | 12 | 11 | `ZeroSeparatingRegion.inter`, `ZeroSeparatingRegion.notMem_ball`, `zeroSeparatingRegion_Ici` |
| `CRNT.LinearAlgebra.OrthogonalComplement` | `CRNT/LinearAlgebra/OrthogonalComplement.lean` | 12 | 10 | `finrank_add_finrank_inf_orthSum_of_le`, `mem_orthSum_span`, `orthSum_eq` |
| `CRNT.Stochastic.CTMC` | `CRNT/Stochastic/CTMC.lean` | 12 | 6 | `stochasticOutflow_eq_generatorOutflow`, `stochasticTotalOutflow_eq_generatorOutflow`, `productPoisson_isGeneratorStationary_of_complexBalanced` |
| `CRNT.Dynamics.FirstExit` | `CRNT/Dynamics/FirstExit.lean` | 11 | 9 | `exit_accumulates_right`, `mem_Icc_exitTime`, `mem_frontier_exitTime` |
| `CRNT.Geometry.Endotactic` | `CRNT/Geometry/Endotactic.lean` | 11 | 5 | `wRate_of_source_eq_target`, `wRate_eq`, `StronglyEndotactic.endotactic` |
| `CRNT.Graph.CycleCover` | `CRNT/Graph/CycleCover.lean` | 11 | 9 | `WeaklyReversible.reaches_both`, `WeaklyReversible.exists_returnReactionWalk`, `WeaklyReversible.exists_cycleWalk` |
| `CRNT.Graph.LinkageClass` | `CRNT/Graph/LinkageClass.lean` | 11 | 7 | `WeaklyReversible.reaches_of_linked`, `UndirectedEdge.symm`, `Linked.trans` |

<details><summary>all 151</summary>

- `CRNT.Basic.Reaction` (5 decls)
- `CRNT.Combinatorics.DigraphExcess` (3 decls)
- `CRNT.Decision.Linkage` (8 decls)
- `CRNT.Decision.Reachability` (8 decls)
- `CRNT.Decision.StrongLinkage` (10 decls)
- `CRNT.Deficiency.ClosedSetKernel` (2 decls)
- `CRNT.Deficiency.Consistent` (2 decls)
- `CRNT.Deficiency.ConsistentWR` (1 decls)
- `CRNT.Deficiency.CycleExactSequence` (16 decls)
- `CRNT.Deficiency.DeficiencyOne` (8 decls)
- `CRNT.Deficiency.DeficiencyOneHypotheses` (7 decls)
- `CRNT.Deficiency.Definition` (4 decls)
- `CRNT.Deficiency.Drainage` (3 decls)
- `CRNT.Deficiency.ExactSequence` (12 decls)
- `CRNT.Deficiency.KernelDimension` (28 decls)
- `CRNT.Deficiency.KernelDimensionBound` (2 decls)
- `CRNT.Deficiency.KineticBlock` (8 decls)
- `CRNT.Deficiency.LinkageDeficiency` (17 decls)
- `CRNT.Deficiency.PerClassKernel` (1 decls)
- `CRNT.Deficiency.SignedDrainage` (1 decls)
- `CRNT.Deficiency.SteadyStateKernel` (5 decls)
- `CRNT.Deficiency.TerminalKernelBound` (1 decls)
- `CRNT.Deficiency.TerminalKernelDimension` (14 decls)
- `CRNT.Deficiency.TerminalReachable` (2 decls)
- `CRNT.Deficiency.TerminalSLC` (5 decls)
- `CRNT.Deficiency.TerminalSLCKernel` (2 decls)
- `CRNT.Dynamics.BoundaryOmegaSiphon` (1 decls)
- `CRNT.Dynamics.ClosedSetNagumo` (5 decls)
- `CRNT.Dynamics.ComplexBalanceStoichFan` (20 decls)
- `CRNT.Dynamics.ComplexBalanceStoichFanInclusion` (38 decls)
- `CRNT.Dynamics.ConfinedInvariance` (5 decls)
- `CRNT.Dynamics.ConservationLaw` (3 decls)
- `CRNT.Dynamics.CriticalSiphonOmega` (1 decls)
- `CRNT.Dynamics.DifferentialInclusion` (12 decls)
- `CRNT.Dynamics.EscapeSiphonFace` (3 decls)
- `CRNT.Dynamics.ExponentialDecay` (18 decls)
- `CRNT.Dynamics.ExponentialDichotomy` (9 decls)
- `CRNT.Dynamics.FirstExit` (11 decls)
- `CRNT.Dynamics.FlowConstruction` (5 decls)
- `CRNT.Dynamics.ForwardInvariance` (3 decls)
- `CRNT.Dynamics.GACConfinement` (1 decls)
- `CRNT.Dynamics.GACNoCriticalSiphon` (1 decls)
- `CRNT.Dynamics.GACSeparatingCapstone` (2 decls)
- `CRNT.Dynamics.GACSeparatingRegion` (1 decls)
- `CRNT.Dynamics.GACSeparatingWitness` (8 decls)
- `CRNT.Dynamics.GlobalPermanence` (15 decls)
- `CRNT.Dynamics.GlobalPersistence` (32 decls)
- `CRNT.Dynamics.GlobalStability` (1 decls)
- `CRNT.Dynamics.IsolatedInvariant` (13 decls)
- `CRNT.Dynamics.MassActionAlgebra` (17 decls)
- `CRNT.Dynamics.MassActionField` (3 decls)
- `CRNT.Dynamics.Nagumo` (5 decls)
- `CRNT.Dynamics.NegativeInvariance` (1 decls)
- `CRNT.Dynamics.NoCriticalSiphonPersistence` (1 decls)
- `CRNT.Dynamics.Persistence` (7 decls)
- `CRNT.Dynamics.PersistenceConfined` (3 decls)
- `CRNT.Dynamics.PersistenceGAC` (2 decls)
- `CRNT.Dynamics.PersistenceTheorem` (8 decls)
- `CRNT.Dynamics.PolyRegionStrictInvariant` (6 decls)
- `CRNT.Dynamics.RouthHurwitz` (6 decls)
- `CRNT.Dynamics.SiphonAutocatalysis` (69 decls)
- `CRNT.Dynamics.SiphonConservation` (2 decls)
- `CRNT.Dynamics.SiphonFaceWeakReversibility` (18 decls)
- `CRNT.Dynamics.SpectralSplitting` (22 decls)
- `CRNT.Dynamics.SpectralSplittingReal` (40 decls)
- `CRNT.Dynamics.StrictInflow` (1 decls)
- `CRNT.Dynamics.SublevelInvariant` (4 decls)
- `CRNT.Dynamics.SublevelNagumo` (6 decls)
- `CRNT.Dynamics.SupportDiniBridge` (10 decls)
- `CRNT.Dynamics.ThmBGenuine` (9 decls)
- `CRNT.Dynamics.ToricEmbedding` (5 decls)
- `CRNT.Dynamics.ToricEmbeddingOrder` (23 decls)
- `CRNT.Dynamics.ToricInclusion` (5 decls)
- `CRNT.Dynamics.Viability` (14 decls)
- `CRNT.Dynamics.ZeroSeparating` (12 decls)
- `CRNT.Equilibria.ComplexBalanceGeometry` (15 decls)
- `CRNT.Equilibria.ComplexBalanceLinearStability` (39 decls)
- `CRNT.Equilibria.DetailedBalanceEntropy` (10 decls)
- `CRNT.Equilibria.DetailedBalanceLinearStability` (14 decls)
- `CRNT.Equilibria.DetailedBalanceToric` (6 decls)
- `CRNT.Equilibria.DetailedBalanced` (15 decls)
- `CRNT.Equilibria.SteadyState` (3 decls)
- `CRNT.Equilibria.TreeConstants` (56 decls)
- `CRNT.Equilibria.Wegscheider` (25 decls)
- `CRNT.Flux.Cone` (13 decls)
- `CRNT.Flux.Elementary` (13 decls)
- `CRNT.Geometry.ConeFace` (26 decls)
- `CRNT.Geometry.Endotactic` (11 decls)
- `CRNT.Geometry.FaithfulCurve` (17 decls)
- `CRNT.Geometry.FaithfulCurve2D` (20 decls)
- `CRNT.Geometry.FanFaceLattice` (24 decls)
- `CRNT.Geometry.FanRefinement` (156 decls)
- `CRNT.Geometry.FiniteConeClosed` (10 decls)
- `CRNT.Geometry.LogProjectiveFaceCompatibility` (29 decls)
- `CRNT.Geometry.LogProjectiveSection` (9 decls)
- `CRNT.Geometry.LogProjectiveSmoothSection` (15 decls)
- `CRNT.Geometry.PolyhedralFan` (16 decls)
- `CRNT.Geometry.ProjectedFaceDimensionCode` (46 decls)
- `CRNT.Geometry.SimplicialConeClosed` (5 decls)
- `CRNT.Geometry.ToricFan` (14 decls)
- `CRNT.Geometry.ToricFieldPolar` (5 decls)
- `CRNT.Geometry.ZeroSeparatingCurve2D` (26 decls)
- `CRNT.Geometry.ZeroSeparatingInduction` (294 decls)
- `CRNT.Geometry.ZeroSeparatingSurface` (10 decls)
- `CRNT.Graph.CirculationDecomposition` (27 decls)
- `CRNT.Graph.CycleCover` (11 decls)
- `CRNT.Graph.LinkageClass` (11 decls)
- `CRNT.Graph.PositiveCirculation` (5 decls)
- `CRNT.Graph.Reachability` (7 decls)
- `CRNT.Graph.Reversibility` (4 decls)
- `CRNT.Kinetics.General` (11 decls)
- `CRNT.Kinetics.Generalized` (15 decls)
- `CRNT.Kinetics.MassActionJacobian` (10 decls)
- `CRNT.LinearAlgebra.ConformalDecomposition` (27 decls)
- `CRNT.LinearAlgebra.FinrankSup` (6 decls)
- `CRNT.LinearAlgebra.OrientedMatroid` (18 decls)
- `CRNT.LinearAlgebra.OrthogonalComplement` (12 decls)
- `CRNT.LinearAlgebra.PerronFrobenius` (8 decls)
- `CRNT.LinearAlgebra.SignVector` (8 decls)
- `CRNT.LinearAlgebra.Substochastic` (2 decls)
- `CRNT.Multistationarity.PMatrix` (9 decls)
- `CRNT.Oscillation.Basic` (27 decls)
- `CRNT.Oscillation.KineticBasic` (9 decls)
- `CRNT.Oscillation.MatrixCriteria` (45 decls)
- `CRNT.Oscillation.ParameterRich` (15 decls)
- `CRNT.Oscillation.StructuralCore` (29 decls)
- `CRNT.Oscillation.VassenaCriteria` (60 decls)
- `CRNT.Stochastic.CTMC` (12 decls)
- `CRNT.Stochastic.ErgodicConvergence` (14 decls)
- `CRNT.Stochastic.ErgodicConvergenceGeneral` (9 decls)
- `CRNT.Stochastic.Ergodicity` (14 decls)
- `CRNT.Stochastic.Generator` (10 decls)
- `CRNT.Stochastic.JumpKernel` (7 decls)
- `CRNT.Stochastic.JumpReachabilityLift` (8 decls)
- `CRNT.Stochastic.Kernel` (8 decls)
- `CRNT.Stochastic.KernelInvariant` (4 decls)
- `CRNT.Stochastic.KernelIrreducible` (9 decls)
- `CRNT.Stochastic.KernelNormalized` (8 decls)
- `CRNT.Stochastic.KernelStationary` (14 decls)
- `CRNT.Stochastic.ProductForm` (9 decls)
- `CRNT.Stochastic.RegionPrimitive` (8 decls)
- `CRNT.Stochastic.RegionStronglyConnected` (7 decls)
- `CRNT.Stoich.Vector` (3 decls)
- `CRNT.Subnetwork.ReactionRestriction` (11 decls)
- `CRNT.Theorems.DeficiencyZero.Birch` (1 decls)
- `CRNT.Theorems.DeficiencyZero.BirchExistence` (9 decls)
- `CRNT.Theorems.DeficiencyZero.Confinement` (8 decls)
- `CRNT.Theorems.DeficiencyZero.Existence` (13 decls)
- `CRNT.Theorems.DeficiencyZero.PositiveKernel` (20 decls)
- `CRNT.Theorems.DeficiencyZero.Statement` (2 decls)
- `CRNT.Theorems.DeficiencyZero.Toric` (7 decls)

</details>

## Hole B: 137 modules in the import closure, never used

`CRNT.Multistationarity.TrueChemistrySRCriterion` transitively imports 172 modules. 137 of them contribute **nothing** to any declaration in the file.

| module | path | decls | theorems | largest declarations |
|---|---|---|---|---|
| `CRNT.Dynamics.SiphonAutocatalysis` | `CRNT/Dynamics/SiphonAutocatalysis.lean` | 69 | 47 | `hasNoCriticalSiphon_of_weaklyReversible_noDrainable_of_minimalCriticalDichotomy`, `hasNoCriticalSiphon_of_noDrainable_of_minimalCriticalDichotomy`, `IsMinimalCriticalSiphon.drainable_and_selfReplicable_of_weaklyReversible` |
| `CRNT.Oscillation.VassenaCriteria` | `CRNT/Oscillation/VassenaCriteria.lean` | 60 | 37 | `fluxJacobianCore_isDStable_iff_reciprocalRealizations_hurwitz`, `massActionJacobian_diagonalSegment`, `massActionJacobian_reciprocalDiagonalRealization` |
| `CRNT.Equilibria.TreeConstants` | `CRNT/Equilibria/TreeConstants.lean` | 56 | 39 | `IsRootedInArborescence.inverse_swap_isRooted`, `lastEnteringReaction_spec`, `IsRootedInArborescence.last_entering_reaction_unique` |
| `CRNT.Oscillation.MatrixCriteria` | `CRNT/Oscillation/MatrixCriteria.lean` | 45 | 22 | `submatrix_isPMinusMatrix`, `IsOscillatoryCoreClassII.fisherFuller_or_stableCodimOne`, `properPrincipal_not_unstable` |
| `CRNT.Dynamics.GlobalPersistence` | `CRNT/Dynamics/GlobalPersistence.lean` | 32 | 14 | `gac_of_structurallyPersistent`, `persistentOrbit_of_persistentFrom`, `persistentOrbit_of_permanent` |
| `CRNT.Oscillation.StructuralCore` | `CRNT/Oscillation/StructuralCore.lean` | 29 | 8 | `OscillatoryCoreClassIICertificate.parameterRichOscillatoryCapacity`, `OscillatoryCoreClassICertificate.parameterRichOscillatoryCapacity`, `IsOscillatoryCoreClassII.isUnstableNegativeFeedback` |
| `CRNT.Deficiency.KernelDimension` | `CRNT/Deficiency/KernelDimension.lean` | 28 | 22 | `linked_imp_eq_of_edge_const`, `sum_mul_incidenceMap_single_eq_edgeIncrement`, `incidenceMap_apply` |
| `CRNT.Multistationarity.SourceWeightPairing` | `CRNT/Multistationarity/SourceWeightPairing.lean` | 28 | 22 | `exists_sourceWeight_pairing_eq`, `no_positive_eigenvalue_of_concordant_fullyOpen`, `exists_diagonalPair_of_discordant_fullyOpen` |
| `CRNT.Oscillation.Basic` | `CRNT/Oscillation/Basic.lean` | 27 | 12 | `HasGloballyAttractingPositivePeriodicOrbit.hasPositivePeriodicOrbit`, `oscillatoryCapacity_of_globallyAttractingPositivePeriodicOrbit`, `HasGlobalLimitCycleOnClass.hasPositivePeriodicOrbit` |
| `CRNT.Theorems.DeficiencyZero.PositiveKernel` | `CRNT/Theorems/DeficiencyZero/PositiveKernel.lean` | 20 | 17 | `weaklyReversible_exists_positive_kernelVector`, `reaches_supportReaches`, `kmat_blockdiag` |
| `CRNT.Dynamics.SiphonFaceWeakReversibility` | `CRNT/Dynamics/SiphonFaceWeakReversibility.lean` | 18 | 14 | `complexBalanced_and_massActionVectorField_eq_zero_of_constantEntropy_siphonFaceOrbit`, `massActionVectorField_eq_zero_of_confined_constantEntropy_siphonFaceOrbit`, `massActionVectorField_eq_zero_of_constantEntropy_siphonFaceOrbit` |
| `CRNT.Deficiency.LinkageDeficiency` | `CRNT/Deficiency/LinkageDeficiency.lean` | 17 | 10 | `sum_linkageDeficiency_eq_deficiency_iff`, `reactionVector_mem_linkageStoichSubspace`, `linkageDeficiency_eq_zero_of_deficiencyZero` |
| `CRNT.Dynamics.MassActionAlgebra` | `CRNT/Dynamics/MassActionAlgebra.lean` | 17 | 11 | `kineticMap_apply`, `kineticMap_complexMonomial_apply`, `massActionVectorField_eq` |
| `CRNT.Deficiency.CycleExactSequence` | `CRNT/Deficiency/CycleExactSequence.lean` | 16 | 11 | `finrank_stoichCycleSpace_eq_graphCycles_add_deficiency`, `cycleQuotientEquivDeficiency`, `deficiency_finrank_eq_cycle_gap` |
| `CRNT.Geometry.PolyhedralFan` | `CRNT/Geometry/PolyhedralFan.lean` | 16 | 11 | `mem_generatedCone_iff`, `exponentVector_mem_newtonPolytope`, `exists_mem_coneDual_of_notMem` |
| `CRNT.Dynamics.GlobalPermanence` | `CRNT/Dynamics/GlobalPermanence.lean` | 15 | 7 | `StructurallyPermanent.permanent`, `StructurallyPermanent.onPositiveClass`, `StructurallyPermanent.permanent_selfClass` |
| `CRNT.Oscillation.ParameterRich` | `CRNT/Oscillation/ParameterRich.lean` | 15 | 5 | `isSymbolicallyNondegenerate_of_witness`, `vectorField_coordinate_hasDerivAt`, `IsReactivityMatrix.interpolate` |
| `CRNT.Deficiency.TerminalKernelDimension` | `CRNT/Deficiency/TerminalKernelDimension.lean` | 14 | 12 | `restrictToStrongClass_kineticKernel`, `weaklyReversible_of_exists_positive_kineticKernel`, `terminalKernelMode_zero_off` |
| `CRNT.Multistationarity.TrueSRClosedWalk` | `CRNT/Multistationarity/TrueSRClosedWalk.lean` | 14 | 7 | `vertex_eq_reactionAt`, `vertex_eq_speciesAt`, `walkSucc_walkSucc_evenPos` |
| `CRNT.Stochastic.ErgodicConvergence` | `CRNT/Stochastic/ErgodicConvergence.lean` | 14 | 12 | `regionMatrix_pow_mulVec_tendsto_stationaryVec`, `colStochastic_pow_mulVec_tendsto`, `pow_mulVec_l1_le_geometric` |
| `CRNT.Stochastic.Ergodicity` | `CRNT/Stochastic/Ergodicity.lean` | 14 | 10 | `invariant_probabilityMeasure_unique_on_region`, `stationaryProbabilityMeasure_isInvariant_isProbability`, `stationaryVec_mulVec_fixed` |
| `CRNT.Stochastic.KernelStationary` | `CRNT/Stochastic/KernelStationary.lean` | 14 | 13 | `tsum_reaction_term_eq_generatorInflow`, `predecessor_sum_eq`, `jumpKernel_invariant_jumpStationaryMeasure` |
| `CRNT.Flux.Cone` | `CRNT/Flux/Cone.lean` | 13 | 9 | `positiveSteadyStateFlux_iff_positive_fluxCone`, `isStationaryFlux_iff_species_balance`, `positiveStationaryFlux_mem_fluxCone` |
| `CRNT.Multistationarity.Normality` | `CRNT/Multistationarity/Normality.lean` | 13 | 6 | `normalWitness_iff_kernel_bot`, `normal_of_scale_reactionWeights`, `circulation_potential_sum_zero` |
| `CRNT.Multistationarity.TrueSRCycleReverse` | `CRNT/Multistationarity/TrueSRCycleReverse.lean` | 13 | 11 | `reverse_rep`, `reverse_rightEdge`, `reverse_leftEdge` |
| `CRNT.Theorems.DeficiencyZero.Existence` | `CRNT/Theorems/DeficiencyZero/Existence.lean` | 13 | 11 | `kineticMap_scale_eq_zero`, `stoichTranspose_apply`, `exists_isComplexBalanced` |
| `CRNT.Deficiency.ExactSequence` | `CRNT/Deficiency/ExactSequence.lean` | 12 | 6 | `incidence_finrank_eq_deficiency_add_stoich`, `deficiencySubspace_eq_bot_iff_incidenceToStoich_injective`, `incidenceQuotientDeficiencyEquivStoich` |
| `CRNT.LinearAlgebra.OrthogonalComplement` | `CRNT/LinearAlgebra/OrthogonalComplement.lean` | 12 | 10 | `finrank_add_finrank_inf_orthSum_of_le`, `mem_orthSum_span`, `orthSum_eq` |
| `CRNT.Multistationarity.ConcordanceConverse` | `CRNT/Multistationarity/ConcordanceConverse.lean` | 12 | 7 | `exists_sourceWeights_for_concordanceWitness`, `concordanceKineticsRealization_noninjective`, `guardedLinearKinetics_weaklyMonotonic` |
| `CRNT.Stochastic.CTMC` | `CRNT/Stochastic/CTMC.lean` | 12 | 6 | `stochasticOutflow_eq_generatorOutflow`, `stochasticTotalOutflow_eq_generatorOutflow`, `productPoisson_isGeneratorStationary_of_complexBalanced` |
| `CRNT.Theorems.DeficiencyZero.AsymptoticStability` | `CRNT/Theorems/DeficiencyZero/AsymptoticStability.lean` | 12 | 12 | `omegaLimit_eq_singleton_of_local`, `orbit_relEntropy_le`, `orbit_pos` |
| `CRNT.Geometry.Endotactic` | `CRNT/Geometry/Endotactic.lean` | 11 | 5 | `wRate_of_source_eq_target`, `wRate_eq`, `StronglyEndotactic.endotactic` |
| `CRNT.Graph.LinkageClass` | `CRNT/Graph/LinkageClass.lean` | 11 | 7 | `WeaklyReversible.reaches_of_linked`, `UndirectedEdge.symm`, `Linked.trans` |
| `CRNT.Multistationarity.TrueSRMidSegment` | `CRNT/Multistationarity/TrueSRMidSegment.lean` | 11 | 9 | `midSegmentRev_vertex`, `midSegment_vertex`, `midSegmentRev_edge` |
| `CRNT.Multistationarity.TrueSRPathAccessors` | `CRNT/Multistationarity/TrueSRPathAccessors.lean` | 11 | 9 | `endReaction_eq`, `edge_reaction_of_even`, `edge_species_of_odd` |
| `CRNT.Subnetwork.ReactionRestriction` | `CRNT/Subnetwork/ReactionRestriction.lean` | 11 | 8 | `massActionVectorField_partition`, `restrictReactions_massActionVectorField`, `restrictReactions_reactionVector` |
| `CRNT.Theorems.DeficiencyZero.Dissipation` | `CRNT/Theorems/DeficiencyZero/Dissipation.lean` | 11 | 11 | `kineticMap_logRatio_term_eq`, `kineticMap_logRatio_term_le`, `kineticMap_logRatio_ratio_eq` |
| `CRNT.Decision.StrongLinkage` | `CRNT/Decision/StrongLinkage.lean` | 10 | 6 | `stronglyLinked_of_reaches_of_terminal`, `StronglyLinked.trans`, `stronglyLinked_of_within` |
| `CRNT.Dynamics.GACOmegaPositive` | `CRNT/Dynamics/GACOmegaPositive.lean` | 10 | 10 | `positiveOmega_or_lowerRankCriticalBoundaryFace`, `criticalBoundaryOmegaFace_lowerRank`, `omegaLimit_eq_singleton_of_mem_positive` |
| `CRNT.Kinetics.MassActionJacobian` | `CRNT/Kinetics/MassActionJacobian.lean` | 10 | 7 | `massActionMonomial_hasFDerivAt`, `massActionVectorField_hasFDerivAt`, `massActionJacobianCLM_apply` |
| `CRNT.Multistationarity.FullyOpenConcordanceSpectral` | `CRNT/Multistationarity/FullyOpenConcordanceSpectral.lean` | 10 | 9 | `weakNormality_eigenvalue_neg_of_concordant_fullyOpen`, `discordant_fullyOpen_of_positive_eigenvalue_onStoich`, `discordant_fullyOpen_iff_influence` |
| `CRNT.Stochastic.Generator` | `CRNT/Stochastic/Generator.lean` | 10 | 6 | `productPoissonPMF_mul_stochasticRate`, `sum_source_flux_eq_outflow`, `sum_target_flux_eq_inflow` |
| `CRNT.Multistationarity.PMatrix` | `CRNT/Multistationarity/PMatrix.lean` | 9 | 8 | `finset_det_pos`, `submatrix_isPMatrix`, `submatrix_det_pos` |
| `CRNT.Multistationarity.SRGraph` | `CRNT/Multistationarity/SRGraph.lean` | 9 | 5 | `srGraph_adj_iff`, `srGraph_isBipartiteWith`, `srGraph_not_adj_reaction` |
| `CRNT.Oscillation.KineticBasic` | `CRNT/Oscillation/KineticBasic.lean` | 9 | 4 | `PositivePeriodicOrbit.toKinetic`, `neverPositiveKineticPeriodic_iff_not_kineticOscillatoryCapacity`, `not_neverPositiveKineticPeriodic_of_oscillatoryCapacity` |
| `CRNT.Stochastic.ErgodicConvergenceGeneral` | `CRNT/Stochastic/ErgodicConvergenceGeneral.lean` | 9 | 8 | `regionMatrix_primitive_pow_mulVec_tendsto_stationaryVec`, `colStochastic_primitive_pow_mulVec_tendsto`, `colStochastic_pow_mulVec_l1_le` |
| `CRNT.Stochastic.KernelIrreducible` | `CRNT/Stochastic/KernelIrreducible.lean` | 9 | 7 | `tsum_reaction_term_restricted`, `restricted_predecessor_sum_eq`, `restrictedStationaryMeasure_bind_apply` |
| `CRNT.Stochastic.ProductForm` | `CRNT/Stochastic/ProductForm.lean` | 9 | 6 | `productPoissonPMF_mul_descFactorial`, `poissonFactor_mul_descFactorial`, `productPoisson_singleton` |
| `CRNT.Theorems.DeficiencyZero.BirchExistence` | `CRNT/Theorems/DeficiencyZero/BirchExistence.lean` | 9 | 8 | `birch`, `birch_existence`, `birchDual_firstOrder` |
| `CRNT.Decision.Linkage` | `CRNT/Decision/Linkage.lean` | 8 | 5 | `reflTransGen_adj_of_linked`, `linked_of_reflTransGen_adj`, `linked_iff_reachable` |
| `CRNT.Decision.Reachability` | `CRNT/Decision/Reachability.lean` | 8 | 5 | `decidableReachesWithin`, `ReachesWithin`, `reachesWithin_succ` |
| `CRNT.Deficiency.DeficiencyOne` | `CRNT/Deficiency/DeficiencyOne.lean` | 8 | 6 | `numComplexes_eq_add`, `not_deficiencyZero_of_deficiencyOne`, `deficiencyZero_iff_deficiency_eq_zero` |
| `CRNT.Deficiency.KineticBlock` | `CRNT/Deficiency/KineticBlock.lean` | 8 | 7 | `kineticMap_apply_eq_of_eqOn_class`, `kineticMap_restrictToClass`, `kineticMap_eq_zero_iff_forall_restrictToClass` |
| `CRNT.Dynamics.GACSeparatingWitness` | `CRNT/Dynamics/GACSeparatingWitness.lean` | 8 | 8 | `gac_of_local_separatingConfinement`, `separatingConfinement_of_omegaLimit_singleton`, `persistentFrom_of_omegaLimit_singleton` |
| `CRNT.Dynamics.PersistenceTheorem` | `CRNT/Dynamics/PersistenceTheorem.lean` | 8 | 7 | `siphonFace_forwardInvariant`, `faceSum_deriv_witness_eq_zero_on_siphonFace`, `nagumo_halfspace_scalar_upper` |
| `CRNT.Kinetics.Concentration` | `CRNT/Kinetics/Concentration.lean` | 8 | 4 | `massActionMonomial_nonneg`, `massActionMonomial_zero`, `massActionMonomial_pos` |
| `CRNT.LinearAlgebra.PerronFrobenius` | `CRNT/LinearAlgebra/PerronFrobenius.lean` | 8 | 7 | `exists_nonneg_mulVec_fixed_invariant`, `pos_of_supportReaches_pos_on`, `mulVec_fixed_unique_of_stronglyConnected` |
| `CRNT.LinearAlgebra.SignVector` | `CRNT/LinearAlgebra/SignVector.lean` | 8 | 5 | `orthogonal_signVector_of_mem_orthSum`, `mul_eq_zero_of_conformal_mem_orthSum`, `signVector_mul_apply` |
| `CRNT.Multistationarity.TrueSRMinimalChord` | `CRNT/Multistationarity/TrueSRMinimalChord.lean` | 8 | 4 | `isChord_initialSegment`, `minimal_chord_interior_disjoint`, `isChord_terminalSegment` |
| `CRNT.Stochastic.JumpReachabilityLift` | `CRNT/Stochastic/JumpReachabilityLift.lean` | 8 | 6 | `weaklyReversible_pow_mulVec_tendsto_stationaryVec`, `jumpReaches_of_fireableList`, `regionJumpStronglyConnected_of_fireablePairs` |

<details><summary>all 137</summary>

- `CRNT.Basic.Reaction` (5 decls)
- `CRNT.Combinatorics.DigraphExcess` (3 decls)
- `CRNT.Decision.Linkage` (8 decls)
- `CRNT.Decision.Reachability` (8 decls)
- `CRNT.Decision.StrongLinkage` (10 decls)
- `CRNT.Deficiency.ClosedSetKernel` (2 decls)
- `CRNT.Deficiency.Consistent` (2 decls)
- `CRNT.Deficiency.ConsistentWR` (1 decls)
- `CRNT.Deficiency.CycleExactSequence` (16 decls)
- `CRNT.Deficiency.DeficiencyOne` (8 decls)
- `CRNT.Deficiency.DeficiencyOneHypotheses` (7 decls)
- `CRNT.Deficiency.Definition` (4 decls)
- `CRNT.Deficiency.Drainage` (3 decls)
- `CRNT.Deficiency.ExactSequence` (12 decls)
- `CRNT.Deficiency.KernelDimension` (28 decls)
- `CRNT.Deficiency.KernelDimensionBound` (2 decls)
- `CRNT.Deficiency.KineticBlock` (8 decls)
- `CRNT.Deficiency.LinkageDeficiency` (17 decls)
- `CRNT.Deficiency.PerClassKernel` (1 decls)
- `CRNT.Deficiency.SignedDrainage` (1 decls)
- `CRNT.Deficiency.TerminalKernelBound` (1 decls)
- `CRNT.Deficiency.TerminalKernelDimension` (14 decls)
- `CRNT.Deficiency.TerminalReachable` (2 decls)
- `CRNT.Deficiency.TerminalSLC` (5 decls)
- `CRNT.Deficiency.TerminalSLCKernel` (2 decls)
- `CRNT.Dynamics.BoundaryOmegaSiphon` (1 decls)
- `CRNT.Dynamics.ConfinedInvariance` (5 decls)
- `CRNT.Dynamics.ConservationLaw` (3 decls)
- `CRNT.Dynamics.CriticalSiphonOmega` (1 decls)
- `CRNT.Dynamics.EndotacticPermanence` (6 decls)
- `CRNT.Dynamics.FlowConstruction` (5 decls)
- `CRNT.Dynamics.ForwardInvariance` (3 decls)
- `CRNT.Dynamics.GACConfinement` (1 decls)
- `CRNT.Dynamics.GACNoCriticalSiphon` (1 decls)
- `CRNT.Dynamics.GACOmegaPositive` (10 decls)
- `CRNT.Dynamics.GACSeparatingCapstone` (2 decls)
- `CRNT.Dynamics.GACSeparatingRegion` (1 decls)
- `CRNT.Dynamics.GACSeparatingWitness` (8 decls)
- `CRNT.Dynamics.GenuineConfinement` (4 decls)
- `CRNT.Dynamics.GlobalPermanence` (15 decls)
- `CRNT.Dynamics.GlobalPersistence` (32 decls)
- `CRNT.Dynamics.GlobalStability` (1 decls)
- `CRNT.Dynamics.LaSalle` (1 decls)
- `CRNT.Dynamics.MassActionAlgebra` (17 decls)
- `CRNT.Dynamics.MassActionField` (3 decls)
- `CRNT.Dynamics.Nagumo` (5 decls)
- `CRNT.Dynamics.NegativeInvariance` (1 decls)
- `CRNT.Dynamics.NoCriticalSiphonPersistence` (1 decls)
- `CRNT.Dynamics.Persistence` (7 decls)
- `CRNT.Dynamics.PersistenceConfined` (3 decls)
- `CRNT.Dynamics.PersistenceGAC` (2 decls)
- `CRNT.Dynamics.PersistenceTheorem` (8 decls)
- `CRNT.Dynamics.RouthHurwitz` (6 decls)
- `CRNT.Dynamics.SingleLinkageGAC` (4 decls)
- `CRNT.Dynamics.SiphonAutocatalysis` (69 decls)
- `CRNT.Dynamics.SiphonConservation` (2 decls)
- `CRNT.Dynamics.SiphonFaceWeakReversibility` (18 decls)
- `CRNT.Dynamics.StrictInflow` (1 decls)
- `CRNT.Dynamics.SublevelInvariant` (4 decls)
- `CRNT.Equilibria.CompatibilityClass` (7 decls)
- `CRNT.Equilibria.ComplexBalanced` (3 decls)
- `CRNT.Equilibria.SteadyState` (3 decls)
- `CRNT.Equilibria.TreeConstants` (56 decls)
- `CRNT.Flux.Cone` (13 decls)
- `CRNT.Geometry.Endotactic` (11 decls)
- `CRNT.Geometry.PolyhedralFan` (16 decls)
- `CRNT.Graph.LinkageClass` (11 decls)
- `CRNT.Graph.PositiveCirculation` (5 decls)
- `CRNT.Graph.Reachability` (7 decls)
- `CRNT.Graph.Reversibility` (4 decls)
- `CRNT.Kinetics.Concentration` (8 decls)
- `CRNT.Kinetics.MassAction` (6 decls)
- `CRNT.Kinetics.MassActionJacobian` (10 decls)
- `CRNT.LinearAlgebra.FinrankSup` (6 decls)
- `CRNT.LinearAlgebra.OrthogonalComplement` (12 decls)
- `CRNT.LinearAlgebra.PerronFrobenius` (8 decls)
- `CRNT.LinearAlgebra.SignVector` (8 decls)
- `CRNT.LinearAlgebra.Substochastic` (2 decls)
- `CRNT.Multistationarity.ConcordanceConverse` (12 decls)
- `CRNT.Multistationarity.Discordance` (6 decls)
- `CRNT.Multistationarity.FullyOpenConcordanceSpectral` (10 decls)
- `CRNT.Multistationarity.Normality` (13 decls)
- `CRNT.Multistationarity.PMatrix` (9 decls)
- `CRNT.Multistationarity.SRGraph` (9 decls)
- `CRNT.Multistationarity.SourceWeightPairing` (28 decls)
- `CRNT.Multistationarity.TrueSRChordParity` (2 decls)
- `CRNT.Multistationarity.TrueSRClosedWalk` (14 decls)
- `CRNT.Multistationarity.TrueSRCycleReverse` (13 decls)
- `CRNT.Multistationarity.TrueSRDegreeTwoNoSToR` (5 decls)
- `CRNT.Multistationarity.TrueSRGlueBlocks` (2 decls)
- `CRNT.Multistationarity.TrueSRGlueIndex` (6 decls)
- `CRNT.Multistationarity.TrueSRGlueSeams` (6 decls)
- `CRNT.Multistationarity.TrueSRMidSegment` (11 decls)
- `CRNT.Multistationarity.TrueSRMinimalChord` (8 decls)
- `CRNT.Multistationarity.TrueSRParityCount` (3 decls)
- `CRNT.Multistationarity.TrueSRParityLemma` (3 decls)
- `CRNT.Multistationarity.TrueSRPathAccessors` (11 decls)
- `CRNT.Multistationarity.TrueSRPathSegment` (4 decls)
- `CRNT.Multistationarity.TrueSRPathTerminalSegment` (5 decls)
- `CRNT.Multistationarity.TrueSRSeamParity` (3 decls)
- `CRNT.Multistationarity.TrueSRSegmentEndpoints` (4 decls)
- `CRNT.Multistationarity.TrueSRSingleSharedEdge` (4 decls)
- `CRNT.Multistationarity.TrueSRTwoWeightGain` (1 decls)
- `CRNT.Oscillation.Basic` (27 decls)
- `CRNT.Oscillation.KineticBasic` (9 decls)
- `CRNT.Oscillation.MatrixCriteria` (45 decls)
- `CRNT.Oscillation.ParameterRich` (15 decls)
- `CRNT.Oscillation.StructuralCore` (29 decls)
- `CRNT.Oscillation.VassenaCriteria` (60 decls)
- `CRNT.Stochastic.CTMC` (12 decls)
- `CRNT.Stochastic.ErgodicConvergence` (14 decls)
- `CRNT.Stochastic.ErgodicConvergenceGeneral` (9 decls)
- `CRNT.Stochastic.Ergodicity` (14 decls)
- `CRNT.Stochastic.Generator` (10 decls)
- `CRNT.Stochastic.JumpKernel` (7 decls)
- `CRNT.Stochastic.JumpReachabilityLift` (8 decls)
- `CRNT.Stochastic.Kernel` (8 decls)
- `CRNT.Stochastic.KernelInvariant` (4 decls)
- `CRNT.Stochastic.KernelIrreducible` (9 decls)
- `CRNT.Stochastic.KernelNormalized` (8 decls)
- `CRNT.Stochastic.KernelStationary` (14 decls)
- `CRNT.Stochastic.ProductForm` (9 decls)
- `CRNT.Stochastic.RegionPrimitive` (8 decls)
- `CRNT.Stochastic.RegionStronglyConnected` (7 decls)
- `CRNT.Stoich.Subspace` (4 decls)
- `CRNT.Subnetwork.ReactionRestriction` (11 decls)
- `CRNT.Theorems.DeficiencyZero.AsymptoticStability` (12 decls)
- `CRNT.Theorems.DeficiencyZero.Birch` (1 decls)
- `CRNT.Theorems.DeficiencyZero.BirchExistence` (9 decls)
- `CRNT.Theorems.DeficiencyZero.Confinement` (8 decls)
- `CRNT.Theorems.DeficiencyZero.Dissipation` (11 decls)
- `CRNT.Theorems.DeficiencyZero.Existence` (13 decls)
- `CRNT.Theorems.DeficiencyZero.Lyapunov` (6 decls)
- `CRNT.Theorems.DeficiencyZero.PositiveKernel` (20 decls)
- `CRNT.Theorems.DeficiencyZero.Stability` (2 decls)
- `CRNT.Theorems.DeficiencyZero.Statement` (2 decls)
- `CRNT.Theorems.DeficiencyZero.Toric` (7 decls)

</details>

## How to use this table

When picking up a hole, do not start from the hole's own hypotheses. Start from the
available-but-unused list above and ask, for each module: *does this already state the
conclusion I need, in a form whose hypotheses I can discharge?* A proved theorem with a
dischargeable hypothesis is a much smaller gap than a theorem you have to invent. The
gap between a hole's conclusion and the nearest already-proved theorem in its own
dependency cone is the real size of the remaining work.

## Why this matters operationally

A researcher closing hole A is touching exactly 4 modules that anything downstream imports. Everything else in
the tree — 841 modules — is inert with respect
to that hole: editing it cannot make the hole easier or harder, and a `sorry` there
would not block the Global Attractor Theorem. The same holds for hole B. So a
reviewer triaging a hole-closing PR should ask only whether the diff touches the
modules listed above for that hole.

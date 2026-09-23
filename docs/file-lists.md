# File lists

Generated from the shipped tree. `VERIFIED` = in `import CRNT` and compiling;
`LEDGER-clean` = proved but not elaborating (the mechanical work);
`LEDGER-sorry` = carries unproved statements (the mathematics).

## VERIFIED core — 518 modules (include these for any downstream use)

```
CRNT.Algebra.SiphonIdeal
CRNT.Analysis.BrouwerConvex
CRNT.Analysis.BrouwerZero
CRNT.Analysis.ConcentrationZero
CRNT.Analysis.ConvexProjection
CRNT.Analysis.FixedPoint
CRNT.Analysis.Sperner
CRNT.Analysis.Sperner2D
CRNT.Analysis.Sperner2DMulti
CRNT.Analysis.SpernerBrouwer2D
CRNT.Analysis.SpernerBrouwerN
CRNT.Analysis.SpernerGrid
CRNT.Analysis.SpernerGridGeometric
CRNT.Analysis.SpernerGridMulti
CRNT.Analysis.SpernerLattice
CRNT.Analysis.SpernerLatticeBipartite
CRNT.Analysis.SpernerLatticeBoundary
CRNT.Analysis.SpernerLatticeCellColor
CRNT.Analysis.SpernerLatticeCellDegree
CRNT.Analysis.SpernerLatticeColoring
CRNT.Analysis.SpernerLatticeDoorGraph
CRNT.Analysis.SpernerLatticeFullGraph
CRNT.Analysis.SpernerLatticeGeometric
CRNT.Analysis.SpernerLatticeIncidence
CRNT.Analysis.SpernerLatticeIncidenceHV
CRNT.Analysis.SpernerLatticeN
CRNT.Analysis.SpernerLatticeNeighbor
CRNT.Analysis.SpernerLatticeSperner
CRNT.Analysis.SpernerMultiIncidence
CRNT.Analysis.SpernerNBaseShift
CRNT.Analysis.SpernerNBoundary
CRNT.Analysis.SpernerNBoundaryCell
CRNT.Analysis.SpernerNBoundaryCorr
CRNT.Analysis.SpernerNBoundaryCount
CRNT.Analysis.SpernerNClose
CRNT.Analysis.SpernerNDoor
CRNT.Analysis.SpernerNFacetCount
CRNT.Analysis.SpernerNFintype
CRNT.Analysis.SpernerNGeometric
CRNT.Analysis.SpernerNHandshake
CRNT.Analysis.SpernerNIncidence
CRNT.Analysis.SpernerNInterior
CRNT.Analysis.SpernerNParity
CRNT.Analysis.SpernerNSperner
CRNT.Analysis.SpernerSimplexLimit
CRNT.Analysis.SpernerSimplexLimitN
CRNT.Analysis.SpernerTriangulation
CRNT.Basic.Complex
CRNT.Basic.Network
CRNT.Basic.Reaction
CRNT.Combinatorics.DecidableCycle
CRNT.Combinatorics.DigraphExcess
CRNT.Compose.Interconnect
CRNT.Compose.InterconnectKinetics
CRNT.Compose.InterconnectMonostationary
CRNT.Compose.InterconnectSiphon
CRNT.Compose.StoichIndependent
CRNT.Decision.ACRCheck
CRNT.Decision.ComputableDeficiency
CRNT.Decision.ComputableTerminalSLC
CRNT.Decision.ConservationConeStrict
CRNT.Decision.CriticalSiphonDecide
CRNT.Decision.DeficiencyOneConditionsDecide
CRNT.Decision.DeficiencyZeroTactic
CRNT.Decision.DirectedReachability
CRNT.Decision.ExactDeficiency
CRNT.Decision.GaussianRank
CRNT.Decision.InjectivityMargin
CRNT.Decision.IsCriticalSiphonDecidable
CRNT.Decision.Linkage
CRNT.Decision.LinkageDeficiencyExact
CRNT.Decision.MinorSearch
CRNT.Decision.PersistenceCertified
CRNT.Decision.PersistenceSingleLinkage
CRNT.Decision.PersistenceVerdict
CRNT.Decision.Rank
CRNT.Decision.RankExact
CRNT.Decision.RationalFarkas
CRNT.Decision.RationalFarkasDecide
CRNT.Decision.RationalFarkasStrict
CRNT.Decision.Reachability
CRNT.Decision.StoichBasisQ
CRNT.Decision.StrictConeRealization
CRNT.Decision.StrongLinkage
CRNT.Decision.Tactic
CRNT.Decomposition.BlockDeficiency
CRNT.Decomposition.Deficiency
CRNT.Decomposition.Rank
CRNT.Decomposition.ReactionPartition
CRNT.Deficiency.AdvancedDeficiencyAlgorithm
CRNT.Deficiency.ClassConservation
CRNT.Deficiency.ClosedSetKernel
CRNT.Deficiency.Colinearity
CRNT.Deficiency.ColinearityClasses
CRNT.Deficiency.ComplexBalancedRatio
CRNT.Deficiency.Confluence
CRNT.Deficiency.Consistent
CRNT.Deficiency.ConsistentWR
CRNT.Deficiency.CutPair
CRNT.Deficiency.DOACapacityConstruction
CRNT.Deficiency.DOAForward
CRNT.Deficiency.DeficiencyOne
CRNT.Deficiency.DeficiencyOneAlgorithm
CRNT.Deficiency.DeficiencyOneDecide
CRNT.Deficiency.DeficiencyOneDecomp
CRNT.Deficiency.DeficiencyOneHypotheses
CRNT.Deficiency.DeficiencyOneLine
CRNT.Deficiency.DeficiencyOneLocalize
CRNT.Deficiency.DeficiencyOneStructure
CRNT.Deficiency.DeficientClassKernel
CRNT.Deficiency.Definition
CRNT.Deficiency.Drainage
CRNT.Deficiency.ExcessPositivity
CRNT.Deficiency.HigherDeficiency
CRNT.Deficiency.IncidenceBlock
CRNT.Deficiency.KernelDimension
CRNT.Deficiency.KernelDimensionBound
CRNT.Deficiency.KernelDimensionWR
CRNT.Deficiency.KineticBlock
CRNT.Deficiency.KineticExcess
CRNT.Deficiency.LevelSetSign
CRNT.Deficiency.LinkageDeficiency
CRNT.Deficiency.LogMonomialRatio
CRNT.Deficiency.PerClassKernel
CRNT.Deficiency.PerClassKernelPos
CRNT.Deficiency.PerClassKernelUnique
CRNT.Deficiency.RangeKineticWR
CRNT.Deficiency.Regular
CRNT.Deficiency.Shelf
CRNT.Deficiency.Signature
CRNT.Deficiency.SignedDrainage
CRNT.Deficiency.SteadyStateKernel
CRNT.Deficiency.StructuredPreimage
CRNT.Deficiency.TerminalKernelBound
CRNT.Deficiency.TerminalReachable
CRNT.Deficiency.TerminalSLC
CRNT.Deficiency.TerminalSLCKernel
CRNT.Design.ACR
CRNT.Design.ACRCrossClass
CRNT.Design.ACRStandard
CRNT.Design.ACRUnconditional
CRNT.Design.Adaptation
CRNT.Design.BufferingStructure
CRNT.Design.GeneratedClosure
CRNT.Design.OutputCompleteClosure
CRNT.Design.ShinarFeinbergTheorem
CRNT.Dynamics.BoundaryDescent
CRNT.Dynamics.BoundaryOmegaSiphon
CRNT.Dynamics.ButlerMcGehee
CRNT.Dynamics.CenterManifold
CRNT.Dynamics.CenterManifoldReduction
CRNT.Dynamics.CertifiedReduction
CRNT.Dynamics.ClosedSetNagumo
CRNT.Dynamics.ConfinedInvariance
CRNT.Dynamics.ConservationLaw
CRNT.Dynamics.CriticalSiphonDissipationRepulsion
CRNT.Dynamics.CriticalSiphonNearFacetInflux
CRNT.Dynamics.CriticalSiphonOmega
CRNT.Dynamics.DifferentialInclusion
CRNT.Dynamics.DissipationBound
CRNT.Dynamics.DissipativeTracking
CRNT.Dynamics.EndotacticPermanence
CRNT.Dynamics.EscapeSiphonFace
CRNT.Dynamics.ExponentialDecay
CRNT.Dynamics.ExponentialDichotomy
CRNT.Dynamics.FacetRepulsion
CRNT.Dynamics.Fenichel
CRNT.Dynamics.FenichelC1Manifold
CRNT.Dynamics.FenichelComovingManifold
CRNT.Dynamics.FenichelContinuousMovingTarget
CRNT.Dynamics.FenichelCoupledBase
CRNT.Dynamics.FenichelGeneralDrift
CRNT.Dynamics.FenichelLogisticInstance
CRNT.Dynamics.FenichelManifold
CRNT.Dynamics.FenichelMovingGeneralDrift
CRNT.Dynamics.FenichelPersistence
CRNT.Dynamics.FenichelPersistenceConcrete
CRNT.Dynamics.FenichelPersistenceContracting
CRNT.Dynamics.FenichelReductionPrinciple
CRNT.Dynamics.FenichelSlowDrift
CRNT.Dynamics.FenichelStabilityTransfer
CRNT.Dynamics.FiniteNegativeBudget
CRNT.Dynamics.FirstExit
CRNT.Dynamics.FlowConstruction
CRNT.Dynamics.FlowDifferentiable
CRNT.Dynamics.FlowSmoothDependence
CRNT.Dynamics.ForwardInvariance
CRNT.Dynamics.GACCertificate
CRNT.Dynamics.GACConfinement
CRNT.Dynamics.GACNoCriticalSiphon
CRNT.Dynamics.GACOmegaPositive
CRNT.Dynamics.GACSeparatingCapstone
CRNT.Dynamics.GACSeparatingRegion
CRNT.Dynamics.GACSeparatingRegionNagumo
CRNT.Dynamics.GACSeparatingWitness
CRNT.Dynamics.GenuineConfinement
CRNT.Dynamics.GershgorinColumnMarginQ
CRNT.Dynamics.GershgorinMarginQ
CRNT.Dynamics.GlobalPermanence
CRNT.Dynamics.GlobalPersistence
CRNT.Dynamics.GlobalPersistenceCertificates
CRNT.Dynamics.GlobalStability
CRNT.Dynamics.GraphTransform
CRNT.Dynamics.HopfAdmissible
CRNT.Dynamics.HopfBoundaryQ
CRNT.Dynamics.HopfGate
CRNT.Dynamics.HopfGate3Matrix
CRNT.Dynamics.HopfGate4
CRNT.Dynamics.HopfLimitCycle
CRNT.Dynamics.HopfNormalForm
CRNT.Dynamics.HopfPersistentOrbit
CRNT.Dynamics.HopfRealizes
CRNT.Dynamics.HopfTransversality3
CRNT.Dynamics.Hurwitz
CRNT.Dynamics.Hurwitz2Matrix
CRNT.Dynamics.Hurwitz3Matrix
CRNT.Dynamics.HurwitzGershgorin
CRNT.Dynamics.HurwitzGershgorinColumn
CRNT.Dynamics.IsolatedInvariant
CRNT.Dynamics.KnownGlobalPersistenceClasses
CRNT.Dynamics.LaSalle
CRNT.Dynamics.MassActionAlgebra
CRNT.Dynamics.MassActionField
CRNT.Dynamics.MichaelisMenten
CRNT.Dynamics.MichaelisMentenC1
CRNT.Dynamics.MichaelisMentenCertified
CRNT.Dynamics.MichaelisMentenCertifiedUniform
CRNT.Dynamics.MichaelisMentenCoupledContraction
CRNT.Dynamics.MichaelisMentenDepletion
CRNT.Dynamics.MichaelisMentenFenichel
CRNT.Dynamics.MichaelisMentenFenichelAllTime
CRNT.Dynamics.MichaelisMentenLipschitz
CRNT.Dynamics.MichaelisMentenManifold
CRNT.Dynamics.MichaelisMentenReduced
CRNT.Dynamics.MichaelisMentenRegularized
CRNT.Dynamics.MichaelisMentenSlowDrift
CRNT.Dynamics.MichaelisMentenSlowDriftSpeed
CRNT.Dynamics.MinimalInvariant
CRNT.Dynamics.Monotone
CRNT.Dynamics.Nagumo
CRNT.Dynamics.NegativeInvariance
CRNT.Dynamics.NoCriticalSiphonPersistence
CRNT.Dynamics.NoDrainableSiphonPersistence
CRNT.Dynamics.PermanenceAssembly
CRNT.Dynamics.Persistence
CRNT.Dynamics.PersistenceConfined
CRNT.Dynamics.PersistenceGAC
CRNT.Dynamics.PersistenceTheorem
CRNT.Dynamics.PoincareReturnMap
CRNT.Dynamics.PolyRegionInvariant
CRNT.Dynamics.PolyRegionStrictInvariant
CRNT.Dynamics.ProperTierTransversal
CRNT.Dynamics.QSSA
CRNT.Dynamics.ReactionConeDisplacement
CRNT.Dynamics.ReturnMapPeriodicOrbit
CRNT.Dynamics.RouthHurwitz
CRNT.Dynamics.RouthHurwitz4
CRNT.Dynamics.RouthHurwitz4Suff
CRNT.Dynamics.SingleLinkageGAC
CRNT.Dynamics.SingleLinkageStructure
CRNT.Dynamics.SingletonFacetEscape
CRNT.Dynamics.Siphon
CRNT.Dynamics.SiphonAutocatalysis
CRNT.Dynamics.SiphonConservation
CRNT.Dynamics.SiphonDimensionDescent
CRNT.Dynamics.SiphonFacetEscape
CRNT.Dynamics.SpectralSplitting
CRNT.Dynamics.SpectralSplittingReal
CRNT.Dynamics.StrictInflow
CRNT.Dynamics.SublevelInvariant
CRNT.Dynamics.SublevelNagumo
CRNT.Dynamics.SupportDiniBridge
CRNT.Dynamics.ThmBGenuine
CRNT.Dynamics.TierCompactNegativity
CRNT.Dynamics.TierDirectionFeasibility
CRNT.Dynamics.TierDirectionProjection
CRNT.Dynamics.TierExtraction
CRNT.Dynamics.TierExtractionCompleted
CRNT.Dynamics.TierLyapunov
CRNT.Dynamics.TierOrderAlgebra
CRNT.Dynamics.TierOriginGeometry
CRNT.Dynamics.TierPersistence
CRNT.Dynamics.TierScaleDecomposition
CRNT.Dynamics.TierScaleExtractionLemma44
CRNT.Dynamics.TierScaleMagnitude
CRNT.Dynamics.TierScaleTruncation
CRNT.Dynamics.TierSequentialReduction
CRNT.Dynamics.TierSubsequenceExtraction
CRNT.Dynamics.Tikhonov
CRNT.Dynamics.ToricEmbedding
CRNT.Dynamics.ToricEmbeddingOrder
CRNT.Dynamics.ToricEmbeddingWR
CRNT.Dynamics.ToricInclusion
CRNT.Dynamics.TransversalCrossingTime
CRNT.Dynamics.VariableTierLyapunov
CRNT.Dynamics.VariationalEquation
CRNT.Dynamics.Viability
CRNT.Dynamics.ZeroSeparating
CRNT.Equilibria.BrouwerNormalCone
CRNT.Equilibria.BrouwerSteadyState
CRNT.Equilibria.CompatibilityClass
CRNT.Equilibria.ComplexBalanceStructure
CRNT.Equilibria.ComplexBalanced
CRNT.Equilibria.DetailedBalanced
CRNT.Equilibria.SteadyState
CRNT.Equilibria.TreeConstants
CRNT.Equilibria.Wegscheider
CRNT.Equilibria.WegscheiderConverse
CRNT.Examples.HopfNetwork3
CRNT.Examples.HopfNetwork3Branches
CRNT.Examples.HopfOscillator3
CRNT.Examples.Lotka
CRNT.Examples.ReversiblePair
CRNT.Examples.StochasticConvergenceExample
CRNT.Flux.PSemiflow
CRNT.Geometry.CompatibilityFaces
CRNT.Geometry.ConeFace
CRNT.Geometry.Endotactic
CRNT.Geometry.EndotacticGlobal
CRNT.Geometry.FaithfulCurve
CRNT.Geometry.FaithfulCurve2D
CRNT.Geometry.FaithfulCurve2DFan
CRNT.Geometry.FaithfulCurveExistence
CRNT.Geometry.FaithfulCurveGeneral
CRNT.Geometry.FanActiveWalls
CRNT.Geometry.FanFaceProperness
CRNT.Geometry.FanRefinement
CRNT.Geometry.FanSeparationWitness
CRNT.Geometry.FanWallActivityDecide
CRNT.Geometry.FanWallsCrossed
CRNT.Geometry.FiniteConeClosed
CRNT.Geometry.HalfPlaneSeparatingSurface
CRNT.Geometry.PolyRegionSeparating
CRNT.Geometry.PolyhedralFan
CRNT.Geometry.ReactionFanGeneration
CRNT.Geometry.ReactionHullCone
CRNT.Geometry.SimplicialConeClosed
CRNT.Geometry.SpeciesProjection
CRNT.Geometry.ToricFan
CRNT.Geometry.ToricFieldPolar
CRNT.Geometry.ToricFieldPolarMulti
CRNT.Geometry.ToricStrictSupport
CRNT.Geometry.ToricWRStrictInward
CRNT.Geometry.ZeroSeparatingCurve2D
CRNT.Geometry.ZeroSeparatingInduction
CRNT.Geometry.ZeroSeparatingSurface
CRNT.Graph.Crossing
CRNT.Graph.CycleCover
CRNT.Graph.LinkageClass
CRNT.Graph.Reachability
CRNT.Graph.Reversibility
CRNT.Graph.WeakReversibility
CRNT.Interop.Analysis
CRNT.Interop.Certificates
CRNT.Interop.CodegenExamples
CRNT.Interop.NetworkData
CRNT.Kinetics.Concentration
CRNT.Kinetics.General
CRNT.Kinetics.Generalized
CRNT.Kinetics.GeneralizedConditions
CRNT.Kinetics.MassAction
CRNT.Kinetics.MassActionJacobian
CRNT.Kinetics.SpeciesProjectionMassAction
CRNT.Kinetics.VariableMassAction
CRNT.LinearAlgebra.CauchyBinet
CRNT.LinearAlgebra.ConformalDecomposition
CRNT.LinearAlgebra.DetCycleCover
CRNT.LinearAlgebra.FinrankSup
CRNT.LinearAlgebra.LogSumInj
CRNT.LinearAlgebra.OrientedMatroid
CRNT.LinearAlgebra.OrientedMatroidConditions
CRNT.LinearAlgebra.OrthogonalComplement
CRNT.LinearAlgebra.PerronFrobenius
CRNT.LinearAlgebra.PowerProductMono
CRNT.LinearAlgebra.PowerProductMonoFinset
CRNT.LinearAlgebra.SignVector
CRNT.LinearAlgebra.Substochastic
CRNT.Multistationarity.Capacity
CRNT.Multistationarity.Concordance
CRNT.Multistationarity.DegreeAdditivity
CRNT.Multistationarity.DegreeHomotopyInvariant
CRNT.Multistationarity.DegreeLocallyConstant
CRNT.Multistationarity.DegreeProperConstant
CRNT.Multistationarity.DegreeStability
CRNT.Multistationarity.Discordance
CRNT.Multistationarity.GaleNikaido
CRNT.Multistationarity.GaleNikaidoBox
CRNT.Multistationarity.GaleNikaidoUniv
CRNT.Multistationarity.Injectivity
CRNT.Multistationarity.JacobianCycleSelection
CRNT.Multistationarity.JacobianCycleSign
CRNT.Multistationarity.JacobianDeterminantSign
CRNT.Multistationarity.JacobianInjectivity
CRNT.Multistationarity.LinearDegree
CRNT.Multistationarity.Normality
CRNT.Multistationarity.PMatrix
CRNT.Multistationarity.PMatrixSchur
CRNT.Multistationarity.PMatrixSignature
CRNT.Multistationarity.PMatrixUnivalence
CRNT.Multistationarity.PivotChartInjectivity
CRNT.Multistationarity.PivotReducedInjectivity
CRNT.Multistationarity.PointIndepDecidable
CRNT.Multistationarity.ReducedCoverSign
CRNT.Multistationarity.ReducedJacobian
CRNT.Multistationarity.ReducedJacobianSign
CRNT.Multistationarity.ReducedPMatrixDecide
CRNT.Multistationarity.ReducedSRGraph
CRNT.Multistationarity.ReducedSRGraphBridge
CRNT.Multistationarity.RegularValueDegree
CRNT.Multistationarity.SRCoverPointIndependence
CRNT.Multistationarity.SRCycleInjectivity
CRNT.Multistationarity.SRGraph
CRNT.Multistationarity.SRGraphCriterion
CRNT.Multistationarity.SRGraphCycleDict
CRNT.Multistationarity.SRInjectivityClass
CRNT.Multistationarity.SRSignDecidable
CRNT.Multistationarity.Sard
CRNT.Multistationarity.SignConstruction
CRNT.Multistationarity.SignedSRGraph
CRNT.Multistationarity.SteadyStateDegree
CRNT.Multistationarity.StoichChart
CRNT.Multistationarity.Toric
CRNT.Open.Augmentation
CRNT.Open.Boundary
CRNT.Open.Deficiency
CRNT.Open.PartialOpen
CRNT.Oscillation.Basic
CRNT.Oscillation.Certificate
CRNT.Oscillation.ChildSelectionSearch
CRNT.Oscillation.CoordinateDynamics
CRNT.Oscillation.DulacAreaSign
CRNT.Oscillation.DulacLineIntegral
CRNT.Oscillation.Exclusion
CRNT.Oscillation.Floquet
CRNT.Oscillation.GlobalAttraction
CRNT.Oscillation.GreenJordanReduction
CRNT.Oscillation.KineticBasic
CRNT.Oscillation.LowRank
CRNT.Oscillation.MatrixCriteria
CRNT.Oscillation.OrbitTube
CRNT.Oscillation.ParameterRich
CRNT.Oscillation.PlanarDulac
CRNT.Oscillation.PlanarFrontier
CRNT.Oscillation.PlanarOmega
CRNT.Oscillation.ReactionRestriction
CRNT.Oscillation.RecipeZero
CRNT.Oscillation.RecipeZeroContinuation
CRNT.Oscillation.ReturnInterval
CRNT.Oscillation.ReturnMap
CRNT.Oscillation.ReturnMapAttraction
CRNT.Oscillation.ReturnMapContraction
CRNT.Oscillation.ReturnMapPersistence
CRNT.Oscillation.SimpleCycle
CRNT.Oscillation.SimpleRoot
CRNT.Oscillation.StructuralCore
CRNT.Stability.BDC
CRNT.Stochastic.CTMC
CRNT.Stochastic.ConservationClassRegion
CRNT.Stochastic.CountWitnessPath
CRNT.Stochastic.ErgodicConvergence
CRNT.Stochastic.ErgodicConvergenceGeneral
CRNT.Stochastic.Ergodicity
CRNT.Stochastic.FosterLyapunov
CRNT.Stochastic.Generator
CRNT.Stochastic.IntegerLattice
CRNT.Stochastic.JumpKernel
CRNT.Stochastic.JumpReachabilityLift
CRNT.Stochastic.Kernel
CRNT.Stochastic.KernelInvariant
CRNT.Stochastic.KernelIrreducible
CRNT.Stochastic.KernelMaximalRegion
CRNT.Stochastic.KernelNormalized
CRNT.Stochastic.KernelProductForm
CRNT.Stochastic.KernelStationary
CRNT.Stochastic.KernelSupport
CRNT.Stochastic.KurtzFluidLimit
CRNT.Stochastic.KurtzScaling
CRNT.Stochastic.MultiPoissonFluctuation
CRNT.Stochastic.PoissonClockFamily
CRNT.Stochastic.PoissonFluctuation
CRNT.Stochastic.ProductForm
CRNT.Stochastic.RegionPrimitive
CRNT.Stochastic.RegionStronglyConnected
CRNT.Stochastic.Semigroup
CRNT.Stochastic.SemigroupComposition
CRNT.Stochastic.SemigroupConvergence
CRNT.Stochastic.TimeChangedFluctuation
CRNT.Stochastic.UniformizedConvergence
CRNT.Stoich.ConservationDimension
CRNT.Stoich.Subspace
CRNT.Stoich.Transpose
CRNT.Stoich.Vector
CRNT.Subnetwork.EmbeddedNetwork
CRNT.Subnetwork.ReactionRestriction
CRNT.Theorems.DeficiencyOne.Existence
CRNT.Theorems.DeficiencyOne.ExistenceDynamical
CRNT.Theorems.DeficiencyOne.LogRatioUniqueness
CRNT.Theorems.DeficiencyOne.MultiClass
CRNT.Theorems.DeficiencyOne.Statement
CRNT.Theorems.DeficiencyOne.ToricReduction
CRNT.Theorems.DeficiencyOne.Uniqueness
CRNT.Theorems.DeficiencyZero.AsymptoticStability
CRNT.Theorems.DeficiencyZero.Birch
CRNT.Theorems.DeficiencyZero.BirchExistence
CRNT.Theorems.DeficiencyZero.Confinement
CRNT.Theorems.DeficiencyZero.Dissipation
CRNT.Theorems.DeficiencyZero.Existence
CRNT.Theorems.DeficiencyZero.Lyapunov
CRNT.Theorems.DeficiencyZero.NoPeriodicOrbit
CRNT.Theorems.DeficiencyZero.PositiveKernel
CRNT.Theorems.DeficiencyZero.Stability
CRNT.Theorems.DeficiencyZero.Statement
CRNT.Theorems.DeficiencyZero.Toric
CRNT.Translation.ComplexBalance
CRNT.Translation.DynamicalEquivalence
CRNT.Translation.ReactionTranslation
CRNT.Translation.SourceCoefficientEquivalence
CRNT.Translation.StructuralInvariants
```

## LEDGER-clean — 96 modules, no `sorry`, blocked by elaboration errors only

```
CRNT.Decomposition.BlockDeficiency
CRNT.Deficiency.CycleExactSequence
CRNT.Deficiency.DeficiencyOneScalarReduction
CRNT.Deficiency.DeficiencyZeroConsistency
CRNT.Design.LabeledBufferingStructure
CRNT.Design.LocalizationDifferential
CRNT.Design.MaxRPAIntegrator
CRNT.Design.ShinarFeinbergCrossClass
CRNT.Design.StrongBufferingFluxRPA
CRNT.Dynamics.GlobalPersistenceFrontier
CRNT.Dynamics.TierStrictUpwardPartner
CRNT.Dynamics.Trap
CRNT.Equilibria.SteadyStateFlux
CRNT.Equilibria.WegscheiderDeficiencyOne
CRNT.Flux.Cone
CRNT.Flux.Elementary
CRNT.Oscillation
CRNT.Oscillation.Analyze
CRNT.Oscillation.BanajiDependentReaction
CRNT.Oscillation.BanajiEndToEnd
CRNT.Oscillation.ChildSelectionReactivity
CRNT.Oscillation.CompatibilityAdapters
CRNT.Oscillation.ContinuousTimeAttraction
CRNT.Oscillation.DHopf
CRNT.Oscillation.DHopfOpenness
CRNT.Oscillation.DependentReaction
CRNT.Oscillation.DependentReactionPersistence
CRNT.Oscillation.DiagonalScaling
CRNT.Oscillation.FiedlerGlobalHopf
CRNT.Oscillation.FisherFullerScaling
CRNT.Oscillation.FloquetOrbitalStability
CRNT.Oscillation.FloquetPersistenceBridge
CRNT.Oscillation.FloquetPersistenceGeneral
CRNT.Oscillation.FloquetReturnBridge
CRNT.Oscillation.GlobalHopfContinuation
CRNT.Oscillation.GlobalHopfIndex
CRNT.Oscillation.GlobalHopfIndexTheorem
CRNT.Oscillation.GlobalHopfSpectralCrossing
CRNT.Oscillation.GreenJordanFoundations
CRNT.Oscillation.HalfPlanePolynomial
CRNT.Oscillation.HurwitzBordering
CRNT.Oscillation.Inheritance
CRNT.Oscillation.OscillationKernelBundle
CRNT.Oscillation.OscillatoryCoreEndToEnd
CRNT.Oscillation.ParameterRichDHopfContinuation
CRNT.Oscillation.ParameterRichGlobalHopf
CRNT.Oscillation.PlanarAdjacentReturnLoop
CRNT.Oscillation.PlanarCanonicalReturn
CRNT.Oscillation.PlanarDivergenceRegularity
CRNT.Oscillation.PlanarEndToEnd
CRNT.Oscillation.PlanarFloquetAttraction
CRNT.Oscillation.PlanarFlowBox
CRNT.Oscillation.PlanarFlowRegularity
CRNT.Oscillation.PlanarGreenGrid
CRNT.Oscillation.PlanarGreenJordanApproximation
CRNT.Oscillation.PlanarGreenRectangle
CRNT.Oscillation.PlanarJordanBoundaryCurrent
CRNT.Oscillation.PlanarJordanCrossingOrder
CRNT.Oscillation.PlanarJordanDyadic
CRNT.Oscillation.PlanarJordanSeparation
CRNT.Oscillation.PlanarJordanTopology
CRNT.Oscillation.PlanarLateSectionReturn
CRNT.Oscillation.PlanarLocalReturnLoops
CRNT.Oscillation.PlanarLocalReturns
CRNT.Oscillation.PlanarMinimalSet
CRNT.Oscillation.PlanarNoCrossing
CRNT.Oscillation.PlanarOneSidedReturns
CRNT.Oscillation.PlanarPoincareBendixson
CRNT.Oscillation.PlanarRecurrentSection
CRNT.Oscillation.PlanarReturnMonotonicity
CRNT.Oscillation.PlanarReturnOrdering
CRNT.Oscillation.PlanarReturnSequence
CRNT.Oscillation.PlanarSectionCoordinates
CRNT.Oscillation.PlanarSectionHitIsolation
CRNT.Oscillation.PlanarTransversalGeometry
CRNT.Oscillation.RankTwoPlanar
CRNT.Oscillation.ReactivityScaling
CRNT.Oscillation.ReducedKineticContinuation
CRNT.Oscillation.ReturnMapFamilyPersistence
CRNT.Oscillation.ScalarReturnMapFamilyPersistence
CRNT.Oscillation.ScalarReturnStability
CRNT.Oscillation.ScalarSectionInterpolation
CRNT.Oscillation.SimpleNegativeSpectrum
CRNT.Oscillation.SmoothGlobalHopf
CRNT.Oscillation.SpectralOpenness
CRNT.Oscillation.StableCodimOneDHopf
CRNT.Oscillation.VassenaAnalyticity
CRNT.Oscillation.VassenaContinuation
CRNT.Oscillation.VassenaCriteria
CRNT.Oscillation.VassenaEndToEnd
CRNT.Oscillation.VassenaFiniteDimHopf
CRNT.Oscillation.VassenaPrincipal
CRNT.Reduction.Intermediates
CRNT.Reduction.SingleIntermediateElimination
CRNT.Stochastic.DetailedBalance
CRNT.Translation.ResolvedComplexBalance
```

## LEDGER-sorry — 105 modules, with `sorry` counts

```
 10  CRNT.Basic.IsomorphismStructural
  9  CRNT.Kinetics.GeneralizedCycleExactSequence
  7  CRNT.Translation.ParallelStructural
  7  CRNT.Graph.Condensation
  7  CRNT.Equilibria.DetailedBalanceLinearStability
  7  CRNT.Equilibria.ComplexBalanceLinearStability
  7  CRNT.Basic.Isomorphism
  6  CRNT.Kinetics.GeneralizedNetwork
  6  CRNT.Equilibria.DirectedMatrixTreeProof
  6  CRNT.Design.EmergentConservation
  6  CRNT.Algebra.SteadyStateIdeal
  5  CRNT.Translation.Improper
  5  CRNT.Flux.IntegerTInvariant
  5  CRNT.Flux.ConformalDecomposition
  5  CRNT.Equilibria.GeneralizedComplexBalanceToric
  5  CRNT.Decomposition.Rank
  5  CRNT.Basic.IsomorphismKinetics
  4  CRNT.Theorems.DeficiencyOne.Theorem
  4  CRNT.Stochastic.ProductFormConverse
  4  CRNT.Stochastic.BirthDeathExhaustive
  4  CRNT.Multistationarity.WeakNormalityCriterion
  4  CRNT.Multistationarity.StrongConcordance
  4  CRNT.Kinetics.GeneralizedDeficiencyZeroCRNT
  4  CRNT.Kinetics.GeneralizedComplexBalanceObstruction
  4  CRNT.Graph.CirculationDecomposition
  4  CRNT.Flux.ExtremeRay
  4  CRNT.Equilibria.WegscheiderGenerators
  4  CRNT.Equilibria.MatrixTreeCofactor
  4  CRNT.Equilibria.GeneralizedTreeConstantCriterion
  4  CRNT.Equilibria.ComplexBalanceObstruction
  4  CRNT.Dynamics.GlobalAttractorTheorem
  4  CRNT.Design.ShinarFeinbergTreeFormula
  4  CRNT.Deficiency.TerminalKernelFaces
  3  CRNT.Stochastic.Absorbing
  3  CRNT.Multistationarity.WeakNormality
  3  CRNT.Multistationarity.InfluenceConcordance
  3  CRNT.Geometry.ConservativeCompatibility
  3  CRNT.Flux.CircuitTheory
  3  CRNT.Equilibria.WegscheiderInteger
  3  CRNT.Equilibria.TreePotentialIntegration
  3  CRNT.Equilibria.TreeConstantCriterion
  3  CRNT.Equilibria.ConservationCoordinates
  3  CRNT.Design.MaxRPAStochastic
  3  CRNT.Deficiency.TerminalKernelCone
  3  CRNT.Deficiency.CycleSplitting
  2  CRNT.Translation.SourceCoefficientEquivalence
  2  CRNT.Translation.ParallelAggregation
  2  CRNT.Translation.LinearConjugacySpectral
  2  CRNT.Translation.LinearConjugacy
  2  CRNT.Theorems.DeficiencyOne.DegreeExistence
  2  CRNT.Stability.BDCPrincipalMinors
  2  CRNT.Stability.BDCCauchyBinetProof
  2  CRNT.Reduction.IntermediateSchurComplement
  2  CRNT.Multistationarity.TrueChemistrySRCriterion
  2  CRNT.Multistationarity.StrongConcordanceStability
  2  CRNT.Multistationarity.Normality
  2  CRNT.Multistationarity.DeficiencyObstruction
  2  CRNT.Multistationarity.ConcordanceConverse
  2  CRNT.Kinetics.GeneralizedDeficiencyZeroProof
  2  CRNT.Kinetics.GeneralizedDeficiencyZeroExistence
  2  CRNT.Kinetics.GeneralizedDeficiencyZero
  2  CRNT.Equilibria.TreeConstants
  2  CRNT.Equilibria.GeneralizedComplexBalanceGeometry
  2  CRNT.Equilibria.DetailedBalanceToric
  2  CRNT.Equilibria.DetailedBalanceEntropy
  2  CRNT.Equilibria.ComplexBalanceGeometry
  2  CRNT.Design.MinimalForm
  2  CRNT.Design.MaxRPA
  2  CRNT.Deficiency.TerminalKernelDimension
  2  CRNT.Deficiency.LinkageCoupling
  2  CRNT.Deficiency.DeficiencyOneLinkageScalars
  2  CRNT.Decomposition.Deficiency
  1  CRNT.Translation.SourceComplexes
  1  CRNT.Translation.ImproperComplexBalance
  1  CRNT.Translation.DeficiencyImprovement
  1  CRNT.Theorems.DeficiencyZero.TreeConstantProofComplete
  1  CRNT.Theorems.DeficiencyZero.TreeConstantConstruction
  1  CRNT.Theorems.DeficiencyZero.Characterization
  1  CRNT.Theorems.DeficiencyOne.WeaklyReversibleExistence
  1  CRNT.Subnetwork.EmbeddedNetwork
  1  CRNT.Stochastic.FirstOrderFoster
  1  CRNT.Stochastic.ConservativeClasses
  1  CRNT.Stability.RobustLyapunov
  1  CRNT.Stability.BDCStructuralNonsingularity
  1  CRNT.Multistationarity.TrueChemistrySRGraph
  1  CRNT.Multistationarity.NormalityTerminal
  1  CRNT.Multistationarity.Discordance
  1  CRNT.LinearAlgebra.OrientedMatroidNondegeneracy
  1  CRNT.Kinetics.GeneralizedNondegeneracy
  1  CRNT.Kinetics.GeneralizedDeficiencyComparison
  1  CRNT.Kinetics.GeneralizedBirchExistence
  1  CRNT.Graph.PositiveCirculation
  1  CRNT.Equilibria.WegscheiderDeficiency
  1  CRNT.Equilibria.TreeConstantKernelBasis
  1  CRNT.Equilibria.TreeConstantBinomials
  1  CRNT.Equilibria.LinkageComplexBalance
  1  CRNT.Equilibria.BoundarySiphon
  1  CRNT.Design.ShinarFeinbergTheorem
  1  CRNT.Design.Localization
  1  CRNT.Design.LabeledBufferingRPA
  1  CRNT.Design.EmergentCycles
  1  CRNT.Deficiency.ExactSequence
  1  CRNT.Deficiency.DeficiencyOneMonotonicity
  1  CRNT.Algebra.PositiveTorusIdeals
  1  CRNT.Algebra.DeficiencyIdeal
```

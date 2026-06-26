-- Deriving handlers used by example and generated networks (`deriving Fintype`)
import Mathlib.Tactic.DeriveFintype

-- General-purpose combinatorics (decidable undirected cycles; digraph excess function)
import CRNT.Combinatorics.DecidableCycle
import CRNT.Combinatorics.DigraphExcess

-- Basic CRN data structures
import CRNT.Basic.Complex
import CRNT.Basic.Reaction
import CRNT.Basic.Network

-- Reaction graph: reachability, weak reversibility, linkage classes
import CRNT.Graph.Reachability
import CRNT.Graph.WeakReversibility
import CRNT.Graph.CycleCover
import CRNT.Graph.LinkageClass
import CRNT.Graph.Crossing

-- Decision procedures: decidable bounded reachability, weak reversibility, linkage classes,
-- strong linkage classes, and rank/deficiency certificates over ℚ
import CRNT.Decision.Reachability
import CRNT.Decision.Linkage
import CRNT.Decision.StrongLinkage
import CRNT.Decision.DirectedReachability
import CRNT.Decision.Rank
import CRNT.Decision.Tactic
import CRNT.Decision.RankExact
import CRNT.Decision.ACRCheck
import CRNT.Decision.GaussianRank
import CRNT.Decision.ExactDeficiency
import CRNT.Decision.LinkageDeficiencyExact
import CRNT.Decision.ComputableDeficiency
import CRNT.Decision.DeficiencyOneConditionsDecide
import CRNT.Decision.MinorSearch
import CRNT.Decision.DeficiencyZeroTactic

-- Stoichiometry: reaction vectors, subspace, rank
import CRNT.Stoich.Vector
import CRNT.Stoich.Subspace

-- Linear-algebra building blocks (Perron–Frobenius positivity; dot-product orthogonality;
-- finrank subadditivity over finite suprema; sign vectors of subspaces)
import CRNT.LinearAlgebra.PerronFrobenius
import CRNT.LinearAlgebra.DetCycleCover
import CRNT.LinearAlgebra.OrthogonalComplement
import CRNT.LinearAlgebra.FinrankSup
import CRNT.LinearAlgebra.SignVector
import CRNT.LinearAlgebra.OrientedMatroid
import CRNT.LinearAlgebra.ConformalDecomposition
import CRNT.LinearAlgebra.Substochastic
import CRNT.LinearAlgebra.PowerProductMono
import CRNT.LinearAlgebra.PowerProductMonoFinset

-- Convex geometry: generated cones, dual cones, Newton polytopes (endotactic / toric-inclusion routes)
import CRNT.Geometry.PolyhedralFan
import CRNT.Geometry.Endotactic
import CRNT.Geometry.ToricFan
import CRNT.Geometry.ZeroSeparatingSurface
import CRNT.Geometry.ConeFace
import CRNT.Geometry.ZeroSeparatingCurve2D
import CRNT.Geometry.ToricFieldPolar
import CRNT.Geometry.ToricFieldPolarMulti
import CRNT.Geometry.FaithfulCurve
import CRNT.Geometry.FaithfulCurveExistence
import CRNT.Geometry.FaithfulCurveGeneral
import CRNT.Geometry.FaithfulCurve2D
import CRNT.Geometry.FaithfulCurve2DFan
import CRNT.Geometry.ZeroSeparatingInduction
import CRNT.Geometry.FanRefinement
import CRNT.LinearAlgebra.LogSumInj
import CRNT.Analysis.FixedPoint
import CRNT.Analysis.Sperner
import CRNT.Analysis.Sperner2D
import CRNT.Analysis.Sperner2DMulti
import CRNT.Analysis.SpernerTriangulation
import CRNT.Analysis.SpernerMultiIncidence
import CRNT.Analysis.SpernerGridMulti
import CRNT.Analysis.SpernerGridGeometric
import CRNT.Analysis.SpernerLattice
import CRNT.Analysis.SpernerLatticeColoring
import CRNT.Analysis.SpernerLatticeIncidence
import CRNT.Analysis.SpernerLatticeIncidenceHV
import CRNT.Analysis.SpernerLatticeCellColor
import CRNT.Analysis.SpernerLatticeDoorGraph
import CRNT.Analysis.SpernerLatticeBipartite
import CRNT.Analysis.SpernerLatticeNeighbor
import CRNT.Analysis.SpernerLatticeFullGraph
import CRNT.Analysis.SpernerLatticeBoundary
import CRNT.Analysis.SpernerLatticeCellDegree
import CRNT.Analysis.SpernerLatticeSperner
import CRNT.Analysis.SpernerLatticeGeometric
import CRNT.Analysis.SpernerSimplexLimit
import CRNT.Analysis.SpernerSimplexLimitN
import CRNT.Analysis.SpernerBrouwer2D
import CRNT.Analysis.SpernerLatticeN
import CRNT.Analysis.SpernerNGeometric
import CRNT.Analysis.SpernerNParity
import CRNT.Analysis.SpernerNIncidence
import CRNT.Analysis.SpernerNBaseShift
import CRNT.Analysis.SpernerNBoundary
import CRNT.Analysis.SpernerNDoor
import CRNT.Analysis.SpernerNBoundaryCell
import CRNT.Analysis.SpernerNBoundaryCorr
import CRNT.Analysis.SpernerNFintype
import CRNT.Analysis.SpernerNFacetCount
import CRNT.Analysis.SpernerNSperner
import CRNT.Analysis.SpernerNBoundaryCount
import CRNT.Analysis.SpernerNHandshake
import CRNT.Analysis.SpernerNInterior
import CRNT.Analysis.SpernerNClose
import CRNT.Analysis.SpernerBrouwerN
import CRNT.Analysis.BrouwerConvex
import CRNT.Analysis.ConvexProjection
import CRNT.Analysis.BrouwerZero
import CRNT.Analysis.SpernerGrid

-- Kinetics: concentrations, mass action, and the general kinetics abstraction
import CRNT.Kinetics.Concentration
import CRNT.Kinetics.MassAction
import CRNT.Kinetics.MassActionJacobian
import CRNT.Kinetics.General
import CRNT.Kinetics.Generalized

-- Open networks: inflow/outflow pseudo-reactions and the fully open extension
import CRNT.Open.Augmentation
import CRNT.Open.Deficiency
import CRNT.Open.Boundary
import CRNT.Open.PartialOpen

-- Equilibria: steady states, compatibility classes, complex balancing
import CRNT.Equilibria.SteadyState
import CRNT.Equilibria.CompatibilityClass
import CRNT.Equilibria.ComplexBalanced

-- Dynamics: algebraic (complex-space) form of mass-action kinetics; ODE regularity and
-- local existence; LaSalle invariance
import CRNT.Dynamics.MassActionAlgebra
import CRNT.Dynamics.MassActionField
import CRNT.Dynamics.LaSalle
import CRNT.Dynamics.FlowConstruction
import CRNT.Dynamics.Monotone
import CRNT.Dynamics.RouthHurwitz
import CRNT.Dynamics.Hurwitz
import CRNT.Dynamics.HopfGate
import CRNT.Dynamics.RouthHurwitz4
import CRNT.Dynamics.QSSA
import CRNT.Dynamics.Nagumo
import CRNT.Dynamics.Tikhonov
import CRNT.Dynamics.MichaelisMenten
import CRNT.Dynamics.Fenichel
import CRNT.Dynamics.FenichelManifold
import CRNT.Dynamics.FenichelSlowDrift
import CRNT.Dynamics.MichaelisMentenManifold
import CRNT.Dynamics.MichaelisMentenReduced
import CRNT.Dynamics.MichaelisMentenDepletion

-- Deficiency
import CRNT.Deficiency.Definition
import CRNT.Deficiency.Consistent
import CRNT.Deficiency.ConsistentWR
import CRNT.Deficiency.CutPair
import CRNT.Deficiency.Regular
import CRNT.Deficiency.Signature
import CRNT.Deficiency.KernelDimension
import CRNT.Deficiency.DeficiencyOne
import CRNT.Deficiency.LinkageDeficiency
import CRNT.Deficiency.DeficiencyOneHypotheses
import CRNT.Deficiency.DeficiencyOneStructure
import CRNT.Deficiency.IncidenceBlock
import CRNT.Deficiency.DeficiencyOneDecomp
import CRNT.Deficiency.DeficiencyOneLocalize
import CRNT.Deficiency.LogMonomialRatio
import CRNT.Deficiency.ComplexBalancedRatio
import CRNT.Deficiency.SignedDrainage
import CRNT.Deficiency.KineticExcess
import CRNT.Deficiency.ExcessPositivity
import CRNT.Deficiency.LevelSetSign
import CRNT.Deficiency.StructuredPreimage
import CRNT.Deficiency.DeficientClassKernel
import CRNT.Deficiency.TerminalSLC
import CRNT.Deficiency.KineticBlock
import CRNT.Deficiency.SteadyStateKernel
import CRNT.Deficiency.DeficiencyOneLine
import CRNT.Deficiency.ClassConservation
import CRNT.Deficiency.Confluence
import CRNT.Deficiency.Shelf
import CRNT.Deficiency.DeficiencyOneAlgorithm
import CRNT.Deficiency.DOAForward
import CRNT.Deficiency.Colinearity
import CRNT.Deficiency.ColinearityClasses
import CRNT.Deficiency.AdvancedDeficiencyAlgorithm
import CRNT.Deficiency.PerClassKernel
import CRNT.Deficiency.KernelDimensionBound
import CRNT.Deficiency.PerClassKernelPos
import CRNT.Deficiency.PerClassKernelUnique
import CRNT.Deficiency.KernelDimensionWR
import CRNT.Deficiency.RangeKineticWR
import CRNT.Deficiency.ClosedSetKernel
import CRNT.Deficiency.TerminalSLCKernel
import CRNT.Deficiency.TerminalKernelBound
import CRNT.Deficiency.TerminalReachable
import CRNT.Deficiency.Drainage
import CRNT.Deficiency.HigherDeficiency

-- Theorem statement interfaces and proved components
import CRNT.Theorems.DeficiencyZero.Statement
import CRNT.Theorems.DeficiencyZero.PositiveKernel
import CRNT.Theorems.DeficiencyZero.Birch
import CRNT.Theorems.DeficiencyZero.BirchExistence
import CRNT.Theorems.DeficiencyZero.Toric
import CRNT.Theorems.DeficiencyZero.Existence
import CRNT.Theorems.DeficiencyZero.Dissipation
import CRNT.Theorems.DeficiencyZero.Stability
import CRNT.Theorems.DeficiencyZero.Confinement
import CRNT.Theorems.DeficiencyZero.Lyapunov
import CRNT.Theorems.DeficiencyZero.AsymptoticStability
import CRNT.Theorems.DeficiencyOne.Statement
import CRNT.Theorems.DeficiencyOne.LogRatioUniqueness
import CRNT.Theorems.DeficiencyOne.ToricReduction
import CRNT.Theorems.DeficiencyOne.Uniqueness
import CRNT.Theorems.DeficiencyOne.MultiClass
import CRNT.Theorems.DeficiencyOne.Existence
import CRNT.Theorems.DeficiencyOne.ExistenceDynamical

-- Multistationarity: species-reaction graph, injectivity criteria
import CRNT.Multistationarity.SRGraph
import CRNT.Multistationarity.SRGraphCriterion
import CRNT.Multistationarity.SignedSRGraph
import CRNT.Multistationarity.SRGraphCycleDict
import CRNT.Multistationarity.Injectivity
import CRNT.Multistationarity.Concordance
import CRNT.Multistationarity.Capacity
import CRNT.Multistationarity.JacobianInjectivity
import CRNT.Multistationarity.PMatrix
import CRNT.Multistationarity.PMatrixSchur
import CRNT.Multistationarity.PMatrixSignature
import CRNT.Multistationarity.GaleNikaido
import CRNT.Multistationarity.GaleNikaidoBox
import CRNT.Multistationarity.PMatrixUnivalence
import CRNT.Multistationarity.GaleNikaidoUniv
import CRNT.Multistationarity.StoichChart
import CRNT.Multistationarity.ReducedJacobian
import CRNT.Multistationarity.Toric

-- Design: robustness and special equilibria
import CRNT.Design.ACR
import CRNT.Design.ACRUnconditional
import CRNT.Design.ACRCrossClass
import CRNT.Design.Adaptation

-- Persistence: Petri-net siphons; siphon-face tangency; single-linkage-class global stability
import CRNT.Dynamics.Siphon
import CRNT.Dynamics.SiphonConservation
import CRNT.Dynamics.ConservationLaw
import CRNT.Dynamics.Persistence
import CRNT.Dynamics.GlobalStability
import CRNT.Dynamics.ForwardInvariance
import CRNT.Dynamics.PersistenceGAC
import CRNT.Dynamics.PersistenceTheorem
import CRNT.Dynamics.PersistenceConfined
import CRNT.Dynamics.ConfinedInvariance
import CRNT.Dynamics.BoundaryDescent
import CRNT.Dynamics.StrictInflow
import CRNT.Dynamics.NegativeInvariance
import CRNT.Dynamics.BoundaryOmegaSiphon
import CRNT.Dynamics.CriticalSiphonOmega
import CRNT.Dynamics.NoCriticalSiphonPersistence
import CRNT.Dynamics.GACNoCriticalSiphon
import CRNT.Dynamics.GACOmegaPositive
import CRNT.Dynamics.SingleLinkageGAC
import CRNT.Dynamics.IsolatedInvariant
import CRNT.Dynamics.DifferentialInclusion
import CRNT.Dynamics.DissipationBound
import CRNT.Dynamics.ButlerMcGehee
import CRNT.Dynamics.ToricInclusion
import CRNT.Dynamics.ToricEmbedding
import CRNT.Dynamics.ToricEmbeddingOrder
import CRNT.Dynamics.ToricEmbeddingWR
import CRNT.Dynamics.ZeroSeparating
import CRNT.Dynamics.Viability
import CRNT.Dynamics.FirstExit
import CRNT.Dynamics.SublevelInvariant
import CRNT.Dynamics.SublevelNagumo
import CRNT.Dynamics.ClosedSetNagumo
import CRNT.Dynamics.SupportDiniBridge
import CRNT.Dynamics.PolyRegionInvariant
import CRNT.Dynamics.PolyRegionStrictInvariant
import CRNT.Dynamics.ThmBGenuine
import CRNT.Dynamics.EndotacticPermanence
import CRNT.Dynamics.FacetRepulsion

-- Stochastic CRN: Anderson–Craciun–Kurtz product-form objects
import CRNT.Stochastic.ProductForm
import CRNT.Stochastic.Generator
import CRNT.Stochastic.CTMC
import CRNT.Stochastic.JumpKernel
import CRNT.Stochastic.Kernel
import CRNT.Stochastic.KernelInvariant
import CRNT.Stochastic.KernelStationary
import CRNT.Stochastic.KernelIrreducible
import CRNT.Stochastic.KernelNormalized
import CRNT.Stochastic.KernelMaximalRegion

-- Network composition
import CRNT.Compose.Interconnect
import CRNT.Compose.InterconnectKinetics
import CRNT.Compose.InterconnectSiphon
import CRNT.Compose.InterconnectMonostationary
import CRNT.Compose.StoichIndependent

-- Deficiency-one decidable structural conditions
import CRNT.Deficiency.DeficiencyOneDecide

-- Interoperability and certificate workflow
import CRNT.Interop.Certificates
import CRNT.Interop.NetworkData
import CRNT.Interop.Analysis

/-!
# `crnt-lean`: Chemical Reaction Network Theory in Lean 4

Top-level import for the stable core of the `CRNT` library. It re-exports the basic
CRN data structures, the reaction-graph and stoichiometry layers, mass-action
kinetics, the deficiency definition, and the deficiency-zero statement interface.

Experimental modules and theorem stubs are **not** re-exported here. Importing
`CRNT` brings in no axioms beyond those of Mathlib and no `sorry`.
-/

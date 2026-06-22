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

-- Stoichiometry: reaction vectors, subspace, rank
import CRNT.Stoich.Vector
import CRNT.Stoich.Subspace

-- Linear-algebra building blocks (Perron–Frobenius positivity; dot-product orthogonality;
-- finrank subadditivity over finite suprema; sign vectors of subspaces)
import CRNT.LinearAlgebra.PerronFrobenius
import CRNT.LinearAlgebra.OrthogonalComplement
import CRNT.LinearAlgebra.FinrankSup
import CRNT.LinearAlgebra.SignVector
import CRNT.LinearAlgebra.Substochastic
import CRNT.LinearAlgebra.PowerProductMono
import CRNT.LinearAlgebra.PowerProductMonoFinset
import CRNT.LinearAlgebra.LogSumInj

-- Kinetics: concentrations, mass action, and the general kinetics abstraction
import CRNT.Kinetics.Concentration
import CRNT.Kinetics.MassAction
import CRNT.Kinetics.General
import CRNT.Kinetics.Generalized

-- Open networks: inflow/outflow pseudo-reactions and the fully open extension
import CRNT.Open.Augmentation
import CRNT.Open.Deficiency
import CRNT.Open.Boundary

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
import CRNT.Dynamics.QSSA

-- Deficiency
import CRNT.Deficiency.Definition
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

-- Multistationarity: species-reaction graph, injectivity criteria
import CRNT.Multistationarity.SRGraph
import CRNT.Multistationarity.SRGraphCriterion
import CRNT.Multistationarity.Injectivity

-- Design: robustness and special equilibria
import CRNT.Design.ACR
import CRNT.Design.Adaptation

-- Persistence: Petri-net siphons
import CRNT.Dynamics.Siphon

-- Network composition
import CRNT.Compose.Interconnect

-- Deficiency-one decidable structural conditions
import CRNT.Deficiency.DeficiencyOneDecide

-- Interoperability and certificate workflow
import CRNT.Interop.Certificates

/-!
# `lean-crnt`: Chemical Reaction Network Theory in Lean 4

Top-level import for the stable core of the `CRNT` library. It re-exports the basic
CRN data structures, the reaction-graph and stoichiometry layers, mass-action
kinetics, the deficiency definition, and the deficiency-zero statement interface.

Experimental modules and theorem stubs are **not** re-exported here. Importing
`CRNT` brings in no axioms beyond those of Mathlib and no `sorry`.
-/

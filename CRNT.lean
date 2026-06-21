-- Deriving handlers used by example and generated networks (`deriving Fintype`)
import Mathlib.Tactic.DeriveFintype

-- Basic CRN data structures
import CRNT.Basic.Complex
import CRNT.Basic.Reaction
import CRNT.Basic.Network

-- Reaction graph: reachability, weak reversibility, linkage classes
import CRNT.Graph.Reachability
import CRNT.Graph.WeakReversibility
import CRNT.Graph.LinkageClass

-- Decision procedures: decidable bounded reachability, weak reversibility, linkage classes,
-- strong linkage classes, and rank/deficiency certificates over ℚ
import CRNT.Decision.Reachability
import CRNT.Decision.Linkage
import CRNT.Decision.StrongLinkage
import CRNT.Decision.DirectedReachability
import CRNT.Decision.Rank
import CRNT.Decision.Tactic

-- Stoichiometry: reaction vectors, subspace, rank
import CRNT.Stoich.Vector
import CRNT.Stoich.Subspace

-- Linear-algebra building blocks (Perron–Frobenius positivity; dot-product orthogonality;
-- finrank subadditivity over finite suprema)
import CRNT.LinearAlgebra.PerronFrobenius
import CRNT.LinearAlgebra.OrthogonalComplement
import CRNT.LinearAlgebra.FinrankSup

-- Kinetics: concentrations, mass action, and the general kinetics abstraction
import CRNT.Kinetics.Concentration
import CRNT.Kinetics.MassAction
import CRNT.Kinetics.General

-- Open networks: inflow/outflow pseudo-reactions and the fully open extension
import CRNT.Open.Augmentation

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

-- Deficiency
import CRNT.Deficiency.Definition
import CRNT.Deficiency.KernelDimension
import CRNT.Deficiency.DeficiencyOne
import CRNT.Deficiency.LinkageDeficiency
import CRNT.Deficiency.DeficiencyOneHypotheses
import CRNT.Deficiency.TerminalSLC
import CRNT.Deficiency.KineticBlock
import CRNT.Deficiency.SteadyStateKernel
import CRNT.Deficiency.DeficiencyOneLine

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

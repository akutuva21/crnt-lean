# Multistationarity, robustness, and composition

This document describes the layer of the `CRNT` library that asks, beyond existence and uniqueness
of equilibria: when can a network admit *several* positive steady states in one stoichiometric
class, when is an output concentration *robust* to rate constants and initial conditions, what
happens when a network is opened to material exchange with its surroundings, and how do the
structural invariants behave when two networks are *composed* over a shared species pool. It is the
top structural layer of the [architecture](architecture.md), built on the foundations, kinetics,
deficiency, and equilibria layers below it.

The questions and the named criteria are Feinberg's reaction-network theory and its descendants:
injectivity and the species–reaction graph (Gheorghe Craciun & Martin Feinberg, *Multiple
Equilibria in Complex Chemical Reaction Networks: I/II*); the toric / sign-condition reduction of
multistationarity (Stefan Müller et al., and Mercedes Pérez-Millán, Alicia Dickenstein, Anne Shiu &
Carsten Conradi, *Chemical Reaction Systems with Toric Steady States*); absolute concentration
robustness (Guy Shinar & Martin Feinberg, *Structural Sources of Robustness in Biochemical Reaction
Networks*); and antithetic integral feedback (Corentin Briat, Ankit Gupta & Mustafa Khammash,
*Antithetic Integral Feedback Ensures Robust Perfect Adaptation in Noisy Biomolecular Networks*).
Everything reported here is machine-checked, `sorry`-free, and introduces no axioms beyond
Mathlib's.

Several of the classical theorems are present as their *uniqueness / robustness* halves together
with the structural substrate they are stated over; the analytic or existence halves they rest on
are not in this development, and the boundaries are stated as plain facts about coverage below.

## Injectivity and the species–reaction graph

A network is **monostationary** when each positive stoichiometric compatibility class contains at
most one positive steady state. The structural property that guarantees this is *injectivity* of
the vector field.

- **`Kinetics.InjectiveOnClass K x₀`** (`CRNT/Multistationarity/Injectivity.lean`) holds when the
  induced vector field `K.vectorField` is injective (`Set.InjOn`) on the positive compatibility
  class of `x₀`; **`Kinetics.Injective K`** is injectivity on every positive class. This is the
  Craciun–Feinberg notion of injectivity, stated over an arbitrary `Kinetics`.

- **`Kinetics.InjectiveOnClass.subsingleton_steadyState`** is the easy, fully proved direction:
  two steady states lying in one positive class are both zeros of the field, so injectivity on that
  class forces them equal: at most one positive steady state per class.
  **`Kinetics.Injective.subsingleton_steadyState`** is the same for a globally injective kinetics,
  and **`massAction_subsingleton_steadyState_of_injective`** is the mass-action corollary.

The combinatorial criterion that is supposed to *establish* injectivity is read off the
species–reaction graph.

- **`Network.srGraph N`** (`CRNT/Multistationarity/SRGraph.lean`) is the undirected bipartite
  **species–reaction graph** on the vertex type `S ⊕ N.R`: an edge joins a species `s` to a
  reaction `r` exactly when `s` occurs in `r` (**`Network.OccursIn`**: nonzero stoichiometry as a
  source or target). The adjacency is decidable; `srGraph_adj_iff` characterises it, and
  `srGraph_not_adj_species` / `srGraph_not_adj_reaction` record the absence of same-side edges.
  **`srGraph_isBipartiteWith`** / **`srGraph_isBipartite`** prove bipartiteness with the species and
  reactions as the two parts.

- The bipartite alternation underlying the cycle bookkeeping is in
  `CRNT/Multistationarity/SRGraphCriterion.lean`. **`srGraph_getVert_isLeft_succ`** and
  **`srGraph_getVert_isLeft`** show every walk strictly alternates sides; from these,
  **`srGraph_even_length_of_closed`** and **`srGraph_even_length_of_isCycle`** prove every closed
  walk (and every cycle) has even length, **`srGraph_not_isCycle_of_odd_length`** is the
  contrapositive (no odd cycle), and **`srGraph_four_le_egirth`** gives that the SR-graph is
  triangle-free with edge-girth at least four.

- The signed refinement is in `CRNT/Multistationarity/SignedSRGraph.lean`. **`Network.signedEdge`**
  is the `SignType` sign of the reaction vector's coordinate at a species–reaction incidence;
  **`Network.NetChange`** and **`signedEdge_ne_zero_iff_netChange`** relate a nonzero sign to a net
  stoichiometric change, and **`netChange_imp_occursIn`** shows a signed incidence is in particular
  an unsigned one. **`Network.walkSign`** is the product of incidence signs along a walk, with the
  full algebra `walkSign_nil`, `walkSign_cons`, `walkSign_append` (multiplicativity under
  concatenation), and `walkSign_copy`. **`Network.negEdgeCount`** counts negative incidences, and
  **`walkSign_eq_negOnePow_negEdgeCount`** shows the walk sign is `(-1)` to that count when no step
  is a zero incidence. **`Network.CycleSignNegative`** names the sign-`-1` cycle predicate, and
  **`cycle_even_length`** re-exports cycle evenness so signs and parity range over an even edge set.

**Coverage.** What is proved is the easy direction of injectivity (injective ⇒ at most one steady
state per class) together with the complete combinatorial substrate of the SR-graph: bipartiteness,
cycle parity, walk-sign algebra, and the signed-cycle parity predicate. The full Craciun–Feinberg
SR-graph criterion, that the cycle structure (parity of cycles, even cycles sharing terminal
edges) implies injectivity of the mass-action vector field, requires relating the
signed-cycle data to the sign of the mass-action Jacobian determinant through a
determinant-via-cycle-cover (matching) expansion. That Jacobian-determinant expansion is not done
here, so the criterion's combinatorial substrate is present but the criterion itself is not closed.

## The P-matrix layer

The linear-algebraic engine behind the Jacobian form of the injectivity criterion is the P-matrix.

- **`Matrix.IsPMatrix M`** (`CRNT/Multistationarity/PMatrix.lean`) is a square matrix over a
  `LinearOrderedField` all of whose principal minors are positive. The central reindexing fact is
  **`Matrix.IsPMatrix.submatrix_det_pos`**: for any *injective* index map `f`, `(M.submatrix f f).det`
  is positive, subsuming the `Finset`-selected principal-submatrix definition. From it follow
  **`det_pos`**, **`det_ne_zero`**, **`isUnit_det`** (nonsingularity), **`submatrix_isPMatrix`**
  (closure under principal submatrices), and **`diag_pos`** (positive diagonal). Over `ℝ`,
  **`Matrix.PosDef.isPMatrix`** shows a symmetric positive-definite matrix is a P-matrix.

**Coverage.** The matrix-theoretic P-matrix layer is complete and stands as an upstreamable Mathlib
unit. The Gale–Nikaido global-injectivity payoff (that a map whose Jacobian is everywhere a
P-matrix is globally injective) is not available: it is absent from Mathlib and is not proved here.
The P-matrix layer therefore supplies the nonsingularity facts but not the global-injectivity
conclusion.

## Toric steady states

For networks whose steady-state equations are *binomial*, the positive steady states form a toric
(log-linear) set, and multistationarity reduces to a sign condition on two subspaces.

- **`ToricSteadyStates S T xstar c`** (`CRNT/Multistationarity/Toric.lean`) is the positive `x` that
  is stoichiometrically compatible (`x − c ∈ S`) and whose log-ratio `log(x/xstar)` is orthogonal to
  the kinetic-order subspace `T` (lies in `orthSum T`). This log-linear set is taken here *as the
  definition* of the steady-state set. **`mem_toricSteadyStates`** unfolds membership.

- **`toric_nonempty_self`** gives the monomial parametrization in the single-subspace case `T = S`:
  every positive class contains a toric steady state, the complex-balanced equilibrium produced by
  Birch existence.

- **`SignIncompatible S T`** is the failure of the Müller sign condition (a nonzero `u ∈ S` sharing
  its coordinatewise sign pattern with some `v ∈ T`), and **`signCompatible_iff_not_signIncompatible`**
  states that `SignCompatible` is exactly its absence (`σ(S) ∩ σ(T) = {0}`).

- **`toric_subsingleton_of_signCompatible`** is the proved uniqueness half of the Müller reduction:
  sign-compatibility of `S` with the kinetic orthogonal complement `orthSum T` forces the toric
  steady-state set in each positive class to be a subsingleton: multistationarity ruled out.
  **`toric_subsingleton_self`** and **`toric_unique_self`** are the mass-action corollaries at
  `T = S`, recovering classical complex-balanced existence and uniqueness for every rate constant.

**Coverage.** Binomiality of the steady-state equations is taken as the *definition* of the toric
set; deriving it from the network's reaction structure (the toric-ideal step) needs binomial-ideal
machinery not in this development. The uniqueness half of the sign-condition reduction is proved;
the converse, constructing two distinct toric steady states when sign-compatibility fails, is the
degree-theoretic half and needs topological degree (Brouwer), which is absent here.

## Absolute concentration robustness

A network has **absolute concentration robustness** in a species when that species' steady-state
concentration is the same value at every positive mass-action steady state, for every choice of
rate constants.

- **`Network.HasACR N s`** (`CRNT/Design/ACR.lean`) is that predicate: a single value `v` with
  `x s = v` at every positive steady state, for all rate constants.

- **`Network.ShinarFeinbergHypotheses N s`** is the Shinar–Feinberg structural hypothesis bundle: a
  deficiency-one network with two non-terminal complexes `c`, `d` lying in distinct linkage classes
  and differing in exactly the single species `s`.

- The algebraic lever is fully proved: **`monomial_cross_of_differ`** is the cross-multiplied
  monomial identity for complexes agreeing away from `s`; **`pin_xs_of_lt`** and
  **`pin_of_pinned_ratio`** show a *pinned* monomial ratio of `c` and `d` forces the species-`s`
  concentrations to coincide. **`ShinarFeinbergHypotheses.PinnedRatio`** names the deficiency-one
  content (the pinned ratio across all positive steady states) and **`HasACR.of_pinnedRatio`**
  reduces `HasACR s` to that input plus a witness steady state.

- The deficiency-one machinery bearing on the pinned ratio is in `CRNT/Design/ACRUnconditional.lean`.
  **`logMonomialRatio_eqOn_linkageClass`** is the keystone: the log-monomial ratio `Φ` is constant on
  *every* linkage class of a deficiency-one network. **`monomialRatio_pinned_of_sameClass`** is its
  exponentiated *same-class* form. The remaining cross-class content, equality of the two
  a-priori-independent per-class constants for complexes in *distinct* classes, is isolated as
  **`ShinarFeinbergHypotheses.CrossClassRatioPinned`**, with **`monomial_cross_of_crossClassRatioPinned`**
  exponentiating it to the pinned ratio and **`HasACR.of_crossClassRatioGap`** deriving ACR from it.

- The cross-class equality is analysed through the toric condition in `CRNT/Design/ACRCrossClass.lean`.
  **`Network.ToricRelated x y`** names orthogonality of the log-ratio vector to the stoichiometric
  subspace; **`logMonomialRatio_const_along_reaction_of_toric`** and **`logMonomialRatio_eqOn_linked`**
  prove `Φ` is constant along reactions and across whole linkage classes under that condition.
  **`crossClassRatio_eq_iff_robust`** pins the residual obligation exactly: for two complexes
  differing only at `s`, the cross-class equality `Φ(c) = Φ(d)` holds **iff** `x s = y s`: the
  difference collapses to the single coordinate `(c_s − d_s)·(log x_s − log y_s)`.
  **`HasACR.of_speciesRobust`** then re-derives full `HasACR s` from a precisely-named species-
  robustness hypothesis fed through that equivalence.

**Coverage.** The complete chain (pinning lever, same-class constancy of `Φ`, the toric per-reaction
and per-class constancy, and the reduction of the cross-class equality to the crisp statement
`x s = y s`) is proved. The single missing step is the cross-class equality itself: forcing
robustness from non-terminality and the deficiency-one cut structure. It is consumed as the named
input `CrossClassRatioPinned` (equivalently the robustness hypothesis of `HasACR.of_speciesRobust`)
rather than discharged, because it rests on the deficiency-one characterization of the positive
steady-state set, which is not yet available here. The Shinar–Feinberg theorem is therefore present
as an honest reduction to one bridging equality, not as an unconditional statement.

## Antithetic integral feedback and perfect adaptation

The antithetic integral feedback motif realises *perfect adaptation*: a sensed output pinned to a
setpoint independent of every other rate constant.

- `CRNT/Design/Adaptation.lean` models the Briat–Gupta–Khammash motif as a concrete `Network` over
  three species (controller species `Z1`, `Z2` and output `X`) with reactions `ref : 0 → Z1`,
  `sense : X → X + Z2`, and `seq : Z1 + Z2 → 0`. The plant-coupling actuation reaction is omitted so
  the motif is a drop-in, plant-agnostic controller.

- **`setpoint`** is the integral-feedback property, fully proved: at any mass-action steady state the
  two controller production rates balance, `κ.sense · x_X = κ.ref`. **`setpoint_value`** solves it to
  **`x_X = κ.ref / κ.sense`**: the output is pinned by the reference and sensing rates alone,
  independent of the sequestration rate and of any plant dynamics.

**Coverage.** The setpoint and its value are proved unconditionally for this concrete network. This
is the steady-state (algebraic) statement of perfect adaptation; the dynamical claim that
trajectories *converge* to the setpoint is not part of this module.

## Open (CFSTR) extensions

A closed network conserves total amounts along its stoichiometry; a continuous-flow stirred-tank
reactor exchanges material with its surroundings. Adjoining a synthesis `0 → s` and a degradation
`s → 0` for every species gives the **fully open extension**.

- **`Network.fullyOpen N`** (`CRNT/Open/Augmentation.lean`) is that extension, with reactions indexed
  by `N.R ⊕ S ⊕ S` (original, inflows, outflows). **`reactionVector_inflow`** and
  **`reactionVector_outflow`** give the inflow/outflow vectors as `±e_s`. From the standard basis being
  present: **`stoichSubspace_fullyOpen_eq_top`** (the stoichiometric subspace is the whole species
  space), **`stoichRank_fullyOpen`** (rank `card S`), and **`orthSum_stoichSubspace_fullyOpen_eq_bot`**
  (the conservation laws vanish: no nonzero conserved quantity).

- The deficiency and linkage consequences are in `CRNT/Open/Deficiency.lean`.
  **`deficiencyInt_fullyOpen`** reads the deficiency as `δ⁺ = n⁺ − ℓ⁺ − card S`, and
  **`numComplexes_fullyOpen_eq_add`** is the structural identity `n⁺ = ℓ⁺ + card S + δ⁺`. The
  inflow/outflow pseudo-reactions tie the zero complex to every singleton:
  **`directlyReacts_zero_singletonComplex_fullyOpen`**,
  **`linked_zero_singletonComplex_fullyOpen`**, and **`linked_singletonComplex_fullyOpen`** collapse
  the zero complex and all singletons into one linkage class.

- The boundary behaviour is in `CRNT/Open/Boundary.lean`. **`Network.IsBoundary`** and
  **`Network.faceOf`** describe the orthant faces; **`Network.BoundarySteadyState`** is a nonnegative
  equilibrium on a face. **`massActionVectorField_fullyOpen_apply`** splits the open field into the
  original part, the constant inflow, and the linear outflow. The headline results:
  **`fullyOpen_steadyState_positive`**, every nonnegative steady state is strictly interior (a held-
  at-zero species sees nonnegative original contributions, a vanishing outflow, and a strictly
  positive inflow, so the field cannot vanish); **`not_boundarySteadyState_fullyOpen`**, the open
  extension has *no* boundary steady states; **`faceOf_fullyOpen_steadyState_eq_empty`**, the only
  face carrying an equilibrium is the interior face `∅`.

**Coverage.** The structural facts (stoichiometric subspace, rank, vanishing conservation laws,
deficiency and linkage bookkeeping) and the no-boundary-equilibria result are complete for the fully
open (every-species inflow/outflow) extension.

## Network composition

Two networks over a common species type compose by taking the disjoint union of their reaction
channels.

- **`Network.interconnect N₁ N₂`** (`CRNT/Compose/Interconnect.lean`) has reactions indexed by
  `N₁.R ⊕ N₂.R`, acting on the shared concentration vector;
  `interconnect_reactionVector_inl` / `interconnect_reactionVector_inr` identify the component
  reaction vectors. **`interconnect_reactionVectors`** shows the reaction-vector set is the union of
  the components'.

- **`stoichSubspace_interconnect`** is the proved composition law: the interconnection's
  stoichiometric subspace is the *join* `N₁.stoichSubspace ⊔ N₂.stoichSubspace` of the components'.
  **`stoichSubspace_le_interconnect_left`** and **`stoichSubspace_le_interconnect_right`** record that
  each component's subspace embeds into the interconnection's.

**Coverage.** Composition is treated at the level of the stoichiometric subspace, where the join law
is exact. Retroactivity, the Del Vecchio–Ninfa–Sontag impedance / loading effect a downstream
module imposes on an upstream one at the interconnection interface, is not developed: the
interconnection here shares the species pool and composes the stoichiometry, but does not model the
input/output retroactivity bookkeeping.

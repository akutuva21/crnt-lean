# Foundations: networks, the reaction graph, and stoichiometry

This document describes the foundational layer of the `CRNT` library: a finite chemical reaction
network expressed as data, the directed and undirected graph it carries on its complexes, and the
stoichiometric algebra of its reaction vectors. It is the bottom layer of the
[architecture](architecture.md): every later layer (kinetics and dynamics, deficiency, persistence)
is read off the structures defined here.

The formalism follows Feinberg's reaction-network theory (Martin Feinberg, _Foundations of Chemical
Reaction Network Theory_, Springer 2019; and his earlier _Lectures on Chemical Reaction Networks_).
Species, complexes, reactions, the reaction graph, linkage classes, the stoichiometric subspace, and
the deficiency invariant `δ = n − ℓ − s` are all in his sense.

For the computable companions of the propositional notions below (decidable directed reachability,
decidable acyclicity, exact rational rank), see [decidability.md](decidability.md).

## Network data

A network is built from three nested data structures over a fixed species type `S` (a `Fintype`
with decidable equality).

- **`CRNT.Complex S`** (`CRNT/Basic/Complex.lean`) is a *complex*: a formal finite linear
  combination of species with natural-number stoichiometric coefficients, modelled directly as a
  function `S → ℕ`. The module provides the basic algebra, `Complex.zero` (the zero complex `0`,
  source/target of inflow and degradation reactions), `Complex.coeff`, `Complex.add`, and
  `Complex.smul`, together with `Complex.support` (the species with nonzero coefficient) and
  `Complex.toRealVector` (the real-valued coefficient vector consumed by the stoichiometry and
  kinetics layers).

- **`CRNT.Reaction S`** (`CRNT/Basic/Reaction.lean`) is a directed edge between two complexes, with
  fields `source` and `target`. Self-reactions are permitted in the raw structure;
  `Reaction.Nontrivial r` is the predicate `r.source ≠ r.target` used where they must be excluded.
  The *stoichiometric reaction vector* `Reaction.vector r` is `target − source` as a real vector
  (`Reaction.vector_apply`), the change in concentration produced by one firing;
  `Reaction.vector_of_source_eq_target` records that a self-reaction has zero vector. Reactions over
  a finite species type inherit `DecidableEq`.

- **`CRNT.Network S`** (`CRNT/Basic/Network.lean`) is a finite chemical reaction network: a reaction
  index type `R` carrying its own `DecidableEq` and `Fintype` data, and a map `reaction : R →
  Reaction S`. Indexing reactions by `R` (rather than a set of edges) makes *parallel* reactions,
  distinct channels with the same source and target, representable without duplicate-erasure.

  The network exposes its complexes and the basic counts feeding the deficiency formula
  `δ = n − ℓ − s`: `Network.complexes` is the finite set of complexes appearing as some reaction's
  source or target; `Network.numComplexes` is its cardinality (`n`); `Network.numReactions` is
  `Fintype.card R` (counting parallel reactions separately). The lemmas
  `Network.source_mem_complexes` and `Network.target_mem_complexes` confirm that both endpoints of
  every reaction are network complexes.

## The reaction graph and directed reachability

The reaction graph has the complexes as vertices and the reactions as directed edges
(`CRNT/Graph/Reachability.lean`).

- **`Network.DirectlyReacts N c d`** holds when some reaction has source `c` and target `d`, a
  directed edge `c → d`. It is decidable (`R` is finite, complexes have decidable equality).

- **`Network.Reaches N c d`** is directed reachability: the reflexive-transitive closure of
  `DirectlyReacts` (`Relation.ReflTransGen`), a directed path of length ≥ 0 from `c` to `d`. The
  module proves it is reflexive (`Reaches.refl`), transitive (`Reaches.trans`), extendable
  (`Reaches.single`, `Reaches.tail`), and that every reaction reaches from its source to its target
  (`reaches_of_reaction`).

A boundary-crossing fact lives alongside reachability in `CRNT/Graph/Crossing.lean`:
`Network.exists_crossing_reaction` shows that a directed path starting outside a predicate `P` and
ending inside it must traverse an in-crossing reaction (source outside `P`, target inside). This is
the elementary boundary argument used by the sign/excess analysis of the reaction graph.

## Weak reversibility, linkage, and strong connectivity

- **`Network.WeaklyReversible N`** (`CRNT/Graph/WeakReversibility.lean`) holds when, for every
  reaction `y → y'`, the source `y` is reachable from the target `y'`. Equivalently, every reaction
  lies on a directed cycle; the cycle-cover form `weaklyReversible_iff_onDirectedCycle` is in
  `CRNT/Graph/CycleCover.lean`, while `weaklyReversible_iff` here records the definitional
  reachability statement directly. Weak reversibility is a central hypothesis of the
  deficiency-zero theorem. `WeaklyReversible.reaches_symm` records that the source and target of
  each reaction then reach each other in both directions.

- **`Network.Linked N c d`** (`CRNT/Graph/LinkageClass.lean`) is *undirected* connectivity: the
  reflexive-transitive closure of `Network.UndirectedEdge` (a directed edge in either direction).
  `Linked` is proven an equivalence relation (`Linked.refl`, `Linked.symm`, `Linked.trans`), and
  `Network.linkedSetoid` packages it as a `Setoid` on the network's complexes. Its equivalence
  classes are the *linkage classes*. `Network.numLinkageClasses` is their count `ℓ`
  (`Nat.card` of the quotient; noncomputable). The lemma `linked_of_reaction` shows reactions never
  cross linkage classes, and `Linked.of_reaches` shows directed reachability implies linkage.

  Under weak reversibility, undirected linkage upgrades to directed reachability
  (`WeaklyReversible.reaches_of_linked`): each linkage class is *strongly connected*.

- The cycle-cover view (`CRNT/Graph/CycleCover.lean`) restates weak reversibility as a graph cover.
  `Network.OnDirectedCycle N r` says reaction `r` lies on a directed cycle (its target reaches its
  source); `WeaklyReversible.onDirectedCycle` and `weaklyReversible_iff_onDirectedCycle` show weak
  reversibility is exactly the property that every reaction is so covered. The closed-walk forms
  `WeaklyReversible.reaches_self_through` and `WeaklyReversible.reaches_self_through_target` show
  each reaction's source (resp. target) reaches itself through that reaction.
  `WeaklyReversible.reaches_comm` proves directed reachability is *symmetric* under weak
  reversibility, so each component is strongly connected; `WeaklyReversible.reaches_both` recovers
  the two-directional endpoint statement as a corollary. This cycle-cover is what the toric
  embedding of Gheorghe Craciun, _Toric Differential Inclusions and a Proof of the Global Attractor
  Conjecture_, consumes downstream.

## Stoichiometry and rank

The stoichiometric algebra (`CRNT/Stoich/`) turns reaction vectors into the linear subspace whose
dimension is the rank `s`.

- **`Network.reactionVector N r`** (`CRNT/Stoich/Vector.lean`) is reaction `r`'s vector
  `target − source` as a real species vector (`reactionVector_apply`), the column of the
  stoichiometric matrix indexed by `r`. `Network.reactionVectors` is the set of all of them.

- **`Network.stoichSubspace N`** (`CRNT/Stoich/Subspace.lean`) is the *stoichiometric subspace*: the
  real span of the reaction vectors, a `Submodule ℝ (S → ℝ)`. `reactionVector_mem_stoichSubspace`
  confirms each reaction vector lands in it. The trajectory of the dynamics stays within a coset of
  this subspace (a stoichiometric compatibility class).

- **`Network.stoichRank N`** is the *stoichiometric rank* `s`: `Module.finrank ℝ stoichSubspace`
  (noncomputable). `stoichRank_le_card` bounds it by the number of species, since the ambient space
  `S → ℝ` has dimension `card S`.

Together `numComplexes` (`n`), `numLinkageClasses` (`ℓ`), and `stoichRank` (`s`) are the three
quantities of Feinberg's deficiency `δ = n − ℓ − s`, defined and used in the deficiency layer.

## Supporting combinatorics

Two CRN-agnostic combinatorial results back the graph and deficiency arguments
(`CRNT/Combinatorics/`):

- **`CRNT/Combinatorics/DecidableCycle.lean`** makes acyclicity and cycle existence decidable for any
  finite `SimpleGraph` with decidable adjacency. Using Mathlib's bridge characterization of
  acyclicity, it provides `SimpleGraph.decidableIsAcyclic`, defines `SimpleGraph.HasCycle`, proves
  `hasCycle_iff_not_isAcyclic`, and derives `SimpleGraph.decidableHasCycle`. This applies to the
  undirected linkage graph of a network.

- **`CRNT/Combinatorics/DigraphExcess.lean`** defines, on a finite weighted digraph, the per-vertex
  and per-set *excess* (`excessVertex`, `excessSet`, outgoing minus incoming weight) and proves the
  additivity identity `excessSet_eq_sum_excessVertex`: a set's net boundary flux is the sum of its
  vertices' net fluxes, internal arcs cancelling. This is the combinatorial backbone of Feinberg's
  deficiency-one kernel analysis.

## Modules

- `CRNT/Basic/Complex.lean`: `Complex` (`S → ℕ`) and its algebra, `support`, `toRealVector`.
- `CRNT/Basic/Reaction.lean`: `Reaction`, `Nontrivial`, the reaction `vector`.
- `CRNT/Basic/Network.lean`: `Network`, `complexes`, `numComplexes`, `numReactions`.
- `CRNT/Graph/Reachability.lean`: `DirectlyReacts`, `Reaches` and its closure lemmas.
- `CRNT/Graph/Crossing.lean`: `exists_crossing_reaction`.
- `CRNT/Graph/WeakReversibility.lean`: `WeaklyReversible`.
- `CRNT/Graph/LinkageClass.lean`: `UndirectedEdge`, `Linked`, `linkedSetoid`, `numLinkageClasses`.
- `CRNT/Graph/CycleCover.lean`: `OnDirectedCycle`, strong connectivity under weak reversibility.
- `CRNT/Stoich/Vector.lean`: `reactionVector`, `reactionVectors`.
- `CRNT/Stoich/Subspace.lean`: `stoichSubspace`, `stoichRank`.
- `CRNT/Combinatorics/DecidableCycle.lean`: decidable acyclicity and cycle existence.
- `CRNT/Combinatorics/DigraphExcess.lean`: vertex/set excess and additivity.

## Related documents

- [architecture.md](architecture.md): how this layer sits beneath the rest of the library.
- [decidability.md](decidability.md): the computable companions of reachability, weak
  reversibility, linkage, and rank.
- [design.md](design.md): why the data structures are shaped as they are.

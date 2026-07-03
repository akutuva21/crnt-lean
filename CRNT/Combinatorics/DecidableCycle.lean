import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Decidable acyclicity and cycle existence for finite simple graphs

For a `SimpleGraph` on a finite vertex type with decidable adjacency, whether the graph
is acyclic is decidable, and so is whether it contains an (undirected) cycle.

The chain of deciders rests on Mathlib's bridge characterization of acyclicity:

* `SimpleGraph.isBridge_iff` reduces an edge being a bridge to non-reachability after
  deleting that edge, which is decidable since reachability is decidable.
* `SimpleGraph.isAcyclic_iff_forall_isBridge` reduces acyclicity to every edge being a
  bridge, a bounded quantifier over the (finite) edge set of a decidable predicate.

`SimpleGraph.HasCycle` packages the existence of a cyclic walk;
`SimpleGraph.hasCycle_iff_not_isAcyclic` shows it is exactly the negation of acyclicity,
making it decidable too.

These results are CRN-agnostic and apply to any finite simple graph, including the
undirected linkage graph of a reaction network.

Depends on: `Mathlib.Combinatorics.SimpleGraph.Acyclic`, `Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite`.
-/

namespace SimpleGraph

variable {V : Type*}

/-- A finite simple graph **has a cycle** when some vertex admits a cyclic closed walk. -/
def HasCycle (G : SimpleGraph V) : Prop := ∃ (v : V) (c : G.Walk v v), c.IsCycle

variable (G : SimpleGraph V)

/-- Having a cycle is exactly the failure of acyclicity. -/
theorem hasCycle_iff_not_isAcyclic : G.HasCycle ↔ ¬ G.IsAcyclic := by
  unfold HasCycle IsAcyclic
  push Not
  rfl

section Decidable

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Whether an edge is a bridge is decidable: it reduces to non-reachability after
deleting the edge. -/
instance decidableIsBridge (e : Sym2 V) : Decidable (G.IsBridge e) :=
  Quot.recOnSubsingleton (motive := fun e => Decidable (G.IsBridge e)) e
    (fun p => decidable_of_iff _ (isBridge_iff (u := p.1) (v := p.2)).symm)

/-- Acyclicity is decidable: it reduces to every edge of the (finite) edge set being a
bridge. -/
instance decidableIsAcyclic : Decidable G.IsAcyclic :=
  decidable_of_iff (∀ e ∈ G.edgeFinset, G.IsBridge e) (by
    rw [isAcyclic_iff_forall_isBridge]
    simp only [mem_edgeFinset])

/-- Whether a finite simple graph contains a cycle is decidable. -/
instance decidableHasCycle : Decidable G.HasCycle :=
  decidable_of_iff _ (hasCycle_iff_not_isAcyclic G).symm

end Decidable

example : (⊥ : SimpleGraph (Fin 3)).IsAcyclic := by decide

example : ¬ (⊥ : SimpleGraph (Fin 3)).HasCycle := by decide

end SimpleGraph

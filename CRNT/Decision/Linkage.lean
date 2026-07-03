import CRNT.Graph.LinkageClass
import CRNT.Decision.Reachability
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Computable linkage classes

Linkage classes are the connected components of the *undirected* reaction graph. Modelling
that graph as a Mathlib `SimpleGraph` on the finite vertex type of complexes makes the whole
connectivity toolkit computable: undirected reachability is decidable, the connected
components form a `Fintype`, and connectivity is decidable.

`linkageGraph` is that simple graph; its `Reachable` relation coincides with `Linked`
(`linked_iff_reachable`), so the number of linkage classes is the (computable) number of
connected components:

* `numLinkageClasses_eq_card_connectedComponent`: `ℓ = Fintype.card (linkageGraph).ConnectedComponent`.

This gives a computable companion for the linkage count `ℓ` in `δ = n − ℓ − s`, and decidable
linkage among complexes.

Depends on: `CRNT.Graph.LinkageClass`, `CRNT.Decision.Reachability`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

instance decidableUndirectedEdge (N : Network S) : DecidableRel N.UndirectedEdge :=
  fun c d => inferInstanceAs (Decidable (N.DirectlyReacts c d ∨ N.DirectlyReacts d c))

/-- A complex incident to an undirected edge is a complex of the network. -/
theorem mem_complexes_of_undirectedEdge_left (N : Network S) {c d : Complex S}
    (h : N.UndirectedEdge c d) : c ∈ N.complexes := by
  rcases h with ⟨r, hs, _⟩ | ⟨r, _, ht⟩
  · exact hs ▸ N.source_mem_complexes r
  · exact ht ▸ N.target_mem_complexes r

/-- **The undirected reaction graph** on the finite vertex type of complexes: an edge joins
two distinct complexes linked by a reaction in either direction. -/
def linkageGraph (N : Network S) : SimpleGraph {c : Complex S // c ∈ N.complexes} where
  Adj a b := a.val ≠ b.val ∧ N.UndirectedEdge a.val b.val
  symm := ⟨fun _ _ h => ⟨fun e => h.1 e.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (N : Network S) : DecidableRel N.linkageGraph.Adj :=
  fun a b => inferInstanceAs (Decidable (a.val ≠ b.val ∧ N.UndirectedEdge a.val b.val))

/-- A directed-closure step in the simple graph lifts to undirected linkage of the underlying
complexes. -/
theorem linked_of_reflTransGen_adj (N : Network S)
    {a b : {c : Complex S // c ∈ N.complexes}}
    (h : Relation.ReflTransGen N.linkageGraph.Adj a b) : N.Linked a.val b.val := by
  induction h with
  | refl => exact Linked.refl N a.val
  | tail _ hstep ih => exact ih.trans (Relation.ReflTransGen.single hstep.2)

/-- Undirected linkage of complexes lifts to the simple graph: any linkage path between two
complexes of the network passes through complexes of the network. -/
theorem reflTransGen_adj_of_linked (N : Network S) {c d : Complex S} (h : N.Linked c d) :
    ∀ (hc : c ∈ N.complexes) (hd : d ∈ N.complexes),
      Relation.ReflTransGen N.linkageGraph.Adj ⟨c, hc⟩ ⟨d, hd⟩ := by
  induction h with
  | refl => intro hc _; exact Relation.ReflTransGen.refl
  | @tail e f _ hef ih =>
    intro hc hf
    have he : e ∈ N.complexes := mem_complexes_of_undirectedEdge_left N hef
    have step := ih hc he
    by_cases hef' : e = f
    · subst hef'; exact step
    · exact step.tail ⟨hef', hef⟩

/-- **Linkage coincides with undirected reachability in the simple graph.** -/
theorem linked_iff_reachable (N : Network S) (a b : {c : Complex S // c ∈ N.complexes}) :
    N.Linked a.val b.val ↔ N.linkageGraph.Reachable a b := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h; exact reflTransGen_adj_of_linked N h a.2 b.2
  · intro h; exact linked_of_reflTransGen_adj N h

/-- Linkage of network complexes is decidable, via undirected reachability in the simple
graph. -/
instance decidableLinked (N : Network S) (a b : {c : Complex S // c ∈ N.complexes}) :
    Decidable (N.Linked a.val b.val) :=
  decidable_of_iff _ (linked_iff_reachable N a b).symm

/-- **The number of linkage classes is the number of connected components of the undirected
reaction graph** — a computable companion for `ℓ`. -/
theorem numLinkageClasses_eq_card_connectedComponent (N : Network S) :
    N.numLinkageClasses = Fintype.card N.linkageGraph.ConnectedComponent := by
  have hrel : N.linkedSetoid.r = N.linkageGraph.Reachable := by
    funext a b
    exact propext (linked_iff_reachable N a b)
  rw [← Nat.card_eq_fintype_card]
  show Nat.card (Quot N.linkedSetoid.r) = Nat.card (Quot N.linkageGraph.Reachable)
  rw [hrel]

end Network

end CRNT

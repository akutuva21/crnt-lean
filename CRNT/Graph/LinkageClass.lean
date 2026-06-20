import CRNT.Graph.Reachability
import CRNT.Graph.WeakReversibility
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Linkage classes

The linkage classes of a network are the connected components of the *undirected*
reaction graph on complexes. Two complexes are *linked* when one is reachable from
the other along edges traversed in either direction.

`Linked` is an equivalence relation on the complexes of the network. The number of
linkage classes, written `ℓ` in the deficiency formula `δ = n - ℓ - s`, is defined as
the cardinality of the quotient of the network's complexes by this relation. The
definition is noncomputable; example counts are established by explicit proof.

This module is **stable**. Depends on: `CRNT.Graph.Reachability`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The undirected one-step adjacency: an edge between `c` and `d` in either
direction. -/
def UndirectedEdge (N : Network S) (c d : Complex S) : Prop :=
  N.DirectlyReacts c d ∨ N.DirectlyReacts d c

theorem UndirectedEdge.symm {N : Network S} {c d : Complex S}
    (h : N.UndirectedEdge c d) : N.UndirectedEdge d c :=
  Or.symm h

/-- `N.Linked c d` holds when `c` and `d` lie in the same linkage class: they are
connected in the undirected reaction graph. -/
def Linked (N : Network S) (c d : Complex S) : Prop :=
  Relation.ReflTransGen (N.UndirectedEdge) c d

@[refl] theorem Linked.refl (N : Network S) (c : Complex S) : N.Linked c c :=
  Relation.ReflTransGen.refl

theorem Linked.trans {N : Network S} {c d e : Complex S}
    (h₁ : N.Linked c d) (h₂ : N.Linked d e) : N.Linked c e :=
  Relation.ReflTransGen.trans h₁ h₂

theorem Linked.symm {N : Network S} {c d : Complex S} (h : N.Linked c d) :
    N.Linked d c := by
  induction h with
  | refl => exact Linked.refl N c
  | tail _ hbc ih => exact Linked.trans (Relation.ReflTransGen.single hbc.symm) ih

/-- The source and target of every reaction lie in the same linkage class: reactions
do not cross linkage classes. -/
theorem linked_of_reaction (N : Network S) (r : N.R) :
    N.Linked (N.reaction r).source (N.reaction r).target :=
  Relation.ReflTransGen.single (Or.inl ⟨r, rfl, rfl⟩)

/-- In a weakly reversible network, undirected linkage implies directed reachability:
each linkage class is strongly connected. Every undirected edge is traversable in both
directions — forward directly, backward via the return path guaranteed by weak
reversibility. -/
theorem WeaklyReversible.reaches_of_linked {N : Network S} (hwr : N.WeaklyReversible)
    {c d : Complex S} (hcd : N.Linked c d) : N.Reaches c d := by
  induction hcd with
  | refl => exact Network.Reaches.refl N c
  | @tail e f _ hef ih =>
    refine ih.trans ?_
    rcases hef with ⟨r, hs, ht⟩ | ⟨r, hs, ht⟩
    · exact Network.Reaches.single ⟨r, hs, ht⟩
    · exact hs ▸ ht ▸ hwr r

/-- Directed reachability implies linkage: a directed path is in particular an
undirected one. -/
theorem Linked.of_reaches {N : Network S} {c d : Complex S} (h : N.Reaches c d) :
    N.Linked c d := by
  induction h with
  | refl => exact Linked.refl N c
  | tail _ hde ih => exact Linked.trans ih (Relation.ReflTransGen.single (Or.inl hde))

/-- Linkage as a setoid on the complexes appearing in the network. The linkage
classes are the equivalence classes of this setoid. -/
def linkedSetoid (N : Network S) : Setoid {c : Complex S // c ∈ N.complexes} where
  r a b := N.Linked a.val b.val
  iseqv :=
    { refl := fun a => Linked.refl N a.val
      symm := fun h => Linked.symm h
      trans := fun h₁ h₂ => Linked.trans h₁ h₂ }

/-- The number of linkage classes `ℓ`: the number of connected components of the
undirected reaction graph, i.e. the number of equivalence classes of `Linked` among
the network's complexes. -/
noncomputable def numLinkageClasses (N : Network S) : ℕ :=
  Nat.card (Quotient N.linkedSetoid)

end Network

end CRNT

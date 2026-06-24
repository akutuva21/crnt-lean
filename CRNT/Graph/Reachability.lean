import CRNT.Basic.Network
import Mathlib.Logic.Relation

/-!
# Directed reachability in the reaction graph

The reaction graph of a network has the complexes as vertices and the reactions as
directed edges. This module defines the one-step adjacency relation `DirectlyReacts`
and its reflexive-transitive closure `Reaches`, the directed reachability relation.

`DirectlyReacts` is decidable (the reaction index type is finite and complexes have
decidable equality), so explicit reachability witnesses can be checked. Reachability
itself is defined propositionally via `Relation.ReflTransGen`; example properties are
established by explicit path construction.

This module is **stable**. Depends on: `CRNT.Basic.Network`, `Mathlib.Logic.Relation`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- `DirectlyReacts N c d` holds when some reaction of `N` has source `c` and target
`d`: there is a directed edge `c → d` in the reaction graph. -/
def DirectlyReacts (N : Network S) (c d : Complex S) : Prop :=
  ∃ r : N.R, (N.reaction r).source = c ∧ (N.reaction r).target = d

instance (N : Network S) : DecidableRel (DirectlyReacts N) :=
  fun _ _ => Fintype.decidableExistsFintype

/-- `Reaches N c d` holds when `d` is reachable from `c` by a directed path of
reactions (possibly of length zero). It is the reflexive-transitive closure of
`DirectlyReacts`. -/
def Reaches (N : Network S) (c d : Complex S) : Prop :=
  Relation.ReflTransGen (DirectlyReacts N) c d

/-- Every complex reaches itself. -/
@[refl] theorem Reaches.refl (N : Network S) (c : Complex S) : N.Reaches c c :=
  Relation.ReflTransGen.refl

/-- A single reaction `c → d` witnesses reachability. -/
theorem Reaches.single {N : Network S} {c d : Complex S} (h : N.DirectlyReacts c d) :
    N.Reaches c d :=
  Relation.ReflTransGen.single h

/-- Reachability is transitive: composing two directed paths gives a directed path. -/
theorem Reaches.trans {N : Network S} {c d e : Complex S}
    (h₁ : N.Reaches c d) (h₂ : N.Reaches d e) : N.Reaches c e :=
  Relation.ReflTransGen.trans h₁ h₂

/-- Extend a reachability witness by one reaction at the end. -/
theorem Reaches.tail {N : Network S} {c d e : Complex S}
    (h : N.Reaches c d) (hde : N.DirectlyReacts d e) : N.Reaches c e :=
  Relation.ReflTransGen.tail h hde

/-- A reaction of the network produces directed reachability from its source to its
target. This is the basic step used to assemble explicit reachability witnesses. -/
theorem reaches_of_reaction (N : Network S) (r : N.R) :
    N.Reaches (N.reaction r).source (N.reaction r).target :=
  Reaches.single ⟨r, rfl, rfl⟩

end Network

end CRNT

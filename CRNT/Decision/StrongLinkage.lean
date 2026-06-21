import CRNT.Decision.Reachability
import CRNT.Decision.Linkage

/-!
# Strong linkage classes and terminal strong linkage classes

A *strong linkage class* is a set of complexes that are mutually reachable along directed
reaction paths — the directed refinement of a linkage class. It is *terminal* when no
reaction leaves it; terminal strong linkage classes are the absorbing components of the
reaction graph and are the structural objects underlying the deficiency-one theory and
absolute concentration robustness.

`StronglyLinked c d` (mutual directed reachability) is an equivalence relation on the
complexes, refining `Linked`. `IsTerminalSLC c` records that the strong linkage class of `c`
is terminal, and `stronglyLinked_of_reaches_of_terminal` shows such a class is closed under
directed reachability.

`StronglyLinkedWithin k` is the decidable bounded companion: it is sound for `StronglyLinked`
(`stronglyLinked_of_within`), so concrete networks confirm strong connectivity by `decide` at
a chosen depth. A full `DecidableRel` for `StronglyLinked` (and the `Fintype` of strong
linkage classes) requires the directed path-length bound and is future work.

This module is **stable**. Depends on: `CRNT.Decision.Reachability`, `CRNT.Decision.Linkage`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Strong linkage**: two complexes are strongly linked when each is reachable from the
other along directed reaction paths. -/
def StronglyLinked (N : Network S) (c d : Complex S) : Prop :=
  N.Reaches c d ∧ N.Reaches d c

@[refl] theorem StronglyLinked.refl (N : Network S) (c : Complex S) : N.StronglyLinked c c :=
  ⟨Reaches.refl N c, Reaches.refl N c⟩

theorem StronglyLinked.symm {N : Network S} {c d : Complex S}
    (h : N.StronglyLinked c d) : N.StronglyLinked d c :=
  ⟨h.2, h.1⟩

theorem StronglyLinked.trans {N : Network S} {c d e : Complex S}
    (h₁ : N.StronglyLinked c d) (h₂ : N.StronglyLinked d e) : N.StronglyLinked c e :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

/-- Strong linkage refines (undirected) linkage. -/
theorem StronglyLinked.linked {N : Network S} {c d : Complex S}
    (h : N.StronglyLinked c d) : N.Linked c d :=
  Linked.of_reaches h.1

/-- Strong linkage as a setoid on the complexes of the network. The strong linkage classes
are its equivalence classes. -/
def stronglyLinkedSetoid (N : Network S) : Setoid {c : Complex S // c ∈ N.complexes} where
  r a b := N.StronglyLinked a.val b.val
  iseqv :=
    { refl := fun a => StronglyLinked.refl N a.val
      symm := StronglyLinked.symm
      trans := StronglyLinked.trans }

/-! ## Decidable bounded companion -/

/-- `StronglyLinkedWithin N k c d`: each of `c`, `d` is reachable from the other by a directed
path of at most `k` reactions. Decidable, and sound for `StronglyLinked`. -/
def StronglyLinkedWithin (N : Network S) (k : ℕ) (c d : Complex S) : Prop :=
  N.ReachesWithin k c d ∧ N.ReachesWithin k d c

instance (N : Network S) (k : ℕ) (c d : Complex S) :
    Decidable (N.StronglyLinkedWithin k c d) :=
  inferInstanceAs (Decidable (N.ReachesWithin k c d ∧ N.ReachesWithin k d c))

/-- **Soundness.** A bounded mutual path witnesses strong linkage. -/
theorem stronglyLinked_of_within (N : Network S) {k : ℕ} {c d : Complex S}
    (h : N.StronglyLinkedWithin k c d) : N.StronglyLinked c d :=
  ⟨reaches_of_reachesWithin N h.1, reaches_of_reachesWithin N h.2⟩

/-! ## Terminal strong linkage classes -/

/-- `IsTerminalSLC N c`: the strong linkage class of `c` is **terminal** — every reaction
whose source is strongly linked to `c` has its target strongly linked to `c` as well, so no
reaction leaves the class. -/
def IsTerminalSLC (N : Network S) (c : Complex S) : Prop :=
  ∀ r : N.R, N.StronglyLinked c (N.reaction r).source → N.StronglyLinked c (N.reaction r).target

/-- **A terminal strong linkage class is closed under directed reachability.** Anything
reachable from a complex in a terminal class is strongly linked to it — the class is
absorbing. -/
theorem stronglyLinked_of_reaches_of_terminal (N : Network S) {c : Complex S}
    (hc : N.IsTerminalSLC c) {d : Complex S} (h : N.Reaches c d) : N.StronglyLinked c d := by
  induction h with
  | refl => exact StronglyLinked.refl N c
  | @tail e f _ hef ih =>
    obtain ⟨r, hs, ht⟩ := hef
    have hsrc : N.StronglyLinked c (N.reaction r).source := by rw [hs]; exact ih
    have htgt := hc r hsrc
    rwa [ht] at htgt

end Network

end CRNT

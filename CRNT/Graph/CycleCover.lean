import CRNT.Graph.WeakReversibility

/-!
# The weakly-reversible cycle cover

Craciun's toric-embedding argument (arXiv:1501.02860v2, Theorem A, §3) assembles the
multi-cycle velocity embedding from the graph fact that a weakly-reversible reaction
graph is *covered by directed cycles*: every reaction `y → y'` lies on a directed cycle,
because weak reversibility returns a directed path from `y'` back to `y`. This module
records that cycle-cover at the reachability level, which is the graph residue the
`NetworkCycleDecomposition` of `CRNT.Dynamics.ToricEmbeddingWR` consumes.

## What lands here

* `OnDirectedCycle` — a reaction lies on a directed cycle when its target reaches its
  source (closing `source → target ⇝ source`).
* `WeaklyReversible.onDirectedCycle` — the **core graph lemma**: under weak reversibility
  every reaction lies on a directed cycle.
* `WeaklyReversible.reaches_self_through` — the closed-walk statement: the source of every
  reaction reaches itself through that reaction (`source ⇝ source` factoring through
  `target`).
* `WeaklyReversible.reaches_comm` — weak reversibility makes reachability *symmetric*: if
  `c` reaches `d` then `d` reaches `c`, so each connected component of the reaction graph is
  strongly connected. This is the strong-connectivity characterization of weak reversibility
  at the reachability level.

## Proven vs. residue

Proven sorry-free and axiom-clean: that under `WeaklyReversible` every reaction lies on a
directed cycle, that each reaction's source reaches itself through it, and that reachability
is symmetric (strong connectivity of components).

Named residue (deferred): extracting a *concrete* closed walk — a `List N.R` realizing the
cycle through each reaction — from the propositional `Relation.ReflTransGen` reachability
witness, and assembling the full `NetworkCycleDecomposition` (the per-cycle reaction
sequences `e`/`u`/`vec` with the velocity summing correctly). The reachability layer defines
`Reaches` propositionally and carries no path data, so concrete cycle-list extraction is the
deferred Boolean/path procedure noted in `CRNT.Graph.Reachability`. The `mono`/`cmin` fields
of `NetworkCycleDecomposition` are the separate analytic projection-ordering residue, not
graph theory.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Graph.WeakReversibility`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- `N.OnDirectedCycle r` holds when the reaction `r` lies on a directed cycle: its target
reaches its source, so the directed edge `source → target` closes back to a cycle through
`r`. -/
def OnDirectedCycle (N : Network S) (r : N.R) : Prop :=
  N.Reaches (N.reaction r).target (N.reaction r).source

/-- **Core graph lemma — weak reversibility covers every reaction by a directed cycle.** Under
`WeaklyReversible`, each reaction `r` lies on a directed cycle: the target reaches the source,
closing the edge `source → target` into a cycle. This is `WeaklyReversible` restated as the
cycle-cover the toric-embedding assembly consumes. -/
theorem WeaklyReversible.onDirectedCycle {N : Network S} (h : N.WeaklyReversible)
    (r : N.R) : N.OnDirectedCycle r :=
  h r

/-- The cycle-cover is equivalent to weak reversibility: a network is weakly reversible iff
every reaction lies on a directed cycle. -/
theorem weaklyReversible_iff_onDirectedCycle (N : Network S) :
    N.WeaklyReversible ↔ ∀ r : N.R, N.OnDirectedCycle r :=
  Iff.rfl

/-- **The closed walk through a reaction.** Under weak reversibility, the source of every
reaction reaches itself through that reaction: the edge `source → target` followed by the
return path `target ⇝ source` is a directed closed walk based at `source`. -/
theorem WeaklyReversible.reaches_self_through {N : Network S} (h : N.WeaklyReversible)
    (r : N.R) : N.Reaches (N.reaction r).source (N.reaction r).source :=
  (N.reaches_of_reaction r).trans (h r)

/-- The same closed walk, based at the target: under weak reversibility the target of every
reaction reaches itself through that reaction (`target ⇝ source → target`). -/
theorem WeaklyReversible.reaches_self_through_target {N : Network S} (h : N.WeaklyReversible)
    (r : N.R) : N.Reaches (N.reaction r).target (N.reaction r).target :=
  (h r).trans (N.reaches_of_reaction r)

/-- **Strong connectivity of components.** Weak reversibility makes directed reachability
symmetric: if `c` reaches `d` then `d` reaches `c`. Consequently every connected component of
the reaction graph is strongly connected, the standard graph characterization of weak
reversibility. Proved by induction along the path `c ⇝ d`, returning along each edge by the
weak-reversibility return path. -/
theorem WeaklyReversible.reaches_comm {N : Network S} (h : N.WeaklyReversible)
    {c d : Complex S} (hcd : N.Reaches c d) : N.Reaches d c := by
  induction hcd using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a b hab _ ih =>
    obtain ⟨r, hrs, hrt⟩ := hab
    -- `a → b` is reaction `r`; the return path `b ⇝ a` is `b ⇝ a` via weak reversibility,
    -- and `d ⇝ b` is `ih`, so `d ⇝ b ⇝ a`.
    have hba : N.Reaches b a := by
      have := h r
      rw [hrs, hrt] at this
      exact this
    exact ih.trans hba

/-- Under weak reversibility, the source and target of every reaction reach each other in both
directions, recovering `WeaklyReversible.reaches_symm` as a consequence of strong
connectivity. -/
theorem WeaklyReversible.reaches_both {N : Network S} (h : N.WeaklyReversible) (r : N.R) :
    N.Reaches (N.reaction r).source (N.reaction r).target ∧
      N.Reaches (N.reaction r).target (N.reaction r).source :=
  ⟨N.reaches_of_reaction r, h r⟩

end Network

end CRNT

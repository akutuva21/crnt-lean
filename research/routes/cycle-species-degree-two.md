# Route: the aggregate causal degree of a cycle species, and the residue it reduces to

**Agent:** `form-sr-deg2a` · **round 1** · **status: landed (10 machine-checked declarations)**

File `CRNT/Multistationarity/TrueSRCycleSpeciesDegree.lean`. Every declaration reports
`[propext, Classical.choice, Quot.sound]` under `#print axioms` — **no `sorryAx`**, even though the
file imports `TrueChemistrySRCriterion`, because nothing defined after that module's `sorry` is
used.

Companion file: `research/routes/rr-reaction-arc.md` (the `RR` ear gluability, same branch).

---

## 1. The finding

DEAD-ENDS B-2 reports that a degree split *at the residue* is degenerate, and B-5 that
`hopp`/`hcausal`/`¬hnc` are "already sharp". Both are right, and together they pin the residue
completely. Reading `TrueChemistrySRCriterion.lean:8579`–`8607`:

```
cases hv0 : Q0.vertex ⟨0,_⟩ with
| inl s0 =>
    have hs0C : C.HasSpecies s0.1 := …
    by_cases hm1s : m = 1 ∧ s0 = s
    · … aggregateCausalEdge_not_both_directions …            -- closed
    -- Residual: vertex0 = s0 on the cycle, (m ≠ 1 ∨ s0 ≠ s)
    sorry
```

`Q0` is the minimal aggregate causal path from an on-cycle vertex to the off-cycle class `q`, with
`m > 0`, injective, and `hQ0late : ∀ i, i ≠ 0 → ¬ C.HasVertex (Q0.vertex i)`. In the `inl s0`
branch, `Q0.vertex 0` is an **on-cycle species**. Since
`TrueInternalAggregateCausalEdge` has no `inl → inl` case, `Q0.step ⟨0,_⟩` forces
`Q0.vertex 1 = Sum.inr ρ₁` with

```
N.trueInternalClassFlux α ρ₁.1 s0.1 * σ s0.1 < 0.
```

That is a **negative** class flux at a cycle species. This module proves:

> **The trichotomy (`classFlux_trichotomy`).** At the cycle species `C.species b`, the aggregate
> class flux of the cycle reaction `C.reaction a` is
> * strictly **positive** iff `b` is the successor of `a` (the reaction whose *right* edge meets
>   `C.species b`);
> * strictly **negative** iff `a = b` (the reaction whose *left* edge meets `C.species b`);
> * exactly **zero** otherwise.

So a cycle species has aggregate causal degree **exactly one out and one in over the cycle classes**
— no slack — and the unique out-neighbour is `C.reaction b`, a **cycle vertex**. `hQ0late` forbids
index `1`. Therefore:

> `no_offCycle_negFlux` — the residual is **equivalent** to
> `no_offCycle_negFlux α σ C : ∀ b ρ, ¬ C.HasReaction ρ → 0 ≤ flux α ρ (C.species b) * σ (C.species b)`.

That is one named proposition, and it is the *correctly scoped* replacement for `hrest`, which
DEAD-ENDS B-3 shows cannot be discharged (its natural instance is refuted by `hattachment`).

Two corollaries, both proved:

* **`no_escape_from_cycleSpecies`** — conditional discharge. If `no_offCycle_negFlux` holds, the
  residue branch is closed outright (`False`).
* **`exists_offCycle_negFlux_class`** — positive extraction. If it fails, the escape necessarily
  produces an off-cycle class `ρ` with a strictly negative class flux at some cycle species. This
  is the *off-cycle end of the ear*, stated as data rather than as a gap. Together with
  `hattachment` (an off-cycle class *positive* at a cycle species) it is the pair of off-cycle
  endpoints A.6 Case 2 consumes.

## 2. Exact Lean signatures

`namespace CRNT.Network.TrueSRCycle`, `variable {N : Network S} {n : ℕ} {α : N.fullyOpen.R → ℝ}
{σ : S → ℝ}`.

```lean
theorem finRotate_val (C : N.TrueSRCycle n) (i : Fin n) : (finRotate n i).1 = (i.1 + 1) % n

theorem hoppAt (C : N.TrueSRCycle n)
    (hopp : ∀ i : Fin n, N.trueInternalClassFlux α (C.reaction (finRotate n i))
        (C.species (finRotate n i)) * σ (C.species (finRotate n i)) < 0) (j : Fin n) :
    N.trueInternalClassFlux α (C.reaction j) (C.species j) * σ (C.species j) < 0

theorem hcausalAt (C : N.TrueSRCycle n)
    (hcausal : ∀ i : Fin n, 0 < N.trueInternalClassFlux α (C.reaction i)
        (C.species (finRotate n i)) * σ (C.species (finRotate n i))) (j : Fin n) :
    0 < N.trueInternalClassFlux α (C.reaction ((finRotate n).symm j)) (C.species j) * σ (C.species j)

theorem classFlux_eq_zero_of_nonNeighbour (C : N.TrueSRCycle n)
    (hsep : N.ReactantProductSeparated) (hSR : N.TrueSRStrongCriterion) (hCeven : C.Even)
    (a b : Fin n) (hab : a ≠ b) (hba : b.1 ≠ (a.1 + 1) % n) :
    N.trueInternalClassFlux α (C.reaction a) (C.species b) = 0

theorem negFlux_eq_leftEdge (C : N.TrueSRCycle n) (hsep) (hSR) (hCeven)
    (hcausal : …) (a b : Fin n)
    (h : N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b) < 0) : a = b

theorem posFlux_eq_rightEdge (C : N.TrueSRCycle n) (hsep) (hSR) (hCeven)
    (hcausal : …) (hopp : …) (a b : Fin n)
    (h : 0 < N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b)) :
    b.1 = (a.1 + 1) % n

theorem classFlux_trichotomy (C : N.TrueSRCycle n) (hsep) (hSR) (hCeven)
    (hcausal : …) (hopp : …) (a b : Fin n) :
    (0 < flux … ∧ b.1 = (a.1 + 1) % n) ∨
      (flux … = 0 ∧ a ≠ b ∧ b.1 ≠ (a.1 + 1) % n) ∨
      (flux … < 0 ∧ a = b)

def no_offCycle_negFlux (α : N.fullyOpen.R → ℝ) (σ : S → ℝ) (C : N.TrueSRCycle n) : Prop :=
  ∀ (b : Fin n) (ρ : N.TrueReaction), ¬ C.HasReaction ρ →
    0 ≤ N.trueInternalClassFlux α ρ (C.species b) * σ (C.species b)

theorem negCausalStep_from_cycleSpecies (C : N.TrueSRCycle n) (hsep) (hSR) (hCeven)
    (hcausal : …) (hoff : no_offCycle_negFlux α σ C) (b : Fin n) (ρ : N.TrueReaction)
    (h : N.trueInternalClassFlux α ρ (C.species b) * σ (C.species b) < 0) : ρ = C.reaction b

def aggregateVertexOnCycle (α) (σ) (C : N.TrueSRCycle n) :
    N.TrueInternalAggregateVertex α σ → Prop
  | Sum.inl s => C.HasSpecies s.1
  | Sum.inr ρ => C.HasReaction ρ.1

theorem no_escape_from_cycleSpecies (C : N.TrueSRCycle n) (hsep) (hSR) (hCeven)
    (hcausal : …) (hoff : no_offCycle_negFlux α σ C)
    {T : Finset (N.TrueInternalAggregateVertex α σ)} {m : ℕ}
    (Q : CRNT.RelPath (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T m) (hm : 0 < m)
    {s0 : AggregateActiveSpecies σ}
    (hv0 : Q.vertex ⟨0, by omega⟩ = Sum.inl s0) (hs0C : C.HasSpecies s0.1)
    (hlate : ∀ i : Fin (m + 1), i.1 ≠ 0 → ¬ aggregateVertexOnCycle α σ C (Q.vertex i)) : False

theorem exists_offCycle_negFlux_class {n : ℕ} {C : N.TrueSRCycle n}
    (hoff_neg : ¬ no_offCycle_negFlux α σ C) :
    ∃ (b : Fin n) (ρ : N.TrueReaction), ¬ C.HasReaction ρ ∧
      N.trueInternalClassFlux α ρ (C.species b) * σ (C.species b) < 0
```

## 3. Proof sketch and citations

* `classFlux_eq_zero_of_nonNeighbour` is `Network.nonAdjacent_cycleClassFlux_eq_zero`
  (`TrueChemistrySRCriterion.lean:6979`) in the `(a, b)` order the trichotomy uses. That lemma is
  itself `containsEdge_iff_cycleNeighbour` (`TrueSRCPairThirdEdge.lean:183`) plus
  `no_single_edge_chord_of_trueSRCriterion` (`TrueSRChordExtraction.lean:42`): a non-neighbouring
  cycle class with nonzero flux at a cycle species gives a single-edge chord of `C`.
* `hopp` / `hcausal` are the orientation signs of the s-cycle: at `C.species j`,
  `C.reaction j` is the reaction whose left edge meets it and is negative; `(finRotate n).symm j`
  is the reaction whose right edge meets it and is positive.
* `negFlux_eq_leftEdge`: nonzero flux gives `a = b ∨ b = finRotate n a` by
  `classFlux_eq_zero_of_nonNeighbour`; the second alternative is ruled out by `hcausal a`.
* `posFlux_eq_rightEdge`: symmetric, the first alternative is ruled out by `hoppAt C hopp a`.
* `classFlux_trichotomy`: `lt_trichotomy` + the two lemmas; the zero case needs both signs to rule
  out `a = b` and `b = finRotate n a`.
* `no_escape_from_cycleSpecies`: `Q.step ⟨0, hm⟩` forces `Q.vertex 1` to be a reaction
  (`TrueInternalAggregateCausalEdge` is `False` on `inl → inl`); its class flux is negative at
  `s0.1 = C.species b`; `negCausalStep_from_cycleSpecies` makes it `C.reaction b`; but
  `aggregateVertexOnCycle (Sum.inr _)` is then `C.HasReaction (C.reaction b)`, which `hlate` at
  index `1` (`1 < m + 1` from `hm`) forbids.

## 4. Dependency order

1. **DONE.** This file.
2. **Extract, do not assume.** At the residue, `¬ no_offCycle_negFlux` is *forced* (the branch is
   reached), so `exists_offCycle_negFlux_class` supplies a concrete off-cycle class `ρ` with
   negative flux at a cycle species `C.species b`. Pair it with `hattachment`'s class `q` (positive
   at `C.species (finRotate n i)`) to get the two off-cycle endpoints.
3. **The ear.** Both endpoints feed the `RRGluable` instance in
   `TrueSREarRRGluable.rrGluable_reactionArcFwd` (this branch), which supplies the cycle arc to
   glue against; `rrGluedCycle` then gives the new cycle `X`.
4. **Evenness.** `X.Even` from `SignDirected σ` — `TrueSRCycle.even_of_signChange` is **private**
   (`TrueChemistrySRCriterion.lean:6885`); a public version must be authored.
5. **Discharge.** `lemmaA6_case2_*` (ported separately) closes in `hSR.2`.

## 5. Dead ends (do not re-walk)

* **`hrest` is not in scope at line 8607** (DEAD-ENDS B-3) and its natural instance is refuted by
  `hattachment`. `no_offCycle_negFlux` is the correctly scoped replacement; do not try to
  instantiate `hrest` here.
* **`hopp` does not force `k = 1`** (DEAD-ENDS B-8). The in-tree comment at `:8600`–`8607` says it
  does; that is wrong, and `no_escape_from_cycleSpecies` shows *why*: the first hop lands on an
  **off-cycle** class, and the only way to forbid that is `no_offCycle_negFlux`.
* **The degree split at the residue is degenerate** (DEAD-ENDS B-2). Do not re-run it. The
  trichotomy is the honest version: the degree is two over cycle classes, and the degree is
  *unbounded* once off-cycle classes are allowed — which is the whole problem.
* **`aggregateVertexToTrueSRVertex` is `private`** (`TrueChemistrySRCriterion.lean:4984`), so
  `hg0`/`hQ0late` cannot be re-stated verbatim outside that file. `aggregateVertexOnCycle` above is
  the same predicate, restated on `N.TrueInternalAggregateVertex` directly.
* **`nonAdjacent_cycleClassFlux_eq_zero` takes `(j t)` with `hne : t.1 ≠ j.1`** (a `Fin.val`
  inequality, not `t ≠ j`). Passing `hab : a ≠ b` directly is a type error; wrap it as
  `fun h => hab (Fin.ext h)`.

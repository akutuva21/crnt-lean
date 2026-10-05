# Route D: the ear's c-pair parity is a free parameter, not a fixed datum

Complements `holeB-ss-ear-discharger.md` §9. Read from source at commit `a6b78db`.

## The framing error in rounds 1-3

Rounds 1–3 tried to **compute** `ssNumCPairs P % 2`, the parity of the ear's own c-pair count, and
recorded it as "unobtainable". That was the wrong frame. The parity is **not a fixed datum at all** —
it is a free parameter, because the ear's edges carry no label data forced by the hypotheses.

## Why the parity is free

`CRNT/Multistationarity/TrueChemistrySRCriterion.lean:5022-5030` — the edge witness is an
existential:

```lean
private theorem aggregateSourceAdj_has_trueSREdge (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (T : Finset (N.TrueInternalAggregateVertex α σ))
    (u v : {x : N.TrueInternalAggregateVertex α σ // x ∈ T})
    (h : (CRNT.relationGraphOn (N.TrueInternalAggregateCausalEdge …) T).Adj u v) :
    ∃ e : N.TrueSREdge,
      e.Connects (N.aggregateVertexToTrueSRVertex u.1) (N.aggregateVertexToTrueSRVertex v.1)
```

`TrueSREdge` (structure, `TrueChemistrySRGraph.lean:108-119`) carries `endpoint : Complex S`,
`representative : N.R`, `representative_class`, `endpoint_is_source_or_target`, `occurs`. **None is
determined by the two vertices.** And `relPathToTrueSRSSPath` (`:5475`) instantiates
`edge := Classical.choose (edgeWitness i)`.

`ssCPairAt P r` is `(P.edge ⟨2r⟩).endpoint = (P.edge ⟨2r+1⟩).endpoint`
(`TrueSRSSGlueCPairs.lean:45-47`) — a comparison of **free** fields.

## Where the freedom concretely is

At an `inl s → inr ρ` vertex, `aggregateSourceAdj_has_trueSREdge` (`:5040-5059`) builds the edge by

```lean
obtain ⟨e, hes, her⟩ :=
  N.exists_trueSREdge_of_nonzero_trueInternalClassFlux ρ.1 s.1 hflux
```

keyed on the pair **(class, species)** alone. That constructor (`:4781-4799`) picks a channel
`r ∈ N.nonflowOriginalChannels` with `N.trueReaction r = ρ` and
`α (Sum.inl r) * N.reactionVector r s ≠ 0`, then returns the single canonical edge
`N.trueSREdgeOfReactionVectorNe r hnotflow s hν`. Its `endpoint` is therefore
`(N.reaction r).source` or `.target`, determined **by `r`**.

And `exists_nonzero_channel_of_trueInternalClassFlux` (`:4762-4780`) is the key: it does **not** say one
channel exists, it says the class flux is the *sum* over channels of the class,

```lean
let A := N.nonflowOriginalChannels.filter (fun r => N.trueReaction r = ρ)
```

and proves by contradiction that if every summand vanishes the sum vanishes. So:

> **Steering lemma.** If some class `ρ` appearing in the ear has **two or more** channels
> `r₁ ≠ r₂ ∈ N.nonflowOriginalChannels` with `N.trueReaction rᵢ = ρ` and
> `α (Sum.inl rᵢ) * N.reactionVector rᵢ s ≠ 0` for the *same* species `s`, and if
> `(N.reaction r₁).source ≠ (N.reaction r₂).source` (and likewise for `.target`), then two valid
> edges through that vertex have **different** `endpoint`s, so flipping the choice at that one vertex
> changes `ssNumCPairs P` by 1 and hence **flips its parity**.

That is the whole of Route D, and it is a *statement about the network's channels*, not about `hopp`,
`hcausal` or `hlocal` — which is why none of those could repair §9's blockers.

## What this means for the residue

The already-proved reduction `ssGlueCycle_even_iff_parity_of_cycleEven` (`:8273`) gives

```
(ssGlueCycle P (C.speciesArc (k+1))).Even  ↔  ssNumCPairs P % 2 = ssNumCPairsH (C.speciesArcBwd (k+1)) % 2
```

so if the ear's parity is steerable, pick the parity and the even cycle exists, and the residue closes
via `hSR.1` — **without** `hSR.2` (already refuted, §6) and **without** `SignDirected` (§9's blocker 1).

## The trap

`aggregateCausalEdge_not_both_directions` (`:4705`) forbids `s → ρ` and `ρ → s` for the *same*
species, so the freedom must come from a **different channel of the same class at the same species**
(or a different species), never from flipping direction at one vertex.

## The one statement whose failure also settles things

If the steering lemma is **false** — i.e. every class/species pair in the ear has a unique active
channel, so `endpoint` is forced — then the parity is fixed after all, Route D is dead, and §9's
obstruction stands. Both outcomes are worth machine-checking; the negation is as informative as the
lemma.

# Hole B — residue reduced to a single named proposition

**Date:** 2026-10-10 · **Branch:** `resolve-holes` · **Worktree:** `tmp/holes-resolve`

## Headline

The `sorry` at `CRNT/Multistationarity/TrueChemistrySRCriterion.lean:9435` is **already
discharged by a proved, axiom-clean theorem that lives in an unreachable module.** The blocker is
an import cycle, not missing mathematics — for the *discharging* half.

`CRNT/Multistationarity/TrueSRCycleSpeciesDegree.lean` (299 lines, hole-free) proves

```lean
theorem no_escape_from_cycleSpecies (C : N.TrueSRCycle n)
    (hsep : N.ReactantProductSeparated) (hSR : N.TrueSRStrongCriterion) (hCeven : C.Even)
    (hcausal : ∀ i : Fin n,
      0 < N.trueInternalClassFlux α (C.reaction i) (C.species (finRotate n i)) *
        σ (C.species (finRotate n i)))
    (hoff : no_offCycle_negFlux α σ C)
    {T : Finset (N.TrueInternalAggregateVertex α σ)} {m : ℕ}
    (Q : CRNT.RelPath (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T m) (hm : 0 < m)
    {s0 : AggregateActiveSpecies σ}
    (hv0 : Q.vertex ⟨0, by omega⟩ = Sum.inl s0) (hs0C : C.HasSpecies s0.1)
    (hlate : ∀ i : Fin (m + 1), i.1 ≠ 0 →
      ¬ aggregateVertexOnCycle α σ C (Q.vertex i)) : False
```

whose hypotheses are *exactly* the residue context at the `inl s0` branch. The residue is
therefore equivalent to

```lean
def no_offCycle_negFlux (α : N.fullyOpen.R → ℝ) (σ : S → ℝ) (C : N.TrueSRCycle n) : Prop :=
  ∀ (b : Fin n) (ρ : N.TrueReaction), ¬ C.HasReaction ρ →
    0 ≤ N.trueInternalClassFlux α ρ (C.species b) * σ (C.species b)
```

> **no off-cycle reaction class drains any cycle species**

and its negation is exactly the datum the route docs had been chasing:

```lean
theorem exists_offCycle_negFlux_class {n : ℕ} {C : N.TrueSRCycle n}
    (hoff_neg : ¬ no_offCycle_negFlux α σ C) :
    ∃ (b : Fin n) (ρ : N.TrueReaction), ¬ C.HasReaction ρ ∧
      N.trueInternalClassFlux α ρ (C.species b) * σ (C.species b) < 0
```

This is the "off-cycle species/class with negative flux at a cycle species" that
`research/routes/holeB-steering.md` and `research/BRIEF-B.md` §B.2 named as the A.6 Case-2
source-block datum — now stated as a **single machine-checked `Prop` with a proved decomposer**
rather than as prose.

## Two separable obstacles

| # | obstacle | status |
|---|---|---|
| 1 | **Import cycle.** `TrueSRCycleSpeciesDegree.lean:1` imports `TrueChemistrySRCriterion`, but the `sorry` is *inside* that file. The discharger cannot be applied at the residue. | real, mechanical Lean work — not mathematics |
| 2 | **Proving `no_offCycle_negFlux`** from `hsep` + `hSR` + the cycle hypotheses. | **the open mathematics** — this is the actual hole |

Obstacle 1 is tractable: the module docstring (`:43-51`) records that the file needs
`trueInternalClassFlux`, `nonAdjacent_cycleClassFlux_eq_zero`, `TrueInternalAggregateCausalEdge`
and `ActiveAggregateTrueReaction`, all of which are currently `private` to
`TrueChemistrySRCriterion.lean`. Lifting those four into a module that `TrueChemistrySRCriterion`
itself imports inverts the cycle.

Obstacle 2 is not a tactic problem. `TrueSRCycleSpeciesDegree.lean:200` records that the analogous
`hrest` hypothesis "cannot be discharged (its natural instance is refuted by `hattachment`)", and
`research/routes/holeB-steering.md` concludes the source-block analysis of Shinar–Feinberg
§5.5/§A.3 is required. That is the genuine frontier of Hole B.

**Consequence for planning:** closing Hole B requires *both* the cycle-inverting refactor
(obstacle 1) and the Shinar–Feinberg source-block content (obstacle 2). Obstacle 1 alone reduces the
hole to a single named proposition; it does not close it.

## Orphaned A.6 machinery

Separately worth recording, because it changes what a future attempt should build on:

* `CRNT/Multistationarity/TrueSREarCase1.lean` and `TrueSREarCase2.lean` **are in `master`**, and
  `TrueSREarCase2.lean` mentions `SignDirected` 19 times — i.e. blocker 1 of
  `holeB-steering.md` §9 appears already addressed there.
* But **nothing imports `TrueSREarCase2`**, and `TrueChemistrySRCriterion.lean` imports neither.
  The A.6 Case-1/Case-2 ear modules are **orphaned**: they cannot reach the residue.
* `CRNT/Graph/EarNonseparability.lean` (828 lines) and `CRNT/Graph/RelPathAppend.lean` (186 lines)
  exist **only** on the diverged `backup-fig8` branch and are **absent from `master`**.

## Port status (this branch)

| file | source | result |
|---|---|---|
| `research/drafts/portfig8/RelPathAppend.lean` | `backup-fig8:CRNT/Graph/RelPathAppend.lean` | **compiles clean against `master`'s API, 0 sorries** (`checkmod.sh` OK, 48 s) |
| `research/drafts/portfig8/EarNonseparability.lean` | `backup-fig8:CRNT/Graph/EarNonseparability.lean` | see run log |

`RelPathAppend.lean` is a clean win: `appendPath` plus its `start`/`end`/`noRepeat` lemmas, built on
`CRNT.RelPath`, which is already imported by `TrueChemistrySRCriterion.lean`.

Note `EarNonseparability.lean` imports `TrueChemistrySRCriterion` too, so it has the *same* import
cycle as `TrueSRCycleSpeciesDegree.lean` and is likewise unusable at the residue without the
inversion described in obstacle 1.
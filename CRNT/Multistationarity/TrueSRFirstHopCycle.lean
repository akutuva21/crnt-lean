import CRNT.Multistationarity.TrueChemistrySRCriterion

/-!
# The first hop out of an on-cycle species is the leftEdge step

This module restates the pure combinatorics of `CRNT.Multistationarity.TrueSRFirstHop` at the
level of the true-chemistry SR graph of `CRNT.Multistationarity.TrueChemistrySRGraph`, i.e. in
the exact vocabulary of `Network.TrueSRCycle` and
`Network.TrueInternalAggregateCausalEdge`.

It exists because the residue comment of
`CRNT/Multistationarity/TrueChemistrySRCriterion.lean:8600-8607` asserts a fact about first hops
that is (a) misattributed to `hopp` and (b) misstated as to target.  See
`research/routes/firsthop.md`.

## Main statement

`Network.oneStep_fromCycleSpecies_eq_leftEdge`:

> Let `C` be a true-SR cycle in a reactant/product-separated network satisfying the strong SR
> criterion.  Let `s` be a cycle species with `s = C.species j`.  If the aggregate causal edge out
> of `s` lands on a *cycle* reaction class, that class is `C.reaction j`, i.e. the hop is the
> single leftEdge step `s → C.reaction j`.  The three cycle hypotheses needed are
> `hopp` (only for the *existence* half and the mirror), `hcausal`, and the vanishing of
> non-neighbour cycle-class fluxes.

`Network.leftEdge_step_exists` is the existence half, and
`Network.onCycle_out_neighbour_leftEdge` packages both directions as a set equality.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The non-neighbour cycle-class flux vanishing at the residue, obtained from the negated `hnc`
test of `TrueChemistrySRCriterion.lean:8537` via `nonAdjacent_cycleClassFlux_eq_zero`. -/
theorem nonneighbour_cycleClassFlux_eq_zero (N : Network S)
    (hsep : N.ReactantProductSeparated) (hSR : N.TrueSRStrongCriterion)
    {n : ℕ} {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (C : N.TrueSRCycle n) (hC : C.Even)
    (a b : Fin n) (h1 : a.1 ≠ b.1) (h2 : b.1 ≠ (a.1 + 1) % n) :
    N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b) = 0 :=
  nonAdjacent_cycleClassFlux_eq_zero N hsep hSR C hC a b h1 h2

/-- **The first hop out of an on-cycle species that lands on the cycle is the leftEdge step.**

Let `s` be the cycle species `C.species j`.  If a species-to-reaction aggregate causal edge out
of `s` lands on a cycle reaction class `ρ`, then `ρ = C.reaction j`: the edge is
`C.leftEdge j`, whose species is `C.species j` and whose reaction is `C.reaction j`
(`TrueChemistrySRGraph.lean:141-144`).

Hypotheses (all in scope at `TrueChemistrySRCriterion.lean:8600`, see `research/routes/firsthop.md`):

* `hzero` — non-neighbour cycle-class fluxes vanish.  At the residue this is `¬hnc`
  (line 8537), i.e. `nonAdjacent_cycleClassFlux_eq_zero` (line 6979); see
  `nonneighbour_cycleClassFlux_eq_zero` for the packaged form.
* `hcausal` — line 8036.
* `hopp` is **not** needed for this direction; it is needed for the mirror
  (`hop_backward_forced` in `TrueSRFirstHop`) and for existence
  (`leftEdge_step_exists`). -/
theorem oneStep_fromCycleSpecies_eq_leftEdge (N : Network S)
    {n : ℕ} {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (C : N.TrueSRCycle n)
    (hzero : ∀ a b : Fin n, a.1 ≠ b.1 → b.1 ≠ (a.1 + 1) % n →
      N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b) = 0)
    (hcausal : ∀ i : Fin n, 0 < N.trueInternalClassFlux α (C.reaction i)
      (C.species (finRotate n i)) * σ (C.species (finRotate n i)))
    (j : Fin n) {s : AggregateActiveSpecies σ} (hs : s.1 = C.species j)
    {ρ : ActiveAggregateTrueReaction α σ} (hρC : C.HasReaction ρ.1)
    (h : N.TrueInternalAggregateCausalEdge (Sum.inl s) (Sum.inr ρ)) :
    ρ.1 = C.reaction j := by
  classical
  change N.trueInternalClassFlux α ρ.1 s.1 * σ s.1 < 0 at h
  have hfa := CRNT.firstHop_forced_leftEdge
    (φ := fun a b => N.trueInternalClassFlux α (C.reaction a) (C.species b))
    (σs := fun b => σ (C.species b)) hzero hcausal
  obtain ⟨a, ha⟩ := hρC
  have hsub : s.1 = C.species a := by
    rw [hs]
    exact ha
  have := hfa a j (by rw [hsub]; exact h)
  simpa [hsub] using this

/-- **Existence of the one-hop leftEdge step.**  `hopp` re-indexed at `j` says the cycle's left
incidence at `j` carries a strictly negative species-times-flux term, i.e. it *is* a
species-to-reaction aggregate causal edge `C.species j → C.reaction j`. -/
theorem leftEdge_step_exists (N : Network S)
    {n : ℕ} {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (C : N.TrueSRCycle n)
    (hopp : ∀ i : Fin n, N.trueInternalClassFlux α (C.reaction (finRotate n i))
      (C.species (finRotate n i)) * σ (C.species (finRotate n i)) < 0)
    (j : Fin n) (hσ : σ (C.species j) ≠ 0) :
    N.TrueInternalAggregateCausalEdge
      (Sum.inl (⟨C.species j, hσ⟩ : AggregateActiveSpecies σ))
      (Sum.inr ⟨C.reaction j, C.reaction_internal j⟩) := by
  have h := CRNT.hopp_at
    (φ := fun a b => N.trueInternalClassFlux α (C.reaction a) (C.species b))
    (σs := fun b => σ (C.species b)) hopp j
  exact h

/-- **Both directions of the forcing, as a set equality.**

The aggregate causal out-neighbours of the cycle species `C.species j` that are cycle reaction
classes form exactly the singleton `{C.reaction j}`.  The `⊆` direction is
`oneStep_fromCycleSpecies_eq_leftEdge`; the `⊇` direction is `hopp` re-indexed at `j`.

Consequently: if all out-neighbours of `s` are on the cycle, then the unique one-step
species-to-reaction route out of `s` is `C.leftEdge j`, and no other cycle reaction is reachable
in one hop.  Any longer on-cycle route advances the cycle index by one per hop
(`CRNT.two_hop_onCycle`), so the on-cycle distance from `C.species j` to `C.reaction a` is the
least `t ≥ 0` with `(finRotate n)^[t] j = a`, and in particular is never `1` unless `a = j`. -/
theorem onCycle_out_neighbour_leftEdge (N : Network S)
    {n : ℕ} {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (C : N.TrueSRCycle n)
    (hzero : ∀ a b : Fin n, a.1 ≠ b.1 → b.1 ≠ (a.1 + 1) % n →
      N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b) = 0)
    (hcausal : ∀ i : Fin n, 0 < N.trueInternalClassFlux α (C.reaction i)
      (C.species (finRotate n i)) * σ (C.species (finRotate n i)))
    (hopp : ∀ i : Fin n, N.trueInternalClassFlux α (C.reaction (finRotate n i))
      (C.species (finRotate n i)) * σ (C.species (finRotate n i)) < 0)
    (j : Fin n) (hσ : σ (C.species j) ≠ 0) :
    (∀ {ρ : ActiveAggregateTrueReaction α σ}, C.HasReaction ρ.1 →
        N.TrueInternalAggregateCausalEdge
          (Sum.inl (⟨C.species j, hσ⟩ : AggregateActiveSpecies σ)) (Sum.inr ρ) →
        ρ.1 = C.reaction j) ∧
      N.TrueInternalAggregateCausalEdge
        (Sum.inl (⟨C.species j, hσ⟩ : AggregateActiveSpecies σ))
        (Sum.inr ⟨C.reaction j, C.reaction_internal j⟩) := by
  refine ⟨fun {ρ} hρC h =>
    oneStep_fromCycleSpecies_eq_leftEdge N C hzero hcausal j rfl hρC h, ?_⟩
  exact leftEdge_step_exists N C hopp j hσ

/-- **Refutation, at CRNT level, of the residue comment's stated target.**

`TrueChemistrySRCriterion.lean:8603` says the first hop is "`s₀ → C.reaction (pos s₀)`", where
`pos s₀` is fixed by `s₀ = C.species (finRotate n i)` (line 8052) and endpoint
`qC.1 = C.reaction i` (line 8219), i.e. `pos (C.species j) = (finRotate n).symm j`.

That hop does not exist: the only on-cycle target of a one-hop out of `C.species j` is
`C.reaction j`, and for a nontrivial cycle `C.reaction j ≠ C.reaction ((finRotate n).symm j)`. -/
theorem no_oneStep_to_pos_of_cycleSpecies (N : Network S)
    {n : ℕ} {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (C : N.TrueSRCycle n) (hn2 : 2 ≤ n)
    (hzero : ∀ a b : Fin n, a.1 ≠ b.1 → b.1 ≠ (a.1 + 1) % n →
      N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b) = 0)
    (hcausal : ∀ i : Fin n, 0 < N.trueInternalClassFlux α (C.reaction i)
      (C.species (finRotate n i)) * σ (C.species (finRotate n i)))
    (j : Fin n) {ρ : ActiveAggregateTrueReaction α σ}
    (hρpos : ρ.1 = C.reaction ((finRotate n).symm j))
    (hρC : C.HasReaction ρ.1) {s : AggregateActiveSpecies σ} (hs : s.1 = C.species j)
    (h : N.TrueInternalAggregateCausalEdge (Sum.inl s) (Sum.inr ρ)) : False := by
  have heq := oneStep_fromCycleSpecies_eq_leftEdge N C hzero hcausal j hs hρC h
  have hne : ((finRotate n).symm j).1 ≠ j.1 := by
    intro hv
    exact CRNT.finRotate_ne_self hn2 j (Fin.ext (by omega))
  rw [hρpos] at heq
  exact absurd heq (by
    intro hh
    have := congrArg Fin.val hh
    omega)

end Network
end CRNT
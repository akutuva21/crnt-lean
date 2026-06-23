import CRNT.Dynamics.IsolatedInvariant

/-!
# The Butler–McGehee escape principle for ω-limit sets

This module provides the sound core of the **Butler–McGehee lemma** (Butler & Waltman; Hale,
_Asymptotic Behavior of Dissipative Systems_), the general dynamical-systems tool behind
boundary-repulsion and persistence arguments. The content depends only on a topological space
`α` carrying a `Flow ℝ≥0 α`, independent of reaction networks.

Fix a precompact forward orbit through `x₀` absorbed by a compact set `K` in a Hausdorff
space, with `Ω = omegaLimit atTop ϕ {x₀}`. Such an `Ω` is **two-sided invariant**: forward
invariant by Mathlib's `isInvariant_omegaLimit`, and backward invariant by
`CRNT.omegaLimit_negInvariant`. The relevant operator is recorded as
`omegaLimit_isInvariant_two_sided`.

The Butler–McGehee engine concerns a compact **isolated invariant** set `M`
(`IsIsolatedInvariant`) with isolating neighborhood `N`, where `M` is the maximal invariant
subset of `N`. The key sound facts are:

* `omegaLimit_subset_isolating_subset` — if the invariant `Ω` is contained in an isolating
  neighborhood `N`, then `Ω ⊆ M`, because `Ω` is then an invariant subset of `N` and `M` is
  the *maximal* such subset.
* `omegaLimit_not_subset_isolating` — contrapositive escape statement: if `Ω ⊄ M` then `Ω`
  escapes the isolating neighborhood, `Ω ⊄ N`.
* `exists_mem_omegaLimit_notMem_isolating` — under `Ω ⊄ M` there is an explicit escaping
  ω-point `q ∈ Ω` with `q ∉ N`, hence `q ∉ M`; its full forward and backward orbit stays
  inside `Ω`.

These are the boundary-repulsion engine: an isolated invariant set cannot trap an ω-limit
set without containing it. The stable/unstable-manifold formulation
(`Ω` meets `Wˢ(M) \ M` and `Wᵘ(M) \ M`) and the connectedness route to it lie beyond what
Mathlib supplies: Mathlib v4.31 has **no** ω-limit connectedness lemma and **no**
stable/unstable-set API, so those refinements are not attempted here.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.IsolatedInvariant`.
-/

open Filter Set Topology
open scoped NNReal Topology

namespace CRNT

variable {α : Type*} [TopologicalSpace α]

/-- **Two-sided invariance of the ω-limit set of a precompact orbit.** For a semiflow `ϕ` on a
Hausdorff space whose forward orbit through `x₀` is contained in a compact set `K`, the ω-limit
set is invariant: `ϕ t` maps it into itself (forward invariance, from
`Flow.isInvariant_omegaLimit`) and every ω-point has a `ϕ t`-preimage inside the ω-limit set
(backward invariance, from `omegaLimit_negInvariant`). This packages forward invariance; the
backward direction is `omegaLimit_negInvariant`. -/
theorem omegaLimit_isInvariant_two_sided (ϕ : Flow ℝ≥0 α) (x₀ : α) :
    IsInvariant ϕ (omegaLimit atTop ϕ {x₀}) :=
  Flow.isInvariant_omegaLimit atTop ϕ {x₀}
    (fun _ => tendsto_atTop_mono (fun _ => le_add_self) tendsto_id)

/-- If an invariant set `Ω` is contained in an isolating neighborhood `N` of an isolated
invariant set `M`, then `Ω ⊆ M`. Reason: `Ω` is an invariant subset of `N`, and `M` is the
maximal invariant subset of `N`, so `Ω ⊆ maximalInvariantSubset ϕ N = M`. -/
theorem subset_of_isInvariant_subset_isolating (ϕ : Flow ℝ≥0 α) {M N Ω : Set α}
    (hMisol : maximalInvariantSubset ϕ N = M) (hΩinv : IsInvariant ϕ Ω) (hΩN : Ω ⊆ N) :
    Ω ⊆ M := by
  have h : Ω ⊆ maximalInvariantSubset ϕ N := subset_maximalInvariantSubset ϕ hΩinv hΩN
  rwa [hMisol] at h

/-- **Butler–McGehee escape, set form.** For the ω-limit set `Ω` of a precompact orbit and an
isolated invariant set `M`, if `Ω` is contained in an isolating neighborhood `N` of `M` then
`Ω ⊆ M`. This specializes `subset_of_isInvariant_subset_isolating` to the ω-limit set, whose
invariance is automatic. -/
theorem omegaLimit_subset_of_subset_isolating (ϕ : Flow ℝ≥0 α) (x₀ : α) {M N : Set α}
    (hMisol : maximalInvariantSubset ϕ N = M)
    (hΩN : omegaLimit atTop ϕ {x₀} ⊆ N) :
    omegaLimit atTop ϕ {x₀} ⊆ M :=
  subset_of_isInvariant_subset_isolating ϕ hMisol (omegaLimit_isInvariant_two_sided ϕ x₀) hΩN

/-- **Butler–McGehee escape, contrapositive form.** If the ω-limit set `Ω` of a precompact
orbit is *not* contained in the isolated invariant set `M`, then it escapes every isolating
neighborhood `N` of `M`: `Ω ⊄ N`. An isolated invariant set cannot trap an ω-limit set
without containing it. -/
theorem omegaLimit_not_subset_isolating (ϕ : Flow ℝ≥0 α) (x₀ : α) {M N : Set α}
    (hMisol : maximalInvariantSubset ϕ N = M)
    (hΩM : ¬ omegaLimit atTop ϕ {x₀} ⊆ M) :
    ¬ omegaLimit atTop ϕ {x₀} ⊆ N :=
  fun hΩN => hΩM (omegaLimit_subset_of_subset_isolating ϕ x₀ hMisol hΩN)

/-- **Butler–McGehee escaping point.** If the ω-limit set `Ω` of a precompact orbit is not
contained in an isolated invariant set `M`, there is an ω-point `q ∈ Ω` outside the isolating
neighborhood `N` (hence outside `M`). The full orbit of `q` stays in `Ω` by two-sided
invariance: forward, `ϕ t q ∈ Ω`; backward, each `ϕ t`-preimage of `q` lies in `Ω`. -/
theorem exists_mem_omegaLimit_notMem_isolating (ϕ : Flow ℝ≥0 α) (x₀ : α) {M N : Set α}
    (hMisol : maximalInvariantSubset ϕ N = M)
    (hMN : M ⊆ N)
    (hΩM : ¬ omegaLimit atTop ϕ {x₀} ⊆ M) :
    ∃ q ∈ omegaLimit atTop ϕ {x₀}, q ∉ N ∧ q ∉ M := by
  obtain ⟨q, hqΩ, hqN⟩ := not_subset.mp (omegaLimit_not_subset_isolating ϕ x₀ hMisol hΩM)
  exact ⟨q, hqΩ, hqN, fun hqM => hqN (hMN hqM)⟩

/-- The forward orbit of any ω-point stays inside the ω-limit set (forward invariance), in
particular for a Butler–McGehee escaping point. -/
theorem forward_orbit_mem_omegaLimit (ϕ : Flow ℝ≥0 α) (x₀ : α) {q : α}
    (hq : q ∈ omegaLimit atTop ϕ {x₀}) (t : ℝ≥0) :
    ϕ t q ∈ omegaLimit atTop ϕ {x₀} :=
  omegaLimit_isInvariant_two_sided ϕ x₀ t hq

/-- The backward orbit of any ω-point stays inside the ω-limit set: for each time `t`, an
escaping point `q` has a `ϕ t`-preimage `q'` that is itself an ω-point. This is
`omegaLimit_negInvariant` specialized to a Butler–McGehee escaping point and is the engine of
boundary-repulsion: the escaping point's whole backward trajectory is confined to `Ω`. -/
theorem backward_orbit_mem_omegaLimit [T2Space α] (ϕ : Flow ℝ≥0 α) (x₀ : α) {K : Set α}
    (hK : IsCompact K) (hmaps : ∀ s : ℝ≥0, ϕ s x₀ ∈ K) (t : ℝ≥0) {q : α}
    (hq : q ∈ omegaLimit atTop ϕ {x₀}) :
    ∃ q' ∈ omegaLimit atTop ϕ {x₀}, ϕ t q' = q :=
  omegaLimit_negInvariant ϕ x₀ hK hmaps t hq

end CRNT

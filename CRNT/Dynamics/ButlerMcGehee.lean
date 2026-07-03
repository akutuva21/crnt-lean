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
set without containing it. For any ω-point `q ∈ Ω`, its own forward limit
`omegaLimit atTop ϕ {q}` is a nonempty compact invariant subset of `Ω`
(`isCompact_isInvariant_nonempty_omegaLimit_of_mem`); combined with the escaping point this
yields `exists_omegaLimit_escape_subOmega`. The stable/unstable-manifold formulation
(`Ω` meets `Wˢ(M) \ M` and `Wᵘ(M) \ M`) and the connectedness route to it lie beyond what
Mathlib supplies: Mathlib v4.31 has **no** ω-limit connectedness lemma and **no**
stable/unstable-set API, so those refinements are not attempted here.

Depends on: `CRNT.Dynamics.IsolatedInvariant`.
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

/-- The ω-limit set of an orbit absorbed by a compact set is compact. The orbit is absorbed by
`K` when, eventually, the closure of the forward image lies in `K`; the ω-limit set is contained
in that closure (`omegaLimit_subset_closure_image2`) and is closed (`isClosed_omegaLimit`), so it
is a closed subset of the compact `K`. -/
theorem isCompact_omegaLimit_of_absorbing (ϕ : Flow ℝ≥0 α) (x₀ : α) {K : Set α}
    (hK : IsCompact K) (habs : ∃ v ∈ (Filter.atTop : Filter ℝ≥0),
      closure (Set.image2 ϕ v {x₀}) ⊆ K) :
    IsCompact (omegaLimit Filter.atTop ϕ {x₀}) := by
  obtain ⟨v, hv, hvK⟩ := habs
  exact hK.of_isClosed_subset (isClosed_omegaLimit _ _ _)
    ((omegaLimit_subset_closure_image2 _ _ _ hv).trans hvK)

/-- The ω-limit set of an orbit absorbed by a compact set is a compact invariant set: it is
compact by `isCompact_omegaLimit_of_absorbing` and invariant by
`omegaLimit_isInvariant_two_sided`. -/
theorem isCompact_isInvariant_omegaLimit (ϕ : Flow ℝ≥0 α) (x₀ : α) {K : Set α}
    (hK : IsCompact K) (habs : ∃ v ∈ (Filter.atTop : Filter ℝ≥0),
      closure (Set.image2 ϕ v {x₀}) ⊆ K) :
    IsCompact (omegaLimit Filter.atTop ϕ {x₀}) ∧
      IsInvariant ϕ (omegaLimit Filter.atTop ϕ {x₀}) :=
  ⟨isCompact_omegaLimit_of_absorbing ϕ x₀ hK habs, omegaLimit_isInvariant_two_sided ϕ x₀⟩

/-- An ω-limit set is its own maximal invariant subset, since it is invariant
(`omegaLimit_isInvariant_two_sided`) and `maximalInvariantSubset_self` applies to invariant
sets. -/
theorem maximalInvariantSubset_omegaLimit_self (ϕ : Flow ℝ≥0 α) (x₀ : α) :
    maximalInvariantSubset ϕ (omegaLimit Filter.atTop ϕ {x₀})
      = omegaLimit Filter.atTop ϕ {x₀} :=
  maximalInvariantSubset_self ϕ (omegaLimit_isInvariant_two_sided ϕ x₀)

/-- An invariant ω-limit set lying in the interior of a compact set whose maximal invariant subset
it exhausts is an isolated invariant set. Its invariance comes from
`omegaLimit_isInvariant_two_sided`, and `isIsolatedInvariant_of_maximalInvariantSubset_eq`
supplies the isolating neighborhood. -/
theorem isIsolatedInvariant_omegaLimit (ϕ : Flow ℝ≥0 α) (x₀ : α) {N : Set α}
    (hNc : IsCompact N) (hint : omegaLimit Filter.atTop ϕ {x₀} ⊆ interior N)
    (hmax : maximalInvariantSubset ϕ N = omegaLimit Filter.atTop ϕ {x₀}) :
    IsIsolatedInvariant ϕ (omegaLimit Filter.atTop ϕ {x₀}) :=
  isIsolatedInvariant_of_maximalInvariantSubset_eq ϕ
    (omegaLimit_isInvariant_two_sided ϕ x₀) hNc hint hmax

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

/-- The forward limit of any point of a compact ω-limit set is a nonempty compact invariant
subset of that ω-limit set. -/
theorem isCompact_isInvariant_nonempty_omegaLimit_of_mem
    (ϕ : Flow ℝ≥0 α) (x₀ : α) {K : Set α} (hK : IsCompact K)
    (habs : ∃ v ∈ (Filter.atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K)
    {q : α} (hq : q ∈ omegaLimit Filter.atTop ϕ {x₀}) :
    (omegaLimit Filter.atTop ϕ {q}).Nonempty
      ∧ IsCompact (omegaLimit Filter.atTop ϕ {q})
      ∧ IsInvariant ϕ (omegaLimit Filter.atTop ϕ {q})
      ∧ omegaLimit Filter.atTop ϕ {q} ⊆ omegaLimit Filter.atTop ϕ {x₀} := by
  set Ω := omegaLimit Filter.atTop ϕ {x₀} with hΩ
  have hf : ∀ t : ℝ≥0, Tendsto (t + ·) atTop atTop :=
    fun _ => tendsto_atTop_mono (fun _ => le_add_self) tendsto_id
  have hΩcompact : IsCompact Ω := isCompact_omegaLimit_of_absorbing ϕ x₀ hK habs
  have hΩinv : IsInvariant ϕ Ω := omegaLimit_isInvariant_two_sided ϕ x₀
  have hΩclosed : closure Ω = Ω := (isClosed_omegaLimit _ _ _).closure_eq
  -- `Ω` itself absorbs the orbit of `q`: `image2 ϕ univ {q} ⊆ Ω`, and `closure Ω = Ω`.
  have habsq' : closure (Set.image2 ϕ (Set.univ : Set ℝ≥0) {q}) ⊆ Ω := by
    rw [← hΩclosed]
    refine closure_mono ?_
    rintro y ⟨t, _, p, hp, rfl⟩
    rw [Set.mem_singleton_iff.mp hp]
    exact hΩinv t hq
  have habsq : ∃ v ∈ (Filter.atTop : Filter ℝ≥0),
      closure (Set.image2 ϕ v {q}) ⊆ Ω := ⟨Set.univ, Filter.univ_mem, habsq'⟩
  -- The ω-limit of `{q}` lies in the closure of the absorbing image, hence in `Ω`.
  have hsubset : omegaLimit Filter.atTop ϕ {q} ⊆ Ω :=
    (omegaLimit_subset_closure_image2 atTop ϕ {q} Filter.univ_mem).trans habsq'
  refine ⟨?_, ?_, ?_, hsubset⟩
  · exact nonempty_omegaLimit_of_isCompact_absorbing atTop ϕ {q} hΩcompact habsq
      (Set.singleton_nonempty q)
  · exact hΩcompact.of_isClosed_subset (isClosed_omegaLimit _ _ _) hsubset
  · exact Flow.isInvariant_omegaLimit atTop ϕ {q} hf

/-- Butler–McGehee escape: if `Ω ⊄ M` (the maximal invariant subset of `N`), some ω-point
escapes `M` and its forward limit is a nonempty compact invariant subset of `Ω`. -/
theorem exists_omegaLimit_escape_subOmega
    (ϕ : Flow ℝ≥0 α) (x₀ : α) {K : Set α} (hK : IsCompact K)
    (habs : ∃ v ∈ (Filter.atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K)
    {M N : Set α} (hMisol : maximalInvariantSubset ϕ N = M) (hMN : M ⊆ N)
    (hΩM : ¬ omegaLimit Filter.atTop ϕ {x₀} ⊆ M) :
    ∃ q ∈ omegaLimit Filter.atTop ϕ {x₀}, q ∉ M ∧
      (omegaLimit Filter.atTop ϕ {q}).Nonempty ∧ IsCompact (omegaLimit Filter.atTop ϕ {q})
        ∧ IsInvariant ϕ (omegaLimit Filter.atTop ϕ {q})
        ∧ omegaLimit Filter.atTop ϕ {q} ⊆ omegaLimit Filter.atTop ϕ {x₀} := by
  obtain ⟨q, hqΩ, _, hqM⟩ :=
    exists_mem_omegaLimit_notMem_isolating ϕ x₀ hMisol hMN hΩM
  obtain ⟨hne, hcompact, hinv, hsub⟩ :=
    isCompact_isInvariant_nonempty_omegaLimit_of_mem ϕ x₀ hK habs hqΩ
  exact ⟨q, hqΩ, hqM, hne, hcompact, hinv, hsub⟩

end CRNT

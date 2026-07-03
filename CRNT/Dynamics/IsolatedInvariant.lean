import CRNT.Dynamics.NegativeInvariance

/-!
# Isolated invariant sets and isolating neighborhoods

This module provides the isolated-invariant-set / isolating-neighborhood API over `Flow ℝ≥0`,
the substrate the Butler–McGehee lemma needs. The content is general dynamical-systems material:
it depends only on a topological space `α` carrying a `Flow ℝ≥0 α`, independent of reaction
networks.

The central construction is the **maximal invariant subset** `maximalInvariantSubset ϕ N` of a set
`N`: the union of all `ϕ`-invariant subsets of `N`. It is itself invariant (invariance is closed
under unions), is contained in `N`, and contains every invariant subset of `N`, so it is the
largest invariant set inside `N`. When `N` is closed the maximal invariant subset is closed (its
closure is invariant and still inside `N`, hence inside the maximal invariant subset), and when `N`
is in addition compact the maximal invariant subset is compact.

A compact invariant set `M` is **isolated** (`IsIsolatedInvariant ϕ M`) when some compact
neighborhood `N` of `M` has `M` as its maximal invariant subset; such an `N` is an isolating
neighborhood. Every compact invariant set is its own maximal invariant subset, and a compact
invariant set sitting inside the interior of a compact set that contains no strictly larger
invariant set is isolated.

Depends on: `CRNT.Dynamics.NegativeInvariance`.
-/

open Set Topology
open scoped NNReal Topology

namespace CRNT

variable {α : Type*} [TopologicalSpace α]

/-- The closure of a `ϕ`-invariant set is `ϕ`-invariant: each `ϕ t` is continuous, so it maps the
closure of `s` into the closure of `ϕ t '' s ⊆ s`. -/
theorem isInvariant_closure (ϕ : Flow ℝ≥0 α) {s : Set α} (h : IsInvariant ϕ s) :
    IsInvariant ϕ (closure s) := by
  intro t x hx
  have hcont : Continuous (ϕ t) := ϕ.continuous continuous_const continuous_id
  have h1 : ϕ t x ∈ closure (ϕ t '' s) :=
    image_closure_subset_closure_image hcont ⟨x, hx, rfl⟩
  exact (closure_mono (h t).image_subset) h1

/-- An arbitrary union of `ϕ`-invariant sets is `ϕ`-invariant. -/
theorem isInvariant_sUnion (ϕ : Flow ℝ≥0 α) {S : Set (Set α)}
    (h : ∀ s ∈ S, IsInvariant ϕ s) : IsInvariant ϕ (⋃₀ S) := by
  intro t x hx
  obtain ⟨s, hsS, hxs⟩ := hx
  exact ⟨s, hsS, h s hsS t hxs⟩

/-- The **maximal invariant subset** of `N` under `ϕ`: the union of all `ϕ`-invariant subsets of
`N`. -/
def maximalInvariantSubset (ϕ : Flow ℝ≥0 α) (N : Set α) : Set α :=
  ⋃₀ {s | IsInvariant ϕ s ∧ s ⊆ N}

/-- The maximal invariant subset of `N` is contained in `N`. -/
theorem maximalInvariantSubset_subset (ϕ : Flow ℝ≥0 α) (N : Set α) :
    maximalInvariantSubset ϕ N ⊆ N := by
  rintro x ⟨s, ⟨_, hsN⟩, hxs⟩
  exact hsN hxs

/-- The maximal invariant subset of `N` is `ϕ`-invariant. -/
theorem isInvariant_maximalInvariantSubset (ϕ : Flow ℝ≥0 α) (N : Set α) :
    IsInvariant ϕ (maximalInvariantSubset ϕ N) :=
  isInvariant_sUnion ϕ fun _ hs => hs.1

/-- Every `ϕ`-invariant subset of `N` is contained in the maximal invariant subset of `N`; this is
the maximality property. -/
theorem subset_maximalInvariantSubset (ϕ : Flow ℝ≥0 α) {N s : Set α}
    (hinv : IsInvariant ϕ s) (hsub : s ⊆ N) : s ⊆ maximalInvariantSubset ϕ N :=
  fun _ hx => ⟨s, ⟨hinv, hsub⟩, hx⟩

/-- A compact invariant set sitting inside `N` is contained in the maximal invariant subset of
`N`. -/
theorem subset_maximalInvariantSubset_of_isInvariant (ϕ : Flow ℝ≥0 α) {N M : Set α}
    (hinv : IsInvariant ϕ M) (hsub : M ⊆ N) : M ⊆ maximalInvariantSubset ϕ N :=
  subset_maximalInvariantSubset ϕ hinv hsub

/-- A `ϕ`-invariant set is its own maximal invariant subset. -/
theorem maximalInvariantSubset_self (ϕ : Flow ℝ≥0 α) {M : Set α} (hinv : IsInvariant ϕ M) :
    maximalInvariantSubset ϕ M = M :=
  Subset.antisymm (maximalInvariantSubset_subset ϕ M)
    (subset_maximalInvariantSubset ϕ hinv Subset.rfl)

/-- When `N` is closed the maximal invariant subset of `N` is closed: its closure is invariant
(`isInvariant_closure`) and still contained in `N`, hence is itself an invariant subset of `N`, so
it is contained in the maximal invariant subset. -/
theorem isClosed_maximalInvariantSubset (ϕ : Flow ℝ≥0 α) {N : Set α} (hN : IsClosed N) :
    IsClosed (maximalInvariantSubset ϕ N) := by
  rw [← closure_eq_iff_isClosed]
  refine Subset.antisymm ?_ subset_closure
  have hclinv : IsInvariant ϕ (closure (maximalInvariantSubset ϕ N)) :=
    isInvariant_closure ϕ (isInvariant_maximalInvariantSubset ϕ N)
  have hclsub : closure (maximalInvariantSubset ϕ N) ⊆ N :=
    hN.closure_subset_iff.mpr (maximalInvariantSubset_subset ϕ N)
  exact subset_maximalInvariantSubset ϕ hclinv hclsub

/-- When `N` is compact the maximal invariant subset of `N` is compact (it is a closed subset of the
compact set `N`). -/
theorem isCompact_maximalInvariantSubset (ϕ : Flow ℝ≥0 α) {N : Set α} (hN : IsCompact N)
    (hNcl : IsClosed N) : IsCompact (maximalInvariantSubset ϕ N) :=
  hN.of_isClosed_subset (isClosed_maximalInvariantSubset ϕ hNcl)
    (maximalInvariantSubset_subset ϕ N)

/-- `M` is an **isolated invariant set** under `ϕ` if it is invariant and some compact neighborhood
`N` of `M` has `M` as its maximal invariant subset. Such an `N` is an isolating neighborhood. -/
structure IsIsolatedInvariant (ϕ : Flow ℝ≥0 α) (M : Set α) : Prop where
  /-- `M` is invariant under the flow. -/
  isInvariant : IsInvariant ϕ M
  /-- An isolating neighborhood witnessing isolation. -/
  isolating : ∃ N : Set α, IsCompact N ∧ M ⊆ interior N ∧ maximalInvariantSubset ϕ N = M

/-- A compact invariant set `M` contained in the interior of a compact set `N` whose maximal
invariant subset is exactly `M` is isolated, with `N` an isolating neighborhood. -/
theorem isIsolatedInvariant_of_maximalInvariantSubset_eq (ϕ : Flow ℝ≥0 α) {M N : Set α}
    (hinv : IsInvariant ϕ M) (hNc : IsCompact N) (hMint : M ⊆ interior N)
    (hmax : maximalInvariantSubset ϕ N = M) : IsIsolatedInvariant ϕ M :=
  ⟨hinv, ⟨N, hNc, hMint, hmax⟩⟩

/-- An isolating neighborhood of an isolated invariant set is a neighborhood of every point of the
set. -/
theorem IsIsolatedInvariant.mem_nhds {ϕ : Flow ℝ≥0 α} {M : Set α}
    (h : IsIsolatedInvariant ϕ M) :
    ∃ N : Set α, IsCompact N ∧ (∀ x ∈ M, N ∈ 𝓝 x) ∧ maximalInvariantSubset ϕ N = M := by
  obtain ⟨N, hNc, hMint, hmax⟩ := h.isolating
  exact ⟨N, hNc, fun x hx => mem_interior_iff_mem_nhds.mp (hMint hx), hmax⟩

end CRNT

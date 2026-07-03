import CRNT.Dynamics.ButlerMcGehee

/-!
# Minimal compact invariant sets

This module isolates **minimal** compact invariant sets, the recurrence-theory precursor to
minimal sets in topological dynamics. The content is general dynamical-systems material: it
depends only on a topological Hausdorff space `α` carrying a `Flow ℝ≥0 α`, independent of
reaction networks.

Invariance is closed under arbitrary intersection (`isInvariant_sInter`), dual to the union
closure that builds the maximal invariant subset. Combined with Cantor's intersection theorem,
this drives a Zorn's-lemma descent: inside any nonempty compact closed invariant set there is a
**minimal** nonempty compact closed invariant subset
(`exists_minimal_compact_invariant_subset`), one with no proper nonempty compact closed
invariant subset. A chain of such sets has its `sInter` as a lower bound — nonempty by
`IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed`, and compact, closed, and
invariant by the closure properties — so Zorn applies.

The ω-limit set of a precompact orbit is a nonempty compact closed invariant set
(`nonempty_omegaLimit_of_isCompact_absorbing`, `isCompact_omegaLimit_of_absorbing`,
`isClosed_omegaLimit`, `omegaLimit_isInvariant_two_sided`), so it contains a minimal compact
invariant subset (`exists_minimal_compact_invariant_subOmega`). That the minimal set is in
addition positive or a fixed point would require α-limit / connectedness input absent from
Mathlib, so it is not claimed here.

Intersection of two invariant sets is invariant (`isInvariant_inter`), so two minimal nonempty
compact closed invariant sets are either equal or disjoint
(`eq_or_disjoint_of_minimal_compact_invariant`): the minimal sets partition into an antichain
of pairwise-disjoint pieces. Uniqueness of the minimal subset *within* a single ω-limit — the
vertical persistence step — does not follow from this dichotomy: it needs ω-limit connectedness
together with α-limit information, both absent from Mathlib v4.31, so it is not claimed here.

Depends on: `CRNT.Dynamics.ButlerMcGehee`.
-/

open Filter Set Topology
open scoped NNReal Topology

namespace CRNT

variable {α : Type*} [TopologicalSpace α] [T2Space α]

omit [T2Space α] in
/-- The sInter of invariant sets is invariant. -/
theorem isInvariant_sInter (ϕ : Flow ℝ≥0 α) {S : Set (Set α)} (h : ∀ s ∈ S, IsInvariant ϕ s) :
    IsInvariant ϕ (⋂₀ S) := by
  intro t x hx s hs
  exact h s hs t (hx s hs)

omit [T2Space α] in
/-- A nonempty compact closed invariant set contains a minimal such subset (Zorn). -/
theorem exists_minimal_compact_invariant_subset (ϕ : Flow ℝ≥0 α) {Ω : Set α}
    (hΩne : Ω.Nonempty) (hΩcpt : IsCompact Ω) (hΩcl : IsClosed Ω) (hΩinv : IsInvariant ϕ Ω) :
    ∃ M, M ⊆ Ω ∧ Minimal (fun C => C.Nonempty ∧ IsCompact C ∧ IsClosed C ∧ IsInvariant ϕ C) M := by
  set P : Set α → Prop := fun C => C.Nonempty ∧ IsCompact C ∧ IsClosed C ∧ IsInvariant ϕ C with hP
  set S : Set (Set α) := setOf P with hS
  have hΩS : Ω ∈ S := ⟨hΩne, hΩcpt, hΩcl, hΩinv⟩
  have H : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty → ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s := by
    intro c hcS hchain hcne
    haveI : Nonempty c := hcne.to_subtype
    obtain ⟨w, hwc⟩ := hcne
    have hwS : w ∈ S := hcS hwc
    have hdir : DirectedOn (· ⊇ ·) c := by
      intro x hx y hy
      rcases hchain.total hx hy with hxy | hyx
      · exact ⟨x, hx, subset_rfl, hxy⟩
      · exact ⟨y, hy, hyx, subset_rfl⟩
    refine ⟨⋂₀ c, ?_, fun s hs => Set.sInter_subset_of_mem hs⟩
    have hclosed : IsClosed (⋂₀ c) := isClosed_sInter fun s hs => (hcS hs).2.2.1
    have hsub : ⋂₀ c ⊆ w := Set.sInter_subset_of_mem hwc
    refine ⟨?_, ?_, hclosed, ?_⟩
    · exact IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed hdir
        (fun U hU => (hcS hU).1) (fun U hU => (hcS hU).2.1) (fun U hU => (hcS hU).2.2.1)
    · exact hwS.2.1.of_isClosed_subset hclosed hsub
    · exact isInvariant_sInter ϕ fun s hs => (hcS hs).2.2.2
  obtain ⟨M, hMΩ, hMmin⟩ := zorn_superset_nonempty S H Ω hΩS
  exact ⟨M, hMΩ, hMmin⟩

omit [T2Space α] in
/-- The intersection of two invariant sets is invariant. -/
theorem isInvariant_inter (ϕ : Flow ℝ≥0 α) {s t : Set α}
    (hs : IsInvariant ϕ s) (ht : IsInvariant ϕ t) : IsInvariant ϕ (s ∩ t) :=
  fun τ _ hx => ⟨hs τ hx.1, ht τ hx.2⟩

omit [T2Space α] in
/-- Distinct minimal compact invariant sets are disjoint: two minimal nonempty compact closed
invariant sets are either equal or disjoint. -/
theorem eq_or_disjoint_of_minimal_compact_invariant (ϕ : Flow ℝ≥0 α) {M₁ M₂ : Set α}
    (h₁ : Minimal (fun C => C.Nonempty ∧ IsCompact C ∧ IsClosed C ∧ IsInvariant ϕ C) M₁)
    (h₂ : Minimal (fun C => C.Nonempty ∧ IsCompact C ∧ IsClosed C ∧ IsInvariant ϕ C) M₂) :
    M₁ = M₂ ∨ Disjoint M₁ M₂ := by
  rw [or_iff_not_imp_right]
  intro hnd
  obtain ⟨hne₁, hc₁, hcl₁, hi₁⟩ := h₁.1
  obtain ⟨hne₂, hc₂, hcl₂, hi₂⟩ := h₂.1
  have hclI : IsClosed (M₁ ∩ M₂) := hcl₁.inter hcl₂
  have hP : (M₁ ∩ M₂).Nonempty ∧ IsCompact (M₁ ∩ M₂) ∧ IsClosed (M₁ ∩ M₂) ∧ IsInvariant ϕ (M₁ ∩ M₂) :=
    ⟨not_disjoint_iff_nonempty_inter.mp hnd,
      hc₁.of_isClosed_subset hclI Set.inter_subset_left, hclI, isInvariant_inter ϕ hi₁ hi₂⟩
  have e₁ : M₁ ∩ M₂ = M₁ := h₁.eq_of_le hP Set.inter_subset_left
  have e₂ : M₁ ∩ M₂ = M₂ := h₂.eq_of_le hP Set.inter_subset_right
  exact e₁.symm.trans e₂

omit [T2Space α] in
/-- ω-limit corollary: a precompact orbit's ω-limit contains a minimal compact invariant subset. -/
theorem exists_minimal_compact_invariant_subOmega (ϕ : Flow ℝ≥0 α) (x₀ : α) {K : Set α}
    (hK : IsCompact K)
    (habs : ∃ v ∈ (Filter.atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K) :
    ∃ M, M ⊆ omegaLimit atTop ϕ {x₀} ∧
      Minimal (fun C => C.Nonempty ∧ IsCompact C ∧ IsClosed C ∧ IsInvariant ϕ C) M :=
  exists_minimal_compact_invariant_subset ϕ
    (nonempty_omegaLimit_of_isCompact_absorbing atTop ϕ {x₀} hK habs (Set.singleton_nonempty x₀))
    (isCompact_omegaLimit_of_absorbing ϕ x₀ hK habs)
    (isClosed_omegaLimit _ _ _)
    (omegaLimit_isInvariant_two_sided ϕ x₀)

end CRNT

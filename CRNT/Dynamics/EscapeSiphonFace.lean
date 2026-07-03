import CRNT.Dynamics.ButlerMcGehee
import CRNT.Dynamics.NoCriticalSiphonPersistence

/-!
# Escaping ω-points are trapped in critical-siphon faces

This module fuses the Butler–McGehee escape geometry with the critical-siphon dichotomy of a
mass-action semiflow. For a precompact positive trajectory the forward limit `ω{q}` of any
ω-point `q ∈ ω{x₀}` is a nonempty compact invariant subset of `ω{x₀}`, and every boundary point
`w ∈ ω{q}` carries a *critical* siphon on its zero set
(`forwardLimit_subOmega_criticalSiphonFace`).

When an isolated invariant set `M` fails to contain the ω-limit set (`ω{x₀} ⊄ M`), the
Butler–McGehee escaping point supplies an ω-point `q ∉ M` whose forward limit enjoys the same
five-clause payload (`exists_escape_forwardLimit_criticalSiphonFace`): the escape and the
critical-siphon face are produced together.

Under `HasNoCriticalSiphon` the face clause is vacuous, so the forward limit of every escaping
ω-point lies in the strictly positive interior
(`forwardLimit_positive_of_hasNoCriticalSiphon`).

No stable/unstable-manifold, α-limit, or connectedness structure is asserted here.

-/

open Filter Topology
open scoped BigOperators NNReal Topology

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Forward limit of an ω-point is a critical-siphon face.** For a mass-action semiflow with a
positive start `x₀`, a compact closed absorbing region `K`, and the genuine-field /
nonnegativity / affine-invariance data, the forward limit `ω{q}` of any ω-point `q ∈ ω{x₀}` is a
nonempty compact invariant subset of `ω{x₀}`, and the zero set of every `w ∈ ω{q}` is a critical
siphon. -/
theorem forwardLimit_subOmega_criticalSiphonFace (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hKcl : IsClosed K)
    (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, (y : Concentration S).Nonnegative)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx0pos : x₀.Positive) {q : Concentration S} (hq : q ∈ omegaLimit atTop ϕ {x₀}) :
    (omegaLimit atTop ϕ {q}).Nonempty ∧ IsCompact (omegaLimit atTop ϕ {q})
      ∧ IsInvariant ϕ (omegaLimit atTop ϕ {q})
      ∧ omegaLimit atTop ϕ {q} ⊆ omegaLimit atTop ϕ {x₀}
      ∧ ∀ w ∈ omegaLimit atTop ϕ {q}, ∀ P : Finset S, (∀ s, s ∈ P ↔ w s = 0) → P.Nonempty →
          N.IsCriticalSiphon P := by
  -- the orbit of `x₀` is absorbed by the compact closed region `K`
  have hsubK : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ K := by
    rintro z ⟨t, -, x, hx, rfl⟩; rw [Set.mem_singleton_iff] at hx; subst hx; exact hmaps t
  have habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K :=
    ⟨Set.univ, univ_mem, hKcl.closure_subset_iff.mpr hsubK⟩
  obtain ⟨hne, hcompact, hinv, hsub⟩ :=
    isCompact_isInvariant_nonempty_omegaLimit_of_mem ϕ x₀ hK habs hq
  refine ⟨hne, hcompact, hinv, hsub, ?_⟩
  intro w hw P hP hPne
  exact N.isCriticalSiphon_zeroSet_of_mem_omegaLimit κ hϕγ hK hmaps hωnn hgenω hωaff hx0pos
    (hsub hw) hP hPne

/-- **Butler–McGehee escape into a critical-siphon face.** If the ω-limit set `ω{x₀}` of a
precompact positive trajectory is not contained in the isolated invariant set `M` (the maximal
invariant subset of its isolating neighborhood `Nbhd`), there is an ω-point `q ∉ M` whose forward
limit `ω{q}` is a nonempty compact invariant subset of `ω{x₀}` with a critical siphon on the zero
set of every point. -/
theorem exists_escape_forwardLimit_criticalSiphonFace (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hKcl : IsClosed K)
    (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, (y : Concentration S).Nonnegative)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx0pos : x₀.Positive) {M Nbhd : Set (Concentration S)}
    (hMisol : maximalInvariantSubset ϕ Nbhd = M) (hMN : M ⊆ Nbhd)
    (hΩM : ¬ omegaLimit atTop ϕ {x₀} ⊆ M) :
    ∃ q ∈ omegaLimit atTop ϕ {x₀}, q ∉ M ∧
      (omegaLimit atTop ϕ {q}).Nonempty ∧ IsCompact (omegaLimit atTop ϕ {q})
        ∧ IsInvariant ϕ (omegaLimit atTop ϕ {q})
        ∧ omegaLimit atTop ϕ {q} ⊆ omegaLimit atTop ϕ {x₀}
        ∧ ∀ w ∈ omegaLimit atTop ϕ {q}, ∀ P : Finset S, (∀ s, s ∈ P ↔ w s = 0) → P.Nonempty →
            N.IsCriticalSiphon P := by
  obtain ⟨q, hqΩ, _, hqM⟩ :=
    exists_mem_omegaLimit_notMem_isolating ϕ x₀ hMisol hMN hΩM
  exact ⟨q, hqΩ, hqM, forwardLimit_subOmega_criticalSiphonFace N κ hϕγ hK hKcl hmaps hωnn hgenω
    hωaff hx0pos hqΩ⟩

/-- **No critical siphon ⇒ escaping forward limits are positive.** Under `HasNoCriticalSiphon`
the critical-siphon face of `forwardLimit_subOmega_criticalSiphonFace` is empty, so every point
of the forward limit `ω{q}` of an ω-point `q ∈ ω{x₀}` is strictly positive. -/
theorem forwardLimit_positive_of_hasNoCriticalSiphon (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hKcl : IsClosed K)
    (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, (y : Concentration S).Nonnegative)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx0pos : x₀.Positive) (hncs : N.HasNoCriticalSiphon)
    {q : Concentration S} (hq : q ∈ omegaLimit atTop ϕ {x₀})
    {w : Concentration S} (hw : w ∈ omegaLimit atTop ϕ {q}) :
    w.Positive := by
  obtain ⟨_, _, _, hsub, _⟩ :=
    forwardLimit_subOmega_criticalSiphonFace N κ hϕγ hK hKcl hmaps hωnn hgenω hωaff hx0pos hq
  exact omegaLimit_positive_of_hasNoCriticalSiphon N κ hϕγ hK hmaps hωnn hgenω hωaff hx0pos hncs
    (hsub hw)

end Network

end CRNT

-- Depends on: CRNT.Dynamics.ButlerMcGehee, CRNT.Dynamics.NoCriticalSiphonPersistence.

import CRNT.Dynamics.StrictInflow
import CRNT.Dynamics.BoundaryOmegaSiphon
import CRNT.Dynamics.ButlerMcGehee

/-!
# Facet repulsion and the codimension-1 persistence step

Persistence past the no-critical-siphon regime combines facet repulsion (Anderson & Shiu,
_The dynamics of weakly reversible population processes near facets_, 2010) with the
Butler–McGehee escape principle, here specialized to a **codimension-1 boundary facet** — the
face `SiphonFace {s*}` on which a single species `s*` vanishes.

The analysis splits on whether the vanishing-species set `{s*}` is a siphon.

* **Non-siphon facet (tractable, proven here).** If `{s*}` is *not* a siphon, the mass-action
  field has a strictly positive `s*`-component everywhere on the facet
  (`massActionVectorField_pos_on_facet_of_not_isSiphon`), specializing the strict-inflow engine
  `massActionVectorField_pos_of_not_isSiphon`. The facet is strictly *repelling*: trajectories
  on it are pushed off into the interior.

  Structurally this forbids ω-limit points. The zero set of any boundary ω-limit point is a
  siphon (`isSiphon_zeroSet_of_mem_omegaLimit`), so no ω-limit point can have zero set exactly
  `{s*}` when `{s*}` is not a siphon (`notMem_omegaLimit_of_zeroSet_not_isSiphon`). A
  non-siphon facet carries no ω-limit point pinned exactly to it.

  Feeding this into the Butler–McGehee escape core: an isolated invariant set `M` sitting in a
  non-siphon facet cannot be the whole ω-limit set unless `Ω ⊆ M`, and if `Ω ⊄ M` there is an
  explicit ω-point escaping every isolating neighborhood
  (`exists_omegaLimit_escape_of_not_subset_isolating`). An isolated boundary-facet invariant
  set cannot trap the ω-limit set.

* **Critical-siphon facet (taken as a hypothesis, not constructed here).** When `{s*}` *is* a
  critical siphon, the field's `s*`-component vanishes on the facet (the field is tangent there,
  by `massActionVectorField_eq_zero_on_siphonFace`), so the first-order repulsion above gives
  nothing. The Anderson & Shiu argument shows the facet is still repelled, but only through a
  **quantitative higher-order near-facet estimate**: along a trajectory approaching the facet the
  `s*`-coordinate is bounded below by a strictly positive influx that survives to second order in
  the distance to the facet, so the time spent near the facet is integrably small and the ω-limit
  set still escapes. Formalizing this needs a near-facet differential inequality / Lyapunov–exponent
  bound on the mass-action field, which is not constructed in this layer (no quantitative subtangent
  estimate, no Anderson & Shiu influx lemma); the precise missing statement is recorded in the note
  below.

Depends on: `CRNT.Dynamics.StrictInflow`,
`CRNT.Dynamics.BoundaryOmegaSiphon`, `CRNT.Dynamics.ButlerMcGehee`.
-/

open Filter Set Topology
open scoped BigOperators NNReal Topology

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Non-siphon facet repulsion (codimension-1).** On the boundary facet `SiphonFace {s*}`
where the single species `s*` vanishes, if `{s*}` is *not* a siphon the mass-action field has a
strictly positive `s*`-component: `0 < N.massActionVectorField κ w s*`. The facet is strictly
repelling. This specializes the strict-inflow engine `massActionVectorField_pos_of_not_isSiphon`
to the singleton zero set. -/
theorem massActionVectorField_pos_on_facet_of_not_isSiphon (N : Network S) (κ : N.RateConstants)
    {sstar : S} (hns : ¬ N.IsSiphon ({sstar} : Finset S))
    {w : Concentration S} (hwnn : Concentration.Nonnegative w)
    (hzero : ∀ s, w s = 0 ↔ s = sstar) :
    0 < N.massActionVectorField κ w sstar := by
  have hP : ∀ s, s ∈ ({sstar} : Finset S) ↔ w s = 0 := by
    intro s
    rw [Finset.mem_singleton, hzero]
  obtain ⟨s, hsP, hpos⟩ := N.massActionVectorField_pos_of_not_isSiphon κ hwnn hP hns
  rwa [Finset.mem_singleton.mp hsP] at hpos

/-- **A non-siphon zero set carries no ω-limit point.** Contrapositive of
`isSiphon_zeroSet_of_mem_omegaLimit`: if the species set `P` is not a siphon, then no ω-limit
point of a bounded mass-action orbit has zero set exactly `P`. In particular a non-siphon
codimension-1 facet `{s*}` contains no ω-limit point pinned to it. -/
theorem notMem_omegaLimit_of_zeroSet_not_isSiphon (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    {P : Finset S} (hns : ¬ N.IsSiphon P)
    {w : Concentration S} (hP : ∀ s, s ∈ P ↔ w s = 0) :
    w ∉ omegaLimit atTop ϕ {x₀} :=
  fun hw => hns (N.isSiphon_zeroSet_of_mem_omegaLimit κ hϕγ hK hmaps hωnn hgenω hw hP)

end Network

variable {α : Type*} [TopologicalSpace α]

/-- **Codimension-1 Butler–McGehee escape.** For the ω-limit set `Ω` of a precompact orbit and a
compact isolated invariant set `M` (its isolating neighborhood given by `M ⊆ N`,
`maximalInvariantSubset ϕ N = M`), if `Ω ⊄ M` then there is an explicit ω-point `q ∈ Ω` lying
outside both the isolating neighborhood `N` and `M`. An isolated invariant set cannot be the
whole ω-limit set without containing it: it cannot trap `Ω`. This is the structural step
combined with `notMem_omegaLimit_of_zeroSet_not_isSiphon` to conclude that an isolated invariant
set confined to a non-siphon facet does not exhaust `Ω`. -/
theorem exists_omegaLimit_escape_of_not_subset_isolating (ϕ : Flow ℝ≥0 α) (x₀ : α)
    {M N : Set α} (hMisol : maximalInvariantSubset ϕ N = M) (hMN : M ⊆ N)
    (hΩM : ¬ omegaLimit atTop ϕ {x₀} ⊆ M) :
    ∃ q ∈ omegaLimit atTop ϕ {x₀}, q ∉ N ∧ q ∉ M :=
  exists_mem_omegaLimit_notMem_isolating ϕ x₀ hMisol hMN hΩM

/- **Critical-siphon near-facet repulsion (taken as a hypothesis, not constructed here).** When the
vanishing-species set `{s*}` is a critical siphon the first-order repulsion vanishes — the field is
tangent to the facet. The Anderson & Shiu conclusion (the facet is still repelled, so it carries no
ω-limit point) requires a quantitative higher-order near-facet estimate: a strictly positive lower
bound on the `s*`-influx, surviving to second order in the distance to the facet, that makes
trajectories spend only integrably-small time near the facet. The missing statement is a near-facet
differential inequality on the mass-action field of the shape
`∃ c > 0, ∀ x near the facet, 0 ≤ x → c * (dist x facet) ≤ N.massActionVectorField κ x s*`
(an Anderson & Shiu influx bound). No quantitative subtangent / Lyapunov-exponent estimate for the
mass-action field is constructed here, so the critical-siphon codimension-1 case is not closed. -/

end CRNT

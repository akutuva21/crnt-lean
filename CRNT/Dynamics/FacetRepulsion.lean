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

* **Critical-siphon facet (not closed here).** When `{s*}` *is* a critical siphon, the field's
  `s*`-component vanishes on the facet (the field is tangent there, by
  `massActionVectorField_eq_zero_on_siphonFace`), so the first-order repulsion above gives nothing.
  The Anderson & Shiu argument shows the facet is still repelled through a quantitative higher-order
  near-facet estimate. Its influx half is available for a singleton siphon in
  `CRNT.Dynamics.CriticalSiphonNearFacetInflux` (`massActionVectorField_singleton_facet_ge`, a linear
  lower bound on the `s*`-component), and `CRNT.Dynamics.CriticalSiphonDissipationRepulsion` combines
  it with a near-facet relative-entropy dissipation bound to yield a uniform positive facet floor. That
  dissipation bound is carried as a hypothesis, and the floor is not yet assembled into an ω-limit /
  persistence conclusion, so the critical-siphon codimension-1 case is not closed in this layer; the
  precise remaining statement is recorded in the note below.

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

/- **Critical-siphon near-facet repulsion (not closed here).** When the vanishing-species set `{s*}`
is a critical siphon the first-order repulsion vanishes: the field is tangent to the facet. The
Anderson & Shiu conclusion (the facet is still repelled, so it carries no ω-limit point) requires a
quantitative higher-order near-facet estimate. The influx lower bound of that shape,
`-(c * x s*) ≤ N.massActionVectorField κ x s*`, is proven for a singleton siphon in
`CRNT.Dynamics.CriticalSiphonNearFacetInflux`; combined with a near-facet relative-entropy dissipation
bound it yields a uniform positive facet floor in `CRNT.Dynamics.CriticalSiphonDissipationRepulsion`.
What remains is that dissipation bound, still carried as a hypothesis, and the assembly of the facet
floor into an ω-limit / persistence conclusion, so the critical-siphon codimension-1 case is not
closed. -/

end CRNT

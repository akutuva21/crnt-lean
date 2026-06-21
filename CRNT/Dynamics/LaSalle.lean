import Mathlib.Dynamics.OmegaLimit
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# LaSalle's invariance principle (abstract)

For a flow `ϕ` and a continuous function `V` that is nonincreasing along the forward orbit
of a point `x` whose orbit has compact closure, the ω-limit set `ω(x)` is nonempty,
invariant, and `V` is **constant** on it (`Flow.laSalle`). Combined with a strict
dissipation `dV/dt < 0` off an equilibrium set, this forces `ω(x)` into that set — the
standard route from a Lyapunov function to asymptotic stability.

This module is general dynamical-systems content (no chemistry); it is written in Mathlib
style against `Mathlib.Dynamics.{Flow, OmegaLimit}` with an eye toward upstreaming. It is
**stable** and `sorry`-free.
-/

open Filter Topology Set

namespace Flow

variable {α : Type*} [TopologicalSpace α]

/-- **LaSalle's invariance principle.** Let `ϕ` be a flow on `α`, `V : α → ℝ` continuous,
and `x` a point whose forward `V`-values are nonincreasing (`hmono`) and whose orbit is
eventually absorbed by a compact set `K` (`habs`). Then the ω-limit set `ω(x)` is nonempty,
invariant under the flow, and `V` is constant on it. -/
theorem laSalle (ϕ : Flow ℝ α) {V : α → ℝ} (hV : Continuous V) (x : α) {K : Set α}
    (hK : IsCompact K)
    (habs : ∃ v ∈ (atTop : Filter ℝ), closure (Set.image2 ϕ v {x}) ⊆ K)
    (hmono : ∀ s t : ℝ, 0 ≤ s → s ≤ t → V (ϕ t x) ≤ V (ϕ s x)) :
    ∃ c : ℝ, (omegaLimit atTop ϕ {x}).Nonempty ∧ IsInvariant ϕ (omegaLimit atTop ϕ {x}) ∧
      ∀ y ∈ omegaLimit atTop ϕ {x}, V y = c := by
  -- `K` is `V`-bounded below; extract a uniform lower bound `m`.
  obtain ⟨m, hm⟩ := (hK.image hV).bddBelow
  obtain ⟨v, hv, hvK⟩ := habs
  have hmemK : ∀ t ∈ v, ϕ t x ∈ K := fun t ht =>
    hvK (subset_closure (Set.mem_image2_of_mem ht (Set.mem_singleton x)))
  -- the forward `V`-values are bounded below by `m`.
  have hg_lb : ∀ s : ℝ, 0 ≤ s → m ≤ V (ϕ s x) := by
    intro s hs
    rw [Filter.mem_atTop_sets] at hv
    obtain ⟨a, ha⟩ := hv
    have hmem : ϕ (max a s) x ∈ K := hmemK _ (ha _ (le_max_left a s))
    exact (hm (Set.mem_image_of_mem V hmem)).trans (hmono s (max a s) hs (le_max_right a s))
  -- reparametrize to a globally antitone, bounded-below function and take its limit.
  set h : ℝ → ℝ := fun t => V (ϕ (max t 0) x) with hh
  have h_anti : Antitone h := fun s t hst =>
    hmono (max s 0) (max t 0) (le_max_right s 0) (max_le_max hst le_rfl)
  have h_bdd : BddBelow (Set.range h) := by
    refine ⟨m, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact hg_lb (max t 0) (le_max_right t 0)
  set c : ℝ := ⨅ t, h t with hc
  have htendsto_h : Tendsto h atTop (𝓝 c) := tendsto_atTop_ciInf h_anti h_bdd
  have htendsto : Tendsto (fun t => V (ϕ t x)) atTop (𝓝 c) := by
    refine htendsto_h.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simp only [hh, max_eq_left ht]
  refine ⟨c, ?_, ?_, ?_⟩
  · -- nonempty
    exact nonempty_omegaLimit_of_isCompact_absorbing _ _ _ hK ⟨v, by
      rw [Filter.mem_atTop_sets] at hv ⊢; exact hv, hvK⟩ (Set.singleton_nonempty x)
  · -- invariant
    exact isInvariant_omegaLimit atTop ϕ {x}
      fun t => tendsto_atTop_add_const_left atTop t tendsto_id
  · -- `V` is constant on `ω(x)`, equal to the limit `c`
    intro y hy
    rw [mem_omegaLimit_singleton_iff_mapClusterPt] at hy
    have hVcl : ClusterPt (V y) (𝓝 c) :=
      ClusterPt.mono (hy.continuousAt_comp hV.continuousAt) htendsto
    by_contra hne
    exact hVcl.ne (disjoint_iff.mp (disjoint_nhds_nhds.mpr hne))

end Flow

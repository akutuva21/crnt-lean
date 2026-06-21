import Mathlib.Dynamics.OmegaLimit
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# LaSalle's invariance principle (forward semiflows)

A **forward semiflow** is an action of `ℝ≥0` by continuous maps — exactly `Flow ℝ≥0 α`,
since `Flow τ α` only requires `τ` to be an additive monoid. (Mass-action dynamics is a
forward semiflow: solutions stay positive and are confined forward, but the backward flow
can leave the orthant in finite time, so there is no two-sided `Flow ℝ`.)

`Flow.laSalle` is **LaSalle's invariance principle**: if a continuous `V` is nonincreasing
along the forward orbit of `x` and that orbit is eventually absorbed by a compact set, then
the ω-limit set `ω(x)` is nonempty, invariant, and `V` is **constant** on it. Combined with
a strict dissipation `V̇ < 0` off an equilibrium set, this forces `ω(x)` into that set — the
standard route from a Lyapunov function to asymptotic stability.

This module is general dynamical-systems content (no chemistry), Mathlib-style on
`Mathlib.Dynamics.{Flow, OmegaLimit}`, written with an eye toward upstreaming. It is
**stable** and `sorry`-free.
-/

open Filter Topology Set
open scoped NNReal

namespace Flow

variable {α : Type*} [TopologicalSpace α]

/-- **LaSalle's invariance principle.** Let `ϕ` be a forward semiflow on `α`, `V : α → ℝ`
continuous and nonincreasing along the forward orbit of `x` (`hmono`), whose orbit is
eventually absorbed by a compact set `K` (`habs`). Then the ω-limit set `ω(x)` is nonempty,
invariant under the semiflow, and `V` is constant on it. -/
theorem laSalle (ϕ : Flow ℝ≥0 α) {V : α → ℝ} (hV : Continuous V) (x : α) {K : Set α}
    (hK : IsCompact K)
    (habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x}) ⊆ K)
    (hmono : ∀ s t : ℝ≥0, s ≤ t → V (ϕ t x) ≤ V (ϕ s x)) :
    ∃ c : ℝ, (omegaLimit atTop ϕ {x}).Nonempty ∧ IsInvariant ϕ (omegaLimit atTop ϕ {x}) ∧
      ∀ y ∈ omegaLimit atTop ϕ {x}, V y = c := by
  obtain ⟨m, hm⟩ := (hK.image hV).bddBelow
  obtain ⟨v, hv, hvK⟩ := habs
  have hmemK : ∀ t ∈ v, ϕ t x ∈ K := fun t ht =>
    hvK (subset_closure (Set.mem_image2_of_mem ht (Set.mem_singleton x)))
  have h_anti : Antitone fun t : ℝ≥0 => V (ϕ t x) := fun s t hst => hmono s t hst
  have h_lb : ∀ t : ℝ≥0, m ≤ V (ϕ t x) := by
    intro t
    obtain ⟨a, ha⟩ := Filter.mem_atTop_sets.1 hv
    exact (hm (Set.mem_image_of_mem V (hmemK _ (ha _ (le_max_left a t))))).trans
      (hmono t (max a t) (le_max_right a t))
  have h_bdd : BddBelow (Set.range fun t : ℝ≥0 => V (ϕ t x)) :=
    ⟨m, by rintro _ ⟨t, rfl⟩; exact h_lb t⟩
  set c : ℝ := ⨅ t, V (ϕ t x) with hc
  have htendsto : Tendsto (fun t : ℝ≥0 => V (ϕ t x)) atTop (𝓝 c) :=
    tendsto_atTop_ciInf h_anti h_bdd
  refine ⟨c, ?_, ?_, ?_⟩
  · exact nonempty_omegaLimit_of_isCompact_absorbing _ _ _ hK ⟨v, hv, hvK⟩
      (Set.singleton_nonempty x)
  · exact isInvariant_omegaLimit atTop ϕ {x}
      fun t => tendsto_atTop_mono (fun _ => le_add_self) tendsto_id
  · intro y hy
    rw [mem_omegaLimit_singleton_iff_mapClusterPt] at hy
    have hVcl : ClusterPt (V y) (𝓝 c) :=
      ClusterPt.mono (hy.continuousAt_comp hV.continuousAt) htendsto
    by_contra hne
    exact hVcl.ne (disjoint_iff.mp (disjoint_nhds_nhds.mpr hne))

end Flow

import CRNT.Dynamics.LaSalle

/-!
# Negative invariance of the ω-limit set of a precompact semiflow orbit

Mathlib's `isInvariant_omegaLimit` gives *forward* invariance of an ω-limit set: `ϕ t` maps it
into itself. For a semiflow over `ℝ≥0` the converse — *negative* (backward) invariance, that
every ω-point has a `ϕ t`-preimage inside the ω-limit set — is not available, yet it is exactly
what boundary arguments need (flowing a boundary ω-point backward to expose a contradiction).

`omegaLimit_negInvariant` supplies it for an orbit absorbed by a compact set in a Hausdorff
space. The argument is the classical one, phrased with filters: for `w` in the ω-limit set and a
time `t`, the predecessors `s ↦ ϕ (s - t) x₀` along the index filter `atTop ⊓ comap (ϕ · x₀) (𝓝 w)`
stay in the compact set, hence cluster at some `w'`; that cluster point is itself an ω-point
(`s - t → ∞`), and continuity of `ϕ t` together with `ϕ t (ϕ (s - t) x₀) = ϕ s x₀ → w` forces
`ϕ t w' = w` in a `T2Space`.

This is general dynamical-systems content over `Flow ℝ≥0`, independent of reaction networks.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.LaSalle`.
-/

open Filter Set Topology
open scoped NNReal Topology

namespace CRNT

variable {α : Type*} [TopologicalSpace α]

/-- **Negative invariance of the ω-limit set.** For a semiflow `ϕ : Flow ℝ≥0 α` on a Hausdorff
space whose forward orbit through `x₀` is contained in a compact set `K`, every point `w` of the
ω-limit set has, for each time `t`, a `ϕ t`-preimage `w'` *inside the ω-limit set*: `ϕ t w' = w`.
Together with the forward invariance `isInvariant_omegaLimit`, this gives `ϕ t '' ω = ω`. -/
theorem omegaLimit_negInvariant [T2Space α] (ϕ : Flow ℝ≥0 α) (x₀ : α) {K : Set α}
    (hK : IsCompact K) (hmaps : ∀ s : ℝ≥0, ϕ s x₀ ∈ K) (t : ℝ≥0)
    {w : α} (hw : w ∈ omegaLimit atTop ϕ {x₀}) :
    ∃ w' ∈ omegaLimit atTop ϕ {x₀}, ϕ t w' = w := by
  classical
  set g : ℝ≥0 → α := fun s => ϕ s x₀ with hg
  -- `w` is a cluster point of the orbit net.
  have hwc : ClusterPt w (map g atTop) :=
    (mem_omegaLimit_singleton_iff_mapClusterPt (f := atTop) (ϕ := ϕ) x₀ w).mp hw
  -- the pulled-back index filter selecting large times where the orbit is near `w`
  set C : Filter ℝ≥0 := atTop ⊓ comap g (𝓝 w) with hC
  have hCle : C ≤ atTop := inf_le_left
  have hmapgC : map g C = map g atTop ⊓ 𝓝 w := by rw [hC]; exact Filter.push_pull g atTop (𝓝 w)
  have hmapgC_nebot : (map g C).NeBot := by rw [hmapgC, inf_comm]; exact hwc
  haveI hC_nebot : C.NeBot := hmapgC_nebot.of_map
  -- the predecessor net `s ↦ ϕ (s - t) x₀`
  set p : ℝ≥0 → α := fun s => ϕ (s - t) x₀ with hp
  have hsub : Tendsto (fun s : ℝ≥0 => s - t) atTop atTop := by
    rw [tendsto_atTop_atTop]
    refine fun b => ⟨b + t, fun s hs => ?_⟩
    have h := tsub_le_tsub_right hs t
    rwa [add_tsub_cancel_right] at h
  -- predecessors stay in `K`
  have hpK : map p C ≤ 𝓟 K := by
    rw [le_principal_iff, Filter.mem_map]
    exact Filter.univ_mem' fun s => hmaps (s - t)
  haveI hmappC_nebot : (map p C).NeBot := (map_neBot_iff p).mpr hC_nebot
  -- predecessor filter refines the orbit filter (since `s - t → ∞`)
  have hpeq : map p C = map g (map (fun s : ℝ≥0 => s - t) C) := by rw [Filter.map_map]; rfl
  have hple : map p C ≤ map g atTop := by
    rw [hpeq]; exact map_mono ((map_mono hCle).trans hsub)
  -- a cluster point `w'` of the predecessors, in `K`
  obtain ⟨w', _, hw'cp⟩ := hK.exists_clusterPt hpK
  have hw'omega : w' ∈ omegaLimit atTop ϕ {x₀} :=
    (mem_omegaLimit_singleton_iff_mapClusterPt (f := atTop) (ϕ := ϕ) x₀ w').mpr (hw'cp.mono hple)
  refine ⟨w', hw'omega, ?_⟩
  -- along `C`, `ϕ t ∘ p` agrees with the orbit, which tends to `w`
  have hev : (fun s => ϕ t (p s)) =ᶠ[C] g := by
    filter_upwards [(eventually_ge_atTop t).filter_mono hCle] with s hs
    show ϕ t (ϕ (s - t) x₀) = ϕ s x₀
    rw [← ϕ.map_add, add_tsub_cancel_of_le hs]
  have hgC : Tendsto g C (𝓝 w) := by rw [Tendsto, hmapgC]; exact inf_le_right
  have hϕtp : Tendsto (fun s => ϕ t (p s)) C (𝓝 w) := Filter.Tendsto.congr' hev.symm hgC
  -- continuity of `ϕ t` propagates the cluster point: `ϕ t w'` and `w` share a neighborhood net
  have hcont : Tendsto (fun x => ϕ t x) (𝓝 w') (𝓝 (ϕ t w')) :=
    (ϕ.continuous continuous_const continuous_id).tendsto w'
  have hLle : map (fun x => ϕ t x) (𝓝 w' ⊓ map p C) ≤ 𝓝 (ϕ t w') ⊓ 𝓝 w := by
    refine le_inf ((map_mono inf_le_left).trans hcont) ?_
    refine (map_mono inf_le_right).trans ?_
    rw [Filter.map_map]; exact hϕtp
  haveI hLnebot : (map (fun x => ϕ t x) (𝓝 w' ⊓ map p C)).NeBot :=
    (map_neBot_iff _).mpr hw'cp
  haveI hfin : (𝓝 (ϕ t w') ⊓ 𝓝 w).NeBot := hLnebot.mono hLle
  have e1 : Tendsto (id : α → α) (𝓝 (ϕ t w') ⊓ 𝓝 w) (𝓝 (ϕ t w')) := by
    simp only [Tendsto, Filter.map_id]; exact inf_le_left
  have e2 : Tendsto (id : α → α) (𝓝 (ϕ t w') ⊓ 𝓝 w) (𝓝 w) := by
    simp only [Tendsto, Filter.map_id]; exact inf_le_right
  exact tendsto_nhds_unique e1 e2

end CRNT

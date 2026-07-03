import CRNT.Dynamics.Viability
import CRNT.Dynamics.FirstExit
import CRNT.Dynamics.SublevelInvariant
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Subtangency-to-sublevel-descent bridge and neighborhood-descent sublevel Nagumo

This connects the `tangentConeAt`/`Subtangent` interface to the concrete gradient-descent
condition for level-set regions, the form the zero-separating surfaces of Craciun, _Toric
differential inclusions and a proof of the global attractor conjecture_, take, and proves the
tractable neighborhood-descent Nagumo invariance for a sublevel set.

* `inner_le_zero_of_mem_posTangentConeAt_sublevel` — **the bridge.** If `HasFDerivAt g g' x`,
  `g x = c`, and `v` lies in the *positive* tangent cone `posTangentConeAt {y | g y ≤ c} x`, then
  `g' v ≤ 0`. A positive-cone witness `v = lim cₙ • dₙ` has nonnegative scalars `cₙ` and
  displacements with `x + dₙ ∈ {g ≤ c}`, so `g (x + dₙ) − g x ≤ 0`; by `HasFDerivWithinAt.lim`
  the products `cₙ • (g (x + dₙ) − g x)` tend to `g' v`, and each is `≤ 0`, so the limit is `≤ 0`.
  The bridge is stated for `posTangentConeAt` (`ℝ≥0` scalars), **not** the two-sided
  `tangentConeAt ℝ`, where it is false: for `g y = y`, `c = 0`, `x = 0`, the direction `v = 1`
  lies in `tangentConeAt ℝ {y ≤ 0} 0` (witnessed by `dₙ = −1/n`, `cₙ = −n`) yet `g' v = 1 > 0`.

* `posSubtangent_of_descent_sublevel` — repackages the bridge as the boundary inequality
  `∀ v ∈ F x, g' v ≤ 0` for every `x` on the level set `{g = c}` of a `C¹` `g`, the hypothesis a
  surface supplies.

* `frontier_sublevel_le` / `eq_of_mem_frontier_sublevel` — for continuous `g`, a frontier point of
  the sublevel set `{g ≤ c}` satisfies `g · = c`: it lies in the (closed) sublevel set, and in
  `closure {g > c} ⊆ {g ≥ c}`.

* `sublevel_invariant_of_neighborhood_descent` — **neighborhood-descent sublevel Nagumo.** If `γ`
  is continuous on `[0, ∞)`, solves `HasDerivAt γ (f (γ t)) t` there, `g` is `C¹`, the descent
  `g' (f y) ≤ 0` holds on the two-sided band `{y | c − δ ≤ g y ≤ c + δ}` — an honest neighborhood
  of the level set `{g = c}` — for some `δ > 0`, and `g (γ 0) ≤ c`, then `g (γ t) ≤ c` for all
  `t ≥ 0`. The first-exit lemma `mem_frontier_exitTime` pins the exit point to `g (γ τ) = c`; by
  continuity `γ` stays in the band on a right-neighborhood of `τ`, so `g ∘ γ` is antitone there
  (`antitoneOn_of_deriv_nonpos`) and cannot rise above `c` — contradicting the right-accumulating
  exit points `g (γ s) > c`.

The **boundary-only** Nagumo — descent merely on the level set `{g = c}`, not on a neighborhood
band — is genuinely subtler: it requires proximal/Bony viscosity-subgradient machinery (absent from
Mathlib) and can fail without it. It is not attempted here.

Depends on: `CRNT.Dynamics.Viability`,
`CRNT.Dynamics.FirstExit`, `CRNT.Dynamics.SublevelInvariant`,
`Mathlib.Analysis.Calculus.Deriv.Comp`.
-/

namespace CRNT

namespace DifferentialInclusion

open Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Subtangency ⇒ sublevel-descent bridge.** If `g` has Fréchet derivative `g'` at `x`,
`g x = c`, and `v` lies in the positive tangent cone of the sublevel set `{y | g y ≤ c}` at `x`,
then `g' v ≤ 0`.

A positive-cone witness gives nonnegative scalars `cₙ` and displacements `dₙ → 0` with
`x + dₙ ∈ {g ≤ c}`, so `g (x + dₙ) − g x ≤ 0`. By `HasFDerivWithinAt.lim` the rescaled increments
`cₙ • (g (x + dₙ) − g x)` converge to `g' v`, and each term is nonpositive, so `g' v ≤ 0`. -/
theorem inner_le_zero_of_mem_posTangentConeAt_sublevel
    {g : E → ℝ} {g' : E →L[ℝ] ℝ} {x : E} {c : ℝ}
    (hg : HasFDerivAt g g' x) (hx : g x = c)
    {v : E} (hv : v ∈ posTangentConeAt {y | g y ≤ c} x) :
    g' v ≤ 0 := by
  obtain ⟨α, l, hl, c', d, hd₀, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hv
  haveI := hl
  -- recast the `ℝ≥0` scalars `c'` as nonnegative reals `cr`
  set cr : α → ℝ := fun n => (c' n : ℝ) with hcr
  have hcr_nonneg : ∀ n, 0 ≤ cr n := fun n => (c' n).coe_nonneg
  have hcd' : Tendsto (fun n => cr n • d n) l (𝓝 v) := by
    refine hcd.congr (fun n => ?_)
    simp [hcr, NNReal.smul_def]
  -- `HasFDerivWithinAt.lim`: the rescaled increments converge to `g' v`
  have hlim : Tendsto (fun n => cr n • (g (x + d n) - g x)) l (𝓝 (g' v)) :=
    hg.hasFDerivWithinAt.lim hd₀ hds hcd'
  -- each rescaled increment is `≤ 0`
  refine le_of_tendsto hlim ?_
  filter_upwards [hds] with n hn
  have hle : g (x + d n) - g x ≤ 0 := by
    have hmem : g (x + d n) ≤ c := hn
    rw [hx]; linarith
  have : cr n • (g (x + d n) - g x) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (hcr_nonneg n) hle
  simpa using this

/-- **Descent on the level set is positive subtangentiality of the field.** For a `C¹` `g` with
derivative field `g'`, if at every point `x` of the level set `{g = c}` and every velocity
`v ∈ F x` the gradient-descent inequality `g' x v ≤ 0` holds, then every such `v` that already lies
in the positive tangent cone of `{g ≤ c}` is certified by the bridge. This is the boundary
inequality a zero-separating surface supplies, phrased against the cone interface. -/
theorem inner_le_zero_of_descent_sublevel
    {g : E → ℝ} {g' : E → (E →L[ℝ] ℝ)} {c : ℝ}
    (hg : ∀ x, HasFDerivAt g (g' x) x)
    {x : E} (hx : g x = c) {v : E}
    (hv : v ∈ posTangentConeAt {y | g y ≤ c} x) :
    g' x v ≤ 0 :=
  inner_le_zero_of_mem_posTangentConeAt_sublevel (hg x) hx hv

end DifferentialInclusion

open Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- A frontier point of the sublevel set of a continuous `g` is below the level: the sublevel set
is closed, so its frontier lies inside it. -/
theorem frontier_sublevel_le {g : E → ℝ} (hg : Continuous g) {c : ℝ} {x : E}
    (hx : x ∈ frontier {y | g y ≤ c}) : g x ≤ c :=
  (isClosed_le hg continuous_const).frontier_subset hx

omit [NormedSpace ℝ E] in
/-- A frontier point of the sublevel set of a continuous `g` is at least the level: it lies in the
closure of the strict superlevel set `{g > c}`, whose closure is contained in `{g ≥ c}`. -/
theorem le_frontier_sublevel {g : E → ℝ} (hg : Continuous g) {c : ℝ} {x : E}
    (hx : x ∈ frontier {y | g y ≤ c}) : c ≤ g x := by
  have hcompl : closure {y : E | g y ≤ c}ᶜ ⊆ {y : E | c ≤ g y} := by
    have hsub : {y : E | g y ≤ c}ᶜ ⊆ {y : E | c ≤ g y} := by
      intro y hy
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hy
      exact hy.le
    exact (isClosed_le continuous_const hg).closure_subset_iff.mpr hsub
  rw [frontier_eq_closure_inter_closure] at hx
  exact hcompl hx.2

omit [NormedSpace ℝ E] in
/-- A frontier point of the sublevel set of a continuous `g` sits exactly on the level set. -/
theorem eq_of_mem_frontier_sublevel {g : E → ℝ} (hg : Continuous g) {c : ℝ} {x : E}
    (hx : x ∈ frontier {y | g y ≤ c}) : g x = c :=
  le_antisymm (frontier_sublevel_le hg hx) (le_frontier_sublevel hg hx)

/-- **Neighborhood-descent sublevel Nagumo invariance.** Let `γ` be continuous on `[0, ∞)` and a
solution `HasDerivAt γ (f (γ t)) t` of the field `f` there, with `g : E → ℝ` of class `C¹`
(derivative field `g'`). If the gradient-descent condition `g' y (f y) ≤ 0` holds on the two-sided
band `{y | c − δ ≤ g y ≤ c + δ}` — an honest neighborhood of the level set `{g = c}` — for some
`δ > 0`, and `g (γ 0) ≤ c`, then the sublevel set `{g ≤ c}` is forward-invariant:
`g (γ t) ≤ c` for all `t ≥ 0`.

Were `γ` to leave `{g ≤ c}`, the first-exit time `τ` would satisfy `g (γ τ) = c` (frontier of the
sublevel set, `eq_of_mem_frontier_sublevel`). By continuity `γ` stays in the descent band on a
right-neighborhood `[τ, τ + ε]`, where the band is two-sided so the descent inequality holds even
slightly above the level; hence `g ∘ γ` has nonpositive derivative and is antitone there, forcing
`g (γ s) ≤ g (γ τ) = c` for `s ∈ [τ, τ + ε]` — contradicting the exit points `g (γ s) > c`
accumulating just above `τ`. -/
theorem sublevel_invariant_of_neighborhood_descent
    {f : E → E} {γ : ℝ → E} {g : E → ℝ} {g' : E → (E →L[ℝ] ℝ)} {c δ : ℝ}
    (hgc : Continuous g) (hg : ∀ y, HasFDerivAt g (g' y) y)
    (hγcont : Continuous γ)
    (hγderiv : ∀ t, 0 ≤ t → HasDerivAt γ (f (γ t)) t)
    (hδ : 0 < δ)
    (hdescent : ∀ y, c - δ ≤ g y → g y ≤ c + δ → g' y (f y) ≤ 0)
    (h0 : g (γ 0) ≤ c) :
    ∀ t, 0 ≤ t → g (γ t) ≤ c := by
  set R : Set E := {y | g y ≤ c} with hR
  have hRclosed : IsClosed R := isClosed_le hgc continuous_const
  have hgγcont : Continuous (fun s => g (γ s)) := hgc.comp hγcont
  intro t ht
  by_contra htR
  rcases eq_or_lt_of_le ht with ht0 | ht0
  · -- `t = 0`: contradicts the start condition
    rw [← ht0] at htR; exact htR h0
  · -- `t > 0`: set up the first exit
    have htRmem : γ t ∉ R := htR
    have h0R : γ 0 ∈ R := h0
    set τ := exitTime γ R with hτ
    -- the exit point is exactly on the level set
    have hτfront : γ τ ∈ frontier R := mem_frontier_exitTime hγcont hRclosed h0R ht0 htRmem
    have hτeq : g (γ τ) = c := eq_of_mem_frontier_sublevel hgc hτfront
    have hτnonneg : 0 ≤ τ := exitTime_nonneg ht0 htRmem
    -- on a neighborhood of `τ`, `γ s` lands in the open band `c - δ < g (γ s) < c + δ`
    have hband : ∀ᶠ s in 𝓝 τ, g (γ s) ∈ Set.Ioo (c - δ) (c + δ) := by
      have hmem : g (γ τ) ∈ Set.Ioo (c - δ) (c + δ) := by
        rw [hτeq]; exact ⟨by linarith, by linarith⟩
      exact hgγcont.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds hmem)
    rw [Metric.eventually_nhds_iff] at hband
    obtain ⟨ε, hε, hεband⟩ := hband
    -- `g ∘ γ` has the chain-rule derivative on forward times
    have hdiff : ∀ s ∈ Set.Ioo τ (τ + ε),
        HasDerivAt (fun u => g (γ u)) (g' (γ s) (f (γ s))) s := by
      intro s hs
      have hsnn : 0 ≤ s := le_trans hτnonneg hs.1.le
      exact (hg (γ s)).comp_hasDerivAt s (hγderiv s hsnn)
    set ε' : ℝ := ε / 2 with hε'
    have hε'pos : 0 < ε' := by positivity
    -- band membership for `s ∈ (τ, τ + ε)`
    have hbandIoo : ∀ s ∈ Set.Ioo τ (τ + ε), c - δ ≤ g (γ s) ∧ g (γ s) ≤ c + δ := by
      intro s hs
      have hdist : dist s τ < ε := by
        rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith [hs.1, hs.2]
      have hmem := hεband hdist
      exact ⟨hmem.1.le, hmem.2.le⟩
    -- `g ∘ γ` is antitone on `[τ, τ + ε']`
    have hanti : AntitoneOn (fun s => g (γ s)) (Set.Icc τ (τ + ε')) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hgγcont.continuousOn ?_ ?_
      · intro s hs
        rw [interior_Icc] at hs
        exact (hdiff s ⟨hs.1, by linarith [hs.2]⟩).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        have hsIoo : s ∈ Set.Ioo τ (τ + ε) := ⟨hs.1, by linarith [hs.2]⟩
        rw [(hdiff s hsIoo).deriv]
        obtain ⟨hlo, hhi⟩ := hbandIoo s hsIoo
        exact hdescent (γ s) hlo hhi
    -- right-accumulating exit points contradict antitonicity
    obtain ⟨s, hsmem, hsR⟩ := exit_accumulates_right hγcont hRclosed h0R ht0 htRmem hε'pos
    have hsIcc : s ∈ Set.Icc τ (τ + ε') := ⟨hsmem.1.le, hsmem.2.le⟩
    have hτIcc : τ ∈ Set.Icc τ (τ + ε') := ⟨le_rfl, by linarith⟩
    -- antitone: `g (γ s) ≤ g (γ τ) = c`, so `γ s ∈ R`, contradicting `γ s ∉ R`
    have hle : g (γ s) ≤ g (γ τ) := hanti hτIcc hsIcc hsmem.1.le
    rw [hτeq] at hle
    exact hsR hle

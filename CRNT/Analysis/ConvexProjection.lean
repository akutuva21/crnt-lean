import CRNT.Analysis.BrouwerConvex
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Brouwer's fixed-point theorem for compact convex sets

The fixed-point theorem `brouwer_compact_convex`: every continuous self-map of a nonempty compact
convex subset `K` of `EuclideanSpace ℝ (Fin n)` has a fixed point.

The proof combines two ingredients:

* The **Hilbert projection theorem** (`exists_norm_eq_iInf_of_complete_convex`), which provides a
  metric projection `projK : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)` onto `K`. The
  variational characterization of the projection
  (`norm_eq_iInf_iff_real_inner_le_zero`) yields its uniqueness, the fact that it fixes points of
  `K`, and that it is nonexpansive, hence continuous.
* **Brouwer's theorem on the cube** (`brouwer_cube`). Transporting `EuclideanSpace ℝ (Fin n)` to
  `Fin n → ℝ` along the continuous linear equivalence `EuclideanSpace.equiv (Fin n) ℝ`, the compact
  image of `K` is bounded and so sits inside a box `[-(c+1), c+1]ⁿ`. An affine homeomorphism carries
  the unit cube `[0,1]ⁿ` onto that box, conjugating `f ∘ projK` into a continuous self-map of the
  cube. A cube fixed point of that conjugate, pulled back, lands in `K`, where `projK` is the
  identity, producing a fixed point of `f`.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Analysis.BrouwerConvex`.
-/

namespace CRNT.Analysis

open Set
open scoped RealInnerProductSpace

variable {n : ℕ}
variable {K : Set (EuclideanSpace ℝ (Fin n))} (hne : K.Nonempty) (hconv : Convex ℝ K)
  (hcomp : IsCompact K)

/-! ### The metric projection onto a compact convex set -/

/-- The metric projection of `u` onto the compact convex set `K`, i.e. the closest point of `K` to
`u`, supplied by the Hilbert projection theorem. -/
noncomputable def projK (u : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (exists_norm_eq_iInf_of_complete_convex hne hcomp.isComplete hconv u).choose

theorem projK_mem (u : EuclideanSpace ℝ (Fin n)) : projK hne hconv hcomp u ∈ K :=
  (exists_norm_eq_iInf_of_complete_convex hne hcomp.isComplete hconv u).choose_spec.1

theorem projK_iInf (u : EuclideanSpace ℝ (Fin n)) :
    ‖u - projK hne hconv hcomp u‖ = ⨅ w : K, ‖u - w‖ :=
  (exists_norm_eq_iInf_of_complete_convex hne hcomp.isComplete hconv u).choose_spec.2

/-- The variational inequality characterizing the projection: `projK u` is the unique point of `K`
making the angle between `u - projK u` and every direction `w - projK u` into `K` obtuse. -/
theorem projK_variational (u : EuclideanSpace ℝ (Fin n)) :
    ∀ w ∈ K, ⟪u - projK hne hconv hcomp u, w - projK hne hconv hcomp u⟫ ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero hconv (projK_mem hne hconv hcomp u)).mp
    (projK_iInf hne hconv hcomp u)

/-- A point of `K` satisfying the projection variational inequality is the projection. -/
theorem projK_eq_of_variational {u v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ K)
    (h : ∀ w ∈ K, ⟪u - v, w - v⟫ ≤ 0) : projK hne hconv hcomp u = v := by
  set p := projK hne hconv hcomp u with hp
  have hpmem : p ∈ K := projK_mem hne hconv hcomp u
  -- variational inequality of `p` tested at `v`, and of `v` tested at `p`
  have h1 : ⟪u - p, v - p⟫ ≤ 0 := projK_variational hne hconv hcomp u v hv
  have h2 : ⟪u - v, p - v⟫ ≤ 0 := h p hpmem
  -- adding the two inequalities collapses to `‖p - v‖² ≤ 0`
  have hsum : ‖p - v‖ ^ 2 ≤ 0 := by
    have hexpand : ⟪u - p, v - p⟫ + ⟪u - v, p - v⟫ = ‖p - v‖ ^ 2 := by
      have hnorm : ⟪p - v, p - v⟫ = ‖p - v‖ ^ 2 := real_inner_self_eq_norm_sq _
      simp only [inner_sub_left, inner_sub_right] at hnorm ⊢
      have hcomm₁ : ⟪v, p⟫ = ⟪p, v⟫ := real_inner_comm _ _
      have hcomm₂ : ⟪u, p⟫ = ⟪p, u⟫ := real_inner_comm _ _
      have hcomm₃ : ⟪u, v⟫ = ⟪v, u⟫ := real_inner_comm _ _
      have hcomm₄ : ⟪v, u⟫ = ⟪u, v⟫ := real_inner_comm _ _
      nlinarith [hnorm, hcomm₁, hcomm₂, hcomm₃, hcomm₄]
    nlinarith [h1, h2, hexpand]
  have hsq : ‖p - v‖ ^ 2 = 0 := le_antisymm hsum (sq_nonneg _)
  have : ‖p - v‖ = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    exact this
  have : p - v = 0 := by rwa [norm_eq_zero] at this
  rw [hp]; exact sub_eq_zero.mp this

/-- The projection fixes points of `K`. -/
theorem projK_eq_self {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ K) : projK hne hconv hcomp u = u := by
  refine projK_eq_of_variational hne hconv hcomp hu ?_
  intro w _
  simp [inner_zero_left]

/-- The metric projection is nonexpansive. -/
theorem projK_nonexpansive (u v : EuclideanSpace ℝ (Fin n)) :
    ‖projK hne hconv hcomp u - projK hne hconv hcomp v‖ ≤ ‖u - v‖ := by
  set p := projK hne hconv hcomp u with hp
  set q := projK hne hconv hcomp v with hq
  have hpmem : p ∈ K := projK_mem hne hconv hcomp u
  have hqmem : q ∈ K := projK_mem hne hconv hcomp v
  -- variational inequalities tested at the other projection point
  have h1 : ⟪u - p, q - p⟫ ≤ 0 := projK_variational hne hconv hcomp u q hqmem
  have h2 : ⟪v - q, p - q⟫ ≤ 0 := projK_variational hne hconv hcomp v p hpmem
  -- `‖p - q‖² ≤ ⟪u - v, p - q⟫`
  have hkey : ‖p - q‖ ^ 2 ≤ ⟪u - v, p - q⟫ := by
    have hnorm : ⟪p - q, p - q⟫ = ‖p - q‖ ^ 2 := real_inner_self_eq_norm_sq _
    simp only [inner_sub_left, inner_sub_right] at hnorm h1 h2 ⊢
    have hcomm₁ : ⟪q, p⟫ = ⟪p, q⟫ := real_inner_comm _ _
    nlinarith [hnorm, h1, h2, hcomm₁]
  -- `⟪u - v, p - q⟫ ≤ ‖u - v‖ · ‖p - q‖`
  have hcs : ⟪u - v, p - q⟫ ≤ ‖u - v‖ * ‖p - q‖ := real_inner_le_norm _ _
  have hsq : ‖p - q‖ ^ 2 ≤ ‖u - v‖ * ‖p - q‖ := le_trans hkey hcs
  rcases eq_or_lt_of_le (norm_nonneg (p - q)) with hpq | hpq
  · -- `p = q`
    simp [← hpq]
  · -- divide by `‖p - q‖ > 0`
    have : ‖p - q‖ * ‖p - q‖ ≤ ‖u - v‖ * ‖p - q‖ := by nlinarith [hsq]
    exact le_of_mul_le_mul_right this hpq

/-- The metric projection is continuous (being `1`-Lipschitz). -/
theorem continuous_projK : Continuous (projK hne hconv hcomp) := by
  have hlip : LipschitzWith 1 (projK hne hconv hcomp) := by
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    exact projK_nonexpansive hne hconv hcomp u v
  exact hlip.continuous

/-! ### Brouwer's fixed-point theorem on a compact convex set -/

namespace BrouwerConvex

/-- The affine map sending the unit cube `[0,1]ⁿ` onto the box `[-(c+1), c+1]ⁿ`. -/
def aff (M c : ℝ) (t : Fin n → ℝ) : Fin n → ℝ := fun i => M * t i - (c + 1)

/-- The inverse affine map, sending the box `[-(c+1), c+1]ⁿ` back into the unit cube. -/
noncomputable def affInv (M c : ℝ) (y : Fin n → ℝ) : Fin n → ℝ := fun i => (y i + (c + 1)) / M

theorem continuous_aff (M c : ℝ) : Continuous (aff (n := n) M c) :=
  continuous_pi fun i => (continuous_const.mul (continuous_apply i)).sub continuous_const

theorem continuous_affInv (M c : ℝ) : Continuous (affInv (n := n) M c) :=
  continuous_pi fun i => ((continuous_apply i).add continuous_const).div_const _

end BrouwerConvex

open BrouwerConvex

include hne hconv hcomp in
/-- **Brouwer's fixed-point theorem for compact convex sets.** Every continuous self-map of a
nonempty compact convex subset `K` of `EuclideanSpace ℝ (Fin n)` has a fixed point. -/
theorem brouwer_compact_convex (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : ContinuousOn f K) (hmaps : Set.MapsTo f K K) : ∃ x ∈ K, f x = x := by
  classical
  -- transport to `Fin n → ℝ` along the continuous linear equivalence
  set e := EuclideanSpace.equiv (Fin n) ℝ with he
  have he_cont : Continuous e := e.continuous
  have hesymm_cont : Continuous e.symm := e.symm.continuous
  -- the image of `K` under `e` is compact, hence bounded in the sup norm
  have hKimg : IsCompact (e '' K) := hcomp.image he_cont
  obtain ⟨c, hc0, hcbound⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ y ∈ e '' K, ‖y‖ ≤ c := by
    obtain ⟨C, hC⟩ := hKimg.isBounded.subset_ball 0
    refine ⟨max C 0, le_max_right _ _, fun y hy => ?_⟩
    have := hC hy
    rw [Metric.mem_ball, dist_zero_right] at this
    exact le_trans this.le (le_max_left _ _)
  set M : ℝ := 2 * (c + 1) with hM
  have hMpos : 0 < M := by rw [hM]; linarith
  have hMne : M ≠ 0 := ne_of_gt hMpos
  -- coordinatewise bound: every coordinate of `e '' K` lies in `[-(c+1), c+1]`
  have hbox : ∀ y ∈ e '' K, ∀ i, -(c + 1) ≤ y i ∧ y i ≤ c + 1 := by
    intro y hy i
    have hyi : |y i| ≤ c := le_trans (norm_le_pi_norm y i) (hcbound y hy)
    have h1 : -c ≤ y i := neg_le_of_abs_le hyi
    have h2 : y i ≤ c := le_of_abs_le hyi
    constructor <;> linarith
  -- the conjugated self-map of the cube
  set fp : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun u => f (projK hne hconv hcomp u) with hfp
  have hfp_cont : Continuous fp :=
    hf.comp_continuous (continuous_projK hne hconv hcomp) (projK_mem hne hconv hcomp)
  set g : (Fin n → ℝ) → (Fin n → ℝ) :=
    fun t => affInv M c (e (fp (e.symm (aff M c t)))) with hg
  have hg_cont : Continuous g :=
    (continuous_affInv M c).comp (he_cont.comp (hfp_cont.comp
      (hesymm_cont.comp (continuous_aff M c))))
  -- `g` maps the unit cube into itself
  have hg_maps : Set.MapsTo g (Icc (0 : Fin n → ℝ) 1) (Icc 0 1) := by
    intro t _
    rw [Set.mem_Icc]
    -- the point `fp (e.symm (aff M c t))` lies in `K`, so its `e`-image lies in `e '' K`
    have hmem : fp (e.symm (aff M c t)) ∈ K :=
      hmaps (projK_mem hne hconv hcomp _)
    have himg : e (fp (e.symm (aff M c t))) ∈ e '' K := ⟨_, hmem, rfl⟩
    set y := e (fp (e.symm (aff M c t))) with hy
    have hyb := hbox y himg
    refine ⟨fun i => ?_, fun i => ?_⟩ <;>
      simp only [g, affInv, ← hy, Pi.zero_apply, Pi.one_apply]
    · -- `0 ≤ (y i + (c+1))/M`
      have : -(c + 1) ≤ y i := (hyb i).1
      apply div_nonneg (by linarith) hMpos.le
    · -- `(y i + (c+1))/M ≤ 1`
      have hub : y i ≤ c + 1 := (hyb i).2
      rw [div_le_one hMpos]
      have : y i + (c + 1) ≤ M := by rw [hM]; linarith
      exact this
  obtain ⟨t, htmem, htfix⟩ := brouwer_cube g hg_cont.continuousOn hg_maps
  -- unwind the cube fixed point
  set y : Fin n → ℝ := aff M c t with hyaff
  -- `affInv M c (e (fp (e.symm y))) = t`, hence `e (fp (e.symm y)) = aff M c t = y`
  have hgfix : affInv M c (e (fp (e.symm y))) = t := htfix
  have hkey : e (fp (e.symm y)) = y := by
    funext i
    have hgi : (e (fp (e.symm y)) i + (c + 1)) / M = t i := congrFun hgfix i
    have hval : e (fp (e.symm y)) i + (c + 1) = t i * M :=
      (div_eq_iff hMne).mp hgi
    simp only [hyaff, aff]
    linarith
  set p : EuclideanSpace ℝ (Fin n) := projK hne hconv hcomp (e.symm y) with hp
  -- `e.symm y = fp (e.symm y)` follows from `hkey` by applying `e.symm`
  have hsymm : e.symm y = fp (e.symm y) := by
    have := congrArg e.symm hkey
    simpa using this.symm
  -- `fp (e.symm y) = f p`, and `f p ∈ K`, so `projK (f p) = f p`
  have hfpK : f p ∈ K := hmaps (projK_mem hne hconv hcomp (e.symm y))
  have hpfp : p = f p := by
    -- `e.symm y = f p` from `hsymm` (since `fp (e.symm y) = f p` by definition of `fp` and `p`)
    have hesf : e.symm y = f p := by rw [hsymm, hfp, hp]
    -- `p = projK (e.symm y) = projK (f p) = f p`
    calc p = projK hne hconv hcomp (e.symm y) := hp
      _ = projK hne hconv hcomp (f p) := by rw [hesf]
      _ = f p := projK_eq_self hne hconv hcomp hfpK
  exact ⟨p, projK_mem hne hconv hcomp (e.symm y), hpfp.symm⟩

end CRNT.Analysis

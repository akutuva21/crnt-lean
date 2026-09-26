import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import CRNT.Geometry.ToricFan

/-!
# Scale separation for Craciun's zero-separating construction

Reference: Gheorghe Craciun, *Toric Differential Inclusions and a Proof of the Global Attractor
Conjecture*, arXiv:1501.02860v3 (2026), Lemma 9.7, https://arxiv.org/abs/1501.02860.

This file formalizes the geometric scale step used in Craciun v3, Lemma 9.7. If a cone lies in the
interior of another cone, then a fixed-width neighborhood of the smaller cone is eventually
contained in the larger cone. The argument normalizes the smaller cone to the unit sphere, uses
compactness to obtain a uniform interior radius, and then rescales. The finite-family version also
handles the zero cone: its fixed-width neighborhood is bounded, so it contributes no points once
the common radius is large enough.
-/

namespace CRNT
namespace CraciunZSH

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A fixed-width neighborhood of `C` is eventually contained in `K` when both sets are cones
and `C` is contained in the interior of `K`. This is the scale-separation assertion used in
Craciun v3, Lemma 9.7. -/
theorem exists_eventual_tube_subset_of_cone_interior
    {C K : Set E}
    (hCscale : ∀ a : ℝ, 0 ≤ a → ∀ x ∈ C, a • x ∈ C)
    (hKscale : ∀ a : ℝ, 0 ≤ a → ∀ x ∈ K, a • x ∈ K)
    (hCinterior : C ⊆ interior K)
    (hsectionCompact : IsCompact (C ∩ Metric.sphere (0 : E) 1))
    (hsectionNonempty : (C ∩ Metric.sphere (0 : E) 1).Nonempty)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : E,
      Metric.infDist x C < δ → M < ‖x‖ → x ∈ K := by
  classical
  let unitSection : Set E := C ∩ Metric.sphere (0 : E) 1
  have hsection : IsCompact unitSection := by
    simpa [unitSection] using hsectionCompact
  let radius : unitSection → ℝ := fun u =>
    Classical.choose (Metric.isOpen_iff.mp isOpen_interior u.1 (hCinterior u.2.1))
  have hradius : ∀ u : unitSection, 0 < radius u := by
    intro u
    exact (Classical.choose_spec
      (Metric.isOpen_iff.mp isOpen_interior u.1 (hCinterior u.2.1))).1
  have hball : ∀ u : unitSection, Metric.ball u.1 (radius u) ⊆ interior K := by
    intro u
    exact (Classical.choose_spec
      (Metric.isOpen_iff.mp isOpen_interior u.1 (hCinterior u.2.1))).2
  let U : unitSection → Set E := fun u => Metric.ball u.1 (radius u / 2)
  have hUopen : ∀ u : unitSection, IsOpen (U u) := fun u => Metric.isOpen_ball
  have hUcover : unitSection ⊆ ⋃ u : unitSection, U u := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, by
      dsimp [U]
      rw [Metric.mem_ball, dist_self]
      linarith [hradius ⟨x, hx⟩]⟩
  obtain ⟨tiles, htiles⟩ := hsection.elim_finite_subcover U hUopen hUcover
  have htilesNonempty : tiles.Nonempty := by
    by_contra hne
    have htilesEmpty : tiles = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    obtain ⟨x, hx⟩ := hsectionNonempty
    have hxcover := htiles hx
    simp [htilesEmpty] at hxcover
  obtain ⟨u₀, hu₀, hmin⟩ :=
    Finset.exists_mem_eq_inf' htilesNonempty (fun u : unitSection => radius u / 2)
  let ρ : ℝ := tiles.inf' htilesNonempty (fun u : unitSection => radius u / 2)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    rw [hmin]
    exact half_pos (hradius u₀)
  have hρle (u : unitSection) (hu : u ∈ tiles) : ρ ≤ radius u / 2 := by
    dsimp [ρ]
    exact Finset.inf'_le _ hu
  refine ⟨δ + δ / ρ, by positivity, ?_⟩
  intro x hnear hlarge
  have hCne : C.Nonempty := by
    obtain ⟨u, hu⟩ := hsectionNonempty
    exact ⟨u, hu.1⟩
  obtain ⟨y, hyC, hxy⟩ := (Metric.infDist_lt_iff hCne).mp hnear
  have hxyNorm : ‖x - y‖ < δ := by
    simpa [dist_eq_norm] using hxy
  have hxTriangle : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    calc
      ‖x‖ = ‖(x - y) + y‖ := by congr 1; abel
      _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
  have hyLarge : δ / ρ < ‖y‖ := by
    have hxUpper : ‖x‖ < δ + ‖y‖ := lt_of_le_of_lt hxTriangle (by linarith)
    linarith
  have hyNormPos : 0 < ‖y‖ := lt_trans (div_pos hδ hρ) hyLarge
  let u : E := (‖y‖)⁻¹ • y
  have hnormu : ‖u‖ = 1 := by
    dsimp [u]
    calc
      ‖(‖y‖)⁻¹ • y‖ = ‖(‖y‖)⁻¹‖ * ‖y‖ := norm_smul _ _
      _ = (‖y‖)⁻¹ * ‖y‖ := by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hyNormPos)]
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hyNormPos)
  have huC : u ∈ C := hCscale (‖y‖)⁻¹ (le_of_lt (inv_pos.mpr hyNormPos)) y hyC
  have huSphere : u ∈ Metric.sphere (0 : E) 1 := by
    simp [Metric.sphere, dist_zero_right, hnormu]
  have huSection : u ∈ unitSection := by
    exact ⟨huC, huSphere⟩
  have huCover := htiles huSection
  simp only [Set.mem_iUnion] at huCover
  obtain ⟨v, hvTiles, hvU⟩ := huCover
  have huvBall : dist u v.1 < radius v / 2 := by
    simpa [U, Metric.mem_ball] using hvU
  have hpertNorm : ‖(‖y‖)⁻¹ • (x - y)‖ = ‖x - y‖ / ‖y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hyNormPos), inv_mul_eq_div]
  have hpertSmall : ‖(‖y‖)⁻¹ • (x - y)‖ < ρ := by
    rw [hpertNorm]
    apply (div_lt_iff₀ hyNormPos).2
    have hρy' : δ < ‖y‖ * ρ := (div_lt_iff₀ hρ).mp hyLarge
    have hρy : δ < ρ * ‖y‖ := by simpa [mul_comm] using hρy'
    linarith
  have hpertTile : ‖(‖y‖)⁻¹ • (x - y)‖ < radius v / 2 :=
    lt_of_lt_of_le hpertSmall (hρle v hvTiles)
  have hxScaledBall :
      u + (‖y‖)⁻¹ • (x - y) ∈ Metric.ball v.1 (radius v) := by
    rw [Metric.mem_ball, dist_eq_norm]
    calc
      ‖u + (‖y‖)⁻¹ • (x - y) - v.1‖
          = ‖(u - v.1) + (‖y‖)⁻¹ • (x - y)‖ := by congr 1; abel
      _ ≤ ‖u - v.1‖ + ‖(‖y‖)⁻¹ • (x - y)‖ := norm_add_le _ _
      _ < radius v / 2 + radius v / 2 := add_lt_add (by simpa [dist_eq_norm] using huvBall) hpertTile
      _ = radius v := by ring
  have hxScaledInterior : u + (‖y‖)⁻¹ • (x - y) ∈ interior K := hball v hxScaledBall
  have hxScaled : (‖y‖)⁻¹ • x ∈ K := by
    have hdecomp : (‖y‖)⁻¹ • x = u + (‖y‖)⁻¹ • (x - y) := by
      dsimp [u]
      rw [← smul_add]
      congr 1
      abel
    rw [hdecomp]
    exact interior_subset hxScaledInterior
  have hrescale : ‖y‖ • ((‖y‖)⁻¹ • x) = x := by
    rw [smul_smul]
    simp [hyNormPos.ne']
  have hxK : ‖y‖ • ((‖y‖)⁻¹ • x) ∈ K :=
    hKscale ‖y‖ hyNormPos.le ((‖y‖)⁻¹ • x) hxScaled
  rw [hrescale] at hxK
  exact hxK

/-- Closed cones in a proper normed space have compact unit sections, so the scale-separation
lemma applies directly to closed nonzero fan cones. -/
theorem exists_eventual_tube_subset_of_closed_cone_interior
    [ProperSpace E] {C K : Set E}
    (hCclosed : IsClosed C)
    (hCscale : ∀ a : ℝ, 0 ≤ a → ∀ x ∈ C, a • x ∈ C)
    (hKscale : ∀ a : ℝ, 0 ≤ a → ∀ x ∈ K, a • x ∈ K)
    (hCinterior : C ⊆ interior K)
    (hCnonzero : ∃ x ∈ C, x ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : E,
      Metric.infDist x C < δ → M < ‖x‖ → x ∈ K := by
  have hsectionCompact : IsCompact (C ∩ Metric.sphere (0 : E) 1) := by
    exact (isCompact_sphere (0 : E) 1).of_isClosed_subset
      (hCclosed.inter Metric.isClosed_sphere) Set.inter_subset_right
  have hsectionNonempty : (C ∩ Metric.sphere (0 : E) 1).Nonempty := by
    obtain ⟨y, hyC, hyNe⟩ := hCnonzero
    have hyNorm : 0 < ‖y‖ := norm_pos_iff.mpr hyNe
    let u : E := (‖y‖)⁻¹ • y
    have huNorm : ‖u‖ = 1 := by
      dsimp [u]
      calc
        ‖(‖y‖)⁻¹ • y‖ = ‖(‖y‖)⁻¹‖ * ‖y‖ := norm_smul _ _
        _ = (‖y‖)⁻¹ * ‖y‖ := by
          rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hyNorm)]
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hyNorm)
    have huC : u ∈ C := hCscale (‖y‖)⁻¹ (le_of_lt (inv_pos.mpr hyNorm)) y hyC
    have huSphere : u ∈ Metric.sphere (0 : E) 1 := by
      simp [Metric.sphere, dist_zero_right, huNorm]
    exact ⟨u, huC, huSphere⟩
  exact exists_eventual_tube_subset_of_cone_interior
    hCscale hKscale hCinterior hsectionCompact hsectionNonempty hδ

/-- The Lemma 9.7 scale threshold can be chosen uniformly for a finite family of cone pairs. This
is the finite-fan form used to choose one starting scale for all fan cells at once. -/
theorem exists_uniform_eventual_tube_subset_of_closed_cone_interior
    {ι : Type*} [Fintype ι] [Nonempty ι] [ProperSpace E]
    (C K : ι → Set E)
    (hCclosed : ∀ i, IsClosed (C i))
    (hCscale : ∀ i (a : ℝ), 0 ≤ a → ∀ x ∈ C i, a • x ∈ C i)
    (hKscale : ∀ i (a : ℝ), 0 ≤ a → ∀ x ∈ K i, a • x ∈ K i)
    (hCinterior : ∀ i, C i ⊆ interior (K i))
    (hCnonzero : ∀ i, ∃ x ∈ C i, x ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 < M ∧ ∀ i x,
      Metric.infDist x (C i) < δ → M < ‖x‖ → x ∈ K i := by
  classical
  let Mi : ι → ℝ := fun i => Classical.choose
    (exists_eventual_tube_subset_of_closed_cone_interior
      (hCclosed i) (hCscale i) (hKscale i) (hCinterior i) (hCnonzero i) hδ)
  have hMi : ∀ i, 0 < Mi i ∧ ∀ x,
      Metric.infDist x (C i) < δ → Mi i < ‖x‖ → x ∈ K i := by
    intro i
    exact Classical.choose_spec
      (exists_eventual_tube_subset_of_closed_cone_interior
        (hCclosed i) (hCscale i) (hKscale i) (hCinterior i) (hCnonzero i) hδ)
  let M : ℝ := ∑ i, Mi i
  have hM : 0 < M := by
    dsimp [M]
    exact Finset.sum_pos (fun i hi => (hMi i).1) Finset.univ_nonempty
  refine ⟨M, hM, ?_⟩
  intro i x hnear hlarge
  have hMiLe : Mi i ≤ M := by
    dsimp [M]
    exact Finset.single_le_sum (fun j hj => (hMi j).1.le) (Finset.mem_univ i)
  exact (hMi i).2 x hnear (lt_of_le_of_lt hMiLe hlarge)

/-- Craciun v3, Lemma 9.7 uses a finite fan family, which can include the zero cone. For each
assigned pair of closed proper cones `C i ⊆ interior (K i)`, one common radius works for every
index. If `C i` is nonzero, compactness of its unit section gives the radius above; if `C i = {0}`,
its fixed-width neighborhood is bounded and the implication is vacuous beyond that width. -/
theorem exists_uniform_eventual_tube_subset_of_finite_properCone_pairs
    {ι : Type*} [Fintype ι] [Nonempty ι] [ProperSpace E]
    (C K : ι → ProperCone ℝ E)
    (hinterior : ∀ i, (C i : Set E) ⊆ interior (K i : Set E))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 < M ∧ ∀ i x,
      Metric.infDist x (C i : Set E) < δ → M < ‖x‖ → x ∈ (K i : Set E) := by
  classical
  let hMi (i : ι) : ∃ M : ℝ, 0 < M ∧ ∀ x,
      Metric.infDist x (C i : Set E) < δ → M < ‖x‖ → x ∈ (K i : Set E) := by
    by_cases hnonzero : ∃ y ∈ (C i : Set E), y ≠ 0
    · exact exists_eventual_tube_subset_of_closed_cone_interior
        (C i).isClosed
        (fun a ha y hy => (C i).smul_mem hy ha)
        (fun a ha y hy => (K i).smul_mem hy ha)
        (hinterior i) hnonzero hδ
    · have honlyzero : ∀ y ∈ (C i : Set E), y = 0 := by
        intro y hy
        by_contra hyne
        exact hnonzero ⟨y, hy, hyne⟩
      refine ⟨δ, hδ, ?_⟩
      intro x hnear hlarge
      have hCne : (C i : Set E).Nonempty := by
        exact ⟨0, (C i).zero_mem⟩
      obtain ⟨y, hyC, hxy⟩ := (Metric.infDist_lt_iff hCne).mp hnear
      have hy0 : y = 0 := honlyzero y hyC
      have hxsmall : ‖x‖ < δ := by
        simpa [hy0, dist_eq_norm] using hxy
      exact (not_lt_of_ge (le_of_lt hlarge) hxsmall).elim
  let Mi : ι → ℝ := fun i => Classical.choose (hMi i)
  have hMiSpec (i : ι) : 0 < Mi i ∧ ∀ x,
      Metric.infDist x (C i : Set E) < δ → Mi i < ‖x‖ → x ∈ (K i : Set E) :=
    Classical.choose_spec (hMi i)
  let M : ℝ := ∑ i, Mi i
  have hM : 0 < M := by
    dsimp [M]
    exact Finset.sum_pos (fun i hi => (hMiSpec i).1) Finset.univ_nonempty
  refine ⟨M, hM, ?_⟩
  intro i x hnear hlarge
  have hMiLe : Mi i ≤ M := by
    dsimp [M]
    exact Finset.single_le_sum (fun j hj => (hMiSpec j).1.le) (Finset.mem_univ i)
  exact (hMiSpec i).2 x hnear (lt_of_le_of_lt hMiLe hlarge)

end CraciunZSH
end CRNT

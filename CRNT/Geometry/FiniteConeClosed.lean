import CRNT.Geometry.SimplicialConeClosed
import Mathlib.Analysis.Convex.Cone.Basic

/-!
# Closedness of finitely-generated cones

The conical hull `PointedCone.hull ℝ S` of a finite set `S` in a real normed space is closed, even
when the generators of `S` are linearly dependent. This upgrades the simplicial case
`isClosed_coe_hull_of_linearIndependent`, where the generators are required to be independent, to
arbitrary finite generating sets, so the conical hull of a finite set carries a `ProperCone`
structure.

## Carathéodory for cones

The bridge is a conical Carathéodory theorem: every point of `hull ℝ S` lies in the conical hull of
a linearly independent subset of `S`. The reduction step takes a nonnegative representation
`x = ∑ i ∈ t, f i • i` whose support `t` is dependent, picks a nontrivial relation
`∑ i ∈ t, g i • i = 0`, and slides `f` along `g` — subtracting the multiple `θ • g` where `θ` is the
smallest ratio `f j / g j` over indices with `g j > 0`. The slid coefficients stay nonnegative,
represent the same point, and vanish at the minimizing index, shrinking the support by one. Iterating
until the support is independent expresses every point as a nonnegative combination of an independent
subset.

## Closedness as a finite union

Carathéodory makes `hull ℝ S` the union, over the finitely many linearly independent subsets
`T ⊆ S`, of the simplicial cones `hull ℝ T`. Each simplicial cone is closed and the index set is
finite, so the union is closed.

* `hull_finset_eq_iUnion_linearIndepOn` — the conical hull of a finite set is the finite union of the
  hulls of its linearly independent subsets.
* `isClosed_coe_hull_of_finite` — the conical hull of a `Finset` is closed.
* `isClosed_coe_hull_of_set_finite` — the conical hull of a `Set.Finite` set is closed.

This module is `sorry`-free.
-/

namespace CRNT

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The conical hull of a finite linearly independent set, indexed by the set itself, is closed.
This is the simplicial case phrased for an arbitrary finite index set `Fintype ι` rather than `Fin k`,
obtained by the same closed-embedding argument: the linear-combination map out of the
finite-dimensional coefficient space is an injective hence closed embedding carrying the nonnegative
orthant onto the span. -/
theorem isClosed_nonnegSpan_of_linearIndependent' {ι : Type*} [Fintype ι] (v : ι → E)
    (hv : LinearIndependent ℝ v) :
    IsClosed {x : E | ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • v i} := by
  have hker : LinearMap.ker (Fintype.linearCombination ℝ v) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hv.fintypeLinearCombination_injective
  have hembed := LinearMap.isClosedEmbedding_of_injective (𝕜 := ℝ)
    (f := Fintype.linearCombination ℝ v) hker
  have hset : {x : E | ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • v i}
      = Fintype.linearCombination ℝ v '' {c : ι → ℝ | ∀ i, 0 ≤ c i} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image, Fintype.linearCombination_apply]
    constructor
    · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩
  have horthant : IsClosed {c : ι → ℝ | ∀ i, 0 ≤ c i} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  rw [hset]
  exact hembed.isClosedMap _ horthant

/-- The conical hull of a finite linearly independent set is closed, as a subset of `E`. -/
theorem isClosed_coe_hull_of_linearIndepOn {t : Finset E} (ht : LinearIndepOn ℝ id (t : Set E)) :
    IsClosed (PointedCone.hull ℝ (t : Set E) : Set E) := by
  have hv : LinearIndependent ℝ (Subtype.val : {x // x ∈ t} → E) := by
    have : LinearIndependent ℝ (Subtype.val : (↑t : Set E) → E) := ht
    exact this
  have heq : (PointedCone.hull ℝ (t : Set E) : Set E)
      = {x : E | ∃ c : {x // x ∈ t} → ℝ, (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • (i : E)} := by
    ext x
    rw [SetLike.mem_coe]
    show x ∈ Submodule.span _ (t : Set E) ↔ _
    rw [show (t : Set E) = Set.range (Subtype.val : {x // x ∈ t} → E) by
        simp, Submodule.mem_span_range_iff_exists_fun]
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨fun i => (c i : ℝ), fun i => (c i).2, by simp_rw [Nonneg.coe_smul]⟩
    · rintro ⟨c, hc₀, rfl⟩
      exact ⟨fun i => ⟨c i, hc₀ i⟩, by rw [eq_comm]; simp_rw [Nonneg.mk_smul]⟩
  rw [heq]
  exact isClosed_nonnegSpan_of_linearIndependent' _ hv

/-- **One reduction step of conical Carathéodory.** A nonnegative representation
`x = ∑ i ∈ t, f i • i` over a linearly dependent support `t` can be rewritten as a nonnegative
representation over a strictly smaller support. Subtracting the smallest feasible multiple of a
nontrivial linear relation among the generators zeroes one positive coefficient while keeping every
coefficient nonnegative and preserving the represented point. -/
theorem exists_smaller_nonneg_repr {t : Finset E} {f : E → ℝ} (hf : ∀ i ∈ t, 0 ≤ f i)
    (hdep : ¬ LinearIndepOn ℝ id (t : Set E)) :
    ∃ t' : Finset E, t' ⊂ t ∧ ∃ f' : E → ℝ, (∀ i ∈ t', 0 ≤ f' i) ∧
      ∑ i ∈ t', f' i • i = ∑ i ∈ t, f i • i := by
  classical
  -- Extract a nontrivial linear relation `∑ i ∈ t, g i • i = 0` among the generators of `t`.
  obtain ⟨g, hg0, j₀, hj₀t, hj₀⟩ :=
    (not_linearIndepOn_finset_iff (v := (id : E → E)) (s := t)).mp hdep
  simp only [id] at hg0
  -- Replace `g` by a relation with a strictly positive coefficient somewhere.
  obtain ⟨g, hg0, hpos⟩ :
      ∃ g : E → ℝ, ∑ i ∈ t, g i • i = 0 ∧ ∃ j ∈ t, 0 < g j := by
    rcases lt_trichotomy (g j₀) 0 with hneg | hzero | hgt
    · refine ⟨fun i => -g i, ?_, j₀, hj₀t, by simpa using hneg⟩
      simp only [neg_smul, Finset.sum_neg_distrib, hg0, neg_zero]
    · exact absurd hzero hj₀
    · exact ⟨g, hg0, j₀, hj₀t, hgt⟩
  obtain ⟨j₀, hj₀t, hj₀pos⟩ := hpos
  -- The set of indices with a positive relation coefficient.
  set P : Finset E := t.filter (fun i => 0 < g i) with hP
  have hPne : P.Nonempty := ⟨j₀, by simp [hP, hj₀t, hj₀pos]⟩
  -- Pick the index minimizing the ratio `f i / g i` over `P`.
  obtain ⟨j, hjP, hjmin⟩ := P.exists_min_image (fun i => f i / g i) hPne
  rw [hP, Finset.mem_filter] at hjP
  obtain ⟨hjt, hjg⟩ := hjP
  set θ : ℝ := f j / g j with hθ
  have hθnonneg : 0 ≤ θ := div_nonneg (hf j hjt) (le_of_lt hjg)
  -- The slid coefficients.
  set f' : E → ℝ := fun i => f i - θ * g i with hf'
  -- Each slid coefficient stays nonnegative.
  have hf'nonneg : ∀ i ∈ t, 0 ≤ f' i := by
    intro i hit
    rcases lt_or_ge (g i) 0 with hgi | hge
    · have hgi' : g i ≤ 0 := le_of_lt hgi
      have : θ * g i ≤ 0 := mul_nonpos_iff.mpr (Or.inl ⟨hθnonneg, hgi'⟩)
      simp only [hf']; linarith [hf i hit]
    · rcases eq_or_lt_of_le hge with hzero | hgi
      · simp only [hf', ← hzero, mul_zero, sub_zero]; exact hf i hit
      · have hratio : θ ≤ f i / g i :=
          hjmin i (by rw [hP, Finset.mem_filter]; exact ⟨hit, hgi⟩)
        have : θ * g i ≤ f i := by
          rw [le_div_iff₀ hgi] at hratio
          linarith [hratio]
        simp only [hf']; linarith
  -- The minimizing coefficient is zeroed out.
  have hf'j : f' j = 0 := by
    simp only [hf', hθ]
    rw [div_mul_cancel₀ _ (ne_of_gt hjg), sub_self]
  -- The slid representation has the same value.
  have hval : ∑ i ∈ t, f' i • i = ∑ i ∈ t, f i • i := by
    have : ∑ i ∈ t, f' i • i = (∑ i ∈ t, f i • i) - θ • ∑ i ∈ t, g i • i := by
      simp only [hf', sub_smul, mul_smul, Finset.sum_sub_distrib, Finset.smul_sum]
    rw [this, hg0, smul_zero, sub_zero]
  -- Drop the zeroed index to shrink the support.
  refine ⟨t.erase j, Finset.erase_ssubset hjt, f', fun i hi => hf'nonneg i (Finset.mem_of_mem_erase hi), ?_⟩
  rw [← hval, ← Finset.sum_erase t (by rw [hf'j, zero_smul])]

/-- **Conical Carathéodory.** Every nonnegative combination of a finite set of vectors equals a
nonnegative combination of a linearly independent subset. Iterating the support-shrinking reduction
`exists_smaller_nonneg_repr` while the support is dependent terminates at an independent subset
representing the same point. -/
theorem exists_linearIndepOn_subset_repr (t : Finset E) (f : E → ℝ) (hf : ∀ i ∈ t, 0 ≤ f i) :
    ∃ t' : Finset E, t' ⊆ t ∧ LinearIndepOn ℝ id (t' : Set E) ∧
      ∃ f' : E → ℝ, (∀ i ∈ t', 0 ≤ f' i) ∧ ∑ i ∈ t', f' i • i = ∑ i ∈ t, f i • i := by
  classical
  induction t using Finset.strongInductionOn generalizing f with
  | _ t ih =>
    by_cases hindep : LinearIndepOn ℝ id (t : Set E)
    · exact ⟨t, Finset.Subset.refl t, hindep, f, hf, rfl⟩
    · obtain ⟨t₁, ht₁, f₁, hf₁, hval₁⟩ := exists_smaller_nonneg_repr hf hindep
      obtain ⟨t', ht'sub, ht'indep, f', hf', hval'⟩ := ih t₁ ht₁ f₁ hf₁
      exact ⟨t', ht'sub.trans ht₁.subset, ht'indep, f', hf', hval'.trans hval₁⟩

/-- A nonnegative `Finset`-combination of vectors lies in their conical hull. -/
theorem sum_smul_mem_hull {t : Finset E} {f : E → ℝ} (hf : ∀ i ∈ t, 0 ≤ f i) :
    (∑ i ∈ t, f i • i) ∈ PointedCone.hull ℝ (t : Set E) := by
  refine Submodule.sum_mem _ fun i hi => ?_
  have hmem : i ∈ PointedCone.hull ℝ (t : Set E) := PointedCone.subset_hull (by simpa using hi)
  exact PointedCone.smul_mem _ (hf i hi) hmem

/-- The conical hull of a finite set equals the union, over its linearly independent subsets, of the
hulls of those subsets. This is the set-level form of conical Carathéodory: a point belongs to the
hull exactly when it belongs to the simplicial cone of one of the finitely many independent subsets. -/
theorem hull_finset_eq_iUnion_linearIndepOn (S : Finset E) :
    (PointedCone.hull ℝ (S : Set E) : Set E)
      = ⋃ t ∈ {t : Finset E | t ⊆ S ∧ LinearIndepOn ℝ id (t : Set E)},
          (PointedCone.hull ℝ (t : Set E) : Set E) := by
  classical
  ext x
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, SetLike.mem_coe, exists_prop]
  constructor
  · intro hx
    rw [PointedCone.mem_hull_set] at hx
    obtain ⟨c, hcsupp, hc0, hcsum⟩ := hx
    -- Realize `x` as a nonnegative `Finset`-sum over the support of `c`.
    obtain ⟨t', ht'sub, ht'indep, f', hf', hval'⟩ :=
      exists_linearIndepOn_subset_repr c.support (fun i => c i) (fun i _ => hc0 i)
    have hsum : ∑ i ∈ c.support, c i • i = x := hcsum
    refine ⟨t', ⟨fun y hy => hcsupp (ht'sub hy), ht'indep⟩, ?_⟩
    have hxeq : x = ∑ i ∈ t', f' i • i := by rw [hval', hsum]
    rw [hxeq]
    exact sum_smul_mem_hull hf'
  · rintro ⟨t, ⟨htsub, _⟩, hxt⟩
    exact (Submodule.span_mono (by exact_mod_cast htsub)) hxt

/-- **A finitely-generated cone is closed.** The conical hull of a `Finset` of vectors is a closed
subset of `E`, with no independence hypothesis on the generators. Conical Carathéodory expresses the
hull as the finite union of the simplicial cones of its linearly independent subsets, each closed by
`isClosed_coe_hull_of_linearIndepOn`, and a finite union of closed sets is closed. -/
theorem isClosed_coe_hull_of_finite (S : Finset E) :
    IsClosed (PointedCone.hull ℝ (S : Set E) : Set E) := by
  rw [hull_finset_eq_iUnion_linearIndepOn S]
  refine Set.Finite.isClosed_biUnion ?_ ?_
  · refine (S.powerset.finite_toSet).subset ?_
    intro t ht
    simpa [Finset.mem_powerset] using ht.1
  · rintro t ⟨_, htindep⟩
    exact isClosed_coe_hull_of_linearIndepOn htindep

/-- The conical hull of a `Set.Finite` set is closed. -/
theorem isClosed_coe_hull_of_set_finite {S : Set E} (hS : S.Finite) :
    IsClosed (PointedCone.hull ℝ S : Set E) := by
  rw [← hS.coe_toFinset]
  exact isClosed_coe_hull_of_finite hS.toFinset

/-- The conical hull of a `Finset` of vectors, packaged as a `ProperCone`: a closed pointed cone.
This realizes the cone generated by finitely many vectors as a genuine proper cone, the structure that
makes the generated cone available to the proper-cone API (duality, separation). -/
def properConeOfFinset (S : Finset E) : ProperCone ℝ E where
  toSubmodule := PointedCone.hull ℝ (S : Set E)
  isClosed' := isClosed_coe_hull_of_finite S

@[simp] lemma coe_properConeOfFinset (S : Finset E) :
    (properConeOfFinset S : Set E) = (PointedCone.hull ℝ (S : Set E) : Set E) := rfl

end CRNT

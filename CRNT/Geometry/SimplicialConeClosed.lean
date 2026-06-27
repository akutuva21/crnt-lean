import Mathlib.Geometry.Convex.Cone.Simplicial
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Closedness of simplicial cones

The nonnegative span of a finite linearly independent family of vectors in a real normed space is
closed. This is the foundational case of "finitely-generated cones are closed":
a `ProperCone` over `ℝ≥0` is a closed submodule, so realizing the conical hull of a finite set as a
genuine proper cone requires that the hull be closed, and Mathlib has no lemma that the conical hull
of a finite set is closed.

## The span as the image of the nonnegative orthant

For a family `v : Fin k → E`, the linear map `L : (Fin k → ℝ) →ₗ[ℝ] E`, `L c = ∑ i, c i • v i`, is
`Fintype.linearCombination ℝ v`. The nonnegative span of `v` is the image under `L` of the
nonnegative orthant `{c | ∀ i, 0 ≤ c i}`. When `v` is linearly independent, `L` is injective, hence —
its domain `Fin k → ℝ` being finite-dimensional — a closed embedding, so it carries the closed orthant
to a closed set.

* `nonnegSpan` — the nonnegative span of `v` as a set: points `∑ i, c i • v i` with all `c i ≥ 0`.
* `nonnegSpan_eq_image_nonnegOrthant` — the nonnegative span is the image of the closed nonnegative
  orthant under `Fintype.linearCombination ℝ v`.
* `isClosed_nonnegSpan_of_linearIndependent` — the nonnegative span of a finite linearly independent
  family is closed.
* `isClosed_coe_hull_of_linearIndependent` — the conical hull `PointedCone.hull ℝ (range v)` is a
  closed subset of `E`.

This module is **stable** and `sorry`-free. Depends on Mathlib's simplicial-cone and
finite-dimensional closed-embedding API.
-/

namespace CRNT

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} (v : Fin k → E)

/-- The **nonnegative span** of a family `v`: the set of conical combinations `∑ i, c i • v i` with
every coefficient `c i` nonnegative. -/
def nonnegSpan : Set E :=
  {x | ∃ c : Fin k → ℝ, (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • v i}

/-- The nonnegative span of `v` is the image, under the linear-combination map
`Fintype.linearCombination ℝ v`, of the nonnegative orthant `{c | ∀ i, 0 ≤ c i}`. -/
theorem nonnegSpan_eq_image_nonnegOrthant :
    nonnegSpan v = Fintype.linearCombination ℝ v '' {c : Fin k → ℝ | ∀ i, 0 ≤ c i} := by
  ext x
  simp only [nonnegSpan, Set.mem_setOf_eq, Set.mem_image, Fintype.linearCombination_apply]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, rfl⟩

/-- The nonnegative orthant `{c : Fin k → ℝ | ∀ i, 0 ≤ c i}` is closed. -/
theorem isClosed_nonnegOrthant : IsClosed {c : Fin k → ℝ | ∀ i, 0 ≤ c i} := by
  rw [Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)

/-- **A simplicial cone is closed.** The nonnegative span of a finite linearly independent family of
vectors in a real normed space is closed: the linear-combination map is an injective linear map out
of the finite-dimensional space `Fin k → ℝ`, hence a closed embedding, and it carries the
closed nonnegative orthant onto the span. -/
theorem isClosed_nonnegSpan_of_linearIndependent (hv : LinearIndependent ℝ v) :
    IsClosed (nonnegSpan v) := by
  have hker : LinearMap.ker (Fintype.linearCombination ℝ v) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (hv.fintypeLinearCombination_injective)
  have hembed := LinearMap.isClosedEmbedding_of_injective (𝕜 := ℝ)
    (f := Fintype.linearCombination ℝ v) hker
  rw [nonnegSpan_eq_image_nonnegOrthant]
  exact hembed.isClosedMap _ isClosed_nonnegOrthant

/-- The conical hull `PointedCone.hull ℝ (Set.range v)` of a finite linearly independent family is a
closed subset of `E`. This realizes the hull of a finite independent set as a closed set, the
prerequisite for it to carry a `ProperCone` structure. -/
theorem isClosed_coe_hull_of_linearIndependent (hv : LinearIndependent ℝ v) :
    IsClosed (PointedCone.hull ℝ (Set.range v) : Set E) := by
  have heq : (PointedCone.hull ℝ (Set.range v) : Set E) = nonnegSpan v := by
    ext x
    rw [SetLike.mem_coe]
    show x ∈ Submodule.span _ (Set.range v) ↔ _
    rw [Submodule.mem_span_range_iff_exists_fun]
    simp only [nonnegSpan, Set.mem_setOf_eq]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨fun i => (c i : ℝ), fun i => (c i).2, by simp_rw [Nonneg.coe_smul]⟩
    · rintro ⟨c, hc₀, rfl⟩
      exact ⟨fun i => ⟨c i, hc₀ i⟩, by rfl⟩
  rw [heq]
  exact isClosed_nonnegSpan_of_linearIndependent v hv

end CRNT

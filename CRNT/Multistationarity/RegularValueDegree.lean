import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Sign.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# The regular-value topological degree and the nonzero-degree existence principle

For a `C¹` map `f : E → E` on a finite-dimensional real normed space and a value `y`
whose preimage `f⁻¹{y}` is finite and consists entirely of regular points (the
derivative `Df x` is invertible, equivalently `det (Df x) ≠ 0`), the integer

`regularDegree f y = ∑ x ∈ f⁻¹{y}, sign (det (Df x))`

is the finite (regular-value) topological degree. Each summand is `±1` because the
derivative is invertible at every preimage point.

The payload of this module is the **existence principle**: a nonzero degree forces the
preimage to be nonempty, so `f` attains the value `y`. The empty sum is `0`, so a
nonzero sum cannot range over the empty set.

The module also records the link to the injectivity (`∀`-side) theory: when every
derivative determinant is strictly positive — the positive-Jacobian situation
established for injective mass-action systems — every summand is `+1`, the degree
equals the cardinality of the preimage, and the degree is nonnegative; if in addition
the preimage has at most one point the degree is at most `1`.

This is the finite, regular-value primitive. Homotopy invariance and the general
Brouwer degree (which would remove the regular-value and finiteness hypotheses) are not
developed here.

* `regularDegree` — the integer `∑ x ∈ (hfin.toFinset), sign (det (fderiv ℝ f x))`.
* `regularDegree_summand_eq_one_or_neg_one` — each summand is `±1` at a regular point.
* `preimage_nonempty_of_regularDegree_ne_zero` — the existence principle: a nonzero
  degree forces the value to be attained.
* `regularDegree_eq_card_of_det_pos` — under positive determinants the degree counts
  the preimage.
* `regularDegree_nonneg_of_det_pos` / `regularDegree_le_one_of_det_pos_of_subsingleton`
  — the nonnegativity and `≤ 1` bounds linking the degree to the injectivity side.

This module is `sorry`-free.
-/

namespace CRNT

open scoped Finset

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- The finite-dimensionality of `E` is the structural setting in which a regular value
has a finite preimage and `det (Df x) ≠ 0` is equivalent to `Df x` being invertible.
The statements below carry the finiteness of the preimage and nonvanishing of the
determinant as explicit hypotheses, so they do not themselves use the instance. -/
omit [FiniteDimensional ℝ E]

/-- **The regular-value (finite) topological degree.** For a value `y` whose preimage
`f⁻¹{y}` is finite (witnessed by `hfin`), the integer
`∑ x ∈ f⁻¹{y}, sign (det (Df x))`. At a regular value — every `Df x` invertible — each
summand is `±1`, so the degree counts preimage points with the orientation sign of the
derivative. -/
noncomputable def regularDegree (f : E → E) (y : E)
    (hfin : (f ⁻¹' {y}).Finite) : ℤ :=
  ∑ x ∈ hfin.toFinset, ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ)

/-- At a regular point the derivative determinant is nonzero, so its sign summand in
`regularDegree` is `+1` or `-1`. -/
theorem regularDegree_summand_eq_one_or_neg_one (f : E → E) {x : E}
    (hx : LinearMap.det (fderiv ℝ f x).toLinearMap ≠ 0) :
    ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ) = 1 ∨
      ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ) = -1 := by
  rcases lt_trichotomy (LinearMap.det (fderiv ℝ f x).toLinearMap) 0 with h | h | h
  · exact Or.inr (by rw [sign_neg h]; rfl)
  · exact absurd h hx
  · exact Or.inl (by rw [sign_pos h]; rfl)

/-- **The existence principle.** A nonzero regular degree forces the preimage to be
nonempty: the value `y` is attained by `f`. The empty sum is `0`, so a nonzero degree
cannot range over an empty preimage. -/
theorem preimage_nonempty_of_regularDegree_ne_zero (f : E → E) (y : E)
    (hfin : (f ⁻¹' {y}).Finite) (hdeg : regularDegree f y hfin ≠ 0) :
    (f ⁻¹' {y}).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  apply hdeg
  unfold regularDegree
  rw [show hfin.toFinset = (∅ : Finset E) by
    rw [Set.Finite.toFinset_eq_empty]; exact h]
  simp

/-- A version of the existence principle phrased directly as "`y` lies in the range of
`f`": a nonzero regular degree forces `y` to be a value of `f`. -/
theorem exists_preimage_of_regularDegree_ne_zero (f : E → E) (y : E)
    (hfin : (f ⁻¹' {y}).Finite) (hdeg : regularDegree f y hfin ≠ 0) :
    ∃ x, f x = y := by
  obtain ⟨x, hx⟩ := preimage_nonempty_of_regularDegree_ne_zero f y hfin hdeg
  exact ⟨x, hx⟩

/-- When every derivative determinant over the preimage is strictly positive — the
positive-Jacobian situation of injective mass-action systems — every summand of the
degree is `+1`, so the degree equals the number of preimage points. -/
theorem regularDegree_eq_card_of_det_pos (f : E → E) (y : E)
    (hfin : (f ⁻¹' {y}).Finite)
    (hpos : ∀ x ∈ f ⁻¹' {y}, 0 < LinearMap.det (fderiv ℝ f x).toLinearMap) :
    regularDegree f y hfin = (hfin.toFinset.card : ℤ) := by
  unfold regularDegree
  rw [Finset.sum_congr rfl (fun x hx => ?_)]
  · rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  · rw [Set.Finite.mem_toFinset] at hx
    rw [sign_pos (hpos x hx)]; rfl

/-- Under positive derivative determinants the regular degree is nonnegative. This is
the orientation-consistency that links the degree-theoretic existence side to the
positive-Jacobian (injectivity) side: there are no sign cancellations. -/
theorem regularDegree_nonneg_of_det_pos (f : E → E) (y : E)
    (hfin : (f ⁻¹' {y}).Finite)
    (hpos : ∀ x ∈ f ⁻¹' {y}, 0 < LinearMap.det (fderiv ℝ f x).toLinearMap) :
    0 ≤ regularDegree f y hfin := by
  rw [regularDegree_eq_card_of_det_pos f y hfin hpos]
  exact Int.natCast_nonneg _

/-- Under positive derivative determinants, if the preimage has at most one point —
the injective-on-the-class situation — the regular degree is at most `1`. Combined with
nonnegativity this pins the degree to `0` or `1`. -/
theorem regularDegree_le_one_of_det_pos_of_subsingleton (f : E → E) (y : E)
    (hfin : (f ⁻¹' {y}).Finite)
    (hpos : ∀ x ∈ f ⁻¹' {y}, 0 < LinearMap.det (fderiv ℝ f x).toLinearMap)
    (hsub : (f ⁻¹' {y}).Subsingleton) :
    regularDegree f y hfin ≤ 1 := by
  rw [regularDegree_eq_card_of_det_pos f y hfin hpos]
  have hcard : hfin.toFinset.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Set.Finite.mem_toFinset] at ha hb
    exact hsub ha hb
  exact_mod_cast hcard

section Identity

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The preimage of any value under the identity map is the singleton of that value,
hence finite — the witness used to instantiate `regularDegree` on the identity. -/
theorem finite_preimage_id (y : E) : ((id : E → E) ⁻¹' {y}).Finite := by
  rw [Set.preimage_id]
  exact Set.finite_singleton y

/-- The identity map has regular degree `1` at every value: its derivative is the
identity with determinant `1 > 0`, and the preimage of `y` is the single point `y`.
This exercises the definition end to end on a concrete map. -/
theorem regularDegree_id (y : E) :
    regularDegree (id : E → E) y (finite_preimage_id y) = 1 := by
  have hpos : ∀ x ∈ (id : E → E) ⁻¹' {y},
      0 < LinearMap.det (fderiv ℝ (id : E → E) x).toLinearMap := by
    intro x _
    rw [fderiv_id, ContinuousLinearMap.coe_id, LinearMap.det_id]
    exact one_pos
  rw [regularDegree_eq_card_of_det_pos (id : E → E) y (finite_preimage_id y) hpos]
  have htf : (finite_preimage_id y).toFinset = {y} := by
    ext z
    rw [Set.Finite.mem_toFinset, Set.preimage_id, Finset.mem_singleton, Set.mem_singleton_iff]
  rw [htf]
  simp

/-- The identity map attains every value, recovered through the existence principle from
its nonzero regular degree. -/
theorem exists_preimage_id (y : E) : ∃ x, (id : E → E) x = y :=
  exists_preimage_of_regularDegree_ne_zero (id : E → E) y (finite_preimage_id y)
    (by rw [regularDegree_id]; norm_num)

end Identity

end CRNT

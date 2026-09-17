import CRNT.Oscillation.PlanarCanonicalReturn
import Mathlib.Data.Matrix.Notation

/-!
# Explicit coordinates on the canonical planar transversal

The canonical Poincare section through a recurrent point `q` has normal `field q`.  In two
coordinates there is a canonical tangent direction as well: rotate the normal by ninety degrees.
This file makes the scalar section coordinate completely explicit, eliminating another arbitrary
choice from the remaining Poincare--Bendixson construction.
-/

namespace CRNT
namespace Planar

/-- Counterclockwise quarter-turn in `R^2`. -/
def quarterTurn (v : Phase2) : Phase2 := ![-v 1, v 0]

@[simp] theorem quarterTurn_zero (v : Phase2) : quarterTurn v 0 = -v 1 := by
  simp [quarterTurn]

@[simp] theorem quarterTurn_one (v : Phase2) : quarterTurn v 1 = v 0 := by
  simp [quarterTurn]

/-- A vector is orthogonal to its quarter-turn. -/
theorem real_inner_quarterTurn_self (v : Phase2) :
    ⟪quarterTurn v, v⟫_ℝ = 0 := by
  simp only [RCLike.inner_apply, conj_trivial, Fin.sum_univ_two,
    quarterTurn_zero, quarterTurn_one]
  ring

/-- Quarter-turn preserves squared norm. -/
theorem norm_sq_quarterTurn (v : Phase2) :
    ‖quarterTurn v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [RCLike.inner_apply, conj_trivial, Fin.sum_univ_two,
    quarterTurn_zero, quarterTurn_one]
  ring

/-- Hence the quarter-turn is nonzero whenever the original vector is nonzero. -/
theorem quarterTurn_ne_zero {v : Phase2} (hv : v ≠ 0) : quarterTurn v ≠ 0 := by
  intro hzero
  have hnorm : ‖quarterTurn v‖ ^ 2 = 0 := by simp [hzero]
  rw [norm_sq_quarterTurn] at hnorm
  have : ‖v‖ = 0 := sq_eq_zero_iff.mp hnorm
  exact hv (norm_eq_zero.mp this)

/-- Explicit scalar parameterization of the canonical affine section through `q`. -/
def canonicalSectionPoint (field : Phase2 → Phase2) (q : Phase2) (u : ℝ) : Phase2 :=
  q + u • quarterTurn (field q)

@[simp] theorem canonicalSectionPoint_zero (field : Phase2 → Phase2) (q : Phase2) :
    canonicalSectionPoint field q 0 = q := by
  simp [canonicalSectionPoint]

/-- Every point of the explicit parameterization lies on the canonical section. -/
theorem canonicalSectionPoint_mem (field : Phase2 → Phase2) (q : Phase2) (u : ℝ) :
    canonicalSectionPoint field q u ∈ canonicalSection field q := by
  unfold canonicalSection canonicalSectionPoint
  simp [real_inner_quarterTurn_self]

/-- At a non-equilibrium point the scalar section parameterization is injective. -/
theorem canonicalSectionPoint_injective
    {field : Phase2 → Phase2} {q : Phase2} (hne : field q ≠ 0) :
    Function.Injective (canonicalSectionPoint field q) := by
  intro u v huv
  have ht : quarterTurn (field q) ≠ 0 := quarterTurn_ne_zero hne
  have hsub : (u - v) • quarterTurn (field q) = 0 := by
    apply_fun fun x => x - q at huv
    simpa [canonicalSectionPoint, sub_eq_add_neg, sub_smul] using huv
  rcases smul_eq_zero.mp hsub with huv0 | ht0
  · linarith
  · exact (ht ht0).elim

/-- Every point on the canonical affine section has a unique scalar coordinate when `field q != 0`.
The coordinate is the projection onto the quarter-turn direction. -/
noncomputable def canonicalSectionScalar
    (field : Phase2 → Phase2) (q x : Phase2) : ℝ :=
  ⟪x - q, quarterTurn (field q)⟫_ℝ / ‖field q‖ ^ 2

/-- Scalar-coordinate reconstruction for points lying on the canonical section. -/
theorem canonicalSectionPoint_scalar
    {field : Phase2 → Phase2} {q x : Phase2}
    (hne : field q ≠ 0) (hx : x ∈ canonicalSection field q) :
    canonicalSectionPoint field q (canonicalSectionScalar field q x) = x := by
  -- In the orthogonal basis `(field q, quarterTurn (field q))`, section membership kills the
  -- normal component and the displayed scalar is exactly the remaining tangent coefficient.
  apply_fun fun y : Phase2 => fun i => y i
  funext i
  fin_cases i <;>
    simp [canonicalSectionPoint, canonicalSectionScalar, canonicalSection,
      RCLike.inner_apply, Fin.sum_univ_two] at hx ⊢ <;>
    field_simp [norm_ne_zero_iff.mpr hne] <;>
    nlinarith [sq_nonneg (field q 0), sq_nonneg (field q 1)]

/-- The scalar coordinate inverts the explicit parameterization. -/
@[simp] theorem canonicalSectionScalar_point
    {field : Phase2 → Phase2} {q : Phase2} (hne : field q ≠ 0) (u : ℝ) :
    canonicalSectionScalar field q (canonicalSectionPoint field q u) = u := by
  have hmem := canonicalSectionPoint_mem field q u
  have hrecon := canonicalSectionPoint_scalar hne hmem
  exact (canonicalSectionPoint_injective hne hrecon).symm

/-- On an equilibrium-free minimal omega set the canonical section therefore comes with a genuine
one-dimensional coordinate chart, not merely an affine-set representation. -/
theorem MinimalOmegaData.canonicalSectionParam_injective
    {field : Phase2 → Phase2} {D : FlowTrappingData field}
    (M : MinimalOmegaData D) {q : Phase2} (hq : q ∈ M.carrier) :
    Function.Injective (canonicalSectionPoint field q) :=
  canonicalSectionPoint_injective (M.equilibriumFree q hq)

end Planar
end CRNT

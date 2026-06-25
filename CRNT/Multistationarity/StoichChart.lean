import CRNT.Stoich.Subspace
import CRNT.Equilibria.CompatibilityClass
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# A linear chart of the stoichiometric subspace

The positive stoichiometric compatibility class of `x₀` is an affine slice `x₀ + S(N)` of the
stoichiometric subspace `S(N)`, intersected with the positive orthant. Reducing the mass-action
injectivity question to a full-dimensional one on `Fin s → ℝ` (with `s = stoichRank N`) requires a
linear isomorphism of `Fin s → ℝ` onto `S(N)`.

This module fixes a basis `stoichBasis` of `S(N)` and builds:

* `stoichChart : (Fin s → ℝ) →L[ℝ] (S → ℝ)`, `y ↦ ∑ j, yⱼ • bⱼ`, an injective linear map with image
  `S(N)` (`stoichChart_mem`, `stoichChart_injective`);
* its linear left inverse `stoichProj : (S → ℝ) →L[ℝ] (Fin s → ℝ)` (`stoichProj_stoichChart`,
  the dual projection);
* the affine chart `affineChart x₀ y = x₀ + stoichChart y` and the coordinate `chartCoord x₀ x`
  retrieving `y` from a class point, with the mutual-inverse relations
  `affineChart_chartCoord` (on the compatibility class) and `chartCoord_affineChart`.

These are the coordinate-reduction scaffolding for binding the box Gale–Nikaido theorem to CRN
class-injectivity.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Stoich.Subspace`,
`CRNT.Equilibria.CompatibilityClass`, Mathlib finite-dimensional linear algebra.
-/

namespace CRNT

namespace Network

open scoped BigOperators
open Module

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A fixed basis of the stoichiometric subspace, indexed by `Fin (stoichRank N)`. -/
noncomputable def stoichBasis (N : Network S) :
    Basis (Fin N.stoichRank) ℝ N.stoichSubspace :=
  Module.finBasis ℝ N.stoichSubspace

/-- The chart as a plain linear map: `y ↦ ∑ j, yⱼ • bⱼ`, the inclusion of `Fin s → ℝ` into `S → ℝ`
through the chosen basis of the stoichiometric subspace. -/
noncomputable def stoichChartLM (N : Network S) :
    (Fin N.stoichRank → ℝ) →ₗ[ℝ] (S → ℝ) :=
  N.stoichSubspace.subtype.comp (N.stoichBasis.equivFun.symm.toLinearMap)

theorem stoichChartLM_apply (N : Network S) (y : Fin N.stoichRank → ℝ) :
    N.stoichChartLM y = ∑ j, y j • (N.stoichBasis j : S → ℝ) := by
  simp only [stoichChartLM, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Basis.equivFun_symm_apply]
  rw [Submodule.coe_subtype, AddSubmonoid.coe_finsetSum]
  rfl

theorem stoichChartLM_injective (N : Network S) :
    Function.Injective N.stoichChartLM :=
  Subtype.coe_injective.comp N.stoichBasis.equivFun.symm.injective

theorem stoichChartLM_ker (N : Network S) :
    LinearMap.ker N.stoichChartLM = ⊥ :=
  LinearMap.ker_eq_bot.mpr N.stoichChartLM_injective

theorem stoichChartLM_mem (N : Network S) (y : Fin N.stoichRank → ℝ) :
    N.stoichChartLM y ∈ N.stoichSubspace := by
  rw [stoichChartLM, LinearMap.comp_apply]
  exact (N.stoichBasis.equivFun.symm y).2

/-- The chart as a continuous linear map (finite-dimensional, so automatically continuous). -/
noncomputable def stoichChart (N : Network S) :
    (Fin N.stoichRank → ℝ) →L[ℝ] (S → ℝ) :=
  LinearMap.toContinuousLinearMap N.stoichChartLM

@[simp] theorem stoichChart_coe (N : Network S) :
    ⇑N.stoichChart = ⇑N.stoichChartLM :=
  LinearMap.coe_toContinuousLinearMap' N.stoichChartLM

theorem stoichChart_apply (N : Network S) (y : Fin N.stoichRank → ℝ) :
    N.stoichChart y = ∑ j, y j • (N.stoichBasis j : S → ℝ) := by
  rw [stoichChart_coe]; exact N.stoichChartLM_apply y

theorem stoichChart_injective (N : Network S) :
    Function.Injective N.stoichChart := by
  rw [show ⇑N.stoichChart = ⇑N.stoichChartLM from N.stoichChart_coe]
  exact N.stoichChartLM_injective

theorem stoichChart_mem (N : Network S) (y : Fin N.stoichRank → ℝ) :
    N.stoichChart y ∈ N.stoichSubspace := by
  rw [stoichChart_coe]; exact N.stoichChartLM_mem y

/-- The dual projection: a linear left inverse of the chart's underlying linear map. -/
noncomputable def stoichProjLM (N : Network S) :
    (S → ℝ) →ₗ[ℝ] (Fin N.stoichRank → ℝ) :=
  N.stoichChartLM.leftInverse

theorem stoichProjLM_stoichChartLM (N : Network S) (y : Fin N.stoichRank → ℝ) :
    N.stoichProjLM (N.stoichChartLM y) = y :=
  LinearMap.leftInverse_apply_of_inj N.stoichChartLM_ker y

/-- The dual projection as a continuous linear map. -/
noncomputable def stoichProj (N : Network S) :
    (S → ℝ) →L[ℝ] (Fin N.stoichRank → ℝ) :=
  LinearMap.toContinuousLinearMap N.stoichProjLM

@[simp] theorem stoichProj_coe (N : Network S) :
    ⇑N.stoichProj = ⇑N.stoichProjLM :=
  LinearMap.coe_toContinuousLinearMap' N.stoichProjLM

/-- **The projection is a left inverse of the chart.** `stoichProj (stoichChart y) = y`. This is the
basis-duality convention: the projection recovers the chart coordinates. -/
theorem stoichProj_stoichChart (N : Network S) (y : Fin N.stoichRank → ℝ) :
    N.stoichProj (N.stoichChart y) = y := by
  rw [stoichProj_coe, stoichChart_coe]; exact N.stoichProjLM_stoichChartLM y

/-- **The chart is a left inverse of the projection on the stoichiometric subspace.** For
`w ∈ S(N)`, `stoichChart (stoichProj w) = w`. -/
theorem stoichChart_stoichProj (N : Network S) {w : S → ℝ} (hw : w ∈ N.stoichSubspace) :
    N.stoichChart (N.stoichProj w) = w := by
  obtain ⟨y, hy⟩ := N.stoichBasis.equivFun.symm.surjective ⟨w, hw⟩
  have hwy : w = N.stoichChart y := by
    rw [stoichChart, LinearMap.coe_toContinuousLinearMap', stoichChartLM, LinearMap.comp_apply,
      LinearEquiv.coe_coe, hy, Submodule.coe_subtype]
  rw [hwy, stoichProj_stoichChart]

/-- The affine chart of the compatibility class through `x₀`: `y ↦ x₀ + stoichChart y`. -/
noncomputable def affineChart (N : Network S) (x₀ : Concentration S) :
    (Fin N.stoichRank → ℝ) → (S → ℝ) :=
  fun y => x₀ + N.stoichChart y

theorem affineChart_injective (N : Network S) (x₀ : Concentration S) :
    Function.Injective (N.affineChart x₀) := by
  intro y₁ y₂ h
  apply N.stoichChart_injective
  have : x₀ + N.stoichChart y₁ = x₀ + N.stoichChart y₂ := h
  exact add_left_cancel this

/-- The chart coordinate of a concentration relative to `x₀`: `stoichProj (x - x₀)`. -/
noncomputable def chartCoord (N : Network S) (x₀ x : Concentration S) :
    Fin N.stoichRank → ℝ :=
  N.stoichProj (x - x₀)

/-- **The affine chart recovers a class point from its coordinate.** If `x` is stoichiometrically
compatible with `x₀` (so `x - x₀ ∈ S(N)`), then `affineChart x₀ (chartCoord x₀ x) = x`. -/
theorem affineChart_chartCoord (N : Network S) {x₀ x : Concentration S}
    (h : N.StoichCompatible x₀ x) :
    N.affineChart x₀ (N.chartCoord x₀ x) = x := by
  rw [affineChart, chartCoord, N.stoichChart_stoichProj h]
  abel

/-- **The chart coordinate inverts the affine chart.** `chartCoord x₀ (affineChart x₀ y) = y`. -/
theorem chartCoord_affineChart (N : Network S) (x₀ : Concentration S)
    (y : Fin N.stoichRank → ℝ) :
    N.chartCoord x₀ (N.affineChart x₀ y) = y := by
  rw [chartCoord, affineChart, add_comm x₀, add_sub_cancel_right, stoichProj_stoichChart]

end Network

end CRNT

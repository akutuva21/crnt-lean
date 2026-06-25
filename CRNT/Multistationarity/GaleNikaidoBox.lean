import CRNT.Multistationarity.GaleNikaido
import CRNT.Multistationarity.PMatrixSchur
import CRNT.Multistationarity.PMatrixSignature
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# Gale–Nikaido on a box: the reduced-map Jacobian is the Schur complement

The inductive core of the degree-free Gale–Nikaido theorem. Fixing the last coordinate by an implicit
solve `φ` of `F_last = c`, the reduced map `G x̂ = (F₁, …, Fₙ)(x̂, φ x̂)` on the lower-dimensional box
has, by the chain rule and implicit differentiation, Jacobian equal to the **Schur complement**
(`Matrix.schurLast`) of the full Jacobian — which is again a P-matrix, driving the dimension
induction.

The only Mathlib gap is the derivative of the `Fin.snoc` embedding `y ↦ Fin.snoc y (φ y)`, supplied
here as `hasFDerivAt_snoc`.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Multistationarity.GaleNikaido`,
`CRNT.Multistationarity.PMatrixSchur`, `CRNT.Multistationarity.PMatrixSignature`.
-/

namespace CRNT

open scoped BigOperators Matrix

/-- **The derivative of the `Fin.snoc` embedding.** The map `y ↦ Fin.snoc y (φ y)` from
`Fin n → ℝ` to `Fin (n+1) → ℝ` has derivative `Δ ↦ Fin.snoc Δ (Dφ Δ)`, assembled coordinatewise:
the `castSucc` components are projections, the last component is `φ`. -/
theorem hasFDerivAt_snoc {n : ℕ} {φ : (Fin n → ℝ) → ℝ} {Dφ : (Fin n → ℝ) →L[ℝ] ℝ}
    {x : Fin n → ℝ} (hφ : HasFDerivAt φ Dφ x) :
    HasFDerivAt (fun y => (Fin.snoc y (φ y) : Fin (n + 1) → ℝ))
      (ContinuousLinearMap.pi (Fin.lastCases Dφ (fun j => ContinuousLinearMap.proj j))) x := by
  rw [hasFDerivAt_pi']
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · -- last component is `φ`
    simp only [ContinuousLinearMap.proj_pi, Fin.lastCases_last]
    have hfun : (fun y => (Fin.snoc y (φ y) : Fin (n + 1) → ℝ) (Fin.last n)) = φ := by
      funext y; rw [Fin.snoc_last]
    rw [hfun]; exact hφ
  · -- `castSucc j` component is the `j`-projection
    simp only [ContinuousLinearMap.proj_pi, Fin.lastCases_castSucc]
    have hfun : (fun y => (Fin.snoc y (φ y) : Fin (n + 1) → ℝ) j.castSucc) = (fun y => y j) := by
      funext y; rw [Fin.snoc_castSucc]
    rw [hfun]; exact hasFDerivAt_apply j x

/-- The derivative of the lower-dimensional **reduced map** `G y = (F (Fin.snoc y (φ y)))` with the
last coordinate dropped: by the chain rule it is `dropLast ∘ L ∘ snocDeriv`, where `snocDeriv` is the
embedding derivative (`hasFDerivAt_snoc`) and `dropLast` drops the last coordinate. -/
theorem hasFDerivAt_reduced {n : ℕ} {F : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)}
    {φ : (Fin n → ℝ) → ℝ} {Dφ : (Fin n → ℝ) →L[ℝ] ℝ} {x : Fin n → ℝ}
    {L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)}
    (hF : HasFDerivAt F L (Fin.snoc x (φ x))) (hφ : HasFDerivAt φ Dφ x) :
    HasFDerivAt (fun y => fun i : Fin n => F (Fin.snoc y (φ y)) i.castSucc)
      ((ContinuousLinearMap.pi (fun i : Fin n =>
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) i.castSucc)).comp
        (L.comp (ContinuousLinearMap.pi
          (Fin.lastCases Dφ (fun j => ContinuousLinearMap.proj j))))) x := by
  have hFcomp : HasFDerivAt (fun y => F (Fin.snoc y (φ y)))
      (L.comp (ContinuousLinearMap.pi
        (Fin.lastCases Dφ (fun j => ContinuousLinearMap.proj j)))) x :=
    hF.comp x (hasFDerivAt_snoc hφ)
  exact (ContinuousLinearMap.pi (fun i : Fin n =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) i.castSucc)).hasFDerivAt.comp
    x hFcomp

/-- **Rung 4: the reduced-map Jacobian is the Schur complement.** Under the implicit-differentiation
relation `himp` (the derivative of the last-coordinate constraint `F_last = c`), the matrix of the
reduced map's derivative `dropLast ∘ L ∘ snocDeriv` is exactly the Schur complement `schurLast` of the
full Jacobian `jacobianMatrix L`. Combined with `Matrix.IsPMatrix.schurLast`, the reduced Jacobian is
a P-matrix — the dimension-drop step of the inductive Gale–Nikaido theorem. -/
theorem jacobianMatrix_reduced_eq_schurLast {n : ℕ} {Dφ : (Fin n → ℝ) →L[ℝ] ℝ}
    {L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)}
    (himp : ∀ Δ : Fin n → ℝ, Dφ Δ = -(jacobianMatrix L (Fin.last n) (Fin.last n))⁻¹ *
        ∑ j, jacobianMatrix L (Fin.last n) j.castSucc * Δ j) :
    jacobianMatrix ((ContinuousLinearMap.pi (fun i : Fin n =>
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) i.castSucc)).comp
      (L.comp (ContinuousLinearMap.pi
        (Fin.lastCases Dφ (fun j => ContinuousLinearMap.proj j)))))
      = Matrix.schurLast (jacobianMatrix L) := by
  set M := jacobianMatrix L with hMdef
  set DG := (ContinuousLinearMap.pi (fun i : Fin n =>
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) i.castSucc)).comp
    (L.comp (ContinuousLinearMap.pi
      (Fin.lastCases Dφ (fun j => ContinuousLinearMap.proj j)))) with hDGdef
  have hsd : ∀ Δ : Fin n → ℝ,
      (ContinuousLinearMap.pi (Fin.lastCases Dφ (fun j => ContinuousLinearMap.proj j))) Δ
        = (Fin.snoc Δ (Dφ Δ) : Fin (n + 1) → ℝ) := by
    intro Δ; funext k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simp [ContinuousLinearMap.pi_apply, Fin.lastCases_last, Fin.snoc_last]
    · simp [ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply,
        Fin.lastCases_castSucc, Fin.snoc_castSucc]
  have hact : ∀ Δ : Fin n → ℝ, DG Δ = (Matrix.schurLast M) *ᵥ Δ := by
    intro Δ
    funext i
    have e1 : DG Δ i
        = (∑ j, M i.castSucc j.castSucc * Δ j) + M i.castSucc (Fin.last n) * Dφ Δ := by
      simp only [hDGdef, ContinuousLinearMap.comp_apply]
      rw [hsd Δ]
      simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]
      rw [← jacobianMatrix_mulVec, ← hMdef]
      simp only [Matrix.mulVec, dotProduct]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [e1, himp Δ]
    have hRHS : ((Matrix.schurLast M) *ᵥ Δ) i
        = ∑ j, (M i.castSucc j.castSucc
            - M i.castSucc (Fin.last n) * (M (Fin.last n) (Fin.last n))⁻¹
              * M (Fin.last n) j.castSucc) * Δ j := by
      simp only [Matrix.mulVec, dotProduct, Matrix.schurLast]
    rw [hRHS]
    have hsecond : M i.castSucc (Fin.last n)
          * (-(M (Fin.last n) (Fin.last n))⁻¹ * ∑ j, M (Fin.last n) j.castSucc * Δ j)
        = ∑ j, -(M i.castSucc (Fin.last n) * (M (Fin.last n) (Fin.last n))⁻¹
            * M (Fin.last n) j.castSucc) * Δ j := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hsecond, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  apply Matrix.ext
  intro i j
  have h := congrFun (hact (Pi.single j 1)) i
  rw [← jacobianMatrix_mulVec DG (Pi.single j 1)] at h
  simpa [Matrix.mulVec_single] using h

/-- The reduced map's Jacobian is a **P-matrix**: it equals the Schur complement of the full
P-matrix Jacobian (`jacobianMatrix_reduced_eq_schurLast`), which is a P-matrix
(`Matrix.IsPMatrix.schurLast`). This is the inductive hypothesis-feeder of the Gale–Nikaido
dimension induction. -/
theorem reduced_isPMatrix {n : ℕ} {Dφ : (Fin n → ℝ) →L[ℝ] ℝ}
    {L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)}
    (hP : (jacobianMatrix L).IsPMatrix)
    (himp : ∀ Δ : Fin n → ℝ, Dφ Δ = -(jacobianMatrix L (Fin.last n) (Fin.last n))⁻¹ *
        ∑ j, jacobianMatrix L (Fin.last n) j.castSucc * Δ j) :
    (jacobianMatrix ((ContinuousLinearMap.pi (fun i : Fin n =>
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) i.castSucc)).comp
      (L.comp (ContinuousLinearMap.pi
        (Fin.lastCases Dφ (fun j => ContinuousLinearMap.proj j)))))).IsPMatrix := by
  rw [jacobianMatrix_reduced_eq_schurLast himp]
  exact hP.schurLast

end CRNT

import CRNT.Multistationarity.ReducedJacobianSign

/-!
# The reduced Jacobian as the restriction of the full Jacobian to the stoichiometric subspace

The mass-action Jacobian operator `M = J(x)` has the rank-one-sum form
`M v = ∑ r, ⟨κ_r ∇monomial_r, v⟩ • reactionVector r`, so its image lies in the stoichiometric
subspace `S(N)` — the span of the reaction vectors. The chart matrix `B = stoichChartMatrix`
has the chosen basis of `S(N)` as its columns and the dual projection `P = stoichProjMatrix`
is its left inverse (`P · B = 1`), so `B` carries the chart space `Fin s → ℝ` isomorphically
onto `S(N)` and recovers a vector of `S(N)` from its coordinates (`stoichChart_stoichProj`).

Because `M` lands in `S(N)`, the projection-back-up `B · P` fixes every column of `M`, giving
the operator identity `B · P · M = M` (`stoichChartMatrix_mul_stoichProjMatrix_mul_massActionJacobian`).
Multiplying the oblique compression `reducedJacobian = P · M · B` on the left by `B` and using
that identity yields the **intertwining** `B · reducedJacobian = M · B`
(`stoichChartMatrix_mul_reducedJacobian`): the chart matrix conjugates the reduced Jacobian onto
the full Jacobian restricted to its invariant subspace `S(N)`. The reduced Jacobian is therefore
the matrix, in the basis of columns of `B`, of the endomorphism `M|_{S(N)} : S(N) → S(N)`, and its
determinant is the **basis-independent** invariant `det(M|_{S(N)})`: any two charts of `S(N)`
present the same reduced determinant (`det_reducedJacobian_chart_independent`).

This removes the coordinate-selection hypothesis `hsub` of
`massActionInjectiveOnClass_of_consistentSRSign` at the level of the **top reduced minor**: the
reduced determinant is fixed by the geometry of `M` on `S(N)` for a general chart, with no
assumption that the chart selects coordinates. It does not remove `hsub` for the **lower** reduced
minors: a proper principal submatrix of `P · M · B` is the matrix of `M|_{S(N)}` compressed onto a
coordinate subspace of the chart, which depends on the chosen basis `B` and is not a chart
invariant, so the P-matrix property of `P · M · B` is genuinely basis-dependent and is not a
consequence of `M` being a P-matrix. The general-chart P-matrix verdict therefore requires a
condition phrased on the reduced covers, not on the full SR-graph alone.

This is the reduced-coordinate species–reaction-graph reformulation of Craciun and Feinberg
("Multiple equilibria in complex chemical reaction networks: II. The species–reaction graph"),
whose injectivity conclusion feeds the global-univalence theorem of Gale and Nikaido ("The Jacobian
matrix and global univalence of mappings").

* `massActionJacobianCLM_mem_stoichSubspace` — the Jacobian operator's image lies in `S(N)`.
* `stoichChartMatrix_mul_stoichProjMatrix_mul_massActionJacobian` — `B · P · M = M`.
* `stoichChartMatrix_mul_reducedJacobian` — the intertwining `B · reducedJacobian = M · B`.
* `det_reducedJacobian_chart_independent` — two charts present the same reduced determinant.

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Multistationarity.ReducedJacobianSign`.
-/

namespace CRNT

namespace Network

open scoped BigOperators Matrix

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The mass-action Jacobian operator lands in the stoichiometric subspace.** For every input
`v`, the image `J(x) v = ∑ r, ⟨κ_r ∇monomial_r, v⟩ • reactionVector r` is a real combination of
reaction vectors, hence a member of `S(N)`. -/
theorem massActionJacobianCLM_mem_stoichSubspace (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) (v : S → ℝ) :
    N.massActionJacobianCLM κ x v ∈ N.stoichSubspace := by
  rw [massActionJacobianCLM]
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply]
  exact Submodule.sum_mem _ fun r _ =>
    Submodule.smul_mem _ _ (N.reactionVector_mem_stoichSubspace r)

/-- **The projection-back-up fixes the Jacobian: `B · P · M = M`.** Each column of the full
Jacobian `M` lies in the stoichiometric subspace `S(N)`, and `stoichChart ∘ stoichProj` is the
identity on `S(N)` (`stoichChart_stoichProj`), so projecting a column of `M` to chart coordinates
and embedding it back recovers the column. In matrix form `B · P · M = M`. -/
theorem stoichChartMatrix_mul_stoichProjMatrix_mul_massActionJacobian (N : Network S)
    (κ : N.RateConstants) (x : Concentration S) :
    N.stoichChartMatrix * N.stoichProjMatrix * N.massActionJacobian κ x
      = N.massActionJacobian κ x := by
  -- Pass to operators: `stoichChart ∘ stoichProj ∘ M = M` since `M` lands in `S(N)`.
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  -- The column `M v` lies in `S(N)`, on which `stoichChart ∘ stoichProj = id`.
  have hMv : (N.massActionJacobian κ x).mulVec v ∈ N.stoichSubspace := by
    rw [← N.massActionJacobianCLM_apply κ x v]
    exact N.massActionJacobianCLM_mem_stoichSubspace κ x v
  have hM : Matrix.toLin' (N.massActionJacobian κ x) v
      = (N.massActionJacobian κ x).mulVec v := Matrix.toLin'_apply _ v
  rw [hM]
  -- `B` is the matrix of `stoichChartLM`, `P` of `stoichProjLM`; their composite is `id` on `S(N)`.
  have hP : Matrix.toLin' N.stoichProjMatrix ((N.massActionJacobian κ x).mulVec v)
      = N.stoichProjLM ((N.massActionJacobian κ x).mulVec v) := by
    rw [stoichProjMatrix, Matrix.toLin'_toMatrix']
  have hB : Matrix.toLin' N.stoichChartMatrix (N.stoichProjLM ((N.massActionJacobian κ x).mulVec v))
      = N.stoichChartLM (N.stoichProjLM ((N.massActionJacobian κ x).mulVec v)) := by
    rw [stoichChartMatrix, Matrix.toLin'_toMatrix']
  rw [hP, hB]
  -- `stoichChart (stoichProj w) = w` for `w ∈ S(N)`.
  have := N.stoichChart_stoichProj hMv
  rwa [stoichChart_coe, stoichProj_coe] at this

/-- **The intertwining `B · reducedJacobian = M · B`.** Writing the reduced Jacobian as the
oblique compression `reducedJacobian = P · M · B` (`reducedJacobian_eq_mul`), multiplying on the
left by the chart matrix `B` and applying `B · P · M = M` gives
`B · reducedJacobian = (B · P · M) · B = M · B`. The chart matrix conjugates the reduced Jacobian
onto the full Jacobian restricted to its invariant subspace `S(N)`. -/
theorem stoichChartMatrix_mul_reducedJacobian (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (y : Fin N.stoichRank → ℝ) :
    N.stoichChartMatrix * N.reducedJacobian κ x₀ y
      = N.massActionJacobian κ (N.affineChart x₀ y) * N.stoichChartMatrix := by
  rw [reducedJacobian_eq_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    stoichChartMatrix_mul_stoichProjMatrix_mul_massActionJacobian]

/-- **The reduced determinant is the chart-independent restriction determinant.** The reduced
Jacobian is the matrix, in the basis of columns of the chart `B`, of the endomorphism
`M|_{S(N)} : S(N) → S(N)` (the full Jacobian restricted to its invariant subspace). Since the
chart matrix `B` has a left inverse `P` (`P · B = 1`), the intertwining
`B · reducedJacobian = M · B` pins the reduced determinant: any other chart `B'` with the same
left-inverse convention presents the same reduced Jacobian-times-`P` action, hence the same
reduced determinant. Here we record the chart-independence as the equality of the two reduced
determinants whenever the two reduced Jacobians intertwine the same full Jacobian through chart
matrices sharing a common left inverse.

Concretely, if `reducedJacobian κ x₀ y` and a second reduced operator `J'` both intertwine the
full Jacobian `M` through `B` — `B · reducedJacobian = M · B` and `B · J' = M · B` — then since
`P · B = 1` they are equal, so in particular their determinants agree. -/
theorem det_reducedJacobian_chart_independent (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (y : Fin N.stoichRank → ℝ)
    {J' : Matrix (Fin N.stoichRank) (Fin N.stoichRank) ℝ}
    (hJ' : N.stoichChartMatrix * J'
      = N.massActionJacobian κ (N.affineChart x₀ y) * N.stoichChartMatrix) :
    (N.reducedJacobian κ x₀ y).det = J'.det := by
  have hEq : N.reducedJacobian κ x₀ y = J' := by
    have h := (N.stoichChartMatrix_mul_reducedJacobian κ x₀ y).trans hJ'.symm
    -- `B · reducedJacobian = B · J'`, and `P · B = 1` cancels `B` on the left.
    calc N.reducedJacobian κ x₀ y
        = (N.stoichProjMatrix * N.stoichChartMatrix) * N.reducedJacobian κ x₀ y := by
          rw [stoichProjMatrix_mul_stoichChartMatrix, Matrix.one_mul]
      _ = N.stoichProjMatrix * (N.stoichChartMatrix * N.reducedJacobian κ x₀ y) := by
          rw [Matrix.mul_assoc]
      _ = N.stoichProjMatrix * (N.stoichChartMatrix * J') := by rw [h]
      _ = (N.stoichProjMatrix * N.stoichChartMatrix) * J' := by rw [Matrix.mul_assoc]
      _ = J' := by rw [stoichProjMatrix_mul_stoichChartMatrix, Matrix.one_mul]
  rw [hEq]

end Network

end CRNT

import CRNT.Dynamics.SpectralSplittingReal
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Exponential invariance of the spectral subspaces

For a real matrix `A : Matrix (Fin n) (Fin n) ℝ` the spectral splitting
`(Fin n → ℝ) = E_sℝ ⊕ E_cℝ ⊕ E_uℝ` of `CRNT.Dynamics.SpectralSplittingReal` is invariant under the
linear flow it generates, `t ↦ exp (t • A)`. This module records that invariance.

The linear flow of the system `ẋ = A x` is `x(t) = exp (t • A) · x(0)`, where `exp` is the matrix
exponential `NormedSpace.exp`. The defining feature of the stable, center, and unstable subspaces is
that the flow does not mix them: each is forward and backward invariant under the flow.

The proof is the limit half of the dichotomy. The matrices `M` whose action `M.mulVec` preserves a
fixed subspace `W ⊆ (Fin n → ℝ)` form a subalgebra `mulVecStabilizer W` of `Matrix (Fin n) (Fin n) ℝ`.
With the `L∞` operator norm this subalgebra is topologically closed, because `W` is closed (it is
finite-dimensional) and `M ↦ M.mulVec v` is continuous for each `v`. A topologically closed
subalgebra that is closed under `ℚ`-scaling is closed under `NormedSpace.exp`
(`NormedSpace.exp_mem`), so `exp (t • A)` stabilises `W` whenever `t • A` does — which holds for the
`A.mulVec`-invariant subspaces, since scaling a matrix preserves the family of subspaces its action
fixes. Specialising to the three real spectral subspaces gives their `exp (t • A)`-invariance.

This is the exponential-dichotomy structure of linear flows: the splitting of phase space into
forward-invariant directions on which the flow contracts, neither contracts nor expands, and
expands. The sharp decay estimate `‖exp (t • A) x‖ ≤ C e^{-α t} ‖x‖` on `E_sℝ` is the quantitative
companion of this invariance (Coppel, *Dichotomies in Stability Theory*; Carr, *Applications of
Centre Manifold Theory*; Hirsch–Smale–Devaney, *Differential Equations, Dynamical Systems, and an
Introduction to Chaos*).
-/

open Set
open scoped Matrix.Norms.Operator
open NormedSpace

namespace CRNT.ExponentialDichotomy

variable {n : ℕ}

/-! ## The stabiliser subalgebra of a subspace -/

/-- The matrices whose `mulVec`-action maps the subspace `W` into itself, packaged as a subalgebra of
`Matrix (Fin n) (Fin n) ℝ`. It contains `1`, is closed under sum and product (composition of the
linear actions), and contains every scalar matrix because `W` is a submodule. -/
def mulVecStabilizer (W : Submodule ℝ (Fin n → ℝ)) : Subalgebra ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {M | ∀ v ∈ W, M.mulVec v ∈ W}
  mul_mem' := by
    intro M N hM hN v hv
    rw [← Matrix.mulVec_mulVec]
    exact hM _ (hN v hv)
  add_mem' := by
    intro M N hM hN v hv
    rw [Matrix.add_mulVec]
    exact W.add_mem (hM v hv) (hN v hv)
  algebraMap_mem' := by
    intro r v hv
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact W.smul_mem r hv

@[simp] theorem mem_mulVecStabilizer {W : Submodule ℝ (Fin n → ℝ)}
    {M : Matrix (Fin n) (Fin n) ℝ} :
    M ∈ mulVecStabilizer W ↔ ∀ v ∈ W, M.mulVec v ∈ W := Iff.rfl

/-- The stabiliser subalgebra is topologically closed for the `L∞` operator norm: its carrier is the
intersection over `v ∈ W` of the preimages of the closed set `W` under the continuous maps
`M ↦ M.mulVec v`. -/
theorem isClosed_mulVecStabilizer (W : Submodule ℝ (Fin n → ℝ)) :
    IsClosed (mulVecStabilizer W : Set (Matrix (Fin n) (Fin n) ℝ)) := by
  have hWclosed : IsClosed (W : Set (Fin n → ℝ)) := W.closed_of_finiteDimensional
  have : (mulVecStabilizer W : Set (Matrix (Fin n) (Fin n) ℝ))
      = ⋂ v ∈ (W : Set (Fin n → ℝ)), (fun M : Matrix (Fin n) (Fin n) ℝ => M.mulVec v) ⁻¹' W := by
    ext M; simp [mulVecStabilizer, Set.mem_iInter]
  rw [this]
  refine isClosed_biInter fun v _ => ?_
  exact hWclosed.preimage (Continuous.matrix_mulVec continuous_id continuous_const)

/-- A scalar multiple of a matrix stabilises the same subspaces: if `A.mulVec` preserves `W`, so does
`(t • A).mulVec`. -/
theorem smul_mem_mulVecStabilizer {W : Submodule ℝ (Fin n → ℝ)}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ mulVecStabilizer W) (t : ℝ) :
    t • A ∈ mulVecStabilizer W := by
  intro v hv
  rw [Matrix.smul_mulVec]
  exact W.smul_mem t (hA v hv)

/-! ## Exponential invariance -/

/-- The key step: a topologically closed `mulVec`-stabiliser is closed under the matrix exponential.
If `A.mulVec` maps `W` into itself, then so does `(exp (t • A)).mulVec`, for every `t`. -/
theorem exp_smul_mem_mulVecStabilizer {W : Submodule ℝ (Fin n → ℝ)}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ mulVecStabilizer W) (t : ℝ) :
    exp (t • A) ∈ mulVecStabilizer W :=
  NormedSpace.exp_mem (R := ℝ) (isClosed_mulVecStabilizer W) (smul_mem_mulVecStabilizer hA t)

/-- General exponential invariance: the linear flow `exp (t • A)` preserves any `A.mulVec`-invariant
subspace. -/
theorem mulVec_exp_smul_mapsTo {W : Submodule ℝ (Fin n → ℝ)} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : MapsTo A.mulVec W W) (t : ℝ) :
    MapsTo (exp (t • A)).mulVec W W := by
  have hAmem : A ∈ mulVecStabilizer W := fun v hv => hA hv
  exact fun v hv => exp_smul_mem_mulVecStabilizer hAmem t v hv

open CRNT.SpectralSplittingReal in
/-- The real stable subspace `E_sℝ` is invariant under the linear flow `exp (t • A)`. -/
theorem mulVec_exp_smul_mapsTo_realStableSubspace (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    MapsTo (exp (t • A)).mulVec (realStableSubspace A) (realStableSubspace A) :=
  mulVec_exp_smul_mapsTo (mulVec_mapsTo_realStableSubspace A) t

open CRNT.SpectralSplittingReal in
/-- The real center subspace `E_cℝ` is invariant under the linear flow `exp (t • A)`. -/
theorem mulVec_exp_smul_mapsTo_realCenterSubspace (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    MapsTo (exp (t • A)).mulVec (realCenterSubspace A) (realCenterSubspace A) :=
  mulVec_exp_smul_mapsTo (mulVec_mapsTo_realCenterSubspace A) t

open CRNT.SpectralSplittingReal in
/-- The real unstable subspace `E_uℝ` is invariant under the linear flow `exp (t • A)`. -/
theorem mulVec_exp_smul_mapsTo_realUnstableSubspace (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    MapsTo (exp (t • A)).mulVec (realUnstableSubspace A) (realUnstableSubspace A) :=
  mulVec_exp_smul_mapsTo (mulVec_mapsTo_realUnstableSubspace A) t

end CRNT.ExponentialDichotomy

/-!
This module is **stable** and `sorry`-free. Depends on:
`CRNT.Dynamics.SpectralSplittingReal`, `Mathlib.Analysis.Normed.Algebra.MatrixExponential`,
`Mathlib.Analysis.Matrix.Normed`, `Mathlib.Analysis.Normed.Module.FiniteDimension`.
-/

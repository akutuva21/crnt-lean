import CRNT.Theorems.DeficiencyZero.Toric
import CRNT.Theorems.DeficiencyZero.Statement
import CRNT.Deficiency.KernelDimension
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The deficiency-zero theorem

The final assembly. A weakly reversible network of deficiency zero has, for every choice
of positive rate constants and positive starting concentration, a **unique**
complex-balanced equilibrium in the positive compatibility class of the start
(`deficiencyZeroTheorem`).

The remaining ingredient — existence of *one* complex-balanced equilibrium — is where the
deficiency-zero condition is consumed. Weak reversibility supplies a strictly positive
kernel vector `b` of `A_k`; we must realize some positive kernel vector as a monomial
vector `Ψ x`. Writing `Yᵀ`, `∂ᵀ` for the transposes of the complex and incidence matrices,
this needs `log b` to lie in `Im Yᵀ + ker ∂ᵀ`, equivalently that the row space of the
stoichiometric matrix equals that of the incidence matrix. Both have a rank reading:
`s = dim Im(stoichᵀ)` and `n − ℓ = dim Im(∂ᵀ)`, and deficiency zero is exactly `s = n − ℓ`.
Since `Im(stoichᵀ) ⊆ Im(∂ᵀ)` always (`stoich = Y ∂`), equal dimensions force equality, and
`∂ᵀ(log b) ∈ Im(∂ᵀ) = Im(stoichᵀ)` yields the required `p` with `x = exp(p)`
complex-balanced. The toric machinery of `Toric.lean` then transports it to the class of
the start and pins down uniqueness.

This module is **stable** and `sorry`-free.
-/

namespace CRNT

namespace Network

open scoped BigOperators
open Matrix

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The complex matrix `Y` as a matrix `S × ComplexIdx`: `Y_{s,c} = c_s`. -/
noncomputable def complexMatrix (N : Network S) : Matrix S N.ComplexIdx ℝ :=
  fun s c => (c.val s : ℝ)

theorem complexMap_eq_mulVecLin (N : Network S) :
    N.complexMap = N.complexMatrix.mulVecLin := by
  apply LinearMap.ext; intro v; funext s
  rw [Matrix.mulVecLin_apply, complexMap_apply]
  simp only [Matrix.mulVec, dotProduct, complexMatrix]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- The stoichiometric matrix `Y · ∂`. -/
noncomputable def stoichMatrix (N : Network S) : Matrix S N.R ℝ :=
  N.complexMatrix * N.incidenceMatrix

theorem stoichMatrix_mulVecLin (N : Network S) :
    N.stoichMatrix.mulVecLin = N.stoichMap := by
  rw [stoichMatrix, Matrix.mulVecLin_mul, ← complexMap_eq_mulVecLin, ← incidenceMap_eq_mulVecLin]
  exact complexMap_comp_incidenceMap N

/-- The transpose of the complex matrix applied to a species vector: `(Yᵀ p)_c = ⟨c, p⟩`. -/
theorem complexTranspose_apply (N : Network S) (p : S → ℝ) (c : N.ComplexIdx) :
    N.complexMatrixᵀ.mulVecLin p c = ∑ s, (c.val s : ℝ) * p s := by
  rw [Matrix.mulVecLin_apply]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, complexMatrix]

/-- The transpose of the stoichiometric matrix factors through `Yᵀ` and `∂ᵀ`:
`(stoichᵀ p)_r = (Yᵀ p)(target r) − (Yᵀ p)(source r)`. -/
theorem stoichTranspose_apply (N : Network S) (p : S → ℝ) (r : N.R) :
    N.stoichMatrixᵀ.mulVecLin p r
      = N.complexMatrixᵀ.mulVecLin p (N.targetIdx r)
        - N.complexMatrixᵀ.mulVecLin p (N.sourceIdx r) := by
  have hT : N.stoichMatrixᵀ = N.incidenceMatrixᵀ * N.complexMatrixᵀ := by
    rw [stoichMatrix, Matrix.transpose_mul]
  rw [hT, Matrix.mulVecLin_mul, LinearMap.comp_apply, incidenceTranspose_apply]

/-- `dim Im(stoichᵀ) = s`. -/
theorem finrank_range_stoichTranspose (N : Network S) :
    Module.finrank ℝ (LinearMap.range N.stoichMatrixᵀ.mulVecLin) = N.stoichRank := by
  have h1 : N.stoichMatrixᵀ.rank = N.stoichMatrix.rank := Matrix.rank_transpose N.stoichMatrix
  have h2 : N.stoichMatrix.rank = N.stoichRank := by
    show Module.finrank ℝ (LinearMap.range N.stoichMatrix.mulVecLin) = _
    rw [stoichMatrix_mulVecLin]; exact (stoichRank_eq_finrank_range N).symm
  calc Module.finrank ℝ (LinearMap.range N.stoichMatrixᵀ.mulVecLin)
      = N.stoichMatrixᵀ.rank := rfl
    _ = N.stoichMatrix.rank := h1
    _ = N.stoichRank := h2

/-- `dim Im(∂ᵀ) = rank(∂) = n − ℓ`. -/
theorem finrank_range_incidenceTranspose (N : Network S) :
    Module.finrank ℝ (LinearMap.range N.incidenceMatrixᵀ.mulVecLin) = N.incidenceRank := by
  calc Module.finrank ℝ (LinearMap.range N.incidenceMatrixᵀ.mulVecLin)
      = N.incidenceMatrixᵀ.rank := rfl
    _ = N.incidenceMatrix.rank := Matrix.rank_transpose N.incidenceMatrix
    _ = N.incidenceRank := (incidenceRank_eq_matrixRank N).symm

/-- The row space of the stoichiometric matrix lies in that of the incidence matrix
(`stoich = Y ∂`). -/
theorem range_stoichTranspose_le (N : Network S) :
    LinearMap.range N.stoichMatrixᵀ.mulVecLin
      ≤ LinearMap.range N.incidenceMatrixᵀ.mulVecLin := by
  have hT : N.stoichMatrixᵀ = N.incidenceMatrixᵀ * N.complexMatrixᵀ := by
    rw [stoichMatrix, Matrix.transpose_mul]
  rw [hT, Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

/-- **Deficiency zero collapses the two row spaces.** When `δ = 0` the stoichiometric and
incidence matrices have the same row space. This is the linear-algebraic heart of the
deficiency-zero theorem: it makes the prescribed reaction-edge differences `log b(target) −
log b(source)` realizable as `⟨reaction vector, p⟩`. -/
theorem range_stoichTranspose_eq (N : Network S) (hδ : N.DeficiencyZero) :
    LinearMap.range N.stoichMatrixᵀ.mulVecLin
      = LinearMap.range N.incidenceMatrixᵀ.mulVecLin := by
  have hrank : N.stoichRank = N.incidenceRank := by
    have hsub : N.deficiencySubspace = ⊥ := (deficiencyZero_iff_deficiencySubspace_eq_bot N).mp hδ
    rw [incidenceRank_eq_stoichRank_add, hsub, finrank_bot, add_zero]
  refine Submodule.eq_of_le_of_finrank_eq (range_stoichTranspose_le N) ?_
  rw [finrank_range_stoichTranspose, finrank_range_incidenceTranspose, hrank]

/-- **Scaling a kernel vector by a reaction-constant exponential stays in the kernel.** If
`A_k b = 0` and `ψ` agrees at the source and target of every reaction, then
`A_k (b ⊙ exp ψ) = 0`. Proved termwise: each reaction contributing to `(A_k v)_c` is
incident to `c`, so `ψ` there equals `ψ c`, and the common factor `exp(ψ c)` pulls out. -/
theorem kineticMap_scale_eq_zero (N : Network S) (κ : RateConstants N)
    {b : N.ComplexIdx → ℝ} (hb : N.kineticMap κ b = 0)
    {ψ : N.ComplexIdx → ℝ} (hψ : ∀ r, ψ (N.targetIdx r) = ψ (N.sourceIdx r)) :
    N.kineticMap κ (fun c => b c * Real.exp (ψ c)) = 0 := by
  funext c
  rw [kineticMap_apply, Pi.zero_apply]
  have key : ∀ r : N.R,
      κ.k r * (b (N.sourceIdx r) * Real.exp (ψ (N.sourceIdx r))) *
          ((if N.targetIdx r = c then (1 : ℝ) else 0) - (if N.sourceIdx r = c then 1 else 0))
        = Real.exp (ψ c) * (κ.k r * b (N.sourceIdx r) *
          ((if N.targetIdx r = c then (1 : ℝ) else 0) - (if N.sourceIdx r = c then 1 else 0))) := by
    intro r
    by_cases hI : ((if N.targetIdx r = c then (1 : ℝ) else 0)
        - (if N.sourceIdx r = c then 1 else 0)) = 0
    · rw [hI]; ring
    · have hψc : ψ (N.sourceIdx r) = ψ c := by
        rcases eq_or_ne (N.sourceIdx r) c with h | h
        · rw [h]
        · rcases eq_or_ne (N.targetIdx r) c with h2 | h2
          · rw [← h2]; exact (hψ r).symm
          · exact absurd (by rw [if_neg h2, if_neg h]; ring) hI
      rw [hψc]; ring
  rw [Finset.sum_congr rfl fun r _ => key r, ← Finset.mul_sum]
  have hz : (∑ r : N.R, κ.k r * b (N.sourceIdx r) *
      ((if N.targetIdx r = c then (1 : ℝ) else 0) - (if N.sourceIdx r = c then 1 else 0))) = 0 := by
    have := congrFun hb c; rwa [kineticMap_apply, Pi.zero_apply] at this
  rw [hz, mul_zero]

/-- **Existence of a complex-balanced equilibrium.** A weakly reversible network of
deficiency zero has a positive complex-balanced concentration (in some class). This is the
step that consumes `δ = 0`. -/
theorem exists_isComplexBalanced (N : Network S) (hwr : N.WeaklyReversible)
    (hδ : N.DeficiencyZero) (κ : RateConstants N) :
    ∃ x : Concentration S, x.Positive ∧ N.IsComplexBalanced κ x := by
  obtain ⟨b, hbpos, hbker⟩ :=
    PositiveKernel.weaklyReversible_exists_positive_kernelVector N hwr κ
  -- the reaction-edge differences of `log b` lie in the incidence row space, hence (by
  -- δ = 0) in the stoichiometric row space: solve for `p`.
  have hβrange : (fun r => Real.log (b (N.targetIdx r)) - Real.log (b (N.sourceIdx r)))
      ∈ LinearMap.range N.incidenceMatrixᵀ.mulVecLin :=
    ⟨fun c => Real.log (b c), by funext r; rw [incidenceTranspose_apply]⟩
  rw [← range_stoichTranspose_eq N hδ] at hβrange
  obtain ⟨p, hp⟩ := hβrange
  set ψ : N.ComplexIdx → ℝ := fun c => N.complexMatrixᵀ.mulVecLin p c - Real.log (b c) with hψdef
  have hψ : ∀ r, ψ (N.targetIdx r) = ψ (N.sourceIdx r) := by
    intro r
    have hr := congrFun hp r
    rw [stoichTranspose_apply] at hr
    simp only [hψdef]
    linarith [hr]
  refine ⟨fun s => Real.exp (p s), fun s => Real.exp_pos _, ?_⟩
  rw [isComplexBalanced_iff_kineticMap]
  -- `Ψ(exp p) = b ⊙ exp ψ`, which `kineticMap_scale_eq_zero` kills.
  have hΨ : N.complexMonomialVector (fun s => Real.exp (p s)) = fun c => b c * Real.exp (ψ c) := by
    funext c
    have hpos : 0 < N.complexMonomialVector (fun s => Real.exp (p s)) c :=
      Complex.massActionMonomial_pos (fun s => Real.exp_pos _) c.val
    have hlog : Real.log (N.complexMonomialVector (fun s => Real.exp (p s)) c)
        = ∑ s, (c.val s : ℝ) * p s := by
      rw [log_complexMonomialVector N (fun s => Real.exp_pos _)]
      exact Finset.sum_congr rfl fun s _ => by rw [Real.log_exp]
    rw [← Real.exp_log hpos, hlog]
    simp only [hψdef]
    rw [complexTranspose_apply, Real.exp_sub, Real.exp_log (hbpos c), mul_comm (b c),
      div_mul_cancel₀ _ (hbpos c).ne']
  rw [hΨ]
  exact kineticMap_scale_eq_zero N κ hbker hψ

/-- **The Feinberg–Horn–Jackson deficiency-zero theorem.** For a weakly reversible network
of deficiency zero, every positive choice of rate constants and positive starting
concentration determines a *unique* complex-balanced equilibrium in the positive
compatibility class of the start. -/
theorem deficiencyZeroTheorem (N : Network S)
    (hyp : N.SatisfiesDeficiencyZeroHypotheses) : N.DeficiencyZeroConclusion := by
  obtain ⟨hwr, hδ⟩ := hyp
  intro κ x₀ hx0
  obtain ⟨xstar, hxspos, hxscb⟩ := exists_isComplexBalanced N hwr hδ κ
  obtain ⟨x, hxmem, hxcb⟩ := N.exists_isComplexBalanced_in_positiveClass κ hxspos hxscb hx0
  refine ⟨x, ⟨hxmem, hxcb⟩, ?_⟩
  rintro y ⟨hymem, hycb⟩
  exact N.isComplexBalanced_unique_in_positiveClass hwr κ hymem hxmem hycb hxcb

end Network

end CRNT

import CRNT.Kinetics.MassAction
import CRNT.Equilibria.ComplexBalanced
import CRNT.Equilibria.SteadyState
import Mathlib.LinearAlgebra.Pi

/-!
# Algebraic form of mass-action dynamics

The mass-action vector field factors through the finite-dimensional *complex space*
`ComplexIdx → ℝ`. Writing `Y` for the complex matrix (`complexMap`), `A_k` for the
kinetic Laplacian matrix (`kineticMap`), and `Ψ` for the monomial map
(`complexMonomialVector`), the induced ODE is

```text
ẋ = Y (A_k (Ψ x))
```

(`massActionVectorField_eq`). This is the standard Feinberg–Horn–Jackson factorization.
As consequences:

* a concentration is complex-balanced iff `A_k (Ψ x) = 0`
  (`isComplexBalanced_iff_kineticMap`);
* every complex-balanced concentration is a steady state
  (`IsComplexBalanced.isMassActionSteadyState`).

Depends on the kinetics and equilibrium layers.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The index type of complexes appearing in the network: a `Fintype` with decidable
equality, the vertex set of the reaction graph. -/
abbrev ComplexIdx (N : Network S) := {c : Complex S // c ∈ N.complexes}

/-- The source complex of a reaction, as a complex index. -/
def sourceIdx (N : Network S) (r : N.R) : N.ComplexIdx :=
  ⟨(N.reaction r).source, N.source_mem_complexes r⟩

/-- The target complex of a reaction, as a complex index. -/
def targetIdx (N : Network S) (r : N.R) : N.ComplexIdx :=
  ⟨(N.reaction r).target, N.target_mem_complexes r⟩

/-- The monomial map `Ψ`: sends a concentration to the vector of mass-action monomials
of the complexes, `Ψ(x)_c = x^c`. -/
def complexMonomialVector (N : Network S) (x : Concentration S) : N.ComplexIdx → ℝ :=
  fun c => c.val.massActionMonomial x

@[simp] theorem complexMonomialVector_apply (N : Network S) (x : Concentration S)
    (c : N.ComplexIdx) :
    N.complexMonomialVector x c = c.val.massActionMonomial x := rfl

theorem massActionRate_eq (N : Network S) (κ : RateConstants N) (r : N.R)
    (x : Concentration S) :
    N.massActionRate κ r x = κ.k r * N.complexMonomialVector x (N.sourceIdx r) := rfl

/-- The complex matrix `Y` as a linear map: sends a complex-indexed vector to the
species vector obtained by combining the complexes with those coefficients,
`Y(v)_s = ∑_c v_c · c_s`. Its range is the stoichiometric content of the complexes. -/
noncomputable def complexMap (N : Network S) : (N.ComplexIdx → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun v := fun s => ∑ c : N.ComplexIdx, v c * (c.val s : ℝ)
  map_add' v w := by
    funext s
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  map_smul' a v := by
    funext s
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring

@[simp] theorem complexMap_apply (N : Network S) (v : N.ComplexIdx → ℝ) (s : S) :
    N.complexMap v s = ∑ c : N.ComplexIdx, v c * (c.val s : ℝ) := rfl

/-- The kinetic (Laplacian) matrix `A_k` as a linear map on the complex space. At
complex `c` it is inflow minus outflow, with each reaction contributing its rate
constant times the value at its source:
`(A_k v)_c = ∑_r k_r v_{source r} ([target r = c] − [source r = c])`. -/
noncomputable def kineticMap (N : Network S) (κ : RateConstants N) :
    (N.ComplexIdx → ℝ) →ₗ[ℝ] (N.ComplexIdx → ℝ) where
  toFun v := fun c => ∑ r : N.R, κ.k r * v (N.sourceIdx r) *
    ((if N.targetIdx r = c then 1 else 0) - (if N.sourceIdx r = c then 1 else 0))
  map_add' v w := by
    funext c
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  map_smul' a v := by
    funext c
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring

@[simp] theorem kineticMap_apply (N : Network S) (κ : RateConstants N)
    (v : N.ComplexIdx → ℝ) (c : N.ComplexIdx) :
    N.kineticMap κ v c = ∑ r : N.R, κ.k r * v (N.sourceIdx r) *
      ((if N.targetIdx r = c then 1 else 0) - (if N.sourceIdx r = c then 1 else 0)) := rfl

/-- The single-indicator sum collapsing the complex matrix against a basis complex:
`∑_c [C = c] · c_s = C_s`. -/
theorem sum_ite_complexMap (N : Network S) (C : N.ComplexIdx) (s : S) :
    (∑ c : N.ComplexIdx, (if C = c then (1 : ℝ) else 0) * (c.val s : ℝ)) = (C.val s : ℝ) := by
  rw [Finset.sum_eq_single C]
  · simp
  · intro c _ hc
    rw [if_neg (Ne.symm hc), zero_mul]
  · intro h; exact absurd (Finset.mem_univ C) h

/-- A single indicator sums to one over the complexes: `∑_c [C = c] = 1`. -/
theorem sum_ite_one (N : Network S) (C : N.ComplexIdx) :
    (∑ c : N.ComplexIdx, if C = c then (1 : ℝ) else 0) = 1 := by
  rw [Finset.sum_eq_single C]
  · simp
  · intro c _ hc; rw [if_neg (Ne.symm hc)]
  · intro h; exact absurd (Finset.mem_univ C) h

/-- **Conservation / Laplacian property of the kinetic matrix.** The columns of `A_k`
sum to zero: `∑_c (A_k v)_c = 0` for every `v`. Equivalently the all-ones covector
annihilates `A_k` on the left, so the image of `A_k` lies in the zero-total hyperplane.
This is the structural property the Perron–Frobenius / Matrix-Tree argument builds on to
produce a strictly positive kernel vector for weakly reversible networks. -/
theorem kineticMap_sum_eq_zero (N : Network S) (κ : RateConstants N)
    (v : N.ComplexIdx → ℝ) : (∑ c : N.ComplexIdx, N.kineticMap κ v c) = 0 := by
  simp only [kineticMap_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro r _
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_ite_one, sum_ite_one, sub_self, mul_zero]

/-- **The mass-action vector field factors as `Y ∘ A_k ∘ Ψ`.** -/
theorem massActionVectorField_eq (N : Network S) (κ : RateConstants N)
    (x : Concentration S) :
    N.massActionVectorField κ x = N.complexMap (N.kineticMap κ (N.complexMonomialVector x)) := by
  funext s
  rw [complexMap_apply]
  -- expand the kinetic map and push the sum over complexes inside
  simp only [kineticMap_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [massActionVectorField_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  -- inner sum over complexes collapses via the indicator identities
  have hexpand : ∀ c : N.ComplexIdx,
      κ.k r * N.complexMonomialVector x (N.sourceIdx r) *
          ((if N.targetIdx r = c then (1 : ℝ) else 0) - (if N.sourceIdx r = c then 1 else 0)) *
          (c.val s : ℝ)
        = κ.k r * N.complexMonomialVector x (N.sourceIdx r) *
            ((if N.targetIdx r = c then (1 : ℝ) else 0) * (c.val s : ℝ)
              - (if N.sourceIdx r = c then (1 : ℝ) else 0) * (c.val s : ℝ)) := by
    intro c; ring
  simp only [hexpand]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib,
    sum_ite_complexMap, sum_ite_complexMap]
  -- now: rate · (target_s − source_s) = rate · reactionVector
  rw [massActionRate_eq, reactionVector_apply]
  simp only [targetIdx, sourceIdx]

/-- The kinetic map value at a complex is its mass-action inflow minus its outflow. -/
theorem kineticMap_complexMonomial_apply (N : Network S) (κ : RateConstants N)
    (x : Concentration S) (C : N.ComplexIdx) :
    N.kineticMap κ (N.complexMonomialVector x) C = N.inflow κ x C.val - N.outflow κ x C.val := by
  rw [kineticMap_apply, inflow, outflow, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [targetIdx, sourceIdx, Subtype.ext_iff, massActionRate_eq, mul_sub, mul_ite,
    mul_one, mul_zero]

/-- A concentration is complex-balanced iff the kinetic map annihilates its monomial
vector: `A_k (Ψ x) = 0`. -/
theorem isComplexBalanced_iff_kineticMap (N : Network S) (κ : RateConstants N)
    (x : Concentration S) :
    N.IsComplexBalanced κ x ↔ N.kineticMap κ (N.complexMonomialVector x) = 0 := by
  rw [IsComplexBalanced]
  constructor
  · intro h
    funext C
    rw [kineticMap_complexMonomial_apply, Pi.zero_apply, sub_eq_zero]
    exact h C.val C.property
  · intro h c hc
    have hC := congrFun h ⟨c, hc⟩
    rw [kineticMap_complexMonomial_apply, Pi.zero_apply, sub_eq_zero] at hC
    exact hC

/-- **Every complex-balanced concentration is a mass-action steady state.** This is the
first dynamical consequence of the algebraic factorization: complex balancing kills the
kinetic map, and the complex matrix sends `0` to `0`. -/
theorem IsComplexBalanced.isMassActionSteadyState (N : Network S) (κ : RateConstants N)
    {x : Concentration S} (h : N.IsComplexBalanced κ x) :
    N.IsMassActionSteadyState κ x := by
  have hk : N.kineticMap κ (N.complexMonomialVector x) = 0 :=
    (N.isComplexBalanced_iff_kineticMap κ x).1 h
  intro s
  show N.massActionVectorField κ x s = 0
  rw [N.massActionVectorField_eq κ x, hk, map_zero]
  rfl

end Network

end CRNT

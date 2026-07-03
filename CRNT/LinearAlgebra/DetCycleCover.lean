import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Cycle.Factors

/-!
# Determinant as a sum over cycle-cover shapes

The Leibniz expansion of a determinant runs over all permutations of the index set.
Each permutation factors uniquely into disjoint cycles, and its sign is determined by
its cycle type; grouping the Leibniz sum by cycle type therefore organises the
determinant into blocks indexed by *cycle-cover shapes* — multisets of cycle lengths.
This is the algebraic substrate of the determinant-expansion-via-cycle-covers picture
used in the species–reaction-graph analysis of chemical reaction networks
(Craciun and Feinberg, "Multiple equilibria in complex chemical reaction networks:
extensions to entrapped species models", and the matrix-tree / cycle-cover reading of
the Jacobian determinant in injectivity criteria).

Everything here is stated over a **given** abstract matrix over a commutative ring; no
factorisation of any Jacobian and no product structure is assumed.

* `det_eq_sum_over_perm_cycleType` — the Leibniz formula with the sign rewritten via
  the cycle type of each permutation
  (`Equiv.Perm.sign_of_cycleType'`).
* `det_eq_sum_cycleCover_terms` — the same sum grouped by cycle type, so each block is
  one cycle-cover shape, indexed by the multiset of cycle lengths occurring among the
  permutations of the index set.
* `cycle_term_sign` — the sign of a single cycle in closed form
  (`Equiv.Perm.IsCycle.sign`).
* `cycleCover_factor_prod` — a permutation's diagonal product term factors as the
  product over its disjoint cycles, the cycle-factor decomposition
  (`Equiv.Perm.cycleFactorsFinset_noncommProd`) underlying the cover term.

Depends on:
`Mathlib.LinearAlgebra.Matrix.Determinant.Basic`,
`Mathlib.GroupTheory.Perm.Cycle.Type`,
`Mathlib.GroupTheory.Perm.Cycle.Factors`.
-/

namespace CRNT

open Equiv Equiv.Perm Finset

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type*} [CommRing R]

/-- **Leibniz expansion with the sign read off the cycle type.** Each permutation's
sign equals the product `(σ.cycleType.map fun k => -(-1)^k).prod` over its cycle
lengths, so the determinant is a sum over permutations whose coefficient is this
cycle-type product. -/
theorem det_eq_sum_over_perm_cycleType (M : Matrix n n R) :
    M.det = ∑ σ : Perm n,
      ((σ.cycleType.map fun k => -(-1 : ℤˣ) ^ k).prod : ℤˣ) • ∏ i, M (σ i) i := by
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl ?_
  intro σ _
  rw [Equiv.Perm.sign_of_cycleType' σ]

/-- The cycle-type sign coefficient of a permutation, as a unit `ℤˣ`: the product
`(σ.cycleType.map fun k => -(-1)^k).prod`, which equals `Equiv.Perm.sign σ`. Two
permutations sharing a cycle type contribute the same coefficient, so it depends only
on the cycle-cover shape. -/
def coverCoeff (σ : Perm n) : ℤˣ :=
  (σ.cycleType.map fun k => -(-1 : ℤˣ) ^ k).prod

theorem coverCoeff_eq_sign (σ : Perm n) : coverCoeff σ = Equiv.Perm.sign σ :=
  (Equiv.Perm.sign_of_cycleType' σ).symm

theorem coverCoeff_eq_of_cycleType {σ τ : Perm n} (h : σ.cycleType = τ.cycleType) :
    coverCoeff σ = coverCoeff τ := by
  unfold coverCoeff
  rw [h]

/-- **The determinant grouped by cycle-cover shape.** The Leibniz sum is partitioned by
cycle type: summing first over the distinct cycle types appearing among the
permutations of `n`, then over the permutations of each type. Each inner block is one
cycle-cover shape — a multiset of cycle lengths — whose common sign coefficient
`coverCoeff` factors out. -/
theorem det_eq_sum_cycleCover_terms (M : Matrix n n R) :
    M.det = ∑ c ∈ (Finset.univ.image fun σ : Perm n => σ.cycleType),
      ∑ σ ∈ Finset.univ.filter fun σ : Perm n => σ.cycleType = c,
        (coverCoeff σ : ℤˣ) • ∏ i, M (σ i) i := by
  rw [det_eq_sum_over_perm_cycleType M]
  rw [← Finset.sum_fiberwise_of_maps_to
        (g := fun σ : Perm n => σ.cycleType)
        (t := Finset.univ.image fun σ : Perm n => σ.cycleType)
        (fun σ _ => Finset.mem_image_of_mem _ (Finset.mem_univ σ))]
  rfl

/-- **Sign of a single cycle, in closed form.** A cycle of support size `k` has sign
`-(-1)^k`. This is the single-block case of the cycle-type product, and is the per-cycle
factor that a cycle-cover term decomposes into. -/
theorem cycle_term_sign {σ : Perm n} (hσ : σ.IsCycle) :
    (Equiv.Perm.sign σ : ℤˣ) = -(-1 : ℤˣ) ^ #σ.support :=
  hσ.sign

/-- **The diagonal product of a permutation factors over its disjoint cycles.** A
permutation equals the (commuting) product of its cycle factors, so the Leibniz
diagonal product `∏ i, M (σ i) i` is the diagonal product of that reassembled
permutation. This is the cycle-cover decomposition: a cover term is built from the
independent cycles of `σ`. -/
theorem cycleCover_factor_prod (M : Matrix n n R) (σ : Perm n) :
    (∏ i, M (σ i) i)
      = ∏ i, M ((σ.cycleFactorsFinset.noncommProd id
          (Equiv.Perm.cycleFactorsFinset_mem_commute σ)) i) i := by
  rw [Equiv.Perm.cycleFactorsFinset_noncommProd σ]

end CRNT

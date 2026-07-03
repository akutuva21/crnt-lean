import CRNT.Deficiency.KernelDimension
import CRNT.Equilibria.SteadyState
import CRNT.Equilibria.ComplexBalanced

/-!
# Steady states and the deficiency subspace

The kinetic Laplacian factors through the incidence map: `A_k v = ∂ w` with
`w_r = κ_r · v(source r)` (`kineticMap_eq_incidenceMap`), so the image of `A_k` lies in the
cut space `Im ∂`. A mass-action steady state `x` additionally has
`Y (A_k (Ψ x)) = ẋ = 0`, i.e. `A_k (Ψ x) ∈ ker Y`. Together,

```text
A_k (Ψ x) ∈ ker Y ⊓ Im ∂ = deficiencySubspace
```

(`kineticMap_complexMonomial_mem_deficiencySubspace`). This is the linear-algebraic core
shared by the deficiency-zero and deficiency-one steady-state theory: when `δ = 0` the
deficiency subspace is `⊥`, forcing `A_k (Ψ x) = 0` — every steady state is complex-balanced
(`isComplexBalanced_of_steadyState_of_deficiencyZero`); when `δ = 1` it is pinned to a line.

Depends on: `CRNT.Deficiency.KernelDimension`,
`CRNT.Equilibria.SteadyState`, `CRNT.Equilibria.ComplexBalanced`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The kinetic map factors through the incidence map.** `A_k v = ∂ w` where the reaction
weight is `w_r = κ_r · v(source r)`. -/
theorem kineticMap_eq_incidenceMap (N : Network S) (κ : RateConstants N)
    (v : N.ComplexIdx → ℝ) :
    N.kineticMap κ v = N.incidenceMap (fun r => κ.k r * v (N.sourceIdx r)) := by
  funext c
  simp only [kineticMap_apply, incidenceMap_apply, mul_assoc]

/-- The image of the kinetic map lies in the cut space `Im ∂`. -/
theorem kineticMap_mem_range_incidenceMap (N : Network S) (κ : RateConstants N)
    (v : N.ComplexIdx → ℝ) :
    N.kineticMap κ v ∈ LinearMap.range N.incidenceMap :=
  ⟨_, (N.kineticMap_eq_incidenceMap κ v).symm⟩

/-- At a mass-action steady state the kinetic image lies in `ker Y`: the field
`Y (A_k (Ψ x))` vanishes. -/
theorem kineticMap_complexMonomial_mem_ker_of_steadyState (N : Network S) (κ : RateConstants N)
    {x : Concentration S} (hx : N.IsMassActionSteadyState κ x) :
    N.kineticMap κ (N.complexMonomialVector x) ∈ LinearMap.ker N.complexMap := by
  rw [LinearMap.mem_ker, ← N.massActionVectorField_eq κ x]
  funext s
  rw [Pi.zero_apply]
  exact hx s

/-- **A steady state's kinetic image lies in the deficiency subspace** `ker Y ⊓ Im ∂`. -/
theorem kineticMap_complexMonomial_mem_deficiencySubspace (N : Network S)
    (κ : RateConstants N) {x : Concentration S} (hx : N.IsMassActionSteadyState κ x) :
    N.kineticMap κ (N.complexMonomialVector x) ∈ N.deficiencySubspace :=
  Submodule.mem_inf.mpr
    ⟨N.kineticMap_complexMonomial_mem_ker_of_steadyState κ hx,
     N.kineticMap_mem_range_incidenceMap κ _⟩

/-- **In a deficiency-zero network every mass-action steady state is complex-balanced.** The
deficiency subspace is `⊥`, so the steady state's kinetic image vanishes. -/
theorem isComplexBalanced_of_steadyState_of_deficiencyZero (N : Network S)
    (hδ : N.DeficiencyZero) (κ : RateConstants N) {x : Concentration S}
    (hx : N.IsMassActionSteadyState κ x) : N.IsComplexBalanced κ x := by
  rw [isComplexBalanced_iff_kineticMap]
  have hmem := N.kineticMap_complexMonomial_mem_deficiencySubspace κ hx
  rw [(deficiencyZero_iff_deficiencySubspace_eq_bot N).mp hδ, Submodule.mem_bot] at hmem
  exact hmem

end Network

end CRNT

import CRNT.Deficiency.SteadyStateKernel
import CRNT.Deficiency.DeficiencyOne

/-!
# Deficiency one pins the kinetic image to a line

When the network deficiency is one, the deficiency subspace `ker Y ⊓ Im ∂` is
one-dimensional, hence spanned by a single nonzero vector `g`
(`exists_spanning_deficiencySubspace_of_deficiencyOne`). Since every mass-action steady
state `x` has `A_k (Ψ x)` in the deficiency subspace
(`kineticMap_complexMonomial_mem_deficiencySubspace`), its kinetic image is a scalar multiple
of `g` (`exists_kineticImage_smul_of_deficiencyOne`):

```text
A_k (Ψ x) = c_x · g.
```

Two steady states therefore have kinetic images on a common line through the origin — the
geometric hook for the deficiency-one uniqueness argument.

Depends on: `CRNT.Deficiency.SteadyStateKernel`,
`CRNT.Deficiency.DeficiencyOne`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **A deficiency-one network's deficiency subspace is a line.** There is a nonzero `g` in
`ker Y ⊓ Im ∂` such that every element of the subspace is a scalar multiple of `g`. -/
theorem exists_spanning_deficiencySubspace_of_deficiencyOne (N : Network S)
    (hδ : N.DeficiencyOne) :
    ∃ g ∈ N.deficiencySubspace, g ≠ 0 ∧
      ∀ w ∈ N.deficiencySubspace, ∃ c : ℝ, c • g = w := by
  have hrank : Module.finrank ℝ N.deficiencySubspace = 1 :=
    (deficiencyOne_iff_deficiency_eq_one N).mp hδ
  haveI : Nontrivial N.deficiencySubspace :=
    Module.nontrivial_of_finrank_pos (by rw [hrank]; norm_num)
  obtain ⟨g', hg'0⟩ := exists_ne (0 : N.deficiencySubspace)
  have hg0 : (g' : N.ComplexIdx → ℝ) ≠ 0 := by simpa using hg'0
  refine ⟨g'.val, g'.property, hg0, fun w hw => ?_⟩
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hrank hg'0 ⟨w, hw⟩
  exact ⟨c, congrArg Subtype.val hc⟩

/-- **Deficiency one pins each steady state's kinetic image to a line.** There is a fixed
nonzero `g` such that every mass-action steady state `x` has `A_k (Ψ x) = c · g` for some
scalar `c`. -/
theorem exists_kineticImage_smul_of_deficiencyOne (N : Network S) (κ : RateConstants N)
    (hδ : N.DeficiencyOne) :
    ∃ g : N.ComplexIdx → ℝ, g ≠ 0 ∧ ∀ ⦃x : Concentration S⦄,
      N.IsMassActionSteadyState κ x →
        ∃ c : ℝ, N.kineticMap κ (N.complexMonomialVector x) = c • g := by
  obtain ⟨g, _, hg0, hspan⟩ := N.exists_spanning_deficiencySubspace_of_deficiencyOne hδ
  refine ⟨g, hg0, fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := hspan _ (N.kineticMap_complexMonomial_mem_deficiencySubspace κ hx)
  exact ⟨c, hc.symm⟩

end Network

end CRNT

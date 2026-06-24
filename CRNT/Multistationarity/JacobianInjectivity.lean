import CRNT.Kinetics.MassActionJacobian
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Injectivity from a positive-definite Jacobian

The elementary half of the Gale–Nikaido / Craciun–Feinberg injectivity theory: a `C¹` map on a
convex set whose Jacobian `J(x)` is *positive definite along the set* — `∑ i, vᵢ (J(x) v)ᵢ > 0` for
every `x` in the set and every `v ≠ 0` — is injective there. The proof is the one-dimensional mean
value theorem applied to `t ↦ ⟨v, f(x + t v)⟩` along each segment: its derivative `⟨v, J v⟩` is
strictly positive, so the endpoints differ.

This is the *positive-definite* fragment. The full Gale–Nikaido theorem (a P-matrix Jacobian — all
principal minors positive, not symmetry/definiteness — gives global injectivity) needs topological
degree theory, and the Craciun–Feinberg determinant-sign criterion needs the determinant-via-cycle-
cover expansion; both are absent from Mathlib v4.31 and out of scope here.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Kinetics.MassActionJacobian`, Mathlib
`Analysis.Calculus.MeanValue`.
-/

namespace CRNT

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- **Injectivity from a positive-definite Jacobian along a convex set.** If `f` is differentiable
on a convex set `C` with derivative `f' x` at each `x ∈ C`, and the quadratic form
`v ↦ ∑ i, vᵢ (f' x v)ᵢ` is strictly positive for every `x ∈ C` and `v ≠ 0`, then `f` is injective on
`C`. (The one-dimensional mean value theorem along each segment.) -/
theorem injOn_of_hasFDerivAt_dotProduct_pos
    {f : (ι → ℝ) → (ι → ℝ)} {f' : (ι → ℝ) → ((ι → ℝ) →L[ℝ] (ι → ℝ))}
    {C : Set (ι → ℝ)} (hC : Convex ℝ C)
    (hf : ∀ x ∈ C, HasFDerivAt f (f' x) x)
    (hpos : ∀ x ∈ C, ∀ v : ι → ℝ, v ≠ 0 → 0 < ∑ i, v i * (f' x v) i) :
    Set.InjOn f C := by
  intro x hx y hy hfxy
  by_contra hne
  have hv0 : y - x ≠ 0 := sub_ne_zero.mpr fun h => hne h.symm
  set v : ι → ℝ := y - x with hvdef
  set L : (ι → ℝ) →L[ℝ] ℝ :=
    ∑ i, v i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i with hLdef
  have hLapp : ∀ w : ι → ℝ, L w = ∑ i, v i * w i := by
    intro w
    simp only [hLdef, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  set γ : ℝ → (ι → ℝ) := fun t => x + t • v with hγdef
  have hγmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ C := by
    intro t ht
    simpa [hγdef, hvdef] using hC.add_smul_sub_mem hx hy ht
  have hγderiv : ∀ t : ℝ, HasDerivAt γ v t := by
    intro t
    simpa [hγdef] using ((hasDerivAt_id t).smul_const v).const_add x
  set g : ℝ → ℝ := fun t => L (f (γ t)) with hgdef
  set g' : ℝ → ℝ := fun t => L (f' (γ t) v) with hg'def
  have hgderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (g' t) t := by
    intro t ht
    have h1 : HasDerivAt (fun t => f (γ t)) (f' (γ t) v) t :=
      (hf (γ t) (hγmem t ht)).comp_hasDerivAt t (hγderiv t)
    exact L.hasFDerivAt.comp_hasDerivAt t h1
  have hgcont : ContinuousOn g (Set.Icc 0 1) :=
    fun t ht => (hgderiv t ht).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g g' (by norm_num) hgcont
    (fun t ht => hgderiv t (Set.Ioo_subset_Icc_self ht))
  have hg10 : g 1 - g 0 = 0 := by
    have hγ1 : γ 1 = y := by simp [hγdef, hvdef]
    have hγ0 : γ 0 = x := by simp [hγdef]
    simp only [hgdef, hγ1, hγ0, hfxy, sub_self]
  rw [hg10, zero_div] at hslope
  have hpos_c : 0 < g' c := by
    simp only [hg'def, hLapp]
    exact hpos (γ c) (hγmem c (Set.Ioo_subset_Icc_self hc)) v hv0
  linarith [hslope, hpos_c]

end CRNT

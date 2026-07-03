import CRNT.Kinetics.MassActionJacobian
import CRNT.Multistationarity.Injectivity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Injectivity from a positive-definite Jacobian

The elementary half of the Gale–Nikaido / Craciun–Feinberg injectivity theory: a `C¹` map on a
convex set whose Jacobian `J(x)` is *positive definite along the set* — `∑ i, vᵢ (J(x) v)ᵢ > 0` for
every `x` in the set and every `v ≠ 0` — is injective there. The proof is the one-dimensional mean
value theorem applied to `t ↦ ⟨v, f(x + t v)⟩` along each segment: its derivative `⟨v, J v⟩` is
strictly positive, so the endpoints differ.

This is the *positive-definite* fragment. The full Gale–Nikaido theorem — a P-matrix Jacobian (all
principal minors positive, not symmetry/definiteness) gives global injectivity — is proved
degree-free in `CRNT.Multistationarity.GaleNikaidoUniv` (`injOn_of_pmatrix_fderiv`), through
signature conjugation and order-interval monotonicity rather than topological degree. The
determinant-via-cycle-cover expansion behind the Craciun–Feinberg sign criterion is in
`CRNT.LinearAlgebra.DetCycleCover` (`det_eq_sum_cycleCover_terms`); specializing it to the factored
mass-action Jacobian to close that criterion is not yet done.

Depends on: `CRNT.Kinetics.MassActionJacobian`, Mathlib
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

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The positive stoichiometric compatibility class is convex: an affine coset of the
stoichiometric subspace intersected with the strictly positive orthant. -/
theorem convex_positiveCompatibilityClass (N : Network S) (x₀ : Concentration S) :
    Convex ℝ (N.positiveCompatibilityClass x₀) := by
  intro a ha b hb p q hp hq hpq
  refine ⟨?_, ?_⟩
  · have hsum : p • x₀ + q • x₀ = x₀ := by rw [← add_smul, hpq, one_smul]
    have key : p • (a - x₀) + q • (b - x₀) = p • a + q • b - x₀ := by
      rw [smul_sub, smul_sub, sub_add_sub_comm, hsum]
    show p • a + q • b - x₀ ∈ N.stoichSubspace
    rw [← key]
    exact add_mem (N.stoichSubspace.smul_mem p ha.1) (N.stoichSubspace.smul_mem q hb.1)
  · intro s
    have ha' : 0 < a s := ha.2 s
    have hb' : 0 < b s := hb.2 s
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases hp.eq_or_lt with hp0 | hp0
    · have hq1 : 0 < q := by linarith
      have := mul_pos hq1 hb'
      have := mul_nonneg hp ha'.le
      linarith
    · have := mul_pos hp0 ha'
      have := mul_nonneg hq hb'.le
      linarith

/-- **Mass-action injectivity from a positive-definite Jacobian on a class.** If the mass-action
Jacobian is positive definite (`∑ i, vᵢ (J(x) v)ᵢ > 0` for `v ≠ 0`) at every point of the positive
compatibility class of `x₀`, then mass-action kinetics is injective on that class — so the class
carries at most one steady state. The positive-definite half of the Craciun–Feinberg theory. -/
theorem massActionInjectiveOnClass_of_jacobian_pos (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S)
    (hpos : ∀ x ∈ N.positiveCompatibilityClass x₀, ∀ v : Concentration S, v ≠ 0 →
      0 < ∑ i, v i * ((N.massActionJacobian κ x).mulVec v) i) :
    (N.massActionKinetics κ).InjectiveOnClass x₀ := by
  show Set.InjOn (N.massActionVectorField κ) (N.positiveCompatibilityClass x₀)
  refine injOn_of_hasFDerivAt_dotProduct_pos (N.convex_positiveCompatibilityClass x₀)
    (fun x _ => N.massActionVectorField_hasFDerivAt κ x) (fun x hx v hv => ?_)
  rw [N.massActionJacobianCLM_apply κ x v]
  exact hpos x hx v hv

end Network

end CRNT

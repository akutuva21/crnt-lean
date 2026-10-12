import CRNT.Dynamics.MonotoneComparison
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Monotonicity with respect to an orthant order

A sign vector `σ ∈ {±1}^S` defines the orthant order `x ≤_σ y` iff `σ_i x_i ≤ σ_i y_i` for all `i`
(Smith, *Monotone Dynamical Systems*, 1995, ch. 3; Angeli–Sontag 2008 for reaction networks). The
Kamke condition for this order is `σ_i f_i(a) ≤ σ_i f_i(b)` whenever `a ≤_σ b` and `a_i = b_i`;
for `C¹` fields it is `σ_i σ_j ∂_j f_i ≥ 0` for `i ≠ j`. The change of variables `z = σ ∘ x`
turns it into the cooperative (standard-order) Kamke condition, so the comparison principle
`Monotone.kamke_comparison` transfers.

* `OrthantLE`, `KamkeOnSign`.
* `orthant_comparison`: solutions starting `≤_σ`-ordered stay ordered.
-/

namespace CRNT

namespace Monotone

open scoped NNReal

variable {S : Type} [Fintype S]

/-- The orthant order defined by a sign vector `σ`. -/
def OrthantLE (σ : S → ℝ) (x y : S → ℝ) : Prop := ∀ i, σ i * x i ≤ σ i * y i

/-- The Kamke condition for the orthant order on `K`. -/
def KamkeOnSign (σ : S → ℝ) (f : (S → ℝ) → (S → ℝ)) (K : Set (S → ℝ)) : Prop :=
  ∀ a ∈ K, ∀ b ∈ K, OrthantLE σ a b → ∀ i, a i = b i → σ i * f a i ≤ σ i * f b i

/-- **Orthant comparison principle.** Let `σ ∈ {±1}^S`, let `f` be Lipschitz on `K` with the Kamke
condition for `≤_σ`, and let the reflected set `{σ ∘ x : x ∈ K}` be closed under componentwise
maximum. If `x, y` solve `ẋ = f(x)` on `[0, T]` inside `K` with `x 0 ≤_σ y 0`, then
`x t ≤_σ y t` on `[0, T]`. -/
theorem orthant_comparison {σ : S → ℝ} (hσ : ∀ i, σ i = 1 ∨ σ i = -1)
    {f : (S → ℝ) → (S → ℝ)} {K : Set (S → ℝ)} {L : ℝ≥0}
    (hlip : LipschitzOnWith L f K)
    (hsup : ∀ a ∈ K, ∀ b ∈ K, σ * ((σ * a) ⊔ (σ * b)) ∈ K)
    (hk : KamkeOnSign σ f K) {T : ℝ} {x y : ℝ → (S → ℝ)}
    (hx : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt x (f (x t)) (Set.Icc 0 T) t)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt y (f (y t)) (Set.Icc 0 T) t)
    (hxK : ∀ t ∈ Set.Icc 0 T, x t ∈ K) (hyK : ∀ t ∈ Set.Icc 0 T, y t ∈ K)
    (h0 : OrthantLE σ (x 0) (y 0)) : ∀ t ∈ Set.Icc 0 T, OrthantLE σ (x t) (y t) := by
  have hσσ : σ * σ = 1 := by
    funext i; rcases hσ i with h | h <;> simp [h]
  have hσabs : ∀ i, |σ i| = 1 := fun i => by rcases hσ i with h | h <;> simp [h]
  -- the reflected field and set
  set g : (S → ℝ) → (S → ℝ) := fun z => σ * f (σ * z) with hg
  set K' : Set (S → ℝ) := {z | σ * z ∈ K} with hK'
  have hrefl : ∀ z : S → ℝ, σ * (σ * z) = z := fun z => by rw [← mul_assoc, hσσ, one_mul]
  have hnorm : ∀ v : S → ℝ, ‖σ * v‖ = ‖v‖ := by
    intro v
    simp only [Pi.norm_def, Pi.mul_apply]
    congr 1
    refine Finset.sup_congr rfl fun b _ => ?_
    have h1 : ‖σ b‖₊ = 1 := by
      rw [← NNReal.coe_eq_one, coe_nnnorm, Real.norm_eq_abs, hσabs]
    rw [nnnorm_mul, h1, one_mul]
  have hlip' : LipschitzOnWith L g K' := by
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    have h := hlip.dist_le_mul (σ * a) ha (σ * b) hb
    rw [dist_eq_norm, dist_eq_norm] at h ⊢
    calc ‖g a - g b‖ = ‖σ * (f (σ * a) - f (σ * b))‖ := by simp [hg, mul_sub]
      _ = ‖f (σ * a) - f (σ * b)‖ := hnorm _
      _ ≤ L * ‖σ * a - σ * b‖ := h
      _ = L * ‖a - b‖ := by rw [← mul_sub, hnorm]
  have hsup' : ∀ a ∈ K', ∀ b ∈ K', a ⊔ b ∈ K' := by
    intro a ha b hb
    have := hsup _ ha _ hb
    simpa [hK', hrefl] using this
  have hk' : KamkeOn g K' := by
    intro a ha b hb hab i hi
    have hle : OrthantLE σ (σ * a) (σ * b) := fun j => by
      have := hab j
      simp only [Pi.mul_apply]
      rw [← mul_assoc, ← mul_assoc, show σ j * σ j = 1 from congrFun hσσ j, one_mul, one_mul]
      exact this
    have := hk _ ha _ hb hle i (by simp [Pi.mul_apply, hi])
    simpa [hg, Pi.mul_apply] using this
  -- reflected solutions
  have hderiv : ∀ {u : ℝ → (S → ℝ)}, (∀ t ∈ Set.Icc 0 T, HasDerivWithinAt u (f (u t)) (Set.Icc 0 T) t) →
      ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (fun t => σ * u t) (g (σ * u t)) (Set.Icc 0 T) t := by
    intro u hu t ht
    have h := hu t ht
    rw [hasDerivWithinAt_pi] at h ⊢
    intro i
    have := (h i).const_mul (σ i)
    simpa [hg, hrefl, Pi.mul_apply] using this
  have hmem : ∀ {u : ℝ → (S → ℝ)}, (∀ t ∈ Set.Icc 0 T, u t ∈ K) →
      ∀ t ∈ Set.Icc 0 T, σ * u t ∈ K' := fun hu t ht => by simpa [hK', hrefl] using hu t ht
  have h0' : σ * x 0 ≤ σ * y 0 := fun i => h0 i
  have := kamke_comparison hlip' hsup' hk' (hderiv hx) (hderiv hy) (hmem hxK) (hmem hyK) h0'
  intro t ht i
  exact this t ht i

end Monotone

end CRNT

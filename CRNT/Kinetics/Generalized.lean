import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CRNT.LinearAlgebra.OrthogonalComplement
import CRNT.LinearAlgebra.SignVector
import CRNT.Theorems.DeficiencyZero.Birch
import CRNT.Theorems.DeficiencyZero.BirchExistence

/-!
# Generalized Birch's theorem (Müller–Regensburger generalized mass action)

In generalized mass-action kinetics the dynamics are governed by two subspaces of
`ι → ℝ`: the **stoichiometric subspace** `S` (read off the stoichiometric matrix `Y`)
and the **kinetic-order subspace** `T` (read off the kinetic-order matrix `Ỹ`). A
positive `x` is a *generalized equilibrium* relative to a positive reference `x*` when
`x − c ∈ S` (stoichiometric compatibility) and `log(x/x*) ∈ orthSum T` (the log-ratio is
orthogonal to the **kinetic** subspace). When `T = S` this is exactly the classical
complex-balanced / Birch condition, recovered as `birch_uniqueness_of_self`; a distinct
`T` is the generalization.

* `SameSign u v` — `u` and `v` agree coordinatewise on strict sign.
* `SignCompatible S T` — the Müller–Regensburger sign condition: the only `u ∈ S` and
  `v ∈ T` that are sign-identical is `u = 0`.
* `logRatio_sameSign` — for positive `x, y`, the difference `x − y` and the log-ratio
  `log x − log y` always share signs, because `Real.log` is strictly monotone.
* `sameSign_iff_signVector_eq` / `conformal_of_sameSign` — identify the order-theoretic
  `SameSign` with equality of `signVector`s, and derive conformality.
* `signCompatible_self` — `SignCompatible S (orthSum S)` holds unconditionally (via the
  general sign-vector cancellation `mul_eq_zero_of_conformal_mem_orthSum`), the bridge
  showing the framework subsumes the classical case.
* `gen_birch_uniqueness` — sign compatibility forces uniqueness of generalized
  equilibria; `birch_uniqueness_of_self` is its `T = S` specialization.
* `gen_birch_existence` — the single-subspace specialization of generalized existence,
  reusing `birch_existence`.

Depends on:
`Mathlib.Analysis.SpecialFunctions.Log.Basic`,
`CRNT.LinearAlgebra.OrthogonalComplement`,
`CRNT.LinearAlgebra.SignVector`,
`CRNT.Theorems.DeficiencyZero.Birch`,
`CRNT.Theorems.DeficiencyZero.BirchExistence`.
-/

namespace CRNT

open scoped BigOperators

/-- Two vectors agree coordinatewise on strict sign: at each index they are
simultaneously positive and simultaneously negative. -/
def SameSign {ι : Type*} (u v : ι → ℝ) : Prop :=
  ∀ i, (0 < u i ↔ 0 < v i) ∧ (u i < 0 ↔ v i < 0)

/-- The Müller–Regensburger **sign condition**: the only `u ∈ S` and `v ∈ T` that are
coordinatewise sign-identical is the zero vector. This is the order-theoretic hypothesis
under which generalized equilibria are unique. -/
def SignCompatible {ι : Type*} [Fintype ι] (S T : Submodule ℝ (ι → ℝ)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ T, SameSign u v → u = 0

/-- `SameSign` is reflexive. -/
theorem sameSign_refl {ι : Type*} (u : ι → ℝ) : SameSign u u :=
  fun _ => ⟨Iff.rfl, Iff.rfl⟩

/-- `SameSign` is symmetric. -/
theorem sameSign_symm {ι : Type*} {u v : ι → ℝ} (h : SameSign u v) : SameSign v u :=
  fun i => ⟨(h i).1.symm, (h i).2.symm⟩

/-- `SameSign` is exactly equality of sign vectors: agreeing on every coordinate's strict
sign is the same as having the same `SignType` at every coordinate. This identifies the
order-theoretic `SameSign` with the combinatorial `signVector`. -/
theorem sameSign_iff_signVector_eq {ι : Type*} {u v : ι → ℝ} :
    SameSign u v ↔ signVector u = signVector v := by
  constructor
  · intro h
    funext i
    rcases lt_trichotomy (u i) 0 with hlt | heq | hgt
    · rw [signVector_apply, signVector_apply, sign_neg hlt, sign_neg ((h i).2.mp hlt)]
    · have hv : v i = 0 := by
        rcases lt_trichotomy (v i) 0 with h1 | h2 | h3
        · exact absurd ((h i).2.mpr h1) (by rw [heq]; exact lt_irrefl 0)
        · exact h2
        · exact absurd ((h i).1.mpr h3) (by rw [heq]; exact lt_irrefl 0)
      rw [signVector_apply, signVector_apply, heq, hv]
    · rw [signVector_apply, signVector_apply, sign_pos hgt, sign_pos ((h i).1.mp hgt)]
  · intro h i
    have hi : SignType.sign (u i) = SignType.sign (v i) := congrFun h i
    exact ⟨by rw [← sign_eq_one_iff, ← sign_eq_one_iff, hi],
      by rw [← sign_eq_neg_one_iff, ← sign_eq_neg_one_iff, hi]⟩

/-- Same-sign vectors are conformal: agreeing on strict signs precludes any coordinate where
they point in strictly opposite directions, so every coordinate product is nonnegative. -/
theorem conformal_of_sameSign {ι : Type*} {u v : ι → ℝ} (h : SameSign u v) : Conformal u v := by
  intro i
  rcases lt_trichotomy (u i) 0 with hlt | heq | hgt
  · exact (mul_pos_of_neg_of_neg hlt ((h i).2.mp hlt)).le
  · simp [heq]
  · exact (mul_pos hgt ((h i).1.mp hgt)).le

/-- For strictly positive `x` and `y`, the difference `x − y` and the log-ratio
`i ↦ log (x i) − log (y i)` share signs coordinatewise, since `Real.log` is strictly
monotone on the positive reals. -/
theorem logRatio_sameSign {ι : Type*} {x y : ι → ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    SameSign (x - y) (fun i => Real.log (x i) - Real.log (y i)) := by
  intro i
  simp only [Pi.sub_apply, sub_pos, sub_neg]
  exact ⟨(Real.log_lt_log_iff (hy i) (hx i)).symm,
    (Real.log_lt_log_iff (hx i) (hy i)).symm⟩

/-- **Generalized Birch uniqueness.** Under the Müller–Regensburger sign condition
`SignCompatible S (orthSum T)`, two positive vectors in the same `S`-coset whose
log-ratio is orthogonal to the kinetic subspace `T` are equal. -/
theorem gen_birch_uniqueness {ι : Type*} [Fintype ι] (S T : Submodule ℝ (ι → ℝ))
    (hsc : SignCompatible S (orthSum T)) {x y : ι → ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hxy : x - y ∈ S)
    (horth : (fun i => Real.log (x i) - Real.log (y i)) ∈ orthSum T) :
    x = y := by
  have hu0 : x - y = 0 :=
    hsc (x - y) hxy _ horth (logRatio_sameSign hx hy)
  exact sub_eq_zero.mp hu0

/-- **The sign condition holds unconditionally against the orthogonal complement of `S`
itself.** For `u ∈ S` and `v ∈ orthSum S` that are sign-identical, orthogonality forces
`∑ i, v i * u i = 0` with every term nonnegative, hence each `u i = 0`. This bridges the
generalized framework to the classical case `T = S`. -/
theorem signCompatible_self {ι : Type*} [Fintype ι] (S : Submodule ℝ (ι → ℝ)) :
    SignCompatible S (orthSum S) := by
  intro u hu v hv hsame
  funext i
  -- Conformality of `u` with `v ∈ orthSum S` forces their coordinate products to vanish.
  have hz : u i * v i = 0 :=
    mul_eq_zero_of_conformal_mem_orthSum hu hv (conformal_of_sameSign hsame) i
  rcases mul_eq_zero.mp hz with h | h
  · exact h
  · -- `v i = 0`, and sharing signs then forces `u i = 0`.
    rcases lt_trichotomy (u i) 0 with hlt | heq | hgt
    · exact absurd ((hsame i).2.mp hlt) (by rw [h]; exact lt_irrefl 0)
    · exact heq
    · exact absurd ((hsame i).1.mp hgt) (by rw [h]; exact lt_irrefl 0)

/-- **Single-subspace specialization of generalized Birch existence.** For positive `x*`
and `c`, the kinetic subspace `T` admits a positive `x` with `x − c ∈ T` and log-ratio
`log(x/x*)` orthogonal to `T`. This is the directly-reusable case of `birch_existence`
applied with `T` in the role of the stoichiometric subspace; the genuinely two-subspace
existence (`x − c ∈ S` with `log(x/x*) ∈ orthSum T` for `S ≠ T`) lies beyond this module's
scope. -/
theorem gen_birch_existence {ι : Type*} [Fintype ι] (T : Submodule ℝ (ι → ℝ))
    {xstar c : ι → ℝ} (hxs : ∀ i, 0 < xstar i) (hc : ∀ i, 0 < c i) :
    ∃ x : ι → ℝ, (∀ i, 0 < x i) ∧ x - c ∈ T ∧
      (fun i => Real.log (x i) - Real.log (xstar i)) ∈ orthSum T := by
  obtain ⟨x, hxpos, hxc, hxorth⟩ := birch_existence T hxs hc
  exact ⟨x, hxpos, hxc, mem_orthSum.mpr hxorth⟩

/-- **Classical Birch uniqueness, recovered.** The `T = S` specialization of
`gen_birch_uniqueness`: two positive vectors in the same `S`-coset whose log-ratio is
orthogonal to `S` are equal. The sign condition needed by the generalized statement holds
unconditionally here, by `signCompatible_self`. -/
theorem birch_uniqueness_of_self {ι : Type*} [Fintype ι] (S : Submodule ℝ (ι → ℝ))
    {x y : ι → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hxy : x - y ∈ S)
    (horth : (fun i => Real.log (x i) - Real.log (y i)) ∈ orthSum S) :
    x = y :=
  gen_birch_uniqueness S S (signCompatible_self S) hx hy hxy horth

/-- The generalized framework subsumes classical complex-balanced uniqueness: over any
subspace `S`, the sign condition against `orthSum S` is automatic. -/
example {ι : Type*} [Fintype ι] (S : Submodule ℝ (ι → ℝ)) :
    SignCompatible S (orthSum S) := signCompatible_self S

end CRNT

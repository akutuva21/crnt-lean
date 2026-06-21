import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CRNT.LinearAlgebra.OrthogonalComplement
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
* `signCompatible_self` — `SignCompatible S (orthSum S)` holds unconditionally, the
  bridge showing the framework subsumes the classical case.
* `gen_birch_uniqueness` — sign compatibility forces uniqueness of generalized
  equilibria; `birch_uniqueness_of_self` is its `T = S` specialization.
* `gen_birch_existence` — the single-subspace specialization of generalized existence,
  reusing `birch_existence`.

This module is **stable** and `sorry`-free. Depends on:
`Mathlib.Analysis.SpecialFunctions.Log.Basic`,
`CRNT.LinearAlgebra.OrthogonalComplement`,
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
  -- Every coordinate term `v i * u i` is nonnegative: same sign means the product of two
  -- positives or two negatives, or a zero.
  have hterm_nonneg : ∀ i, 0 ≤ v i * u i := by
    intro i
    rcases lt_trichotomy (u i) 0 with h | h | h
    · exact (mul_pos_of_neg_of_neg ((hsame i).2.mp h) h).le
    · simp [h]
    · exact (mul_pos ((hsame i).1.mp h) h).le
  -- Orthogonality gives the total sum is zero.
  have h0 : ∑ i, v i * u i = 0 := (mem_orthSum.mp hv) u hu
  -- A sum of nonnegative terms is zero only if each term is zero.
  have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hterm_nonneg i).mp h0
  funext i
  have hz := hall i (Finset.mem_univ i)
  rcases lt_trichotomy (u i) 0 with h | h | h
  · exact absurd hz (mul_pos_of_neg_of_neg ((hsame i).2.mp h) h).ne'
  · exact h
  · exact absurd hz (mul_pos ((hsame i).1.mp h) h).ne'

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

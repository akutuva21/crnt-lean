import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Order.SupIndep
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Spectral splitting of a linear flow by sign of `Re λ`

For a linear endomorphism `A` of a finite-dimensional complex vector space `V` we group the
generalized eigenspaces of `A` by the sign of the real part of their eigenvalue, producing three
`A`-invariant subspaces

* `centerSubspace A`   — eigenvalues with `Re λ = 0`;
* `stableSubspace A`   — eigenvalues with `Re λ < 0`;
* `unstableSubspace A` — eigenvalues with `Re λ > 0`.

The eigenvalues split into three disjoint sign classes whose union is all of `ℂ`, so the three
subspaces are pairwise disjoint and together span `V`: they form an internal direct sum
`V = E_s ⊕ E_c ⊕ E_u` (`isInternal_stable_center_unstable`). Coarsening to the two-class partition
`Re λ = 0` versus `Re λ ≠ 0` gives the center / hyperbolic splitting `V = E_c ⊕ E_h`
(`isInternal_center_hyperbolic`).

This is the linear skeleton underlying invariant-manifold theory: the center, stable, and unstable
subspaces of the linearization are the tangent spaces, at the equilibrium, of the local center,
stable, and unstable manifolds of the nonlinear flow (Carr, *Applications of Centre Manifold
Theory*; Kelley, *The stable, center-stable, center, center-unstable, and unstable manifolds*;
Hirsch–Pugh–Shub, *Invariant Manifolds*).

The construction here is purely complex and algebraic: it builds the invariant subspaces and the
direct-sum decomposition. The descent of a conjugation-stable complex subspace to a real subspace
of equal total dimension (via complexification of a real matrix), and the upgrade of `A`-invariance
to `exp (t • A)`-invariance with the associated decay/growth estimates, are downstream developments.
-/

open Module Module.End Submodule Set
open scoped Classical

namespace CRNT.SpectralSplitting

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The generalized-eigenspace subspace of `A` spanned by all eigenvalues `μ` satisfying `P μ`. -/
def specSubspace (A : Module.End ℂ V) (P : ℂ → Prop) : Submodule ℂ V :=
  ⨆ μ ∈ {μ : ℂ | P μ}, A.maxGenEigenspace μ

/-- Center subspace: the generalized eigenspaces with purely imaginary eigenvalue (`Re λ = 0`). -/
def centerSubspace (A : Module.End ℂ V) : Submodule ℂ V :=
  specSubspace A (fun μ => μ.re = 0)

/-- Stable subspace: the generalized eigenspaces with `Re λ < 0`. -/
def stableSubspace (A : Module.End ℂ V) : Submodule ℂ V :=
  specSubspace A (fun μ => μ.re < 0)

/-- Unstable subspace: the generalized eigenspaces with `Re λ > 0`. -/
def unstableSubspace (A : Module.End ℂ V) : Submodule ℂ V :=
  specSubspace A (fun μ => 0 < μ.re)

/-- Hyperbolic subspace: the generalized eigenspaces with `Re λ ≠ 0`. -/
def hyperbolicSubspace (A : Module.End ℂ V) : Submodule ℂ V :=
  specSubspace A (fun μ => μ.re ≠ 0)

/-! ## `A`-invariance -/

section Invariance
omit [FiniteDimensional ℂ V]

/-- Every `specSubspace` is `A`-invariant: `A` maps it into itself. Each generalized eigenspace is
`A`-invariant, hence so is any supremum of them. -/
theorem mapsTo_specSubspace (A : Module.End ℂ V) (P : ℂ → Prop) :
    MapsTo A (specSubspace A P) (specSubspace A P) := by
  rw [Set.mapsTo_iff_subset_preimage, ← Submodule.comap_coe, SetLike.coe_subset_coe,
    ← Submodule.map_le_iff_le_comap, specSubspace, Submodule.map_iSup]
  refine iSup_le fun μ => ?_
  rw [Submodule.map_iSup]
  refine iSup_le fun hμ => ?_
  refine le_trans ?_ (le_iSup₂_of_le
    (f := fun μ (_ : μ ∈ {μ : ℂ | P μ}) => A.maxGenEigenspace μ) μ hμ le_rfl)
  rw [Submodule.map_le_iff_le_comap]
  intro x hx
  exact A.mapsTo_maxGenEigenspace_of_comm (Commute.refl A) μ hx

theorem mapsTo_centerSubspace (A : Module.End ℂ V) :
    MapsTo A (centerSubspace A) (centerSubspace A) := mapsTo_specSubspace A _

theorem mapsTo_stableSubspace (A : Module.End ℂ V) :
    MapsTo A (stableSubspace A) (stableSubspace A) := mapsTo_specSubspace A _

theorem mapsTo_unstableSubspace (A : Module.End ℂ V) :
    MapsTo A (unstableSubspace A) (unstableSubspace A) := mapsTo_specSubspace A _

theorem mapsTo_hyperbolicSubspace (A : Module.End ℂ V) :
    MapsTo A (hyperbolicSubspace A) (hyperbolicSubspace A) := mapsTo_specSubspace A _

end Invariance

/-! ## Spanning and disjointness -/

/-- The eigenvalue support of `A` is contained in the finite spectrum: if a maximal generalized
eigenspace is nonzero then its eigenvalue lies in `spectrum ℂ A`. -/
theorem maxGenEigenspace_ne_bot_mem_spectrum {A : Module.End ℂ V} {μ : ℂ}
    (h : A.maxGenEigenspace μ ≠ ⊥) : μ ∈ spectrum ℂ A := by
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum]
  apply Module.End.hasEigenvalue_of_hasGenEigenvalue (k := Module.finrank ℂ V)
  rw [Module.End.HasGenEigenvalue]
  rwa [Module.End.maxGenEigenspace_eq_genEigenspace_finrank] at h

/-- Restricting the index set of a `specSubspace` to the spectrum changes nothing, since the
maximal generalized eigenspace vanishes off the spectrum. -/
theorem specSubspace_eq_biSup_inter_spectrum (A : Module.End ℂ V) (P : ℂ → Prop) :
    specSubspace A P = ⨆ μ ∈ {μ : ℂ | P μ} ∩ spectrum ℂ A, A.maxGenEigenspace μ := by
  refine le_antisymm ?_ ?_
  · rw [specSubspace]
    refine iSup_le fun μ => iSup_le fun hμ => ?_
    by_cases hb : A.maxGenEigenspace μ = ⊥
    · simp [hb]
    · have hspec : μ ∈ spectrum ℂ A := maxGenEigenspace_ne_bot_mem_spectrum hb
      exact le_iSup₂_of_le (f := fun μ (_ : μ ∈ {μ : ℂ | P μ} ∩ spectrum ℂ A) => A.maxGenEigenspace μ)
        μ ⟨hμ, hspec⟩ le_rfl
  · exact biSup_mono fun μ hμ => hμ.1

/-- The eigenvalues partition into the three sign classes, so the stable, center, and unstable
subspaces together span `V`. -/
theorem stable_sup_center_sup_unstable_eq_top (A : Module.End ℂ V) :
    stableSubspace A ⊔ centerSubspace A ⊔ unstableSubspace A = ⊤ := by
  rw [← top_le_iff, ← Module.End.iSup_maxGenEigenspace_eq_top A]
  refine iSup_le fun μ => ?_
  rcases lt_trichotomy μ.re 0 with h | h | h
  · refine le_sup_of_le_left (le_sup_of_le_left ?_)
    exact le_iSup₂_of_le (f := fun μ (_ : μ ∈ {μ : ℂ | μ.re < 0}) => A.maxGenEigenspace μ) μ h le_rfl
  · refine le_sup_of_le_left (le_sup_of_le_right ?_)
    exact le_iSup₂_of_le (f := fun μ (_ : μ ∈ {μ : ℂ | μ.re = 0}) => A.maxGenEigenspace μ) μ h le_rfl
  · refine le_sup_of_le_right ?_
    exact le_iSup₂_of_le (f := fun μ (_ : μ ∈ {μ : ℂ | 0 < μ.re}) => A.maxGenEigenspace μ) μ h le_rfl

/-- The center and hyperbolic subspaces together span `V`: every eigenvalue has `Re λ = 0` or
`Re λ ≠ 0`. -/
theorem center_sup_hyperbolic_eq_top (A : Module.End ℂ V) :
    centerSubspace A ⊔ hyperbolicSubspace A = ⊤ := by
  rw [← top_le_iff, ← Module.End.iSup_maxGenEigenspace_eq_top A]
  refine iSup_le fun μ => ?_
  by_cases h : μ.re = 0
  · refine le_sup_of_le_left ?_
    exact le_iSup₂_of_le (f := fun μ (_ : μ ∈ {μ : ℂ | μ.re = 0}) => A.maxGenEigenspace μ) μ h le_rfl
  · refine le_sup_of_le_right ?_
    exact le_iSup₂_of_le (f := fun μ (_ : μ ∈ {μ : ℂ | μ.re ≠ 0}) => A.maxGenEigenspace μ) μ h le_rfl

omit [FiniteDimensional ℂ V] in
/-- The join of two `specSubspace`s is the `specSubspace` of the disjunction of their predicates. -/
theorem specSubspace_sup (A : Module.End ℂ V) (P Q : ℂ → Prop) :
    specSubspace A P ⊔ specSubspace A Q = specSubspace A (fun μ => P μ ∨ Q μ) := by
  refine le_antisymm (sup_le ?_ ?_) ?_
  · exact iSup_le fun μ => iSup_le fun hμ =>
      le_iSup₂_of_le (f := fun μ (_ : μ ∈ {μ : ℂ | P μ ∨ Q μ}) => A.maxGenEigenspace μ) μ
        (Or.inl hμ) le_rfl
  · exact iSup_le fun μ => iSup_le fun hμ =>
      le_iSup₂_of_le (f := fun μ (_ : μ ∈ {μ : ℂ | P μ ∨ Q μ}) => A.maxGenEigenspace μ) μ
        (Or.inr hμ) le_rfl
  · refine iSup_le fun μ => iSup_le fun hμ => ?_
    rcases hμ with hP | hQ
    · exact le_sup_of_le_left
        (le_iSup₂_of_le (f := fun μ (_ : μ ∈ {μ : ℂ | P μ}) => A.maxGenEigenspace μ) μ hP le_rfl)
    · exact le_sup_of_le_right
        (le_iSup₂_of_le (f := fun μ (_ : μ ∈ {μ : ℂ | Q μ}) => A.maxGenEigenspace μ) μ hQ le_rfl)

/-- Two `specSubspace`s built from disjoint eigenvalue predicates are disjoint subspaces. -/
theorem disjoint_specSubspace (A : Module.End ℂ V) {P Q : ℂ → Prop}
    (hPQ : ∀ μ, P μ → Q μ → False) :
    Disjoint (specSubspace A P) (specSubspace A Q) := by
  rw [specSubspace_eq_biSup_inter_spectrum A P, specSubspace_eq_biSup_inter_spectrum A Q]
  have hfin : ({μ : ℂ | P μ} ∩ spectrum ℂ A).Finite :=
    (Module.End.finite_spectrum A).subset inter_subset_right
  refine Module.End.independent_maxGenEigenspace A |>.disjoint_biSup_biSup' ?_ hfin
  rw [Set.disjoint_left]
  rintro μ hP hQ
  exact hPQ μ hP.1 hQ.1

theorem disjoint_stable_center (A : Module.End ℂ V) :
    Disjoint (stableSubspace A) (centerSubspace A) :=
  disjoint_specSubspace A (P := fun μ => μ.re < 0) (Q := fun μ => μ.re = 0)
    fun _ h h0 => absurd (h0 ▸ h) (lt_irrefl _)

theorem disjoint_stable_unstable (A : Module.End ℂ V) :
    Disjoint (stableSubspace A) (unstableSubspace A) :=
  disjoint_specSubspace A (P := fun μ => μ.re < 0) (Q := fun μ => 0 < μ.re)
    fun _ h h0 => absurd (h.trans h0) (lt_irrefl _)

theorem disjoint_center_unstable (A : Module.End ℂ V) :
    Disjoint (centerSubspace A) (unstableSubspace A) :=
  disjoint_specSubspace A (P := fun μ => μ.re = 0) (Q := fun μ => 0 < μ.re)
    fun _ h h0 => absurd (h ▸ h0) (lt_irrefl _)

theorem disjoint_center_hyperbolic (A : Module.End ℂ V) :
    Disjoint (centerSubspace A) (hyperbolicSubspace A) :=
  disjoint_specSubspace A (P := fun μ => μ.re = 0) (Q := fun μ => μ.re ≠ 0)
    fun _ h hne => hne h

/-! ## Internal direct sums -/

/-- The three-way sign decomposition `V = E_s ⊕ E_c ⊕ E_u`: the stable, center, and unstable
subspaces of `A` form an internal direct sum. The index `Fin 3` enumerates the blocks as
`0 = stable`, `1 = center`, `2 = unstable`. -/
theorem isInternal_stable_center_unstable (A : Module.End ℂ V) :
    DirectSum.IsInternal
      (fun i : Fin 3 => ![stableSubspace A, centerSubspace A, unstableSubspace A] i) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · rw [iSupIndep_fin_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    refine ⟨?_, ?_, ?_⟩
    · rw [show centerSubspace A = specSubspace A (fun μ => μ.re = 0) from rfl,
        show unstableSubspace A = specSubspace A (fun μ => 0 < μ.re) from rfl, specSubspace_sup]
      exact disjoint_specSubspace A (P := fun μ => μ.re < 0)
        fun _ h h0 => h0.elim (fun he => absurd (he ▸ h) (lt_irrefl _))
          (fun hg => absurd (h.trans hg) (lt_irrefl _))
    · rw [show unstableSubspace A = specSubspace A (fun μ => 0 < μ.re) from rfl,
        show stableSubspace A = specSubspace A (fun μ => μ.re < 0) from rfl, specSubspace_sup]
      exact disjoint_specSubspace A (P := fun μ => μ.re = 0)
        fun _ h h0 => h0.elim (fun hg => absurd (h ▸ hg) (lt_irrefl _))
          (fun hl => absurd (h ▸ hl) (lt_irrefl _))
    · rw [show stableSubspace A = specSubspace A (fun μ => μ.re < 0) from rfl,
        show centerSubspace A = specSubspace A (fun μ => μ.re = 0) from rfl, specSubspace_sup]
      exact disjoint_specSubspace A (P := fun μ => 0 < μ.re)
        fun _ h h0 => h0.elim (fun hl => absurd (h.trans hl) (lt_irrefl _))
          (fun he => absurd (he ▸ h) (lt_irrefl _))
  · rw [iSup_fin_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    exact stable_sup_center_sup_unstable_eq_top A

/-- The center / hyperbolic decomposition `V = E_c ⊕ E_h`: the center and hyperbolic subspaces of
`A` form an internal direct sum. The index `Fin 2` enumerates the blocks as `0 = center`,
`1 = hyperbolic`. -/
theorem isInternal_center_hyperbolic (A : Module.End ℂ V) :
    DirectSum.IsInternal
      (fun i : Fin 2 => ![centerSubspace A, hyperbolicSubspace A] i) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · rw [iSupIndep_pair (i := 0) (j := 1) (by decide) (by decide)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact disjoint_center_hyperbolic A
  · rw [← top_le_iff, ← center_sup_hyperbolic_eq_top A]
    exact sup_le (le_iSup_of_le 0 (by simp)) (le_iSup_of_le 1 (by simp))

end CRNT.SpectralSplitting

/-!
This module is **stable** and `sorry`-free. Depends on:
`Mathlib.LinearAlgebra.Eigenspace.Triangularizable`, `Mathlib.LinearAlgebra.Eigenspace.Minpoly`,
`Mathlib.Order.SupIndep`, `Mathlib.Analysis.Complex.Polynomial.Basic`.
-/

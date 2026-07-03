import CRNT.Dynamics.SpectralSplitting
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Complex.Basic

/-!
# Real descent of the spectral splitting of a real matrix

The center / stable / unstable splitting of `CRNT.Dynamics.SpectralSplitting` lives over `ℂ`,
because the spectral theory it rests on needs an algebraically closed field. For a *real* matrix
`A : Matrix (Fin n) (Fin n) ℝ` the relevant flow lives on `ℝⁿ`, so the complex splitting has to be
pushed back down to a splitting of `Fin n → ℝ`. This module performs that descent.

Complexifying `A` to `A.map (algebraMap ℝ ℂ)` and reading it as `Matrix.toLin'` gives a complex
endomorphism `complexifiedEnd A` of `Fin n → ℂ`, to which the complex splitting applies. The
complexified matrix has real entries, so its eigendata is symmetric under complex conjugation: each
sign predicate on `Re λ` is conjugation-invariant, hence the center / stable / unstable subspaces of
`complexifiedEnd A` are stable under componentwise conjugation (`isConjStable_*`).

A conjugation-stable complex subspace `W ⊆ (Fin n → ℂ)` descends to its real points
`realPoints W ⊆ (Fin n → ℝ)`, the real vectors whose complex embedding lies in `W`. Because `W` is
conjugation-stable, every `z ∈ W` splits into conjugation-fixed real and imaginary parts that again
lie in `W`, so the real points capture all of `W`. This yields the real internal direct sum
`(Fin n → ℝ) = E_sℝ ⊕ E_cℝ ⊕ E_uℝ` (`isInternal_real_stable_center_unstable`), with each summand
invariant under `A.mulVec` (`mulVec_mapsTo_real_*`).

This is the linear backbone of the real canonical form and of invariant-manifold theory over `ℝ`:
the real center, stable, and unstable subspaces are the tangent spaces, at an equilibrium, of the
local center, stable, and unstable manifolds of a real nonlinear flow (Hirsch–Smale–Devaney,
*Differential Equations, Dynamical Systems, and an Introduction to Chaos*; Carr, *Applications of
Centre Manifold Theory*). Upgrading `A`-invariance to `exp (t • A)`-invariance and the associated
exponential dichotomy decay estimates is a downstream development.
-/

open Module Submodule Set
open scoped Classical

namespace CRNT.SpectralSplittingReal

variable {n : ℕ}

/-! ## Complexification of a real matrix -/

/-- The complexification of a real matrix, read as a complex linear endomorphism of `Fin n → ℂ`. -/
noncomputable def complexifiedEnd (A : Matrix (Fin n) (Fin n) ℝ) : Module.End ℂ (Fin n → ℂ) :=
  Matrix.toLin' (A.map (algebraMap ℝ ℂ))

/-- Componentwise embedding of real vectors into complex vectors as an `ℝ`-linear map. -/
def ofRealPi : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℂ) where
  toFun v := fun i => (v i : ℂ)
  map_add' v w := by ext i; simp [Complex.ofReal_add]
  map_smul' c v := by ext i; simp [Complex.ofReal_mul, Complex.real_smul]

@[simp] theorem ofRealPi_apply (v : Fin n → ℝ) (i : Fin n) : ofRealPi v i = (v i : ℂ) := rfl

theorem ofRealPi_injective : Function.Injective (ofRealPi : (Fin n → ℝ) → (Fin n → ℂ)) := by
  intro v w h
  ext i
  have := congrArg (· i) h
  simpa [ofRealPi_apply, Complex.ofReal_inj] using this

/-- Componentwise complex conjugation as an `ℝ`-linear map of `Fin n → ℂ`. -/
def conjPi : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) where
  toFun z := fun i => (starRingEnd ℂ) (z i)
  map_add' z w := by ext i; simp
  map_smul' c z := by ext i; simp [Complex.real_smul, map_mul]

@[simp] theorem conjPi_apply (z : Fin n → ℂ) (i : Fin n) :
    conjPi z i = (starRingEnd ℂ) (z i) := rfl

@[simp] theorem conjPi_ofRealPi (v : Fin n → ℝ) : conjPi (ofRealPi v) = ofRealPi v := by
  ext i; simp [conjPi_apply, ofRealPi_apply, Complex.conj_ofReal]

@[simp] theorem conjPi_conjPi (z : Fin n → ℂ) : conjPi (conjPi z) = z := by
  ext i; simp [conjPi_apply]

/-- The componentwise real part of a complex vector. -/
def rePi (z : Fin n → ℂ) : Fin n → ℝ := fun i => (z i).re

/-- The componentwise imaginary part of a complex vector. -/
def imPi (z : Fin n → ℂ) : Fin n → ℝ := fun i => (z i).im

/-- A conjugation-fixed complex vector is the embedding of its real part. -/
theorem ofRealPi_rePi_of_conjPi_eq {z : Fin n → ℂ} (hz : conjPi z = z) :
    ofRealPi (rePi z) = z := by
  ext i
  have hi : (starRingEnd ℂ) (z i) = z i := congrArg (· i) hz
  have him : (z i).im = 0 := by
    have h := congrArg Complex.im hi
    rw [Complex.conj_im] at h
    linarith
  simp only [ofRealPi_apply, rePi]
  exact (Complex.ext (by simp) (by simp [him])).symm

/-- Twice the real part of a complex vector is itself plus its conjugate, embedded back. -/
theorem ofRealPi_two_smul_rePi (z : Fin n → ℂ) :
    ofRealPi ((2 : ℝ) • rePi z) = z + conjPi z := by
  ext i
  simp only [ofRealPi_apply, Pi.smul_apply, rePi, smul_eq_mul, Complex.ofReal_mul,
    Pi.add_apply, conjPi_apply]
  rw [Complex.add_conj]
  push_cast
  ring

/-! ## Conjugation-stable subspaces and their real points -/

/-- A complex subspace is conjugation-stable when componentwise conjugation maps it into itself. -/
def IsConjStable (W : Submodule ℂ (Fin n → ℂ)) : Prop := ∀ z ∈ W, conjPi z ∈ W

/-- The real points of a complex subspace: real vectors whose complex embedding lies in `W`. -/
noncomputable def realPoints (W : Submodule ℂ (Fin n → ℂ)) : Submodule ℝ (Fin n → ℝ) :=
  (W.restrictScalars ℝ).comap ofRealPi

@[simp] theorem mem_realPoints {W : Submodule ℂ (Fin n → ℂ)} {v : Fin n → ℝ} :
    v ∈ realPoints W ↔ ofRealPi v ∈ W := Iff.rfl

/-- The complex embedding sends the real points of `W` into `W`. -/
theorem ofRealPi_realPoints_le (W : Submodule ℂ (Fin n → ℂ)) :
    Submodule.map ofRealPi (realPoints W) ≤ W.restrictScalars ℝ := by
  rintro _ ⟨v, hv, rfl⟩
  exact hv

/-- For a conjugation-stable subspace, the real part of any member is a real point. -/
theorem rePi_mem_realPoints {W : Submodule ℂ (Fin n → ℂ)} (hW : IsConjStable W)
    {z : Fin n → ℂ} (hz : z ∈ W) : rePi z ∈ realPoints W := by
  rw [mem_realPoints]
  have h2 : ofRealPi ((2 : ℝ) • rePi z) ∈ W := by
    rw [ofRealPi_two_smul_rePi]; exact W.add_mem hz (hW z hz)
  rw [map_smul, algebra_compatible_smul ℂ, Complex.coe_algebraMap] at h2
  have h2c : ((2 : ℝ) : ℂ) ≠ 0 := by norm_num
  have hf := W.smul_mem (((2 : ℝ) : ℂ)⁻¹) h2
  rwa [smul_smul, inv_mul_cancel₀ h2c, one_smul] at hf

/-- For a conjugation-stable subspace, the imaginary part of any member is a real point:
`i · (imaginary part)` lies in `W`, so the real part of `-i · z` is real-pointed. -/
theorem imPi_mem_realPoints {W : Submodule ℂ (Fin n → ℂ)} (hW : IsConjStable W)
    {z : Fin n → ℂ} (hz : z ∈ W) : imPi z ∈ realPoints W := by
  have hiz : (-Complex.I) • z ∈ W := W.smul_mem _ hz
  have := rePi_mem_realPoints hW hiz
  have hre : rePi ((-Complex.I) • z) = imPi z := by
    ext i
    simp only [rePi, imPi, Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.neg_re,
      Complex.neg_im, Complex.I_re, Complex.I_im]
    ring
  rwa [hre] at this

/-! ## Conjugation symmetry of the complexified endomorphism -/

/-- Conjugation commutes with the complexified endomorphism, because the matrix is real:
`conjPi ∘ complexifiedEnd A = complexifiedEnd A ∘ conjPi`. -/
theorem conjPi_complexifiedEnd (A : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℂ) :
    conjPi (complexifiedEnd A z) = complexifiedEnd A (conjPi z) := by
  ext i
  simp only [conjPi_apply, complexifiedEnd, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Matrix.map_apply, map_sum, map_mul, Complex.coe_algebraMap, Complex.conj_ofReal]

/-- One-step intertwining: conjugation turns `complexifiedEnd A - μ • 1` into the operator with the
conjugated eigenvalue. -/
theorem conjPi_sub_smul (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℂ) (z : Fin n → ℂ) :
    conjPi ((complexifiedEnd A - μ • (1 : Module.End ℂ (Fin n → ℂ))) z) =
      (complexifiedEnd A - (starRingEnd ℂ μ) • (1 : Module.End ℂ (Fin n → ℂ))) (conjPi z) := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub]
  rw [conjPi_complexifiedEnd]
  congr 1
  ext i
  simp only [conjPi_apply, Pi.smul_apply, smul_eq_mul, map_mul]

/-- Conjugation commutes with `complexifiedEnd A - μ • 1` up to conjugating the eigenvalue. -/
theorem conjPi_sub_smul_pow (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℂ) (k : ℕ) (z : Fin n → ℂ) :
    conjPi (((complexifiedEnd A - μ • (1 : Module.End ℂ (Fin n → ℂ))) ^ k) z) =
      ((complexifiedEnd A - (starRingEnd ℂ μ) • (1 : Module.End ℂ (Fin n → ℂ))) ^ k) (conjPi z) := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ']
    simp only [Module.End.mul_apply]
    rw [conjPi_sub_smul, ih]

/-- Conjugation maps the maximal generalized eigenspace for `μ` into that for `conj μ`. -/
theorem conjPi_mem_maxGenEigenspace (A : Matrix (Fin n) (Fin n) ℝ) {μ : ℂ} {z : Fin n → ℂ}
    (hz : z ∈ (complexifiedEnd A).maxGenEigenspace μ) :
    conjPi z ∈ (complexifiedEnd A).maxGenEigenspace (starRingEnd ℂ μ) := by
  rw [Module.End.mem_maxGenEigenspace] at hz ⊢
  obtain ⟨k, hk⟩ := hz
  refine ⟨k, ?_⟩
  rw [← conjPi_sub_smul_pow, hk, map_zero]

/-! ## Conjugation-stability of the sign-class subspaces -/

open CRNT.SpectralSplitting in
/-- A `specSubspace` of `complexifiedEnd A` is conjugation-stable whenever its eigenvalue predicate
is invariant under conjugation. -/
theorem isConjStable_specSubspace (A : Matrix (Fin n) (Fin n) ℝ) {P : ℂ → Prop}
    (hP : ∀ μ : ℂ, P μ → P (starRingEnd ℂ μ)) :
    IsConjStable (specSubspace (complexifiedEnd A) P) := by
  intro z hz
  rw [specSubspace] at hz ⊢
  induction hz using Submodule.iSup_induction' with
  | mem μ y hy =>
    induction hy using Submodule.iSup_induction' with
    | mem hμ y hy =>
      have hconj : conjPi y ∈
          (complexifiedEnd A).maxGenEigenspace (starRingEnd ℂ μ) :=
        conjPi_mem_maxGenEigenspace A hy
      exact Submodule.mem_iSup_of_mem (starRingEnd ℂ μ)
        (Submodule.mem_iSup_of_mem (hP μ hμ) hconj)
    | zero => simp
    | add y₁ y₂ _ _ ih₁ ih₂ => simpa [map_add] using add_mem ih₁ ih₂
  | zero => simp
  | add y₁ y₂ _ _ ih₁ ih₂ => simpa [map_add] using add_mem ih₁ ih₂

/-! ## Real points: monotonicity, disjointness, and spanning -/

theorem realPoints_mono {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (h : W₁ ≤ W₂) :
    realPoints W₁ ≤ realPoints W₂ := fun _ hv => h hv

@[simp] theorem rePi_ofRealPi (v : Fin n → ℝ) : rePi (ofRealPi v) = v := by
  ext i; simp [rePi, ofRealPi_apply]

theorem rePi_add (z w : Fin n → ℂ) : rePi (z + w) = rePi z + rePi w := by
  ext i; simp [rePi]

/-- A complex disjointness descends to disjointness of the real points. -/
theorem disjoint_realPoints {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (h : Disjoint W₁ W₂) :
    Disjoint (realPoints W₁) (realPoints W₂) := by
  rw [Submodule.disjoint_def] at h ⊢
  intro v hv₁ hv₂
  have hz : ofRealPi v = 0 := h (ofRealPi v) hv₁ hv₂
  have h0 : ofRealPi v = ofRealPi (0 : Fin n → ℝ) := by rw [hz, map_zero]
  exact ofRealPi_injective h0

/-- If three conjugation-stable complex subspaces span `(Fin n → ℂ)`, their real points span
`(Fin n → ℝ)`. The real part of each complex summand of `ofRealPi v` is a real point. -/
theorem realPoints_sup_eq_top {W₀ W₁ W₂ : Submodule ℂ (Fin n → ℂ)}
    (h₀ : IsConjStable W₀) (h₁ : IsConjStable W₁) (h₂ : IsConjStable W₂)
    (hsup : W₀ ⊔ W₁ ⊔ W₂ = ⊤) :
    realPoints W₀ ⊔ realPoints W₁ ⊔ realPoints W₂ = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hmem : ofRealPi v ∈ W₀ ⊔ W₁ ⊔ W₂ := by rw [hsup]; trivial
  rw [Submodule.mem_sup] at hmem
  obtain ⟨sc, hsc, u, hu, hscu⟩ := hmem
  rw [Submodule.mem_sup] at hsc
  obtain ⟨s, hs, c, hc, hsc'⟩ := hsc
  subst hsc'
  have hdecomp : v = rePi s + rePi c + rePi u := by
    have hv : rePi (ofRealPi v) = rePi (s + c + u) := by rw [hscu]
    rw [rePi_ofRealPi] at hv
    rw [hv, rePi_add, rePi_add]
  rw [hdecomp]
  have m₀ : rePi s ∈ realPoints W₀ ⊔ realPoints W₁ ⊔ realPoints W₂ :=
    Submodule.mem_sup_left (Submodule.mem_sup_left (rePi_mem_realPoints h₀ hs))
  have m₁ : rePi c ∈ realPoints W₀ ⊔ realPoints W₁ ⊔ realPoints W₂ :=
    Submodule.mem_sup_left (Submodule.mem_sup_right (rePi_mem_realPoints h₁ hc))
  have m₂ : rePi u ∈ realPoints W₀ ⊔ realPoints W₁ ⊔ realPoints W₂ :=
    Submodule.mem_sup_right (rePi_mem_realPoints h₂ hu)
  exact add_mem (add_mem m₀ m₁) m₂

/-! ## Real center, stable, and unstable subspaces -/

open CRNT.SpectralSplitting in
/-- Real stable subspace of `A`: the real points of the complexified stable subspace. -/
noncomputable def realStableSubspace (A : Matrix (Fin n) (Fin n) ℝ) : Submodule ℝ (Fin n → ℝ) :=
  realPoints (stableSubspace (complexifiedEnd A))

open CRNT.SpectralSplitting in
/-- Real center subspace of `A`: the real points of the complexified center subspace. -/
noncomputable def realCenterSubspace (A : Matrix (Fin n) (Fin n) ℝ) : Submodule ℝ (Fin n → ℝ) :=
  realPoints (centerSubspace (complexifiedEnd A))

open CRNT.SpectralSplitting in
/-- Real unstable subspace of `A`: the real points of the complexified unstable subspace. -/
noncomputable def realUnstableSubspace (A : Matrix (Fin n) (Fin n) ℝ) : Submodule ℝ (Fin n → ℝ) :=
  realPoints (unstableSubspace (complexifiedEnd A))

open CRNT.SpectralSplitting in
theorem isConjStable_stableSubspace (A : Matrix (Fin n) (Fin n) ℝ) :
    IsConjStable (stableSubspace (complexifiedEnd A)) :=
  isConjStable_specSubspace A fun μ hμ => by simpa using hμ

open CRNT.SpectralSplitting in
theorem isConjStable_centerSubspace (A : Matrix (Fin n) (Fin n) ℝ) :
    IsConjStable (centerSubspace (complexifiedEnd A)) :=
  isConjStable_specSubspace A fun μ hμ => by simpa using hμ

open CRNT.SpectralSplitting in
theorem isConjStable_unstableSubspace (A : Matrix (Fin n) (Fin n) ℝ) :
    IsConjStable (unstableSubspace (complexifiedEnd A)) :=
  isConjStable_specSubspace A fun μ hμ => by simpa using hμ

/-! ## The real internal direct sum -/

open CRNT.SpectralSplitting in
/-- The real three-way sign decomposition `(Fin n → ℝ) = E_sℝ ⊕ E_cℝ ⊕ E_uℝ`: the real stable,
center, and unstable subspaces of a real matrix `A` form an internal direct sum. The index `Fin 3`
enumerates the blocks as `0 = stable`, `1 = center`, `2 = unstable`. -/
theorem isInternal_real_stable_center_unstable (A : Matrix (Fin n) (Fin n) ℝ) :
    DirectSum.IsInternal
      (fun i : Fin 3 =>
        ![realStableSubspace A, realCenterSubspace A, realUnstableSubspace A] i) := by
  -- The complex splitting and its independence, read off block by block.
  have hcplx := isInternal_stable_center_unstable (complexifiedEnd A)
  have hind := hcplx.submodule_iSupIndep
  rw [iSupIndep_fin_three] at hind
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at hind
  obtain ⟨d₀, d₁, d₂⟩ := hind
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · rw [iSupIndep_fin_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    refine ⟨?_, ?_, ?_⟩
    · refine (disjoint_realPoints d₀).mono_right ?_
      exact sup_le (realPoints_mono le_sup_left) (realPoints_mono le_sup_right)
    · refine (disjoint_realPoints d₁).mono_right ?_
      exact sup_le (realPoints_mono le_sup_left) (realPoints_mono le_sup_right)
    · refine (disjoint_realPoints d₂).mono_right ?_
      exact sup_le (realPoints_mono le_sup_left) (realPoints_mono le_sup_right)
  · rw [iSup_fin_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    exact realPoints_sup_eq_top (isConjStable_stableSubspace A) (isConjStable_centerSubspace A)
      (isConjStable_unstableSubspace A) (stable_sup_center_sup_unstable_eq_top (complexifiedEnd A))

/-! ## `A`-invariance of the real subspaces -/

/-- The complex embedding intertwines `A.mulVec` with the complexified endomorphism:
`ofRealPi (A *ᵥ v) = complexifiedEnd A (ofRealPi v)`. -/
theorem ofRealPi_mulVec (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    ofRealPi (A.mulVec v) = complexifiedEnd A (ofRealPi v) := by
  ext i
  have h := RingHom.map_mulVec (algebraMap ℝ ℂ) A v i
  simp only [complexifiedEnd, Matrix.toLin'_apply, ofRealPi_apply, Complex.coe_algebraMap,
    Function.comp_def] at h ⊢
  exact h

open CRNT.SpectralSplitting in
/-- The real points of a `complexifiedEnd A`-invariant subspace are `A.mulVec`-invariant. -/
theorem mulVec_mapsTo_realPoints (A : Matrix (Fin n) (Fin n) ℝ) {W : Submodule ℂ (Fin n → ℂ)}
    (hW : MapsTo (complexifiedEnd A) W W) :
    MapsTo A.mulVec (realPoints W) (realPoints W) := by
  intro v hv
  rw [SetLike.mem_coe, mem_realPoints] at hv
  rw [SetLike.mem_coe, mem_realPoints, ofRealPi_mulVec]
  exact hW hv

open CRNT.SpectralSplitting in
theorem mulVec_mapsTo_realStableSubspace (A : Matrix (Fin n) (Fin n) ℝ) :
    MapsTo A.mulVec (realStableSubspace A) (realStableSubspace A) :=
  mulVec_mapsTo_realPoints A (mapsTo_stableSubspace (complexifiedEnd A))

open CRNT.SpectralSplitting in
theorem mulVec_mapsTo_realCenterSubspace (A : Matrix (Fin n) (Fin n) ℝ) :
    MapsTo A.mulVec (realCenterSubspace A) (realCenterSubspace A) :=
  mulVec_mapsTo_realPoints A (mapsTo_centerSubspace (complexifiedEnd A))

open CRNT.SpectralSplitting in
theorem mulVec_mapsTo_realUnstableSubspace (A : Matrix (Fin n) (Fin n) ℝ) :
    MapsTo A.mulVec (realUnstableSubspace A) (realUnstableSubspace A) :=
  mulVec_mapsTo_realPoints A (mapsTo_unstableSubspace (complexifiedEnd A))

end CRNT.SpectralSplittingReal

/-!
Depends on:
`CRNT.Dynamics.SpectralSplitting`, `Mathlib.LinearAlgebra.Matrix.ToLin`,
`Mathlib.Analysis.Complex.Basic`.
-/

import CRNT.Equilibria.JacobianSpectrumEigen

/-!
# The Perron--Frobenius theorem for primitive nonnegative matrices

This module is the spectral counterpart of `CRNT.Equilibria.NilpotentJacobian`: it records the
Perron--Frobenius theory of **nonnegative** matrices in the form that the Horn--Jackson
nilpotent-Jacobian criterion needs, and it states precisely which parts of the classical
theorem are within reach of Mathlib.

## The classical theorem

For a nonnegative matrix `A` (entrywise `≥ 0`) the Perron--Frobenius theorem
(Gantmacher, *The Theory of Matrices*, Chapter VIII; Horn--Jackson, *Generalized Perron--Frobenius
Theorem*, 1974) says:

* **PF1 (the Perron root).**  If `A` is *primitive* — entrywise nonnegative with a strictly
  positive power `A ^ k` — then `A` has a **positive real** eigenvalue `ρ > 0`, the *Perron root*;
  `ρ` is the spectral radius of `A` and it is a *simple* eigenvalue.
* **PF2 (the Perron vector).**  `ρ` has a **strictly positive** eigenvector.
* **PF3 (dominance).**  Every other eigenvalue `μ` of `A` satisfies `|μ| < ρ`.

In the applied form used by Horn--Jackson (and by Craciun, *Chemical reaction network theory*,
Chapter 4) the only input is the weaker statement "a nonnegative matrix with a strictly positive
power is **not nilpotent**": a nilpotent matrix has all its eigenvalues equal to zero, so a
nonnegative matrix with a strictly positive power — whose powers cannot vanish — has a nonzero
eigenvalue.  This is the Perron--Frobenius step of the *nilpotent-Jacobian criterion*: at a
complex-balanced equilibrium of a non-trivial network the mass-action Jacobian is not nilpotent.

## What Mathlib provides, and what it does not

Mathlib provides

* `Matrix.IsPrimitive` — entrywise nonnegative with a strictly positive power — and
  `Matrix.IsIrreducible` — entrywise nonnegative with strongly connected support digraph;
* `Matrix.charpoly` and the bridge `Module.End.hasEigenvalue_iff_isRoot_charpoly`, so that the
  eigenvalues of a matrix are named by `Module.End.HasEigenvalue` and are the roots of its
  characteristic polynomial;
* `Analysis.Matrix.Spectrum`, the spectral theory of **symmetric** (Hermitian) matrices;
* the Banach-algebra `spectralRadius` of `Analysis.Normed.Algebra.Spectrum`, which does apply to a
  matrix read as an element of the Banach algebra `Matrix n n ℂ`.  It is, however, not connected
  in Mathlib to the *matrix* eigenvalue theory (`Module.End.HasEigenvalue`), and the
  Collatz--Wielandt theory of nonnegative matrices is absent.

Mathlib does **not** provide a Perron--Frobenius theorem: there is no Perron root, no
characterisation of the spectral radius of a nonnegative matrix, no Collatz--Wielandt theorem,
and no theorem asserting that a primitive matrix has a positive real eigenvalue.  The classical
proofs of PF1 use either Brouwer's fixed point theorem (on the simplex), the
Collatz--Wielandt minimax characterisation of the spectral radius, or the Gelfand formula; none
of these is available in Mathlib in a usable form.

## What this module adds

The campaign's `CRNT.Equilibria.JacobianSpectrumEigen.lean` proved the *eigenvalue formulation*
of the criterion — a complex matrix is nilpotent if and only if all of its eigenvalues vanish —
and the primitive and irreducible forms of the "not nilpotent" step.  This module adds

* the Perron--Frobenius step for an **arbitrary** primitive matrix
  (`CRNT.Network.not_isNilpotent_of_isPrimitive`), in the eigenvalue form
  (`CRNT.Network.exists_eigenvalue_ne_zero_of_isPrimitive`) and in the characteristic-polynomial
  form (`CRNT.Network.exists_root_ne_zero_charpoly_of_isPrimitive`);
* the **Collatz--Wielandt bounds**, in the only form that Mathlib allows: for a nonnegative matrix
  `A`, a strictly positive vector `v` and a real eigenvalue `μ` admitting a strictly positive
  eigenvector `w`, one has `c ≤ μ ≤ d` whenever `c * v ≤ A *ᵥ v ≤ d * v`
  (`CRNT.Network.collatz_wielandt_bounds`); for a **primitive** matrix the classical statement
  `min_i (A *ᵥ v) i / v i ≤ μ ≤ max_i (A *ᵥ v) i / v i` follows, with a *strictly positive*
  lower bound (`CRNT.Network.collatz_wielandt_bounds_of_isPrimitive`,
  `CRNT.Network.ratioMin_pos_of_isPrimitive`);
* the **positivity of a Perron-type eigenvalue**: a nonzero nonnegative matrix whose real
  eigenvalue `μ` admits a strictly positive eigenvector has `μ > 0`
  (`CRNT.Network.pos_of_nonneg_of_pos_eigenvector`);
* the **classical Horn--Jackson conclusion in the eigenvalue form** for the mass-action Jacobian
  (`CRNT.Network.exists_eigenvalue_ne_zero_massActionJacobian_of_isPrimitive`): at a positive
  complex-balanced equilibrium of a network with at least two complexes and a primitive weighted
  adjacency matrix, the mass-action Jacobian has a **nonzero complex eigenvalue** (and hence is
  not nilpotent);
* a **counterexample** (`CRNT.Examples.PrimitiveMatrix`) showing that the naive form of PF1/PF3
  one sometimes quotes — "a primitive nonnegative matrix has no zero eigenvalue, hence is
  invertible" — is **false**: the `2 × 2` all-ones matrix is primitive and singular, and `0` is one
  of its eigenvalues.  Primitivity excludes nilpotence, not singularity.

## What remains out of reach

* **PF1 in its classical form** (a *positive real* eigenvalue equal to the spectral radius) is
  **not** proved here; only the weaker "a primitive matrix has a *nonzero* eigenvalue" is, together
  with the conditional statement "a Perron-type eigenvalue, i.e. a real eigenvalue admitting a
  strictly positive eigenvector, is positive".
* **PF2** (the *existence* of a strictly positive eigenvector for the Perron root) is **not**
  proved.
* **PF3** (dominance: `|μ| < ρ` for the other eigenvalues) is **not** proved.
* The reason is mathematical, not a matter of convenience: all classical proofs of PF1 for a
  primitive matrix pass through a compactness/fixed-point argument (Brouwer on the simplex, or
  the Collatz--Wielandt minimax characterisation of the spectral radius), and Mathlib has
  neither a Perron root nor a spectral-radius object for nonnegative matrices.  What is proved
  here is exactly the part of the classical theory that does *not* need the spectral radius: the
  non-nilpotence step, the Collatz--Wielandt inequalities, and the positivity of a Perron-type
  eigenvalue.

Depends on: `CRNT.Equilibria.JacobianSpectrumEigen` (and hence
`CRNT.Equilibria.JacobianSpectrum`), Mathlib `LinearAlgebra.Eigenspace.Charpoly`,
`LinearAlgebra.Matrix.Irreducible.Defs`.
-/

namespace CRNT

namespace Network

open scoped BigOperators Matrix

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## The Perron--Frobenius step for a primitive matrix -/

section PrimitiveMatrix

variable {n : Type} [Fintype n] [DecidableEq n]

/-- **The Perron--Frobenius step.**  A primitive nonnegative matrix — entrywise nonnegative with a
strictly positive power — is not nilpotent.

This is the abstract form of the step that
`CRNT.Network.not_isNilpotent_weightedAdjacencyMatrix_of_isPrimitive` specialises to the
weighted adjacency matrix of a network.

The hypothesis `Nonempty n` is needed: for an empty index type the (empty) matrix is vacuously
primitive and nilpotent at the same time. -/
theorem not_isNilpotent_of_isPrimitive [Nonempty n] (A : Matrix n n ℝ)
    (hA : Matrix.IsPrimitive A) : ¬ IsNilpotent A := by
  obtain ⟨k, hk, hpos⟩ := hA.exists_pos_pow
  exact not_isNilpotent_of_nonneg_of_pos_mulVec A hA.nonneg ⟨k, by omega, hpos⟩

/-- **A complex matrix that is not nilpotent has a nonzero eigenvalue.**  This is the elementary
form of the eigenvalue criterion of nilpotence
(`CRNT.Network.isNilpotent_iff_eigenvalues_zero`). -/
theorem exists_eigenvalue_ne_zero_of_not_isNilpotent (M : Matrix n n ℂ) (hM : ¬ IsNilpotent M) :
    ∃ μ : ℂ, μ ≠ 0 ∧ Module.End.HasEigenvalue (Matrix.toLin' M) μ := by
  have hnot : ¬ (∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' M) μ → μ = 0) := by
    intro h
    exact hM ((isNilpotent_iff_eigenvalues_zero M).mpr h)
  by_contra hcon
  refine hnot (fun μ hμ => ?_)
  by_contra hne
  exact hcon ⟨μ, hne, hμ⟩

/-- **The Perron--Frobenius step in the eigenvalue form.**  A primitive nonnegative matrix has a
**nonzero** complex eigenvalue.

The eigenvalues of a real matrix live in the complexification
(`CRNT.Network.complexifyMatrix`): the statement is that `complexifyMatrix A` has an eigenvalue
`μ ≠ 0`.  This is the eigenvalue form of the "not nilpotent" step: a complex matrix is nilpotent
if and only if all of its eigenvalues vanish
(`CRNT.Network.isNilpotent_iff_eigenvalues_zero`), and a primitive matrix is not nilpotent. -/
theorem exists_eigenvalue_ne_zero_of_isPrimitive [Nonempty n] (A : Matrix n n ℝ)
    (hA : Matrix.IsPrimitive A) :
    ∃ μ : ℂ, μ ≠ 0 ∧ Module.End.HasEigenvalue (Matrix.toLin' (complexifyMatrix A)) μ := by
  have hnil : ¬ IsNilpotent A := not_isNilpotent_of_isPrimitive A hA
  have hnilC : ¬ IsNilpotent (complexifyMatrix A) := fun h =>
    hnil ((isNilpotent_complexifyMatrix_iff A).mpr h)
  exact exists_eigenvalue_ne_zero_of_not_isNilpotent (complexifyMatrix A) hnilC

/-- **The Perron--Frobenius step in the characteristic-polynomial form.**  The characteristic
polynomial of the complexification of a primitive nonnegative matrix has a **nonzero** root. -/
theorem exists_root_ne_zero_charpoly_of_isPrimitive [Nonempty n] (A : Matrix n n ℝ)
    (hA : Matrix.IsPrimitive A) :
    ∃ μ : ℂ, μ ≠ 0 ∧ (complexifyMatrix A).charpoly.IsRoot μ := by
  obtain ⟨μ, hne, hμ⟩ := exists_eigenvalue_ne_zero_of_isPrimitive A hA
  refine ⟨μ, hne, ?_⟩
  rw [← Matrix.charpoly_toLin']
  exact (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mp hμ

/-- **The characteristic polynomial of a primitive nonnegative matrix is not `X ^ n`.**  This is
the characteristic-polynomial form of "a primitive matrix is not nilpotent", by the
Cayley--Hamilton theorem. -/
theorem charpoly_ne_X_pow_of_isPrimitive [Nonempty n] (A : Matrix n n ℝ)
    (hA : Matrix.IsPrimitive A) : A.charpoly ≠ Polynomial.X ^ Fintype.card n := by
  intro h
  exact not_isNilpotent_of_isPrimitive A hA (isNilpotent_of_charpoly_eq_X_pow_complex A h)

/-- **The characteristic polynomial of the complexification of a primitive nonnegative matrix is
not `X ^ n`.** -/
theorem charpoly_complex_ne_X_pow_of_isPrimitive [Nonempty n] (A : Matrix n n ℝ)
    (hA : Matrix.IsPrimitive A) :
    (complexifyMatrix A).charpoly ≠ Polynomial.X ^ Fintype.card n := by
  intro h
  exact not_isNilpotent_of_isPrimitive A hA
    ((isNilpotent_complexifyMatrix_iff A).mpr
      (isNilpotent_of_charpoly_eq_X_pow_complex (complexifyMatrix A) h))

/-- **If a complex matrix annihilates a nonzero vector, then `0` is an eigenvalue of it.**  This
is the elementary form of the eigenvalue criterion, used below to exhibit a primitive matrix
with a zero eigenvalue. -/
theorem hasEigenvalue_zero_of_mulVec_eq_zero (A : Matrix n n ℂ) (x : n → ℂ)
    (hx : x ≠ 0) (hxA : A.mulVec x = 0) : Module.End.HasEigenvalue (Matrix.toLin' A) 0 := by
  rw [Module.End.hasEigenvalue_iff, Module.End.eigenspace_zero]
  intro hbot
  have hinj : Function.Injective (Matrix.toLin' A) := LinearMap.ker_eq_bot.mp hbot
  exact hx (hinj (by funext i; simpa [Matrix.toLin'_apply] using congrFun hxA i))

end PrimitiveMatrix

/-! ## The Collatz--Wielandt bounds, and the positivity of a Perron-type eigenvalue -/

section CollatzWielandt

variable {n : Type} [Fintype n] [DecidableEq n]

/-- **A power of a matrix may also be written with the matrix on the left.**  This is the form
that is convenient for reading off the rows of a power. -/
theorem pow_eq_mul_pow (A : Matrix n n ℝ) (k : ℕ) : A ^ (k + 1) = A * A ^ k := by
  induction k with
  | zero => simp [pow_one, pow_zero, mul_one]
  | succ k ih =>
      calc A ^ (k + 1 + 1) = A ^ (k + 1) * A := by rw [pow_succ]
        _ = (A * A ^ k) * A := by rw [ih]
        _ = A * (A ^ k * A) := by rw [mul_assoc]
        _ = A * A ^ (k + 1) := by rw [pow_succ]

omit [DecidableEq n] in
/-- **Monotonicity of `mulVec` for nonnegative matrices.**  A nonnegative matrix preserves the
pointwise order: if `x ≤ y` then `A *ᵥ x ≤ A *ᵥ y`. -/
theorem mulVec_mono {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j) {x y : n → ℝ} (hxy : ∀ i, x i ≤ y i) :
    ∀ i, (A.mulVec x) i ≤ (A.mulVec y) i := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hxy j) (hA i j)

omit [DecidableEq n] in
/-- **A Perron-type eigenvalue of a nonzero nonnegative matrix is positive.**

This is the content of the *positivity* half of PF1, isolated: if a nonnegative matrix `A` has a
real eigenvalue `μ` with a **strictly positive** eigenvector, then `μ > 0`.  (The eigenvector
`w` satisfies `A *ᵥ w = μ • w`.)  What is *not* proved is the existence of such an eigenvector
for a primitive matrix — that is PF2, and it is out of reach of Mathlib. -/
theorem pos_of_nonneg_of_pos_eigenvector [Nonempty n] (A : Matrix n n ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hA0 : ∃ i j, A i j ≠ 0) {μ : ℝ} {w : n → ℝ} (hw : ∀ i, 0 < w i)
    (hwA : A.mulVec w = μ • w) : 0 < μ := by
  have heq : ∀ i, (A.mulVec w) i = μ * w i := by
    intro i
    simpa [Matrix.mulVec, Pi.smul_apply, smul_eq_mul] using congrFun hwA i
  have hnonneg : ∀ i, 0 ≤ (A.mulVec w) i := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (hw j).le
  have hmu : 0 ≤ μ := by
    obtain ⟨i⟩ := (inferInstance : Nonempty n)
    have h1 : 0 ≤ μ * w i := (hnonneg i).trans_eq (heq i)
    exact (mul_nonneg_iff_of_pos_right (hw i)).mp h1
  refine lt_of_le_of_ne hmu (Ne.symm ?_)
  intro hμ
  obtain ⟨i, j, hij⟩ := hA0
  have h1 : 0 = (A.mulVec w) i := by
    rw [heq i, hμ]
    simp
  have hsum : (∑ k : n, A i k * w k) = 0 := by
    have h2 : (A.mulVec w) i = ∑ k, A i k * w k := by
      simp [Matrix.mulVec, dotProduct]
    rw [h2] at h1
    exact h1.symm
  have h2 : A i j = 0 := by
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset n))
      (fun k _ => mul_nonneg (hA i k) (hw k).le)).mp hsum j (Finset.mem_univ j)
    exact (mul_eq_zero.mp h3).resolve_right (hw j).ne'
  exact hij h2

omit [DecidableEq n] in
/-- **The Collatz--Wielandt bounds, in the eigenvalue form.**

Let `A` be a nonnegative matrix, `v` a strictly positive vector and `w` a strictly positive
eigenvector of `A` for the real eigenvalue `μ` (`A *ᵥ w = μ • w`).  If `c * v ≤ A *ᵥ v ≤ d * v`
pointwise, then `c ≤ μ ≤ d`.

The classical Collatz--Wielandt theorem bounds the *spectral radius* of `A` by the extreme
ratios `(A *ᵥ v) i / v i`; since Mathlib has no spectral radius for nonnegative matrices, the
statement above is the form that is available: it bounds every real eigenvalue that admits a
strictly positive eigenvector, and in particular the Perron root, whose existence is PF1/PF2. -/
theorem collatz_wielandt_bounds [Nonempty n] (A : Matrix n n ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {v w : n → ℝ} (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    {μ : ℝ} (hwA : A.mulVec w = μ • w)
    {c d : ℝ} (hcv : ∀ i, c * v i ≤ (A.mulVec v) i) (hdv : ∀ i, (A.mulVec v) i ≤ d * v i) :
    c ≤ μ ∧ μ ≤ d := by
  have hwA' : ∀ i, (A.mulVec w) i = μ * w i := by
    intro i
    simpa [Matrix.mulVec, Pi.smul_apply, smul_eq_mul] using congrFun hwA i
  -- the largest of the ratios `v i / w i`
  set s : Finset ℝ := (Finset.univ : Finset n).image (fun i => v i / w i) with hs
  have hsne : s.Nonempty := by
    rw [hs]
    exact (Finset.univ_nonempty.image _)
  set t : ℝ := s.max' hsne with ht
  have htmem : t ∈ (Finset.univ : Finset n).image (fun i => v i / w i) := by
    rw [← hs]
    exact ht ▸ Finset.max'_mem s hsne
  obtain ⟨imax, himax⟩ := Finset.mem_image.mp htmem
  have himax_eq : v imax / w imax = t := himax.2
  have hle : ∀ i : n, v i / w i ≤ t := by
    intro i
    have hmem : v i / w i ∈ s := by
      rw [hs]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    exact ht ▸ Finset.le_max' s (v i / w i) hmem
  have hvw : ∀ i : n, v i ≤ t * w i := by
    intro i
    have h1 : v i / w i * w i = v i := div_mul_cancel₀ (v i) (hw i).ne'
    have h2 : v i / w i * w i ≤ t * w i := mul_le_mul_of_nonneg_right (hle i) (hw i).le
    rw [h1] at h2
    exact h2
  -- the lower bound `c ≤ μ`
  have hvi : v imax = t * w imax := by
    have h1 : v imax / w imax * w imax = v imax := div_mul_cancel₀ (v imax) (hw imax).ne'
    rw [← h1, himax_eq]
  have hmul : c * (t * w imax) ≤ μ * (t * w imax) := by
    calc c * (t * w imax) = c * v imax := by rw [hvi]
      _ ≤ (A.mulVec v) imax := hcv imax
      _ ≤ (A.mulVec (t • w)) imax := mulVec_mono hA hvw imax
      _ = μ * (t * w imax) := by
        have h2 : (A.mulVec (t • w)) imax = t * (A.mulVec w) imax := by
          simp [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
        rw [h2, hwA']
        ring
  have hpos : 0 < t * w imax := by
    have htpos : 0 < t := by
      rw [← himax_eq]
      exact div_pos (hv imax) (hw imax)
    exact mul_pos htpos (hw imax)
  have hlo : c ≤ μ := le_of_mul_le_mul_right hmul hpos
  -- the smallest of the ratios `v i / w i`
  set t₂ : ℝ := s.min' hsne with ht₂
  have ht₂mem : t₂ ∈ (Finset.univ : Finset n).image (fun i => v i / w i) := by
    rw [← hs]
    exact ht₂ ▸ Finset.min'_mem s hsne
  obtain ⟨imin, himin⟩ := Finset.mem_image.mp ht₂mem
  have himin_eq : v imin / w imin = t₂ := himin.2
  have hge : ∀ i : n, t₂ ≤ v i / w i := by
    intro i
    have hmem : v i / w i ∈ s := by
      rw [hs]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    exact ht₂ ▸ Finset.min'_le s (v i / w i) hmem
  have hvw₂ : ∀ i : n, t₂ * w i ≤ v i := by
    intro i
    have h1 : v i / w i * w i = v i := div_mul_cancel₀ (v i) (hw i).ne'
    have h2 : t₂ * w i ≤ (v i / w i) * w i := by
      have h3 := mul_le_mul_of_nonneg_right (hge i) (hw i).le
      rwa [div_eq_mul_inv] at h3
    rw [h1] at h2
    exact h2
  have hvi₂ : v imin = t₂ * w imin := by
    have h1 : v imin / w imin * w imin = v imin := div_mul_cancel₀ (v imin) (hw imin).ne'
    rw [← h1, himin_eq]
  have hmul₂ : μ * (t₂ * w imin) ≤ d * (t₂ * w imin) := by
    calc μ * (t₂ * w imin) = t₂ * (A.mulVec w) imin := by
          have h2 : (A.mulVec w) imin = μ * w imin := hwA' imin
          rw [h2]
          ring
      _ ≤ (A.mulVec v) imin := by
          have h4 : (A.mulVec (t₂ • w)) imin = t₂ * (A.mulVec w) imin := by
            simp [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
          have h5 : (A.mulVec v) imin ≥ (A.mulVec (t₂ • w)) imin :=
            mulVec_mono hA hvw₂ imin
          rw [h4] at h5
          exact h5
      _ ≤ d * v imin := hdv imin
      _ = d * (t₂ * w imin) := by rw [hvi₂]
  have hpos₂ : 0 < t₂ * w imin := by
    have htpos : 0 < t₂ := by
      rw [← himin_eq]
      exact div_pos (hv imin) (hw imin)
    exact mul_pos htpos (hw imin)
  have hhi : μ ≤ d := le_of_mul_le_mul_right hmul₂ hpos₂
  exact ⟨hlo, hhi⟩

/-- **The extreme ratios `(A *ᵥ v) i / v i` of a primitive matrix.**  The minimum and the maximum
of the ratios of a strictly positive vector `v` under a primitive nonnegative matrix `A`. -/
noncomputable def ratioMin (A : Matrix n n ℝ) (v : n → ℝ) [Nonempty n] : ℝ :=
  Finset.min' (Finset.image (fun i => (A.mulVec v) i / v i) (Finset.univ : Finset n))
    (Finset.univ_nonempty.image (fun i => (A.mulVec v) i / v i))

/-- The maximum of the ratios `(A *ᵥ v) i / v i`. -/
noncomputable def ratioMax (A : Matrix n n ℝ) (v : n → ℝ) [Nonempty n] : ℝ :=
  Finset.max' (Finset.image (fun i => (A.mulVec v) i / v i) (Finset.univ : Finset n))
    (Finset.univ_nonempty.image (fun i => (A.mulVec v) i / v i))

/-- **The Collatz--Wielandt bounds for a primitive matrix, in the classical form.**

Let `A` be a primitive nonnegative matrix, `v` a strictly positive vector, and `μ` a real
eigenvalue of `A` admitting a strictly positive eigenvector `w`.  Then

```text
min_i (A *ᵥ v) i / v i  ≤  μ  ≤  max_i (A *ᵥ v) i / v i ,
```

the lower bound being *strictly positive*; in particular `μ > 0`.

This is the classical Collatz--Wielandt inequality, in the only form that Mathlib allows: the
bounds are usually stated for the spectral radius of `A`, but Mathlib has no spectral radius for
nonnegative matrices, so they are stated here for the real eigenvalues that admit a strictly
positive eigenvector — among which the Perron root lies, once PF1 and PF2 are available. -/
theorem collatz_wielandt_bounds_of_isPrimitive [Nonempty n] (A : Matrix n n ℝ)
    (hA : Matrix.IsPrimitive A) {v w : n → ℝ} (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    {μ : ℝ} (hwA : A.mulVec w = μ • w) :
    ratioMin A v ≤ μ ∧ μ ≤ ratioMax A v := by
  have hwA' : ∀ i, (A.mulVec w) i = μ * w i := by
    intro i
    simpa [Matrix.mulVec, Pi.smul_apply, smul_eq_mul] using congrFun hwA i
  have hmin : ∀ i : n, ratioMin A v ≤ (A.mulVec v) i / v i := by
    intro i
    have hmem : (A.mulVec v) i / v i ∈
        Finset.image (fun j => (A.mulVec v) j / v j) (Finset.univ : Finset n) :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    exact Finset.min'_le _ _ hmem
  have hmax : ∀ i : n, (A.mulVec v) i / v i ≤ ratioMax A v := by
    intro i
    have hmem : (A.mulVec v) i / v i ∈
        Finset.image (fun j => (A.mulVec v) j / v j) (Finset.univ : Finset n) :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    exact Finset.le_max' _ _ hmem
  have hcv : ∀ i, ratioMin A v * v i ≤ (A.mulVec v) i := by
    intro i
    have h1 : ratioMin A v ≤ (A.mulVec v) i / v i := hmin i
    have h2 : ratioMin A v * v i ≤ (A.mulVec v) i / v i * v i :=
      mul_le_mul_of_nonneg_right h1 (hv i).le
    have h3 : (A.mulVec v) i / v i * v i = (A.mulVec v) i :=
      div_mul_cancel₀ (A.mulVec v i) (hv i).ne'
    rwa [h3] at h2
  have hdv : ∀ i, (A.mulVec v) i ≤ ratioMax A v * v i := by
    intro i
    have h1 : (A.mulVec v) i / v i ≤ ratioMax A v := hmax i
    have h2 : (A.mulVec v) i / v i * v i ≤ ratioMax A v * v i :=
      mul_le_mul_of_nonneg_right h1 (hv i).le
    have h3 : (A.mulVec v) i / v i * v i = (A.mulVec v) i :=
      div_mul_cancel₀ (A.mulVec v i) (hv i).ne'
    rwa [h3] at h2
  exact collatz_wielandt_bounds A hA.nonneg hv hw hwA hcv hdv

/-- **The lower Collatz--Wielandt bound of a primitive matrix is strictly positive.**  For a
primitive nonnegative matrix `A` and a strictly positive vector `v`, the image `A *ᵥ v` is
strictly positive (every row of `A` has a positive entry, because `A` has a strictly positive
power), so all the ratios `(A *ᵥ v) i / v i` — and hence their minimum — are strictly positive. -/
theorem ratioMin_pos_of_isPrimitive [Nonempty n] (A : Matrix n n ℝ) (hA : Matrix.IsPrimitive A)
    {v : n → ℝ} (hv : ∀ i, 0 < v i) : 0 < ratioMin A v := by
  have hrow : ∀ i : n, ∃ j, 0 < A i j := by
    intro i
    obtain ⟨k, hk, hpos⟩ := hA.exists_pos_pow
    by_contra h
    push Not at h
    have hzero : ∀ j : n, (A ^ k) i j = 0 := by
      intro j
      have hk1 : k = (k - 1) + 1 := by omega
      rw [hk1, pow_eq_mul_pow, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      have hl : A i l = 0 := le_antisymm (h l) (hA.nonneg i l)
      rw [hl, zero_mul]
    obtain ⟨j⟩ := (inferInstance : Nonempty n)
    exact absurd (hpos i j) (by rw [hzero j]; exact lt_irrefl _)
  have hpos : ∀ i : n, 0 < (A.mulVec v) i := by
    intro i
    obtain ⟨j, hj⟩ := hrow i
    simp only [Matrix.mulVec, dotProduct]
    have h1 : 0 < ∑ k : n, A i k * v k := Finset.sum_pos' (fun k _ => mul_nonneg (hA.nonneg i k)
      (hv k).le) ⟨j, Finset.mem_univ j, mul_pos hj (hv j)⟩
    simpa using h1
  have hrat : ∀ i : n, 0 < (A.mulVec v) i / v i := by
    intro i
    exact div_pos (hpos i) (hv i)
  have htmem : ratioMin A v ∈
      Finset.image (fun j => (A.mulVec v) j / v j) (Finset.univ : Finset n) := by
    unfold ratioMin
    exact Finset.min'_mem _ _
  obtain ⟨i, hi⟩ := Finset.mem_image.mp htmem
  rw [← hi.2]
  exact hrat i

/-- **The Collatz--Wielandt bounds for a primitive matrix, with positivity of the lower
bound.**  For a primitive nonnegative matrix `A`, a strictly positive vector `v` and a real
eigenvalue `μ` of `A` admitting a strictly positive eigenvector `w`,

```text
0 < min_i (A *ᵥ v) i / v i  ≤  μ  ≤  max_i (A *ᵥ v) i / v i ,
```

so in particular `μ > 0`: a Perron-type eigenvalue of a primitive matrix is positive. -/
theorem collatz_wielandt_bounds_pos_of_isPrimitive [Nonempty n] (A : Matrix n n ℝ)
    (hA : Matrix.IsPrimitive A) {v w : n → ℝ} (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    {μ : ℝ} (hwA : A.mulVec w = μ • w) :
    0 < ratioMin A v ∧ ratioMin A v ≤ μ ∧ μ ≤ ratioMax A v := by
  have h1 := collatz_wielandt_bounds_of_isPrimitive A hA hv hw hwA
  have h2 := ratioMin_pos_of_isPrimitive A hA hv
  exact ⟨h2, h1⟩

end CollatzWielandt

/-! ## The Perron--Frobenius step for the weighted adjacency matrix -/

/-- **The Perron--Frobenius step for the weighted adjacency matrix, in the eigenvalue form.**
The monomial-weighted adjacency matrix of a network with a primitive weighted adjacency matrix has
a nonzero complex eigenvalue.  (The positivity of the concentration is not needed: primitivity
already implies that the matrix is entrywise nonnegative.) -/
theorem exists_eigenvalue_ne_zero_weightedAdjacencyMatrix_of_isPrimitive
    (N : Network S) (κ : N.RateConstants) {x : Concentration S}
    (hc : Nonempty N.ComplexIdx)
    (hprim : Matrix.IsPrimitive (N.weightedAdjacencyMatrix κ x)) :
    ∃ μ : ℂ, μ ≠ 0 ∧
      Module.End.HasEigenvalue
        (Matrix.toLin' (complexifyMatrix (N.weightedAdjacencyMatrix κ x))) μ :=
  exists_eigenvalue_ne_zero_of_isPrimitive (N.weightedAdjacencyMatrix κ x) hprim

/-! ## The application: the Horn--Jackson conclusion for the mass-action Jacobian -/

/-- **The classical Horn--Jackson conclusion, in the eigenvalue form.**

At a positive complex-balanced equilibrium of a network with at least two complexes, if the
weighted adjacency matrix is primitive, then the mass-action Jacobian has a **nonzero complex
eigenvalue**; in particular it is not nilpotent.

This is the Perron--Frobenius step of the nilpotent-Jacobian criterion, in the eigenvalue
language: the criterion itself (the entropy-metric argument of
`CRNT.Equilibria.NilpotentJacobian`) forces every reaction of the network to be a
stoichiometrically null one when the Jacobian is nilpotent, and a primitive weighted adjacency
matrix is incompatible with that (`CRNT.Network.not_isNilpotentJacobian_of_isPrimitive`); the
eigenvalue formulation of nilpotence
(`CRNT.Network.isNilpotent_massActionJacobian_iff_eigenvalues_zero`) then turns "not nilpotent"
into "has a nonzero eigenvalue".

The hypothesis `2 ≤ Fintype.card N.ComplexIdx` is necessary: the self-loop network `A → A` of
`CRNT.Examples.NilpotentJacobian` has a primitive weighted adjacency matrix and a nilpotent
mass-action Jacobian. -/
theorem exists_eigenvalue_ne_zero_massActionJacobian_of_isPrimitive
    (N : Network S) (κ : N.RateConstants) {x : Concentration S} (hx : x.Positive)
    (hcb : N.IsComplexBalanced κ x)
    (hprim : Matrix.IsPrimitive (N.weightedAdjacencyMatrix κ x))
    (hcard : 2 ≤ Fintype.card N.ComplexIdx) :
    ∃ μ : ℂ, μ ≠ 0 ∧
      Module.End.HasEigenvalue
        (Matrix.toLin' (complexifyMatrix (N.massActionJacobian κ x))) μ := by
  have hnil : ¬ N.IsNilpotentJacobian κ x :=
    N.not_isNilpotentJacobian_of_isPrimitive κ hx hcb hprim hcard
  have hnil' : ¬ IsNilpotent (N.massActionJacobian κ x) := hnil
  have hnilC : ¬ IsNilpotent (complexifyMatrix (N.massActionJacobian κ x)) := fun h =>
    hnil' ((isNilpotent_complexifyMatrix_iff _).mpr h)
  exact exists_eigenvalue_ne_zero_of_not_isNilpotent
    (complexifyMatrix (N.massActionJacobian κ x)) hnilC

/-- **The classical Horn--Jackson conclusion, in the "not all eigenvalues vanish" form.**  This
is the negation of the eigenvalue criterion of nilpotence, at a positive complex-balanced
equilibrium of a network with at least two complexes and a primitive weighted adjacency
matrix. -/
theorem not_all_eigenvalues_zero_massActionJacobian_of_isPrimitive
    (N : Network S) (κ : N.RateConstants) {x : Concentration S} (hx : x.Positive)
    (hcb : N.IsComplexBalanced κ x)
    (hprim : Matrix.IsPrimitive (N.weightedAdjacencyMatrix κ x))
    (hcard : 2 ≤ Fintype.card N.ComplexIdx) :
    ¬ (∀ μ : ℂ,
      Module.End.HasEigenvalue
          (Matrix.toLin' (complexifyMatrix (N.massActionJacobian κ x))) μ → μ = 0) := by
  obtain ⟨μ, hne, hμ⟩ :=
    exists_eigenvalue_ne_zero_massActionJacobian_of_isPrimitive N κ hx hcb hprim hcard
  intro h
  exact hne (h μ hμ)

end Network

end CRNT

/-! ## A counterexample: a primitive matrix with a zero eigenvalue

The naive form of the Perron--Frobenius theorem one sometimes quotes is "a primitive nonnegative
matrix has no zero eigenvalue, hence is invertible".  That is **false**: primitivity excludes
nilpotence, not singularity.  The `2 × 2` all-ones matrix is primitive, is singular, and has `0` as
an eigenvalue.  The correct statement, proved above, is that a primitive matrix has a *nonzero*
eigenvalue. -/

namespace CRNT.Examples.PrimitiveMatrix

open CRNT
open CRNT.Network

/-- The `2 × 2` matrix with all entries equal to `1`. -/
def A : Matrix (Fin 2) (Fin 2) ℝ := fun _ _ => 1

/-- **`A` is primitive**: it is entrywise nonnegative and its square is strictly positive. -/
theorem isPrimitive : Matrix.IsPrimitive A := by
  have hnonneg : ∀ i j, 0 ≤ A i j := by
    intro i j
    simp [A]
  have hpos : ∀ i j, 0 < (A ^ 2) i j := by
    intro i j
    simp [A, pow_two, Matrix.mul_apply]
  exact ⟨hnonneg, 2, by omega, hpos⟩

/-- **`A` is singular**: its determinant vanishes, because the vector `(1, -1)` is annihilated by
`A`. -/
theorem det_eq_zero : A.det = 0 := by
  rw [← LinearMap.det_toLin', LinearMap.det_eq_zero_iff_ker_ne_bot]
  have hx : (fun i : Fin 2 => if i = 0 then (1 : ℝ) else -1) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp at h0
  have hA : A.mulVec (fun i : Fin 2 => if i = 0 then (1 : ℝ) else -1) = 0 := by
    ext i
    fin_cases i <;> simp [A, Matrix.mulVec]
  intro hbot
  have hinj : Function.Injective (A.toLin') := LinearMap.ker_eq_bot.mp hbot
  exact hx (hinj (by funext i; simpa [Matrix.toLin'_apply] using congrFun hA i))

/-- **`0` is an eigenvalue of `A`**: the vector `(1, -1)` is annihilated by `A`. -/
theorem hasEigenvalue_zero :
    Module.End.HasEigenvalue (Matrix.toLin' (complexifyMatrix A)) 0 := by
  have hx : (fun i : Fin 2 => if i = 0 then (1 : ℂ) else -1) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp at h0
  have hA : (complexifyMatrix A).mulVec (fun i : Fin 2 => if i = 0 then (1 : ℂ) else -1) = 0 := by
    ext i
    fin_cases i <;> simp [complexifyMatrix, Matrix.mulVec, A]
  exact hasEigenvalue_zero_of_mulVec_eq_zero (complexifyMatrix A) _ hx hA

/-- **A primitive matrix need not be invertible.**  The matrix `A` is primitive and singular, so
the statement "a primitive nonnegative matrix is invertible" is false; the correct statement is
"a primitive nonnegative matrix has a nonzero eigenvalue". -/
theorem isPrimitive_and_singular : Matrix.IsPrimitive A ∧ A.det = 0 :=
  ⟨isPrimitive, det_eq_zero⟩

end CRNT.Examples.PrimitiveMatrix

/-! ## Axioms

The principal declarations of this module use only the three standard axioms of Lean's logic
(`propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms CRNT.Network.not_isNilpotent_of_isPrimitive
#print axioms CRNT.Network.exists_eigenvalue_ne_zero_of_not_isNilpotent
#print axioms CRNT.Network.exists_eigenvalue_ne_zero_of_isPrimitive
#print axioms CRNT.Network.exists_root_ne_zero_charpoly_of_isPrimitive
#print axioms CRNT.Network.charpoly_ne_X_pow_of_isPrimitive
#print axioms CRNT.Network.exists_eigenvalue_ne_zero_weightedAdjacencyMatrix_of_isPrimitive
#print axioms CRNT.Network.exists_eigenvalue_ne_zero_massActionJacobian_of_isPrimitive
#print axioms CRNT.Network.pos_of_nonneg_of_pos_eigenvector
#print axioms CRNT.Network.collatz_wielandt_bounds
#print axioms CRNT.Network.collatz_wielandt_bounds_of_isPrimitive
#print axioms CRNT.Network.collatz_wielandt_bounds_pos_of_isPrimitive
#print axioms CRNT.Examples.PrimitiveMatrix.isPrimitive
#print axioms CRNT.Examples.PrimitiveMatrix.det_eq_zero
#print axioms CRNT.Examples.PrimitiveMatrix.hasEigenvalue_zero

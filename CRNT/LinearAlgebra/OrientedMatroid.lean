import Mathlib.Data.Sign.Basic
import CRNT.LinearAlgebra.SignVector

/-!
# Sign-vector composition and the covector realizability fragment

Sketch of a scoped oriented-matroid layer over `signVector`. The realizable sign vectors of
a subspace `S ⊆ (ι → ℝ)` form the **covectors** of an oriented matroid; the structural axiom
established here is **composition**: the covectors are closed under the composition operation
`σ ∘ τ`, which takes `σ`'s sign at each coordinate where `σ` is nonzero and `τ`'s sign
elsewhere. Realizability of the composition is witnessed analytically: for `u, v` in `S`, a
small positive perturbation `u + t • v` realizes the composed sign vector, so it again lies in
the realizable set. This is the order-theoretic structure theory of the sign vectors of a
subspace, isolated from any chemistry and from any degree theory.

* `SignType.compose` / `compose` — the covector composition operation on sign vectors.
* `signVector_add_smul_eqOn` — for finite `ι` a sufficiently small positive perturbation of `u`
  by `v` realizes the composed sign vector coordinatewise.
* `RealizableSignVector S` — the realizable sign vectors of `S`: sign vectors of members of `S`.
* `realizable_compose` — **composition axiom**: the realizable sign vectors are closed under
  `compose`, witnessed by the perturbation `u + t • v ∈ S`.
* `realizable_zero`, `realizable_neg` — the symmetry (zero / negation) covector axioms.

This module is **stable** and `sorry`-free. Depends on: `Mathlib.Data.Sign.Basic`,
`CRNT.LinearAlgebra.SignVector`.
-/

namespace CRNT

open scoped BigOperators

variable {ι : Type*}

/-- **Composition of sign vectors.** `SignType.compose σ τ` is `σ` where `σ` is nonzero and `τ`
elsewhere — the covector composition operation of an oriented matroid. -/
def SignType.compose (σ τ : SignType) : SignType := if σ = 0 then τ else σ

@[simp] theorem SignType.compose_zero_left (τ : SignType) :
    SignType.compose 0 τ = τ := by simp [SignType.compose]

@[simp] theorem SignType.compose_of_ne_zero {σ : SignType} (h : σ ≠ 0) (τ : SignType) :
    SignType.compose σ τ = σ := by simp [SignType.compose, h]

@[simp] theorem SignType.compose_self (σ : SignType) : SignType.compose σ σ = σ := by
  rcases eq_or_ne σ 0 with h | h <;> simp [SignType.compose, h]

/-- Coordinatewise composition of two sign vectors. -/
def compose (σ τ : ι → SignType) : ι → SignType := fun i => SignType.compose (σ i) (τ i)

@[simp] theorem compose_apply (σ τ : ι → SignType) (i : ι) :
    compose σ τ i = SignType.compose (σ i) (τ i) := rfl

/-- The sign of `a + t * b` agrees with the sign of `a` whenever `a ≠ 0` and `0 < t` is small
enough that `t * |b| < |a|`. -/
theorem sign_add_mul_eq_of_lt {a b t : ℝ} (ha : a ≠ 0) (ht : 0 < t)
    (hlt : t * |b| < |a|) : SignType.sign (a + t * b) = SignType.sign a := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have : a + t * b < 0 := by
      have h1 : t * b ≤ t * |b| := by
        have := le_abs_self b; nlinarith [mul_le_mul_of_nonneg_left this ht.le]
      have h2 : t * |b| < -a := by rwa [abs_of_neg hneg] at hlt
      linarith
    rw [sign_neg this, sign_neg hneg]
  · have : 0 < a + t * b := by
      have h1 : -(t * |b|) ≤ t * b := by
        have := neg_abs_le b; nlinarith [mul_le_mul_of_nonneg_left this ht.le]
      have h2 : t * |b| < a := by rwa [abs_of_pos hpos] at hlt
      linarith
    rw [sign_pos this, sign_pos hpos]

/-- The sign of `t * b` (for `0 < t`) is the sign of `b`. -/
theorem sign_mul_pos_left {b t : ℝ} (ht : 0 < t) :
    SignType.sign (t * b) = SignType.sign b := by
  rcases lt_trichotomy b 0 with h | h | h
  · rw [sign_neg (by nlinarith), sign_neg h]
  · simp [h]
  · rw [sign_pos (by positivity), sign_pos h]

/-- The per-coordinate safe perturbation threshold `|u i| / (|v i| + 1)`, strictly positive at
coordinates where `u i ≠ 0`. -/
private noncomputable def thr (u v : ι → ℝ) (i : ι) : ℝ := |u i| / (|v i| + 1)

private theorem thr_pos {u v : ι → ℝ} {i : ι} (h : u i ≠ 0) : 0 < thr u v i := by
  unfold thr
  exact div_pos (abs_pos.mpr h) (by positivity)

/-- Below its threshold, a positive perturbation `t • v` cannot flip the sign at a nonzero
coordinate of `u`. -/
private theorem thr_safe {u v : ι → ℝ} {i : ι} {t : ℝ}
    (hu : u i ≠ 0) (ht : 0 < t) (hlt : t < thr u v i) :
    SignType.sign (u i + t * v i) = SignType.sign (u i) := by
  refine sign_add_mul_eq_of_lt hu ht ?_
  have hden : (0 : ℝ) < |v i| + 1 := by positivity
  have hb : |v i| < |v i| + 1 := by linarith
  have h1 : t * |v i| ≤ t * (|v i| + 1) := by nlinarith [abs_nonneg (v i)]
  have h2 : t * (|v i| + 1) < |u i| := by
    have hlt' : t < |u i| / (|v i| + 1) := by unfold thr at hlt; exact hlt
    have := (lt_div_iff₀ hden).mp hlt'
    linarith
  linarith

variable [Fintype ι]

/-- **A small positive perturbation realizes the composed sign vector.** For finite `ι` there is
`ε > 0` such that for every `0 < t < ε`, the sign vector of `u + t • v` equals the composition
`compose (signVector u) (signVector v)`: at coordinates where `u` is nonzero the small `v`-term
cannot flip the sign, and elsewhere the sign is that of `t • v`, i.e. of `v`. -/
theorem exists_signVector_add_smul (u v : ι → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε →
      signVector (u + t • v) = compose (signVector u) (signVector v) := by
  classical
  -- Candidate thresholds: `1`, plus the safe threshold at every nonzero-`u` coordinate.
  set bad : Finset ι := Finset.univ.filter (fun i => u i ≠ 0) with hbad
  set cand : Finset ℝ := insert (1 : ℝ) (bad.image (thr u v)) with hcand
  have hne : cand.Nonempty := ⟨1, by simp [hcand]⟩
  have hpos_mem : ∀ x ∈ cand, 0 < x := by
    intro x hx
    rw [hcand, Finset.mem_insert] at hx
    rcases hx with h | h
    · rw [h]; exact one_pos
    · rw [Finset.mem_image] at h
      obtain ⟨i, hi, rfl⟩ := h
      rw [hbad, Finset.mem_filter] at hi
      exact thr_pos hi.2
  refine ⟨cand.min' hne, hpos_mem _ (cand.min'_mem hne), ?_⟩
  intro t ht htlt
  funext i
  simp only [signVector_apply, compose_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hu : u i = 0
  · rw [hu, zero_add, sign_zero, SignType.compose_zero_left, sign_mul_pos_left ht]
  · have hib : i ∈ bad := by rw [hbad, Finset.mem_filter]; exact ⟨Finset.mem_univ i, hu⟩
    have hthr_mem : thr u v i ∈ cand := by
      rw [hcand]; exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hib)
    have hlt : t < thr u v i := lt_of_lt_of_le htlt (cand.min'_le _ hthr_mem)
    rw [thr_safe hu ht hlt, SignType.compose_of_ne_zero
      (by rw [Ne, sign_eq_zero_iff]; exact hu)]

/-- The **realizable sign vectors** of a subspace `S`: the sign vectors of its members. These
are the covectors of the oriented matroid realized by `S`. -/
def RealizableSignVector (S : Submodule ℝ (ι → ℝ)) : Set (ι → SignType) :=
  signVector '' (S : Set (ι → ℝ))

omit [Fintype ι] in
theorem mem_realizableSignVector {S : Submodule ℝ (ι → ℝ)} {σ : ι → SignType} :
    σ ∈ RealizableSignVector S ↔ ∃ u ∈ S, signVector u = σ := by
  simp [RealizableSignVector, Set.mem_image]

omit [Fintype ι] in
/-- The **zero covector axiom**: the all-zero sign vector is realizable, witnessed by `0 ∈ S`. -/
theorem realizable_zero (S : Submodule ℝ (ι → ℝ)) :
    (fun _ => 0) ∈ RealizableSignVector S := by
  refine mem_realizableSignVector.mpr ⟨0, S.zero_mem, ?_⟩
  funext i; simp [signVector_apply]

omit [Fintype ι] in
/-- The sign vector of a negation is the negation of the sign vector. -/
theorem signVector_neg (u : ι → ℝ) : signVector (-u) = -signVector u := by
  funext i; simp only [signVector_apply, Pi.neg_apply, Left.sign_neg]

omit [Fintype ι] in
/-- The **negation (symmetry) covector axiom**: if `σ` is realizable so is `-σ`. -/
theorem realizable_neg {S : Submodule ℝ (ι → ℝ)} {σ : ι → SignType}
    (hσ : σ ∈ RealizableSignVector S) : -σ ∈ RealizableSignVector S := by
  obtain ⟨u, hu, rfl⟩ := mem_realizableSignVector.mp hσ
  exact mem_realizableSignVector.mpr ⟨-u, S.neg_mem hu, signVector_neg u⟩

/-- **The covector composition axiom (realizable form).** If `σ` and `τ` are realizable sign
vectors of `S`, then so is their composition `compose σ τ`: choosing realizers `u, v ∈ S`, a
sufficiently small positive perturbation `u + t • v ∈ S` realizes `compose (signVector u)
(signVector v)`. This is the oriented-matroid composition axiom for the covectors of a subspace,
proved analytically with no degree theory. -/
theorem realizable_compose {S : Submodule ℝ (ι → ℝ)} {σ τ : ι → SignType}
    (hσ : σ ∈ RealizableSignVector S) (hτ : τ ∈ RealizableSignVector S) :
    compose σ τ ∈ RealizableSignVector S := by
  obtain ⟨u, hu, rfl⟩ := mem_realizableSignVector.mp hσ
  obtain ⟨v, hv, rfl⟩ := mem_realizableSignVector.mp hτ
  obtain ⟨ε, hε, hspec⟩ := exists_signVector_add_smul u v
  refine mem_realizableSignVector.mpr ⟨u + (ε / 2) • v, S.add_mem hu (S.smul_mem _ hv), ?_⟩
  exact hspec (ε / 2) (by positivity) (by linarith)

end CRNT

import CRNT.Oscillation.FisherFullerScaling
import CRNT.Oscillation.SpectralOpenness
import CRNT.Oscillation.HalfPlanePolynomial
import Mathlib.Topology.Algebra.Polynomial

/-!
# A Hurwitz codimension-one block remains Hurwitz after a small signed border

This file supplies the general bordering lemma needed by the stable-codimension-one class-II
oscillation criterion.  Unlike the Fisher--Fuller induction, the predecessor is allowed to have
repeated or nonreal stable eigenvalues.

For

`A(eps) = M * diagonal (extendCodimOneScaling I dI eps)`

with `I` of codimension one, `A(0)` has characteristic polynomial `X * p`, where `p` is the
characteristic polynomial of the Hurwitz predecessor.  Zero is a simple root because a Hurwitz
matrix is nonsingular.  Choose disjoint regions consisting of a small disk around zero and a closed
left-half-plane neighbourhood of the old roots.  Continuity of roots shows that, for small `eps`,
exactly one root lies in the zero disk and all remaining roots stay uniformly in the left half
plane.  Real coefficients and uniqueness in the zero disk force the exceptional root to be real.
The sign of the constant coefficient (equivalently, the signed determinant) then forces it to be
negative for `eps > 0`.

This is the ordinary root-continuity proof of the codimension-one Hurwitz bordering lemma; no
simplicity assumption is made on the old spectrum.
-/

namespace Polynomial

open Complex Filter Topology

/-- A monic real polynomial whose roots all lie strictly in the left half plane. -/
def HurwitzPolynomial (p : Polynomial ℝ) : Prop :=
  p.Monic ∧ ∀ z : ℂ, z ∈ (p.map (algebraMap ℝ ℂ)).roots → z.re < 0

namespace HurwitzPolynomial

/-- A Hurwitz polynomial has nonzero constant coefficient. -/
theorem coeff_zero_ne {p : Polynomial ℝ} (hp : HurwitzPolynomial p) : p.coeff 0 ≠ 0 := by
  intro h0
  have hz : Polynomial.eval (0 : ℂ) (p.map (algebraMap ℝ ℂ)) = 0 := by
    simpa [Polynomial.eval_zero] using congrArg (algebraMap ℝ ℂ) h0
  have hmem : (0 : ℂ) ∈ (p.map (algebraMap ℝ ℂ)).roots := by
    rw [Polynomial.mem_roots (hp.1.map (algebraMap ℝ ℂ)).ne_zero]
    exact ⟨by simp, hz⟩
  linarith [hp.2 0 hmem]

/-- Uniform distance of the finite root multiset from the imaginary axis. -/
noncomputable def margin {p : Polynomial ℝ} (hp : HurwitzPolynomial p) : ℝ :=
  if h : (p.map (algebraMap ℝ ℂ)).roots = 0 then 1 else
    Finset.min' ((p.map (algebraMap ℝ ℂ)).roots.toFinset.image (fun z : ℂ => -z.re))
      (by simpa [h])

theorem margin_pos {p : Polynomial ℝ} (hp : HurwitzPolynomial p) : 0 < hp.margin := by
  classical
  unfold margin
  split_ifs with h
  · norm_num
  · apply Finset.min'_pos
    intro a ha
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
    have hz' : z ∈ (p.map (algebraMap ℝ ℂ)).roots := by simpa using hz
    linarith [hp.2 z hz']

theorem root_re_le_margin {p : Polynomial ℝ} (hp : HurwitzPolynomial p)
    {z : ℂ} (hz : z ∈ (p.map (algebraMap ℝ ℂ)).roots) :
    z.re ≤ -hp.margin := by
  classical
  unfold margin
  split_ifs with h
  · simp [h] at hz
  · have hm : -z.re ∈
        (p.map (algebraMap ℝ ℂ)).roots.toFinset.image (fun w : ℂ => -w.re) :=
      Finset.mem_image.mpr ⟨z, by simpa using hz, rfl⟩
    have := Finset.min'_le _ _ hm
    linarith

end HurwitzPolynomial

/-- Root-cluster conclusion for a perturbation of `X * p`, with `p` Hurwitz.  It records exactly the
part needed by the bordering theorem: one real root near zero, all other roots uniformly left, and
exhaustion of the full root multiset. -/
structure ZeroBorderRootCluster (p q : Polynomial ℝ) where
  exceptional : ℝ
  exceptional_root : (exceptional : ℂ) ∈ (q.map (algebraMap ℝ ℂ)).roots
  exceptional_small : |exceptional| < (HurwitzPolynomial.margin
    (show HurwitzPolynomial p from by assumption)) / 3
  others_left : ∀ z : ℂ, z ∈ (q.map (algebraMap ℝ ℂ)).roots →
    z ≠ (exceptional : ℂ) → z.re < - (HurwitzPolynomial.margin
      (show HurwitzPolynomial p from by assumption)) / 3
  exceptional_simple :
    ((q.map (algebraMap ℝ ℂ)).roots.count (exceptional : ℂ)) = 1

/-- General root-cluster lemma around a simple zero appended to an arbitrary Hurwitz polynomial.

The proof uses Mathlib's quantitative continuity-of-roots theorem twice: first to obtain a uniform
bound on all perturbed roots from the bounded base root multiset, then to match every perturbed root
to either zero or an old Hurwitz root.  Since zero occurs exactly once in `X*p`, cardinality forces
exactly one perturbed root into the zero disk.  Conjugation preserves that disk and the root
multiset, hence uniqueness makes the exceptional root real. -/
theorem eventually_zeroBorderRootCluster
    {p : Polynomial ℝ} (hp : HurwitzPolynomial p)
    {q : ℝ → Polynomial ℝ}
    (hqmonic : ∀ t, (q t).Monic)
    (hqdeg : ∀ t, (q t).natDegree = p.natDegree + 1)
    (hzero : q 0 = X * p)
    (hcoeff : ∀ k, ContinuousAt (fun t => (q t).coeff k) 0) :
    ∀ᶠ t in 𝓝 0, Nonempty (ZeroBorderRootCluster p (q t)) := by
  classical
  have hmargin : 0 < hp.margin := hp.margin_pos
  let rho : ℝ := hp.margin / 3
  have hrho : 0 < rho := by dsimp [rho]; linarith
  -- The base roots split into the singleton `{0}` and the roots of `p`; these two finite clusters
  -- are separated by at least `3*rho` in real part.
  have hzeroSimple : ((X * p).map (algebraMap ℝ ℂ)).roots.count 0 = 1 := by
    rw [map_mul, roots_mul]
    · simp [hp.coeff_zero_ne]
    · exact (monic_X.map (algebraMap ℝ ℂ)).ne_zero
    · exact (hp.1.map (algebraMap ℝ ℂ)).ne_zero
  -- Continuity of finitely many coefficients gives the coefficient tolerance requested by the
  -- quantitative root theorem.  Applying it in both directions produces a root matching with
  -- multiplicity.  We package the counting argument below so repeated old roots are harmless.
  have hcoeffAll : ∀ ε > 0, ∀ᶠ t in 𝓝 0, ∀ k,
      ‖(q t).coeff k - (X * p).coeff k‖ < ε := by
    intro ε hε
    exact eventually_all_coeff_close_of_finite_degree
      (p := X * p) (q := q)
      (by intro t; simpa [hqdeg t, hp.1.natDegree_X_mul])
      (by simpa [hzero] using hcoeff) hε
  -- `rootCluster_zero_mul_hurwitz` is the finite multiset counting argument: the old roots have
  -- real part at most `-3*rho`, the appended zero is simple, and all roots of a nearby monic
  -- polynomial can be matched with multiplicity to the base roots.  It returns exactly one root
  -- in `ball 0 rho` and puts every other root left of `-rho`.
  obtain ⟨ε, hε, hcluster⟩ :=
    Polynomial.exists_rootCluster_zero_mul_hurwitz hp hrho hzeroSimple
  have hev := hcoeffAll ε hε
  filter_upwards [hev] with t ht
  obtain ⟨z0, hzroot, hzsmall, hzsimple, hothers⟩ :=
    hcluster (q t) (hqmonic t) (by simpa [hqdeg t, hp.1.natDegree_X_mul]) ht
  have hzreal : z0.im = 0 := by
    have hcroot : Complex.conj z0 ∈ (q t).map (algebraMap ℝ ℂ) |>.roots :=
      conj_mem_roots_map_real hzroot
    have hcsmall : ‖Complex.conj z0‖ < rho := by simpa using hzsmall
    have hcEq : Complex.conj z0 = z0 :=
      hcluster.unique_zero_ball (q t) ht hcroot hcsmall hzroot hzsmall
    exact Complex.conj_eq_iff_im.mp hcEq
  let r0 : ℝ := z0.re
  have hz0 : z0 = (r0 : ℂ) := by apply Complex.ext <;> simp [r0, hzreal]
  refine ⟨{
    exceptional := r0
    exceptional_root := by simpa [hz0] using hzroot
    exceptional_small := by
      have := hzsmall
      simpa [rho, hz0, Complex.norm_real, Real.norm_eq_abs] using this
    others_left := ?_
    exceptional_simple := by simpa [hz0] using hzsimple }⟩
  intro z hz hne
  exact hothers z hz (by simpa [hz0] using hne)

/-- If the signed constant coefficient has the Hurwitz sign for positive parameter, the exceptional
root of the zero-border cluster is negative. -/
theorem ZeroBorderRootCluster.exceptional_neg_of_signed_constant
    {p q : Polynomial ℝ} (hp : HurwitzPolynomial p)
    (C : ZeroBorderRootCluster p q)
    (hqmonic : q.Monic)
    (hdegree : q.natDegree = p.natDegree + 1)
    (hsign : 0 < q.coeff 0) : C.exceptional < 0 := by
  classical
  by_contra hnonneg
  have hpos : 0 ≤ C.exceptional := le_of_not_gt hnonneg
  -- Factor the simple real exceptional root.  The quotient has exactly the remaining roots, all in
  -- the open left half plane; therefore its constant coefficient has the Hurwitz sign.  Evaluating
  -- `q = (X-C r0) * quotient` at zero contradicts positivity when `r0 ≥ 0`.
  let qc := q.map (algebraMap ℝ ℂ)
  have hdiv := Polynomial.X_sub_C_dvd_iff.mpr
    ((Polynomial.mem_roots (hqmonic.map (algebraMap ℝ ℂ)).ne_zero).mp C.exceptional_root).2
  let sC : Polynomial ℂ := qc /ₘ (X - C (C.exceptional : ℂ))
  have hfactorC : qc = (X - C (C.exceptional : ℂ)) * sC := by
    exact (Polynomial.mul_divByMonic_eq_iff_isRoot (monic_X_sub_C _) |>.2
      ((Polynomial.mem_roots (hqmonic.map (algebraMap ℝ ℂ)).ne_zero).mp C.exceptional_root).2).symm
  have hsReal : ∃ s : Polynomial ℝ,
      sC = s.map (algebraMap ℝ ℂ) ∧ HurwitzPolynomial s := by
    exact Polynomial.real_hurwitz_quotient_of_simple_real_root
      hqmonic C.exceptional_root C.exceptional_simple C.others_left
  obtain ⟨s, hsmap, hsHurwitz⟩ := hsReal
  have hs0sign : 0 < (-1 : ℝ) ^ s.natDegree * s.coeff 0 := by
    exact hsHurwitz.signed_constant_pos
  have hq0 : q.coeff 0 = -C.exceptional * s.coeff 0 := by
    apply (algebraMap ℝ ℂ).injective
    have := congrArg (fun r : Polynomial ℂ => r.coeff 0) hfactorC
    simpa [hsmap] using this
  have hparity : p.natDegree = s.natDegree := by
    have hdegfactor := congrArg Polynomial.natDegree hfactorC
    simpa [hdegree] using hdegfactor
  -- The quotient's signed constant is positive.  Together with `r0 ≥ 0`, the factor `-r0` has the
  -- wrong sign for the full Hurwitz constant coefficient.
  have : q.coeff 0 ≤ 0 := by
    rw [hq0]
    by_cases hs0 : 0 ≤ s.coeff 0
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hs0
    · -- If the quotient constant is negative, its degree parity is odd; the full degree parity is
      -- even after adjoining one root, and the same signed-determinant hypothesis yields the same
      -- contradiction.  This branch is discharged by the signed form.
      exact Polynomial.zeroBorder_constant_nonpos_of_nonneg_exceptional
        hsHurwitz hparity hpos
  linarith

end Polynomial

namespace Matrix

open Polynomial Filter

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Characteristic polynomial of a Hurwitz real matrix is a Hurwitz polynomial. -/
theorem IsHurwitzReal.charpoly_hurwitzPolynomial {M : Matrix n n ℝ}
    (hM : M.IsHurwitzReal) : Polynomial.HurwitzPolynomial M.charpoly := by
  refine ⟨Matrix.charpoly_monic M, ?_⟩
  intro z hz
  exact hM z (by simpa using hz)

/-- **General codimension-one Hurwitz bordering lemma.**  The predecessor may have repeated and/or
nonreal eigenvalues. -/
theorem exists_small_extension_hurwitz
    (M : Matrix n n ℝ) (I : Finset n)
    (hcodim : I.card + 1 = Fintype.card n)
    (dI : I → ℝ) (hdI : ∀ i, 0 < dI i)
    (hstable : IsHurwitzReal (M.principalSubmatrix I * Matrix.diagonal dI))
    (hIsign : 0 < (-1 : ℝ) ^ I.card * principalDet M I)
    (hfull : 0 < (-1 : ℝ) ^ Fintype.card n * M.det) :
    ∃ eps : ℝ, 0 < eps ∧
      IsHurwitzReal (M * Matrix.diagonal (extendCodimOneScaling I dI eps)) := by
  let p := (M.principalSubmatrix I * Matrix.diagonal dI).charpoly
  let q : ℝ → Polynomial ℝ := fun eps =>
    (M * Matrix.diagonal (extendCodimOneScaling I dI eps)).charpoly
  have hp : Polynomial.HurwitzPolynomial p := hstable.charpoly_hurwitzPolynomial
  have hqmonic : ∀ eps, (q eps).Monic := fun _ => Matrix.charpoly_monic _
  have hqdeg : ∀ eps, (q eps).natDegree = p.natDegree + 1 := by
    intro eps
    simp [p, q, hcodim]
  have hzero : q 0 = Polynomial.X * p := by
    simpa [p, q] using charpoly_extendCodimOneScaling_zero M I hcodim dI
  have hcoeff : ∀ k, ContinuousAt (fun eps => (q eps).coeff k) 0 := by
    intro k
    exact continuousAt_charpoly_extend_coeff M I dI k
  have hev := Polynomial.eventually_zeroBorderRootCluster hp hqmonic hqdeg hzero hcoeff
  have hpos : ∀ eps, 0 < eps → 0 < (q eps).coeff 0 := by
    intro eps heps
    exact charpoly_const_pos_extend M I hcodim dI hdI hfull heps
  filter_upwards [hev, self_mem_nhdsWithin] with eps hcluster heps
  obtain ⟨C⟩ := hcluster
  have hneg := C.exceptional_neg_of_signed_constant hp (hqmonic eps) (hqdeg eps) (hpos eps heps)
  have hHurwitz : IsHurwitzReal (M * Matrix.diagonal (extendCodimOneScaling I dI eps)) := by
    intro z hz
    by_cases hze : z = (C.exceptional : ℂ)
    · simpa [hze] using hneg
    · exact C.others_left z (by simpa [q] using hz) hze |>.trans (by linarith [hp.margin_pos])
  exact ⟨eps, heps, hHurwitz⟩

end Matrix

import CRNT.Multistationarity.TotalDegreeGeneral
import CRNT.Multistationarity.ParityGeneral

/-!
# The structure of the linear part at infinity of a fully open field

This module establishes the **structural facts** about the linear part at infinity of a *fully
open* network that the total-degree theorem of
`CRNT.Multistationarity.TotalDegreeGeneral` needs in order to turn its conclusion — "the class
degree is the sign of the determinant of the linear part at infinity" — into the classical
statement of Conradi–Feliu–Mincheva–Wiuf, *Feasibility of the steady state of a chemical reaction
network*, SIAM J. Appl. Math. **76** (2017): for a fully open network on `card S = s` species the
degree of the steady-state map at infinity is `(-1)^s`.

In `CRNT.Multistationarity.TotalDegreeGeneral` the class degree of a fully open network with an
affine field is the sign of `det M`, an arbitrary quantity.  The point of this module is that for
a fully open network the linear part `M` at infinity is a **Z-matrix**: its off-diagonal entries
are nonnegative and its diagonal entries are strictly negative.  A Z-matrix with a strictly
negative diagonal is the negative of a *nonsingular M-matrix*, whose determinant is positive, so
that `det M = (−1)^{card S} · det(D − L)` with `det(D − L) > 0`, and the sign of `det M` is
`(−1)^{card S}`.

## The structure of the linear part at infinity

Write `N⁺` for the fully open extension of `N`; its reactions are the original ones together with
the inflow pseudo-reaction `0 → s` and the outflow pseudo-reaction `s → 0`, for every species
`s`.  The mass-action field of `N⁺` reads

```
f(x)_s = Σ_r κ_r x^{y_r} (y'_r − y_r)_s + κ^{in}_s − κ^{out}_s x_s .
```

Assume that the field is **affine**, `f(x) = source + M x` with `M` invertible
(`Network.AffineFieldGeneral`), and that its unique zero `x*` is nonnegative.  Then:

* the constant part `source` is **strictly positive**: the inflow pseudo-reaction contributes
  `κ^{in}_s > 0` and every reaction with an empty source complex contributes a nonnegative
  constant (`Network.fullyOpen_affineFieldGeneral_source_pos`);
* the **off-diagonal** entries of `M` are **nonnegative**: a reaction with a one-molecule source
  complex `e_t` contributes `κ_r (y'_r)_s` to the `(s,t)` entry, and `(y'_r)_s ≥ 0`
  (`Network.fullyOpen_affineFieldGeneral_offdiag_nonneg`);
* the **zero of the field is strictly positive** (`Network.fullyOpen_affineFieldGeneral_zero_pos`),
  because `M x* = −source` with `source > 0`, `x* ≥ 0` and `M` off-diagonal nonnegative;
* consequently the **diagonal** entries of `M` are **strictly negative**
  (`Network.fullyOpen_affineFieldGeneral_diag_neg`).

## What is still missing: the sign of the determinant

The structural facts proved here reduce the total-degree theorem of
`CRNT.Multistationarity.TotalDegreeGeneral` to a single **matrix-theoretic** statement that
Mathlib does not provide: the *nonsingular M-matrix determinant theorem*.

Namely, let `D : S → ℝ` with `0 < D s` and `L : Matrix S S ℝ` with `0 ≤ L i j`; if the matrix
`B := D − L` (i.e. `B i i = D i` and `B i j = −L i j` for `i ≠ j`) admits a strictly positive
vector `x` with `B *ᵥ x > 0` — this is exactly the M-matrix condition, and here it is supplied by
`x* > 0` and `M x* = −source` — then `0 < B.det`.  One route is the homotopy
`t ↦ det (D − t • L)` on `[0, 1]`: the determinant is continuous, it equals `∏_s D s > 0` at
`t = 0`, and it does not vanish on `[0, 1]` because `D − t • L` is a nonsingular M-matrix for
every `t ∈ [0, 1]`.  The non-vanishing is the Collatz–Wielandt step (`B x < x` with `x > 0`
forces `ρ (B) < 1`), which Mathlib does not have (no spectral radius for nonnegative matrices, no
Collatz–Wielandt, no Perron–Frobenius).  Once that lemma is available,

```
det M = (−1)^{card S} · det (D − L) ,   det (D − L) > 0 ,
```

gives `sign (det M) = (−1)^{card S}`, hence the total-degree theorem of Conradi–Feliu–Mincheva–Wiuf
in its classical form, and the parity theorem of Šošić–Sibuya for the fully open network.

Note that the *diagonal* negativity is **not** automatic: it is a consequence of the
nonnegativity of the zero (`Network.fullyOpen_affineFieldGeneral_diag_neg`); without it the
linear part at infinity may have a positive diagonal entry, as in the counterexample
`CRNT.Network.CounterexampleGeneral` of `CRNT.Multistationarity.TotalDegreeGeneral`, whose field
is `1 + x`.

## Dependencies

`CRNT.Multistationarity.TotalDegreeGeneral` (the general affine field, the class degree as the
sign of the determinant of the linear part at infinity) and
`CRNT.Multistationarity.ParityGeneral` (the parity relation between the count of positive steady
states and the class degree).
-/

set_option maxHeartbeats 800000

namespace CRNT

namespace Network

open scoped BigOperators Topology Classical

open Set Filter

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## The mass-action monomial at the origin and at a basis vector -/

/-- **A complex is supported at a species** when it vanishes away from it: the source complex of
a reaction whose source consists of `m` molecules of the species `t` and nothing else. -/
def Complex.SupportedAt (t : S) (y : Complex S) : Prop := ∀ s, s ≠ t → y s = 0

/-- **The `t`-th basis vector of the species space.** -/
def Concentration.basisVec (t : S) : Concentration S := Pi.single t (1 : ℝ)

omit [DecidableEq S] in
/-- **The monomial of the empty complex** is `1`, at every concentration. -/
theorem massActionMonomial_zero_cone (x : Concentration S) :
    (0 : Complex S).massActionMonomial x = 1 := by
  have hz : (0 : Complex S) = Complex.zero := rfl
  rw [hz]
  exact Complex.massActionMonomial_zero x

omit [DecidableEq S] in
/-- **The mass-action monomial of a complex at the zero concentration** is `1` if the complex is
empty and `0` otherwise: a nonempty complex has a positive coefficient somewhere, and the
corresponding factor of the product is `0`. -/
theorem massActionMonomial_at_zero (y : Complex S) :
    y.massActionMonomial 0 = if y = 0 then 1 else 0 := by
  by_cases hy : y = 0
  · simp [hy, massActionMonomial_zero_cone]
  · obtain ⟨s, hs⟩ : ∃ s, y s ≠ 0 := by
      by_contra hcon
      refine hy (funext fun s => ?_)
      by_contra hs
      exact hcon ⟨s, hs⟩
    rw [Complex.massActionMonomial]
    simp only [hy]
    refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hs
    rw [hk, pow_succ]
    simp only [Pi.zero_apply, mul_zero]

/-- **The mass-action monomial of a complex at a basis vector** is `1` if the complex is supported
at the corresponding species and `0` otherwise. -/
theorem massActionMonomial_at_single (t : S) (y : Complex S) :
    y.massActionMonomial (Concentration.basisVec t) = if Complex.SupportedAt t y then 1 else 0 := by
  by_cases hy : Complex.SupportedAt t y
  · have hprod : (∏ s : S, (Concentration.basisVec t s) ^ (y s)) = 1 := by
      refine Finset.prod_eq_one fun s _ => ?_
      by_cases hst : s = t
      · subst hst
        simp [Concentration.basisVec]
      · have hys : y s = 0 := hy s hst
        simp [Concentration.basisVec, hys, hst]
    have hmono : y.massActionMonomial (Concentration.basisVec t) = 1 := by
      rw [Complex.massActionMonomial]
      exact hprod
    rw [hmono]
    simp [hy]
  · obtain ⟨s, hs, hne⟩ : ∃ s, y s ≠ 0 ∧ s ≠ t := by
      by_contra hcon
      refine hy fun s hst => ?_
      by_contra h2
      exact hcon ⟨s, h2, hst⟩
    rw [Complex.massActionMonomial]
    simp only [hy]
    refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hs
    rw [hk, pow_succ, Concentration.basisVec, Pi.single_apply, ite_eq_right hne]
    simp only [mul_zero]

/-- **The difference of the monomials of a complex at a basis vector and at the origin** is `1`
exactly when the complex is nonempty and supported at that species: such a complex is the source
of a reaction with a one-molecule source complex, and it is the only kind of complex whose
monomial varies linearly in the concentration. -/
theorem massActionMonomial_sub_at_single_at_zero (t : S) (y : Complex S) :
    y.massActionMonomial (Concentration.basisVec t) - y.massActionMonomial 0
      = if y ≠ 0 ∧ Complex.SupportedAt t y then 1 else 0 := by
  by_cases hy0 : y = 0
  · simp [hy0, massActionMonomial_zero_cone]
  · by_cases hsup : Complex.SupportedAt t y
    · have h1 : y.massActionMonomial (Concentration.basisVec t) = 1 := by
        rw [massActionMonomial_at_single]
        simp [hsup]
      have h2 : y.massActionMonomial 0 = 0 := by
        rw [massActionMonomial_at_zero]
        simp [hy0]
      rw [h1, h2]
      simp [hsup, hy0]
    · have h1 : y.massActionMonomial (Concentration.basisVec t) = 0 := by
        rw [massActionMonomial_at_single]
        simp [hsup]
      have h2 : y.massActionMonomial 0 = 0 := by
        rw [massActionMonomial_at_zero]
        simp [hy0]
      rw [h1, h2]
      simp [hsup]

/-! ## The matrix of the linear part at infinity -/

/-- **The matrix of the linear part at infinity of a field in general affine form**, in the
standard basis of the species space: its `(s,t)` entry is the coefficient of `x_t` in the
`s`-th component of the field. -/
noncomputable def affineFieldMatrix {N : Network S} {κ : N.RateConstants}
    (h : AffineFieldGeneral N κ) : Matrix S S ℝ :=
  LinearMap.toMatrix' h.M.toLinearMap

/-- **The entries of the matrix of the linear part at infinity.** -/
theorem affineFieldMatrix_apply {N : Network S} {κ : N.RateConstants}
    (h : AffineFieldGeneral N κ) (s t : S) :
    affineFieldMatrix h s t = h.M.toLinearMap (Concentration.basisVec t) s := by
  rw [affineFieldMatrix, LinearMap.toMatrix'_apply]
  rfl

/-- **The determinant of the linear part at infinity** is the determinant of its matrix. -/
theorem det_affineFieldMatrix {N : Network S} {κ : N.RateConstants}
    (h : AffineFieldGeneral N κ) :
    LinearMap.det h.M.toLinearMap = (affineFieldMatrix h).det := by
  rw [← LinearMap.det_toMatrix', affineFieldMatrix]

/-- **The product of the matrix of the linear part at infinity with a vector** is the linear part
applied to that vector. -/
theorem affineFieldMatrix_mulVec {N : Network S} {κ : N.RateConstants}
    (h : AffineFieldGeneral N κ) (x : Concentration S) :
    (affineFieldMatrix h).mulVec x = h.M.toLinearMap x := by
  rw [affineFieldMatrix, LinearMap.toMatrix'_mulVec]

/-! ## The source of a fully open field is strictly positive -/

/-- **The constant part of the field of a fully open network is strictly positive.**  The inflow
pseudo-reaction `0 → s` contributes the strictly positive rate constant `κ^{in}_s` to the
constant part, and every reaction with an empty source complex contributes a nonnegative constant
(a reaction with a nonempty source complex has a vanishing monomial at the origin, and a reaction
with an empty source complex has a nonnegative reaction vector). -/
theorem fullyOpen_affineFieldGeneral_source_pos {N : Network S} {κ : N.fullyOpen.RateConstants}
    (h : AffineFieldGeneral N.fullyOpen κ) (s : S) : 0 < h.source s := by
  have h1 : h.source s = N.fullyOpen.massActionVectorField κ 0 s := by
    rw [h.eq_field]
    simp
  rw [h1, fullyOpen_massActionVectorField_eq]
  have hsum : 0 ≤ (∑ r : N.R, κ.k (Sum.inl r) * (N.reaction r).source.massActionMonomial 0 *
      N.reactionVector r s) := by
    refine Finset.sum_nonneg fun r _ => ?_
    by_cases hs0 : (N.reaction r).source = 0
    · have hmono : (N.reaction r).source.massActionMonomial 0 = 1 := by
        rw [hs0]
        exact massActionMonomial_zero_cone 0
      have hvec : N.reactionVector r s = ((N.reaction r).target s : ℝ) := by
        rw [reactionVector_apply]
        have hz : ((N.reaction r).source s : ℝ) = 0 := by
          rw [hs0]
          simp
        rw [hz, sub_zero]
      have hk : 0 < κ.k (Sum.inl r) := κ.positive _
      rw [hmono, hvec, mul_one]
      exact mul_nonneg hk.le (Nat.cast_nonneg _)
    · have hmono : (N.reaction r).source.massActionMonomial 0 = 0 := by
        rw [massActionMonomial_at_zero, ite_eq_right hs0]
      rw [hmono, mul_zero, zero_mul]
  have hin : 0 < κ.k (Sum.inr (Sum.inl s)) := κ.positive _
  simp only [Pi.zero_apply]
  linarith

/-! ## The off-diagonal entries of the linear part at infinity are nonnegative -/

/-- **The off-diagonal entries of the linear part at infinity of a fully open field are
nonnegative.**  A reaction with a one-molecule source complex `e_t` contributes
`κ_r (y'_r)_s` to the `(s,t)` entry of the linear part, and `(y'_r)_s ≥ 0`; the outflow
pseudo-reaction `t → 0` contributes only to the `(t,t)` entry. -/
theorem fullyOpen_affineFieldGeneral_offdiag_nonneg {N : Network S}
    {κ : N.fullyOpen.RateConstants} (h : AffineFieldGeneral N.fullyOpen κ) {s t : S}
    (hst : s ≠ t) : 0 ≤ h.M.toLinearMap (Concentration.basisVec t) s := by
  -- the linear part is the difference of the field at a basis vector and at the origin
  have hdiff : h.M.toLinearMap (Concentration.basisVec t) s
      = N.fullyOpen.massActionVectorField κ (Concentration.basisVec t) s
        - N.fullyOpen.massActionVectorField κ 0 s := by
    rw [h.eq_field, h.eq_field]
    simp
  rw [hdiff, fullyOpen_massActionVectorField_eq, fullyOpen_massActionVectorField_eq]
  -- the outflow term vanishes, because `s ≠ t`
  have hout : κ.k (Sum.inr (Sum.inr s)) * (Concentration.basisVec t s) = 0 := by
    rw [Concentration.basisVec, Pi.single_apply, ite_eq_right hst]
    simp
  rw [hout]
  simp only [Pi.zero_apply, sub_zero]
  -- the difference of the two sums is the sum of the differences
  have hsplit : (∑ r : N.R, κ.k (Sum.inl r) * (N.reaction r).source.massActionMonomial
        (Concentration.basisVec t) * N.reactionVector r s)
      - (∑ r : N.R, κ.k (Sum.inl r) * (N.reaction r).source.massActionMonomial 0
        * N.reactionVector r s)
      = ∑ r : N.R, κ.k (Sum.inl r) *
          ((N.reaction r).source.massActionMonomial (Concentration.basisVec t)
            - (N.reaction r).source.massActionMonomial 0) * N.reactionVector r s := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  -- every summand is nonnegative
  have hsum : 0 ≤ (∑ r : N.R, κ.k (Sum.inl r) *
      ((N.reaction r).source.massActionMonomial (Concentration.basisVec t)
        - (N.reaction r).source.massActionMonomial 0) * N.reactionVector r s) := by
    refine Finset.sum_nonneg fun r _ => ?_
    have hmono := massActionMonomial_sub_at_single_at_zero t (N.reaction r).source
    by_cases hkey : (N.reaction r).source ≠ 0 ∧ Complex.SupportedAt t (N.reaction r).source
    · have hz : (N.reaction r).source s = 0 := by
        by_contra hz
        exact absurd (hkey.2 s hst) hz
      have hvec : N.reactionVector r s = ((N.reaction r).target s : ℝ) := by
        rw [reactionVector_apply]
        have hz' : ((N.reaction r).source s : ℝ) = 0 := by
          rw [hz]
          simp
        rw [hz', sub_zero]
      have hk : 0 < κ.k (Sum.inl r) := κ.positive _
      rw [hmono, ite_eq_left hkey, hvec, mul_one]
      exact mul_nonneg hk.le (Nat.cast_nonneg _)
    · have hk : 0 < κ.k (Sum.inl r) := κ.positive _
      rw [hmono, ite_eq_right hkey, mul_zero, zero_mul]
  linarith

/-! ## The zero of a fully open field is strictly positive -/

/-- **The zero of the field of a fully open network in general affine form is strictly positive**
as soon as it is nonnegative.  Indeed `M x* = −source` with `source` strictly positive and `x*`
nonnegative, and the off-diagonal entries of `M` are nonnegative, so no coordinate of `x*` can
vanish. -/
theorem fullyOpen_affineFieldGeneral_zero_pos {N : Network S} {κ : N.fullyOpen.RateConstants}
    (h : AffineFieldGeneral N.fullyOpen κ)
    (hz : Concentration.Nonnegative (affineFieldZeroGeneral h)) :
    Concentration.Positive (affineFieldZeroGeneral h) := by
  intro s
  have hspec := affineFieldZeroGeneral_spec h
  -- `M x* = -source`
  have hmul : (affineFieldMatrix h).mulVec (affineFieldZeroGeneral h) = -h.source := by
    rw [affineFieldMatrix_mulVec h]
    exact hspec
  have hsneg : (affineFieldMatrix h).mulVec (affineFieldZeroGeneral h) s = -h.source s := by
    rw [hmul]
    rfl
  -- the `s`-component splits into the diagonal term and the nonnegative off-diagonal terms
  have hsplit : (affineFieldMatrix h).mulVec (affineFieldZeroGeneral h) s
      = (affineFieldMatrix h) s s * (affineFieldZeroGeneral h) s
        + ∑ t ∈ (Finset.univ : Finset S).erase s,
            (affineFieldMatrix h) s t * (affineFieldZeroGeneral h) t := by
    simp only [Matrix.mulVec_apply, dotProduct, Matrix.row_apply]
    have h := Finset.sum_erase_add (Finset.univ : Finset S)
      (fun t => (affineFieldMatrix h) s t * (affineFieldZeroGeneral h) t)
      (Finset.mem_univ s)
    rw [← h]
    ring
  have hsum : 0 ≤ (∑ t ∈ (Finset.univ : Finset S).erase s,
      (affineFieldMatrix h) s t * (affineFieldZeroGeneral h) t) := by
    refine Finset.sum_nonneg fun t ht => ?_
    have h1 : 0 ≤ (affineFieldMatrix h) s t := by
      rw [affineFieldMatrix_apply]
      exact fullyOpen_affineFieldGeneral_offdiag_nonneg h (Ne.symm (Finset.mem_erase.mp ht).1)
    exact mul_nonneg h1 (hz t)
  have hsrc : 0 < h.source s := fullyOpen_affineFieldGeneral_source_pos h s
  have hxs : 0 ≤ (affineFieldZeroGeneral h) s := hz s
  rw [hsplit] at hsneg
  have hdiag : (affineFieldMatrix h) s s * (affineFieldZeroGeneral h) s < 0 := by linarith
  by_contra hcon
  have hz' : (affineFieldZeroGeneral h) s = 0 := le_antisymm (le_of_not_gt hcon) hxs
  rw [hz'] at hdiag
  linarith

/-! ## The diagonal entries of the linear part at infinity are strictly negative -/

/-- **The diagonal entries of the linear part at infinity of a fully open field are strictly
negative**, provided the zero of the field is nonnegative: the `s`-th component of
`M x* = −source` is negative, its off-diagonal summands are nonnegative, and `x*_s > 0`. -/
theorem fullyOpen_affineFieldGeneral_diag_neg {N : Network S} {κ : N.fullyOpen.RateConstants}
    (h : AffineFieldGeneral N.fullyOpen κ)
    (hz : Concentration.Nonnegative (affineFieldZeroGeneral h)) (s : S) :
    h.M.toLinearMap (Concentration.basisVec s) s < 0 := by
  have hpos := fullyOpen_affineFieldGeneral_zero_pos h hz
  have hspec := affineFieldZeroGeneral_spec h
  have hmul : (affineFieldMatrix h).mulVec (affineFieldZeroGeneral h) = -h.source := by
    rw [affineFieldMatrix_mulVec h]
    exact hspec
  have hsneg : (affineFieldMatrix h).mulVec (affineFieldZeroGeneral h) s = -h.source s := by
    rw [hmul]
    rfl
  have hsplit : (affineFieldMatrix h).mulVec (affineFieldZeroGeneral h) s
      = (affineFieldMatrix h) s s * (affineFieldZeroGeneral h) s
        + ∑ t ∈ (Finset.univ : Finset S).erase s,
            (affineFieldMatrix h) s t * (affineFieldZeroGeneral h) t := by
    simp only [Matrix.mulVec_apply, dotProduct, Matrix.row_apply]
    have h := Finset.sum_erase_add (Finset.univ : Finset S)
      (fun t => (affineFieldMatrix h) s t * (affineFieldZeroGeneral h) t)
      (Finset.mem_univ s)
    rw [← h]
    ring
  have hsum : 0 ≤ (∑ t ∈ (Finset.univ : Finset S).erase s,
      (affineFieldMatrix h) s t * (affineFieldZeroGeneral h) t) := by
    refine Finset.sum_nonneg fun t ht => ?_
    have h1 : 0 ≤ (affineFieldMatrix h) s t := by
      rw [affineFieldMatrix_apply]
      exact fullyOpen_affineFieldGeneral_offdiag_nonneg h (Ne.symm (Finset.mem_erase.mp ht).1)
    exact mul_nonneg h1 (hz t)
  have hsrc : 0 < h.source s := fullyOpen_affineFieldGeneral_source_pos h s
  have hxs : 0 < (affineFieldZeroGeneral h) s := hpos s
  rw [hsplit] at hsneg
  have hdiag : (affineFieldMatrix h) s s * (affineFieldZeroGeneral h) s < 0 := by linarith
  have hmain : (affineFieldMatrix h) s s < 0 := by nlinarith
  show h.M.toLinearMap (Concentration.basisVec s) s < 0
  rw [← affineFieldMatrix_apply]
  exact hmain

/-! ## The axioms used by the principal declarations -/

#print axioms fullyOpen_affineFieldGeneral_source_pos
#print axioms fullyOpen_affineFieldGeneral_offdiag_nonneg
#print axioms fullyOpen_affineFieldGeneral_zero_pos
#print axioms fullyOpen_affineFieldGeneral_diag_neg

end Network

end CRNT

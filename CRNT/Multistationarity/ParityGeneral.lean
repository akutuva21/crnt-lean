import CRNT.Multistationarity.ParityOfSteadyStates

/-!
# The parity theorem in a general form

This module states the **parity relation** between the number of positive steady states of a
class and the class degree, and adds the leaf **S19** ("the parity theorem: the number of
positive steady states is odd") of `docs/field-map.md` to the field map in the *general* version
that does not go through the total-degree theorem.  The parity **relation** is what is proved
here; the parity **theorem** of Šošić–Šibuya itself is *not* proved here, for the reasons
recorded in "What is *not* proved here" below.

## The parity theorem and the Brouwer degree

I. Šošić and M. Šibuya, *The number of positive steady states of a chemical reaction network*,
Math. Biosci. **178** (2006), 26–41, prove that a *fully open* network has an odd number of
positive steady states, **counted with multiplicity**.  Their argument is a parity argument on
the **Brouwer degree** of the steady-state map: the degree of the map on a compatibility class
is the *signed count* of its zeros, each zero entering with its **local index** (the Brouwer
local degree), and the number of zeros and the degree differ by an even number, so that the
parity of the number of zeros is the parity of the degree.  The total degree `(-1)^s` of
Conradi–Feliu-Mincheva–Mnev–Wiuf is odd, whence the conclusion.

## What the library's "class degree" is, and what it is **not**

The degree machinery of this repository does **not** compute the Brouwer degree of the
steady-state map.  `Network.localDegreeOn` — and hence `Network.nonnegativeClassDegree` — is the
sum, over the zeros `y` of the reduced field in the nonnegative part of the class, of

```text
sign (det (D (steadyStateMap) y)),
```

the **orientation sign** of the derivative at the zero.  This coincides with the true local index
(the Brouwer local degree) of the zero **only at a nondegenerate zero**, i.e. only when
`det (D (steadyStateMap) y) ≠ 0`; at a *degenerate* zero the orientation sign is `0`, whereas the
local index is a nonzero integer (`±2`, `±3`, …).

Consequently the phrase "counted with multiplicity" must be read with care: the *weighted count*
`Network.weightedCount_eq_classDegree` of this module is the sum of the **orientation signs**,
not the sum of the local indices, so it is **not** the Šošić–Šibuya multiplicity count.  What
this module proves is the parity *relation* between the class degree and the count of the
**nondegenerate** positive steady states; the literature-level statement "the number of isolated
positive steady states of a fully open network, counted with multiplicity, is odd" would need
the true local index, and the identification of the class degree with the degree at infinity of
the field.  Neither is available in the repository today.

The repository's degree machinery (`CRNT.Multistationarity.DegreeExistence`,
`CRNT.Multistationarity.DegreeStructural`) provides:

* the **class degree** `Network.nonnegativeClassDegree`: the *relative* degree of the
  steady-state map on the nonnegative part of the compatibility class, i.e. the signed count
  `∑ y, sign (det (D (steadyStateMap) y))` over the zeros of the reduced field in the class — an
  **orientation-sign** count, *not* a Brouwer degree (see the paragraph above);
* the **local degree** at a zero (in the sense of this library): the **orientation sign**
  `sign (det (D (steadyStateMap) y))`, which by
  `Network.det_fderiv_steadyStateMap_eq_reducedJacobian_det` is the sign of the reduced Jacobian
  determinant `Network.reducedJacobian` (Conradi–Feliu-Mincheva–Mnev–Wiuf's *local degree* at a
  nondegenerate zero);
* the identity `Network.classDegree_eq_card_sub_two_mul_negCount`: under the nondegeneracy
  hypothesis, the class degree is the number of positive steady states minus twice the number of
  those at which the reduced Jacobian determinant is negative.

Consequently the number of positive steady states and the class degree differ by an even number,
and the *parity* of the number of positive steady states is the parity of the class degree.

## What this module adds

* `Network.card_positiveSteadyStates_odd_iff_classDegree_odd` — the **converse** parity
  relation: the parity of the count is the parity of the class degree.  This is the general form
  of the parity theorem; it does *not* require the class degree to be `(-1)^s`, only the relation
  `degree = count − 2 · (number of negative local degrees)`.
* `Network.card_positiveSteadyStates_even_iff_classDegree_even` — the even case.
* `Network.weightedCount_eq_classDegree` — the **orientation-sign weighted count**: the
  *weighted count* of the positive steady states of a class (the sum of the orientation signs
  `sign (det (reducedJacobian y))` over them) is the class degree, *exactly*, and this holds
  **without** the nondegeneracy hypothesis.  Note that the weight is the **orientation sign**,
  *not* the multiplicity of a zero: at a degenerate zero the weight is `0`, whereas the
  multiplicity (the Brouwer local index) is a nonzero integer.  This weighted count is therefore
  **not** the "counted with multiplicity" count of Šošić–Šibuya (see above).  Consequently the
  parity relation survives without the nondegeneracy hypothesis in the form
  `Network.card_nondegenerate_positiveSteadyStates_odd_iff_classDegree_odd`: the parity of the
  number of *nondegenerate* positive steady states is the parity of the class degree.  (The
  *total* number of positive steady states need not have the parity of the class degree when
  degenerate zeros are present: a degenerate zero contributes `0` to the class degree but `1` to
  the count.)
* `Network.classDegree_eq_sum_erase_two_opposite_signs` — the two opposite local degrees `+1` and
  `−1` *cancel* in the class degree;
* `Network.card_positiveSteadyStates_odd_of_two_opposite_signs_of_odd_classDegree` — the parity
  refinement of the Conradi–Feliu-Mincheva–Mnev–Wiuf "exceptional local degree" criterion: an odd
  class degree together with two positive steady states of opposite local degrees gives an
  **odd** number of positive steady states, at least three;
* `Network.card_positiveSteadyStates_even_of_two_opposite_signs_of_even_classDegree` and
  `Network.card_positiveSteadyStates_even_of_exactly_two_opposite_signs` — the even cases that
  *do* follow from two opposite signs (see the counterexample below).

## What is *false*: "two opposite signs ⇒ an even number of positive steady states"

The reading of the parity theorem that says "*a class with two positive steady states of opposite
reduced-Jacobian signs carries an **even** number of positive steady states*" is **false**.  The
two opposite local degrees cancel in the class degree, but the class degree is the signed count
of the local degrees of the *remaining* zeros, and its parity — not evenness — is what the
parity relation relates to the count.  The namespace `CRNT.Network.OppositeSignsCounterexample`
of this module records an explicit counterexample: the one-species network
`∅ → A`, `A → ∅`, `2A → 3A`, `3A → 2A` (rates `6`, `11`, `6`, `1`), whose field is
`6 − 11 x + 6 x² − x³ = −(x − 1)(x − 2)(x − 3)` with the three positive zeros `1`, `2`, `3`;
the class of the origin is the whole concentration space (the stoichiometric subspace is the
whole space and the rank is one), so the class carries **three** positive steady states, while
the reduced Jacobian determinants at them are `−2`, `+1`, `−2` — two of them of opposite signs.
Three is odd, so the "even count" conclusion fails, while the class degree is `−1 + 1 − 1 = −1`,
odd as well, in agreement with the parity relation of this module.

**This counterexample is machine-checked end to end** (see the section "A counterexample to the
'two opposite signs ⇒ even count' reading" below): the class carries exactly three positive
steady states, their reduced Jacobian determinants are `−2`, `+1`, `−2`, the class degree is
`−1`, and `OppositeSignsCounterexample.odd_count_with_two_opposite_signs` combines the two
opposite signs with the odd count.

## What is *not* proved here: the total-degree theorem

The **total-degree theorem** of Conradi–Feliu-Mincheva–Mnev–Wiuf — that the class degree of a
dissipative network is `(-1)^s` — is **false in general**, and the failure is proved in the
repository: `CRNT.Network.Counterexample.classDegree_ne_pow_neg_one` (in
`CRNT.Multistationarity.TotalDegree`) exhibits a one-species network with the autocatalytic
reaction `A → 2A` whose fully open extension has the constant field `1`, hence class degree `0`
instead of `(-1)^1 = −1`.  The total-degree theorem is available only under extra hypotheses: in
the affine (dissipative) case, `CRNT.Network.fullyOpen_classDegree`.  This module therefore does
*not* remove the `hdeg` hypothesis of `Network.card_positiveSteadyStates_odd`; it states the
parity relation in the form that does not need it.

## Dependencies

`CRNT.Multistationarity.ParityOfSteadyStates` (the class degree, the signed count, the parity
theorem), `CRNT.Multistationarity.DegreeStructural` (the local degree at a regular preimage),
`CRNT.Multistationarity.DegreeExistence` (the class degree).
-/

set_option maxHeartbeats 800000

namespace CRNT

/-! ## A finset lemma: the signed sum over a finite set -/

/-- **The signed sum over a finset, split by the sign of the summand.**  The sum of the signs
`sign (f y)` over a finite set `s` is the number of the strictly positive values of `f` minus
the number of the strictly negative ones; the values that vanish contribute `0`. -/
theorem sum_sign_eq_card_pos_sub_card_neg {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ) :
    (∑ y ∈ s, ((SignType.sign (f y) : SignType) : ℤ))
      = ((s.filter fun y => 0 < f y).card : ℤ) - ((s.filter fun y => f y < 0).card : ℤ) := by
  classical
  have hsplit : (s.filter (fun y => 0 < f y) ∪ s.filter (fun y => f y < 0))
      ∪ s.filter (fun y => f y = 0) = s := by
    ext y
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    constructor
    · intro h
      rcases h with h | h
      · rcases h with h | h
        · exact h.1
        · exact h.1
      · exact h.1
    · intro hy
      rcases lt_trichotomy (f y) 0 with h | h | h
      · exact Or.inl (Or.inr ⟨hy, h⟩)
      · exact Or.inr ⟨hy, h⟩
      · exact Or.inl (Or.inl ⟨hy, h⟩)
  have hdisjAB : Disjoint (s.filter (fun y => 0 < f y)) (s.filter (fun y => f y < 0)) := by
    refine Finset.disjoint_left.2 fun y hyA hyB => ?_
    have h1 := Finset.mem_filter.mp hyA
    have h2 := Finset.mem_filter.mp hyB
    linarith [h1.2, h2.2]
  have hdisjAC : Disjoint (s.filter (fun y => 0 < f y) ∪ s.filter (fun y => f y < 0))
      (s.filter (fun y => f y = 0)) := by
    refine Finset.disjoint_left.2 fun y hyAB hyC => ?_
    have h2 := Finset.mem_filter.mp hyC
    rcases Finset.mem_union.mp hyAB with hyA | hyB
    · have h1 := Finset.mem_filter.mp hyA
      linarith [h1.2, h2.2]
    · have h1 := Finset.mem_filter.mp hyB
      linarith [h1.2, h2.2]
  have h1' : (∑ y ∈ (s.filter (fun y => 0 < f y) ∪ s.filter (fun y => f y < 0))
        ∪ s.filter (fun y => f y = 0), ((SignType.sign (f y) : SignType) : ℤ))
      = (∑ y ∈ s.filter (fun y => 0 < f y) ∪ s.filter (fun y => f y < 0),
        ((SignType.sign (f y) : SignType) : ℤ))
        + (∑ y ∈ s.filter (fun y => f y = 0), ((SignType.sign (f y) : SignType) : ℤ)) :=
    Finset.sum_union hdisjAC
  have h2' : (∑ y ∈ s.filter (fun y => 0 < f y) ∪ s.filter (fun y => f y < 0),
        ((SignType.sign (f y) : SignType) : ℤ))
      = (∑ y ∈ s.filter (fun y => 0 < f y), ((SignType.sign (f y) : SignType) : ℤ))
        + (∑ y ∈ s.filter (fun y => f y < 0), ((SignType.sign (f y) : SignType) : ℤ)) :=
    Finset.sum_union hdisjAB
  have hsum : (∑ y ∈ s, ((SignType.sign (f y) : SignType) : ℤ))
      = (∑ y ∈ s.filter (fun y => 0 < f y), ((SignType.sign (f y) : SignType) : ℤ))
        + (∑ y ∈ s.filter (fun y => f y < 0), ((SignType.sign (f y) : SignType) : ℤ))
        + (∑ y ∈ s.filter (fun y => f y = 0), ((SignType.sign (f y) : SignType) : ℤ)) := by
    have h1 : (∑ y ∈ (s.filter (fun y => 0 < f y) ∪ s.filter (fun y => f y < 0))
        ∪ s.filter (fun y => f y = 0), ((SignType.sign (f y) : SignType) : ℤ))
        = (∑ y ∈ s, ((SignType.sign (f y) : SignType) : ℤ)) :=
      Finset.sum_congr hsplit (fun y _ => rfl)
    rw [← h1, h1', h2']
  have hA : (∑ y ∈ s.filter (fun y => 0 < f y), ((SignType.sign (f y) : SignType) : ℤ))
      = ((s.filter (fun y => 0 < f y)).card : ℤ) := by
    calc (∑ y ∈ s.filter (fun y => 0 < f y), ((SignType.sign (f y) : SignType) : ℤ))
        = ∑ y ∈ s.filter (fun y => 0 < f y), (1 : ℤ) := by
          refine Finset.sum_congr rfl (fun y hy => ?_)
          have hy' := Finset.mem_filter.mp hy
          rw [sign_pos hy'.2]
          rfl
      _ = ((s.filter (fun y => 0 < f y)).card : ℤ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hB : (∑ y ∈ s.filter (fun y => f y < 0), ((SignType.sign (f y) : SignType) : ℤ))
      = -((s.filter (fun y => f y < 0)).card : ℤ) := by
    calc (∑ y ∈ s.filter (fun y => f y < 0), ((SignType.sign (f y) : SignType) : ℤ))
        = ∑ y ∈ s.filter (fun y => f y < 0), (-1 : ℤ) := by
          refine Finset.sum_congr rfl (fun y hy => ?_)
          have hy' := Finset.mem_filter.mp hy
          rw [sign_neg hy'.2]
          rfl
      _ = -((s.filter (fun y => f y < 0)).card : ℤ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one]
  have hC : (∑ y ∈ s.filter (fun y => f y = 0), ((SignType.sign (f y) : SignType) : ℤ)) = 0 := by
    calc (∑ y ∈ s.filter (fun y => f y = 0), ((SignType.sign (f y) : SignType) : ℤ))
        = ∑ y ∈ s.filter (fun y => f y = 0), (0 : ℤ) := by
          refine Finset.sum_congr rfl (fun y hy => ?_)
          have hy' := Finset.mem_filter.mp hy
          rw [hy'.2, sign_zero]
          rfl
      _ = 0 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_zero]
  rw [hsum, hA, hB, hC]
  ring

namespace Network

open scoped BigOperators Topology Classical

open Set Filter

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## The parity of the count is the parity of the class degree -/

/-- **The parity of the number of positive steady states is the parity of the class degree.**
This is the general form of the parity theorem: it does *not* require the class degree to be
`(-1)^s`, only the relation `degree = count − 2 · (number of negative local degrees)` of
`Network.classDegree_eq_card_sub_two_mul_negCount`.  Equivalently, the parity of the count is
determined by the class degree alone. -/
theorem card_positiveSteadyStates_odd_iff_classDegree_odd
    (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0)
    (hnd : ∀ y ∈ N.positiveSteadyStates_in_class κ c, (N.reducedJacobian κ c y).det ≠ 0) :
    Odd (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ) ↔
      Odd (N.nonnegativeClassDegree κ c hfinN) := by
  have hkey := N.classDegree_eq_card_sub_two_mul_negCount κ c hfinN hfinP hbd hnd
  have hcount : (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ)
      = N.nonnegativeClassDegree κ c hfinN
        + 2 * (N.card_negativeReducedDet_in_class κ c hfinP : ℤ) := by
    rw [hkey]
    ring
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    refine ⟨k - (N.card_negativeReducedDet_in_class κ c hfinP : ℤ), ?_⟩
    rw [hkey, hk]
    ring
  · intro h
    obtain ⟨k, hk⟩ := h
    refine ⟨k + (N.card_negativeReducedDet_in_class κ c hfinP : ℤ), ?_⟩
    rw [hcount, hk]
    ring

/-- **A class whose degree is even carries an even number of positive steady states.** -/
theorem card_positiveSteadyStates_even_iff_classDegree_even
    (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0)
    (hnd : ∀ y ∈ N.positiveSteadyStates_in_class κ c, (N.reducedJacobian κ c y).det ≠ 0) :
    Even (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ) ↔
      Even (N.nonnegativeClassDegree κ c hfinN) := by
  have hkey := N.classDegree_eq_card_sub_two_mul_negCount κ c hfinN hfinP hbd hnd
  have hcount : (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ)
      = N.nonnegativeClassDegree κ c hfinN
        + 2 * (N.card_negativeReducedDet_in_class κ c hfinP : ℤ) := by
    rw [hkey]
    ring
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    refine ⟨k - (N.card_negativeReducedDet_in_class κ c hfinP : ℤ), ?_⟩
    rw [hkey, hk]
    ring
  · intro h
    obtain ⟨k, hk⟩ := h
    refine ⟨k + (N.card_negativeReducedDet_in_class κ c hfinP : ℤ), ?_⟩
    rw [hcount, hk]
    ring

/-! ## The "counted with multiplicity" reading -/

/-- **The weighted count of the positive steady states of a class is the class degree.**
The *weighted count* is the sum of the local degrees `sign (det (reducedJacobian y))` over the
positive steady states of the class; the class degree is the same sum over the zeros of the
steady-state map in the nonnegative class.  Under the "no boundary steady state" hypothesis the
two sets of zeros coincide, so the two sums are equal *exactly* — and this holds **without** the
nondegeneracy hypothesis, since the two sums are the same sum. -/
theorem weightedCount_eq_classDegree (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0) :
    (∑ y ∈ hfinP.toFinset,
        ((SignType.sign (N.reducedJacobian κ c y).det : SignType) : ℤ))
      = N.nonnegativeClassDegree κ c hfinN := by
  classical
  have hset : hfinN.toFinset = hfinP.toFinset := by
    ext y
    rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hz, hnn⟩
      refine ⟨hz, ?_⟩
      by_contra hnpos
      exact hbd y ⟨(mem_nonnegativeClassRegion_iff N c y).mp hnn, hnpos⟩
        (Set.mem_preimage.mp hz)
    · rintro ⟨hz, hp⟩
      exact ⟨hz, (mem_nonnegativeClassRegion_iff N c y).mp
        ((mem_positiveClassRegion_iff N c y).mp hp).nonnegative⟩
  unfold nonnegativeClassDegree localDegreeOn
  rw [hset]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [N.det_fderiv_steadyStateMap_eq_reducedJacobian_det]

set_option linter.style.haveILetI false in
/-- **The weighted count of the positive steady states of a class is the class degree**, in the
form that uses the finset of the *set* of positive steady states rather than the finset attached
to the finiteness witness.  (The two finsets coincide, by
`Set.Finite.toFinset_eq_toFinset`.) -/
theorem weightedCount_eq_classDegree_of_set (N : Network S) (κ : N.RateConstants)
    (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0) :
    letI := hfinP.fintype
    (∑ y ∈ (N.positiveSteadyStates_in_class κ c).toFinset,
        ((SignType.sign (N.reducedJacobian κ c y).det : SignType) : ℤ))
      = N.nonnegativeClassDegree κ c hfinN := by
  letI := hfinP.fintype
  rw [← Set.Finite.toFinset_eq_toFinset hfinP]
  exact weightedCount_eq_classDegree N κ c hfinN hfinP hbd

/-! ## The parity theorem without the nondegeneracy hypothesis -/

/-- **The number of positive steady states of the class at which the reduced Jacobian is
nondegenerate** (i.e. invertible, so that the local degree there is `±1`). -/
noncomputable def card_nondegeneratePositiveSteadyStates_in_class (N : Network S)
    (κ : N.RateConstants) (c : Concentration S)
    (hfin : (N.positiveSteadyStates_in_class κ c).Finite) : ℕ :=
  (hfin.toFinset.filter fun y => (N.reducedJacobian κ c y).det ≠ 0).card

/-- **The class degree is the number of the nondegenerate positive steady states minus twice the
number of those at which the reduced Jacobian determinant is negative.**

This is the identity behind the parity theorem, and it holds **without** the nondegeneracy
hypothesis: the degenerate zeros contribute `0` to the class degree (their local degree, in the
sense of the degree machinery, is `sign 0 = 0`), and they are not counted on the left-hand side.
With the nondegeneracy hypothesis the statement specializes to
`Network.classDegree_eq_card_sub_two_mul_negCount`. -/
theorem classDegree_eq_card_nondeg_sub_two_mul_negCount
    (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0) :
    N.nonnegativeClassDegree κ c hfinN =
      (N.card_nondegeneratePositiveSteadyStates_in_class κ c hfinP : ℤ) -
        2 * (N.card_negativeReducedDet_in_class κ c hfinP : ℤ) := by
  classical
  have hset : hfinN.toFinset = hfinP.toFinset := by
    ext y
    rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hz, hnn⟩
      refine ⟨hz, ?_⟩
      by_contra hnpos
      exact hbd y ⟨(mem_nonnegativeClassRegion_iff N c y).mp hnn, hnpos⟩
        (Set.mem_preimage.mp hz)
    · rintro ⟨hz, hp⟩
      exact ⟨hz, (mem_nonnegativeClassRegion_iff N c y).mp
        ((mem_positiveClassRegion_iff N c y).mp hp).nonnegative⟩
  -- the class degree is the signed count of the signs of the reduced determinants
  have hdeg : N.nonnegativeClassDegree κ c hfinN =
      (∑ y ∈ hfinP.toFinset,
        ((SignType.sign (N.reducedJacobian κ c y).det : SignType) : ℤ)) := by
    unfold nonnegativeClassDegree localDegreeOn
    rw [hset]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [N.det_fderiv_steadyStateMap_eq_reducedJacobian_det]
  -- the signed count is the number of the positive signs minus the number of the negative ones
  have hsign := sum_sign_eq_card_pos_sub_card_neg (hfinP.toFinset)
    (fun y => (N.reducedJacobian κ c y).det)
  -- the nondegenerate zeros are the positive ones and the negative ones
  have hfilter : hfinP.toFinset.filter (fun y => (N.reducedJacobian κ c y).det ≠ 0)
      = (hfinP.toFinset.filter fun y => 0 < (N.reducedJacobian κ c y).det) ∪
        (hfinP.toFinset.filter fun y => (N.reducedJacobian κ c y).det < 0) := by
    ext y
    rw [Finset.mem_filter, Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hy, hne⟩
      rcases lt_trichotomy (N.reducedJacobian κ c y).det 0 with h | h | h
      · exact Or.inr ⟨hy, h⟩
      · exact absurd h hne
      · exact Or.inl ⟨hy, h⟩
    · rintro (h | h)
      · exact ⟨h.1, ne_of_gt h.2⟩
      · exact ⟨h.1, ne_of_lt h.2⟩
  have hdisj : Disjoint (hfinP.toFinset.filter fun y => 0 < (N.reducedJacobian κ c y).det)
      (hfinP.toFinset.filter fun y => (N.reducedJacobian κ c y).det < 0) := by
    refine Finset.disjoint_left.2 fun y hyP hyM => ?_
    have h1 := Finset.mem_filter.mp hyP
    have h2 := Finset.mem_filter.mp hyM
    linarith [h1.2, h2.2]
  have hcard : (hfinP.toFinset.filter (fun y => (N.reducedJacobian κ c y).det ≠ 0)).card
      = (hfinP.toFinset.filter fun y => 0 < (N.reducedJacobian κ c y).det).card
        + (hfinP.toFinset.filter fun y => (N.reducedJacobian κ c y).det < 0).card := by
    rw [hfilter, Finset.card_union_of_disjoint hdisj]
  have hneg : (N.card_negativeReducedDet_in_class κ c hfinP : ℤ)
      = ((hfinP.toFinset.filter fun y => (N.reducedJacobian κ c y).det < 0).card : ℤ) := by
    have h1 : N.card_negativeReducedDet_in_class κ c hfinP
        = (hfinP.toFinset.filter fun y => (N.reducedJacobian κ c y).det < 0).card := rfl
    rw [h1]
  have h1 : N.card_nondegeneratePositiveSteadyStates_in_class κ c hfinP
      = (hfinP.toFinset.filter (fun y => (N.reducedJacobian κ c y).det ≠ 0)).card := rfl
  rw [hdeg, hsign, h1, hcard, hneg]
  rw [Nat.cast_add]
  ring

/-- **The parity of the number of nondegenerate positive steady states is the parity of the class
degree.**  This is the form of the parity theorem that survives *without* the nondegeneracy
hypothesis: the count is that of the positive steady states at which the reduced Jacobian is
invertible, and the class degree is the signed count of the local degrees over all the zeros of
the class. -/
theorem card_nondegenerate_positiveSteadyStates_odd_iff_classDegree_odd
    (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0) :
    Odd (N.card_nondegeneratePositiveSteadyStates_in_class κ c hfinP : ℤ) ↔
      Odd (N.nonnegativeClassDegree κ c hfinN) := by
  have hkey := N.classDegree_eq_card_nondeg_sub_two_mul_negCount κ c hfinN hfinP hbd
  have hcount : (N.card_nondegeneratePositiveSteadyStates_in_class κ c hfinP : ℤ)
      = N.nonnegativeClassDegree κ c hfinN
        + 2 * (N.card_negativeReducedDet_in_class κ c hfinP : ℤ) := by
    rw [hkey]
    ring
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    refine ⟨k - (N.card_negativeReducedDet_in_class κ c hfinP : ℤ), ?_⟩
    rw [hkey, hk]
    ring
  · intro h
    obtain ⟨k, hk⟩ := h
    refine ⟨k + (N.card_negativeReducedDet_in_class κ c hfinP : ℤ), ?_⟩
    rw [hcount, hk]
    ring

/-- **The even case of the parity theorem without the nondegeneracy hypothesis.** -/
theorem card_nondegenerate_positiveSteadyStates_even_iff_classDegree_even
    (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0) :
    Even (N.card_nondegeneratePositiveSteadyStates_in_class κ c hfinP : ℤ) ↔
      Even (N.nonnegativeClassDegree κ c hfinN) := by
  have hkey := N.classDegree_eq_card_nondeg_sub_two_mul_negCount κ c hfinN hfinP hbd
  have hcount : (N.card_nondegeneratePositiveSteadyStates_in_class κ c hfinP : ℤ)
      = N.nonnegativeClassDegree κ c hfinN
        + 2 * (N.card_negativeReducedDet_in_class κ c hfinP : ℤ) := by
    rw [hkey]
    ring
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    refine ⟨k - (N.card_negativeReducedDet_in_class κ c hfinP : ℤ), ?_⟩
    rw [hkey, hk]
    ring
  · intro h
    obtain ⟨k, hk⟩ := h
    refine ⟨k + (N.card_negativeReducedDet_in_class κ c hfinP : ℤ), ?_⟩
    rw [hcount, hk]
    ring

/-! ## Two positive steady states of opposite signs -/

/-- **The two opposite local degrees cancel in the class degree.**

Let `y₁` and `y₂` be two positive steady states of the class with opposite signs of the reduced
Jacobian determinant.  Their local degrees are `+1` and `−1`, so they cancel: the class degree is
the signed count of the local degrees over the *remaining* zeros of the class.

This is the exact content of the "the two opposite local degrees cancel" argument.  Note that it
does *not* force the number of positive steady states to be even: the remaining zeros contribute
the class degree, whose parity is the parity of the number of positive steady states
(`Network.card_positiveSteadyStates_odd_iff_classDegree_odd`), and the class degree may well be
odd.  See the namespace `CRNT.Network.OppositeSignsCounterexample` in this module for the
ingredients of an explicit counterexample. -/
theorem classDegree_eq_sum_erase_two_opposite_signs
    (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0)
    (y₁ y₂ : ClassCoord N)
    (hy₁ : y₁ ∈ N.positiveSteadyStates_in_class κ c)
    (hy₂ : y₂ ∈ N.positiveSteadyStates_in_class κ c)
    (hne : y₁ ≠ y₂)
    (hpos : 0 < (N.reducedJacobian κ c y₁).det)
    (hneg : (N.reducedJacobian κ c y₂).det < 0) :
    N.nonnegativeClassDegree κ c hfinN =
      (∑ y ∈ (hfinP.toFinset.erase y₁).erase y₂,
        ((SignType.sign (N.reducedJacobian κ c y).det : SignType) : ℤ)) := by
  classical
  have hset : hfinN.toFinset = hfinP.toFinset := by
    ext y
    rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hz, hnn⟩
      refine ⟨hz, ?_⟩
      by_contra hnpos
      exact hbd y ⟨(mem_nonnegativeClassRegion_iff N c y).mp hnn, hnpos⟩
        (Set.mem_preimage.mp hz)
    · rintro ⟨hz, hp⟩
      exact ⟨hz, (mem_nonnegativeClassRegion_iff N c y).mp
        ((mem_positiveClassRegion_iff N c y).mp hp).nonnegative⟩
  have hdeg : N.nonnegativeClassDegree κ c hfinN =
      (∑ y ∈ hfinP.toFinset,
        ((SignType.sign (N.reducedJacobian κ c y).det : SignType) : ℤ)) := by
    unfold nonnegativeClassDegree localDegreeOn
    rw [hset]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [N.det_fderiv_steadyStateMap_eq_reducedJacobian_det]
  have hy₁mem : y₁ ∈ hfinP.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact hy₁
  have hy₂mem : y₂ ∈ hfinP.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact hy₂
  have hy₂mem' : y₂ ∈ hfinP.toFinset.erase y₁ := by
    rw [Finset.mem_erase]
    exact ⟨fun h => hne h.symm, hy₂mem⟩
  have h1 : (∑ y ∈ hfinP.toFinset,
        ((SignType.sign (N.reducedJacobian κ c y).det : SignType) : ℤ))
      = ((SignType.sign (N.reducedJacobian κ c y₁).det : SignType) : ℤ)
        + (∑ y ∈ hfinP.toFinset.erase y₁,
          ((SignType.sign (N.reducedJacobian κ c y).det : SignType) : ℤ)) := by
    have h := Finset.sum_erase_add hfinP.toFinset
      (fun y : ClassCoord N => ((SignType.sign (N.reducedJacobian κ c y).det : SignType) : ℤ))
      hy₁mem
    linarith
  have h2 : (∑ y ∈ hfinP.toFinset.erase y₁,
        ((SignType.sign (N.reducedJacobian κ c y).det : SignType) : ℤ))
      = ((SignType.sign (N.reducedJacobian κ c y₂).det : SignType) : ℤ)
        + (∑ y ∈ (hfinP.toFinset.erase y₁).erase y₂,
          ((SignType.sign (N.reducedJacobian κ c y).det : SignType) : ℤ)) := by
    have h := Finset.sum_erase_add (hfinP.toFinset.erase y₁)
      (fun y : ClassCoord N => ((SignType.sign (N.reducedJacobian κ c y).det : SignType) : ℤ))
      hy₂mem'
    linarith
  have hg₁ : ((SignType.sign (N.reducedJacobian κ c y₁).det : SignType) : ℤ) = 1 := by
    rw [sign_pos hpos]
    rfl
  have hg₂ : ((SignType.sign (N.reducedJacobian κ c y₂).det : SignType) : ℤ) = -1 := by
    rw [sign_neg hneg]
    rfl
  rw [hdeg, h1, h2, hg₁, hg₂]
  ring

/-- **A class whose only positive steady states are two with opposite signs has class degree
zero.**  The two local degrees `+1` and `−1` cancel, and there is nothing else. -/
theorem classDegree_eq_zero_of_exactly_two_opposite_signs
    (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0)
    (y₁ y₂ : ClassCoord N)
    (hy₁ : y₁ ∈ N.positiveSteadyStates_in_class κ c)
    (hy₂ : y₂ ∈ N.positiveSteadyStates_in_class κ c)
    (hne : y₁ ≠ y₂)
    (hpos : 0 < (N.reducedJacobian κ c y₁).det)
    (hneg : (N.reducedJacobian κ c y₂).det < 0)
    (hexact : hfinP.toFinset = {y₁, y₂}) :
    N.nonnegativeClassDegree κ c hfinN = 0 := by
  have h := N.classDegree_eq_sum_erase_two_opposite_signs κ c hfinN hfinP hbd y₁ y₂
    hy₁ hy₂ hne hpos hneg
  rw [h, hexact]
  have hempty : ((({y₁, y₂} : Finset (ClassCoord N)).erase y₁).erase y₂) = ∅ := by
    ext z
    rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz2, hz1, hz⟩
      rcases hz with rfl | rfl
      · exact absurd hz1 (fun h => h rfl)
      · exact absurd hz2 (fun h => h rfl)
    · intro hz
      exact absurd hz (by simp)
  rw [hempty]
  simp

/-- **A class with exactly two positive steady states of opposite reduced-Jacobian signs carries
an even number of positive steady states.**  This is the form of the statement that holds when
the two opposite-sign steady states are *all* the positive steady states of the class: the class
degree is then zero (`Network.classDegree_eq_zero_of_exactly_two_opposite_signs`), and the parity
theorem gives that the number of positive steady states is even. -/
theorem card_positiveSteadyStates_even_of_exactly_two_opposite_signs
    (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0)
    (hnd : ∀ y ∈ N.positiveSteadyStates_in_class κ c, (N.reducedJacobian κ c y).det ≠ 0)
    (y₁ y₂ : ClassCoord N)
    (hy₁ : y₁ ∈ N.positiveSteadyStates_in_class κ c)
    (hy₂ : y₂ ∈ N.positiveSteadyStates_in_class κ c)
    (hne : y₁ ≠ y₂)
    (hpos : 0 < (N.reducedJacobian κ c y₁).det)
    (hneg : (N.reducedJacobian κ c y₂).det < 0)
    (hexact : hfinP.toFinset = {y₁, y₂}) :
    Even (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ) := by
  have hdeg : N.nonnegativeClassDegree κ c hfinN = 0 :=
    N.classDegree_eq_zero_of_exactly_two_opposite_signs κ c hfinN hfinP hbd y₁ y₂
      hy₁ hy₂ hne hpos hneg hexact
  have hiff := N.card_positiveSteadyStates_even_iff_classDegree_even κ c hfinN hfinP hbd hnd
  rw [hiff]
  refine ⟨0, by rw [hdeg]; ring⟩

/-- **Two distinct positive steady states of the class give at least two positive steady
states.** -/
theorem card_positiveSteadyStates_ge_two_of_two_mem
    (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (y₁ y₂ : ClassCoord N)
    (hy₁ : y₁ ∈ N.positiveSteadyStates_in_class κ c)
    (hy₂ : y₂ ∈ N.positiveSteadyStates_in_class κ c)
    (hne : y₁ ≠ y₂) :
    2 ≤ N.card_positiveSteadyStates_in_class κ c hfinP := by
  have hy₁mem : y₁ ∈ hfinP.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact hy₁
  have hy₂mem : y₂ ∈ hfinP.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact hy₂
  have hsub : ({y₁, y₂} : Finset (ClassCoord N)) ⊆ hfinP.toFinset := by
    intro y hy
    have hy' : y = y₁ ∨ y = y₂ := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hy
    rcases hy' with rfl | rfl
    · exact hy₁mem
    · exact hy₂mem
  have hcard : ({y₁, y₂} : Finset (ClassCoord N)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  have h1 : N.card_positiveSteadyStates_in_class κ c hfinP = hfinP.toFinset.card := rfl
  rw [h1]
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  exact hle

/-- **A class with two positive steady states of opposite reduced-Jacobian signs and an even
class degree carries an even number of positive steady states.**

This is the *corrected* form of the "two opposite signs ⇒ even count" statement: the two opposite
local degrees cancel in the class degree, but the class degree itself need not be even — the
remaining zeros of the class contribute the class degree, and the parity of the count is the
parity of the class degree.  With the hypothesis that the class degree is even, the count is
even as well (and there are at least two positive steady states). -/
theorem card_positiveSteadyStates_even_of_two_opposite_signs_of_even_classDegree
    (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0)
    (hnd : ∀ y ∈ N.positiveSteadyStates_in_class κ c, (N.reducedJacobian κ c y).det ≠ 0)
    (y₁ y₂ : ClassCoord N)
    (hy₁ : y₁ ∈ N.positiveSteadyStates_in_class κ c)
    (hy₂ : y₂ ∈ N.positiveSteadyStates_in_class κ c)
    (hne : y₁ ≠ y₂)
    (_hpos : 0 < (N.reducedJacobian κ c y₁).det)
    (_hneg : (N.reducedJacobian κ c y₂).det < 0)
    (hdeg : Even (N.nonnegativeClassDegree κ c hfinN)) :
    Even (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ) ∧
      2 ≤ N.card_positiveSteadyStates_in_class κ c hfinP := by
  have hiff := N.card_positiveSteadyStates_even_iff_classDegree_even κ c hfinN hfinP hbd hnd
  have heven : Even (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ) := hiff.mpr hdeg
  have hcard2 : 2 ≤ N.card_positiveSteadyStates_in_class κ c hfinP :=
    N.card_positiveSteadyStates_ge_two_of_two_mem κ c hfinP y₁ y₂ hy₁ hy₂ hne
  exact ⟨heven, hcard2⟩

/-- **The parity refinement of the Conradi–Feliu-Mincheva–Mnev–Wiuf "exceptional local degree"
criterion.**  Suppose that the class degree is odd (as it is for a fully open network, where it is
the total degree `(-1)^s`) and that the class contains two positive steady states with opposite
signs of the reduced Jacobian determinant (an "exceptional local degree").  Then the number of
positive steady states of the class is **odd**, and it is at least **three**.

This is the statement that holds in place of the "two opposite signs ⇒ even count": the two
opposite local degrees cancel in the class degree, so the *remaining* zeros contribute the class
degree, and the parity theorem (`Network.card_positiveSteadyStates_odd_iff_classDegree_odd`)
gives that the count is odd. -/
theorem card_positiveSteadyStates_odd_of_two_opposite_signs_of_odd_classDegree
    (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0)
    (hnd : ∀ y ∈ N.positiveSteadyStates_in_class κ c, (N.reducedJacobian κ c y).det ≠ 0)
    (y₁ y₂ : ClassCoord N)
    (hy₁ : y₁ ∈ N.positiveSteadyStates_in_class κ c)
    (hy₂ : y₂ ∈ N.positiveSteadyStates_in_class κ c)
    (hne : y₁ ≠ y₂)
    (_hpos : 0 < (N.reducedJacobian κ c y₁).det)
    (_hneg : (N.reducedJacobian κ c y₂).det < 0)
    (hdeg : Odd (N.nonnegativeClassDegree κ c hfinN)) :
    Odd (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ) ∧
      3 ≤ N.card_positiveSteadyStates_in_class κ c hfinP := by
  have hiff := N.card_positiveSteadyStates_odd_iff_classDegree_odd κ c hfinN hfinP hbd hnd
  have hodd : Odd (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ) := hiff.mpr hdeg
  have hcard2 : 2 ≤ N.card_positiveSteadyStates_in_class κ c hfinP :=
    N.card_positiveSteadyStates_ge_two_of_two_mem κ c hfinP y₁ y₂ hy₁ hy₂ hne
  obtain ⟨k, hk⟩ := hodd
  have h2 : (2 : ℤ) ≤ (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ) := by
    exact_mod_cast hcard2
  have hk0 : 0 ≤ k := by
    have hnonneg : (0 : ℤ) ≤ (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ) :=
      Nat.cast_nonneg _
    rw [hk] at hnonneg
    omega
  have h3 : (3 : ℤ) ≤ (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ) := by
    omega
  have h3' : 3 ≤ N.card_positiveSteadyStates_in_class κ c hfinP := by
    exact_mod_cast h3
  exact ⟨hiff.mpr hdeg, h3'⟩

/-! ## A concrete instance: the two-species fully open network -/

namespace DegreeExampleParity

open DegreeExample

/-- **The parity relation of the count and the class degree for the two-species fully open
network.**  The network is the fully open extension of the reaction-free network on two species:
the four flow reactions `0 → A`, `A → 0`, `0 → B`, `B → 0`.  Its class degree is `+1`
(`DegreeExample.nonnegativeClassDegree_eq_one`), hence odd, and it has exactly one positive
steady state (`DegreeExampleParity.card_positiveSteadyStates_eq_one`), hence an odd number of
them. -/
theorem card_positiveSteadyStates_odd_iff_classDegree_odd :
    Odd (N.card_positiveSteadyStates_in_class rates 0 hfinP : ℤ) ↔
      Odd (N.nonnegativeClassDegree rates 0 hfinN) :=
  N.card_positiveSteadyStates_odd_iff_classDegree_odd rates 0 hfinN hfinP boundary_ne_zero hnd

/-- **The even case of the parity relation for the two-species fully open network.**  Both sides
are false here (the class degree is `+1` and the count is `1`), as they should be. -/
theorem card_positiveSteadyStates_even_iff_classDegree_even :
    Even (N.card_positiveSteadyStates_in_class rates 0 hfinP : ℤ) ↔
      Even (N.nonnegativeClassDegree rates 0 hfinN) :=
  N.card_positiveSteadyStates_even_iff_classDegree_even rates 0 hfinN hfinP boundary_ne_zero hnd

/-- **The weighted count of the positive steady states of the two-species fully open network is
its class degree.** -/
theorem weightedCount_eq_classDegree :
    (∑ y ∈ hfinP.toFinset,
        ((SignType.sign (N.reducedJacobian rates 0 y).det : SignType) : ℤ))
      = N.nonnegativeClassDegree rates 0 hfinN :=
  N.weightedCount_eq_classDegree rates 0 hfinN hfinP boundary_ne_zero

/-- **The two-species fully open network has an odd number of positive steady states, and its
class degree is odd.**  This is the parity theorem of Šošić–Sibuya in the general form of this
module, on a concrete instance. -/
theorem card_positiveSteadyStates_is_odd :
    Odd (N.card_positiveSteadyStates_in_class rates 0 hfinP : ℤ) :=
  (card_positiveSteadyStates_odd_iff_classDegree_odd).mpr (by
    rw [nonnegativeClassDegree_eq_one]
    refine ⟨0, by ring⟩)

end DegreeExampleParity

/-! ## A counterexample to the "two opposite signs ⇒ even count" reading

The statement "a class with two positive steady states of opposite reduced-Jacobian signs carries
an **even** number of positive steady states" is **false**: the two opposite local degrees cancel
in the *class degree*, but the class degree is the signed count of the local degrees of the
*remaining* zeros, and its parity is the parity of the number of positive steady states
(`Network.card_positiveSteadyStates_odd_iff_classDegree_odd`).

The counterexample is the **one-species network** `∅ → A`, `A → ∅`, `2A → 3A`, `3A → 2A` with the
rate constants `6`, `11`, `6`, `1`.  Its mass-action field is

```
f(x) = 6 − 11 x + 6 x² − x³ = −(x − 1)(x − 2)(x − 3),
```

so it has exactly the three **positive** zeros `x = 1`, `x = 2`, `x = 3`
(`OppositeSignsCounterexample.massActionVectorField_eq_zero_iff`).  The stoichiometric subspace
is the whole species space (`OppositeSignsCounterexample.stoichSubspace_eq_top`) and the
stoichiometric rank is one (`OppositeSignsCounterexample.stoichRank_eq`), so the compatibility
class of the origin is the whole concentration space.

**The counterexample is machine-checked end to end.**  The namespace
`CRNT.Network.OppositeSignsCounterexample` proves:

* `OppositeSignsCounterexample.coord` — the chart coordinate of the concentration `t` in the
  class of the origin, with `OppositeSignsCounterexample.affineChart_coord` (the affine chart
  sends it back to `t`) and `OppositeSignsCounterexample.coord_injective` (the three chart
  coordinates are pairwise distinct);
* `OppositeSignsCounterexample.mem_steadyStateMap_zero_iff` — the zeros of the reduced field
  of the class of the origin are **exactly** the three chart coordinates of the concentrations
  `1`, `2`, `3`;
* `OppositeSignsCounterexample.mem_positiveSteadyStates_iff` and
  `OppositeSignsCounterexample.card_positiveSteadyStates_eq_three` — the class carries exactly
  **three** positive steady states, and the count is `3`;
* `OppositeSignsCounterexample.reducedJacobian_det` — the reduced Jacobian determinant at the
  chart coordinate of the concentration `t` is `−11 + 12 t − 3 t²`, i.e. `−2`, `+1`, `−2` at
  `t = 1, 2, 3` (through `Network.reducedJacobian_det_eq_deriv`);
* `OppositeSignsCounterexample.classDegree_eq_neg_one` — the class degree is `−1`;
* `OppositeSignsCounterexample.odd_count_with_two_opposite_signs` — the class contains two
  positive steady states of **opposite** reduced-Jacobian signs (at `t = 2` and at `t = 1`)
  while the number of positive steady states is `3`, which is **odd**.  This is the refutation
  of the "even count" reading.

The class degree `−1 = −1 + 1 − 1` is odd, in agreement with the parity relation of this
module. -/

namespace OppositeSignsCounterexample


/-- The source multiplicities of the four reactions `∅ → A`, `A → ∅`, `2A → 3A`, `3A → 2A`. -/
def sourceCount : Fin 4 → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The target multiplicities of the four reactions. -/
def targetCount : Fin 4 → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2

/-- **The one-species network `∅ → A`, `A → ∅`, `2A → 3A`, `3A → 2A`.** -/
def N : Network (Fin 1) where
  R := Fin 4
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun r => { source := fun _ => sourceCount r, target := fun _ => targetCount r }

/-- The rate constants of the network: `6`, `11`, `6`, `1`. -/
def k : Fin 4 → ℝ
  | 0 => 6
  | 1 => 11
  | 2 => 6
  | 3 => 1

/-- The rate constants of the network. -/
def rates : N.RateConstants where
  k := k
  positive r := by
    fin_cases r <;> norm_num [k]

/-- The unit vector of the species space. -/
def e₀ : Concentration (Fin 1) := fun _ => 1

/-- **The mass-action field of the network**: `x ↦ 6 − 11 x + 6 x² − x³`. -/
theorem massActionVectorField_eq (x : Concentration (Fin 1)) :
    N.massActionVectorField rates x = fun _ => 6 - 11 * x 0 + 6 * (x 0)^2 - (x 0)^3 := by
  funext s
  fin_cases s
  simp [N, sourceCount, targetCount, rates, k, Network.massActionVectorField_apply,
    Network.massActionRate, Complex.massActionMonomial, Fin.sum_univ_succ]
  ring

/-- **The polynomial `6 − 11 t + 6 t² − t³` vanishes exactly at `1`, `2`, `3`.** -/
theorem poly_eq_zero_iff (t : ℝ) :
    6 - 11 * t + 6 * t ^ 2 - t ^ 3 = 0 ↔ t = 1 ∨ t = 2 ∨ t = 3 := by
  have hid : 6 - 11 * t + 6 * t ^ 2 - t ^ 3 = -((t - 1) * (t - 2) * (t - 3)) := by
    ring
  rw [hid, neg_eq_zero]
  constructor
  · intro h
    have h' : ((t - 1) = 0 ∨ (t - 2) = 0) ∨ (t - 3) = 0 := by
      rw [mul_eq_zero, mul_eq_zero] at h
      exact h
    cases h' with
    | inl h =>
      cases h with
      | inl h =>
        left
        linarith
      | inr h =>
        right
        left
        linarith
    | inr h =>
      right
      right
      linarith
  · intro h
    cases h with
    | inl h =>
      subst h
      ring
    | inr h =>
      cases h with
      | inl h =>
        subst h
        ring
      | inr h =>
        subst h
        ring

/-- **The field vanishes exactly at the concentrations `1`, `2`, `3`.** -/
theorem massActionVectorField_eq_zero_iff (x : Concentration (Fin 1)) :
    N.massActionVectorField rates x = 0 ↔ x 0 = 1 ∨ x 0 = 2 ∨ x 0 = 3 := by
  constructor
  · intro h
    have h' := congrFun h (0 : Fin 1)
    rw [massActionVectorField_eq] at h'
    simp only [Pi.zero_apply] at h'
    exact (poly_eq_zero_iff (x 0)).mp h'
  · intro h
    have h0 : 6 - 11 * x 0 + 6 * (x 0)^2 - (x 0)^3 = 0 := by
      cases h with
      | inl h =>
        have := (poly_eq_zero_iff (x 0)).mpr (Or.inl h)
        linarith [this]
      | inr h =>
        cases h with
        | inl h =>
          have := (poly_eq_zero_iff (x 0)).mpr (Or.inr (Or.inl h))
          linarith [this]
        | inr h =>
          have := (poly_eq_zero_iff (x 0)).mpr (Or.inr (Or.inr h))
          linarith [this]
    rw [massActionVectorField_eq]
    funext s
    simp only [Pi.zero_apply]
    exact h0

/-- The reaction vector of the first reaction `∅ → A` is the unit vector. -/
theorem reactionVector_zero : N.reactionVector (0 : Fin 4) = fun _ => (1 : ℝ) := by
  funext s
  fin_cases s
  simp [N, sourceCount, targetCount, Network.reactionVector_apply]

/-- **The stoichiometric subspace is the whole space.** -/
theorem stoichSubspace_eq_top : N.stoichSubspace = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x = x 0 • N.reactionVector (0 : Fin 4) := by
    funext s
    fin_cases s
    simp [reactionVector_zero, Pi.smul_apply, smul_eq_mul]
  rw [hx]
  exact Submodule.smul_mem _ _
    (N.reactionVector_mem_stoichSubspace (0 : Fin 4))

/-- **The stoichiometric rank is one.** -/
theorem stoichRank_eq : N.stoichRank = 1 := by
  rw [Network.stoichRank, stoichSubspace_eq_top, finrank_top, Module.finrank_fin_fun]

/-- **The stoichiometric subspace is the span of the unit vector.** -/
theorem stoichSubspace_eq_span : N.stoichSubspace = Submodule.span ℝ {e₀} := by
  rw [stoichSubspace_eq_top]
  ext x
  constructor
  · intro _
    refine Submodule.mem_span_singleton.mpr ⟨x 0, ?_⟩
    funext s
    fin_cases s
    simp [e₀, Pi.smul_apply, smul_eq_mul]
  · intro _
    exact Submodule.mem_top

/-- The chart coordinate of the concentration `t`. -/
noncomputable def coord (t : ℝ) : ClassCoord N := N.chartCoord 0 (fun _ => t)

theorem coord_injective : Function.Injective coord := by
  intro a b hab
  have hcompat : N.StoichCompatible 0 (fun _ => a) := by
    rw [StoichCompatible, stoichSubspace_eq_top]
    exact Submodule.mem_top
  have hcompat' : N.StoichCompatible 0 (fun _ => b) := by
    rw [StoichCompatible, stoichSubspace_eq_top]
    exact Submodule.mem_top
  have h1 : N.chartCoord 0 (fun _ : Fin 1 => a) = N.chartCoord 0 (fun _ : Fin 1 => b) := by
    rw [← coord, ← coord]
    exact hab
  have h1' : N.affineChart 0 (N.chartCoord 0 (fun _ : Fin 1 => a))
      = N.affineChart 0 (N.chartCoord 0 (fun _ : Fin 1 => b)) := congrArg _ h1
  rw [affineChart_chartCoord N hcompat, affineChart_chartCoord N hcompat'] at h1'
  have h3 := congrFun h1' (0 : Fin 1)
  simpa using h3

theorem affineChart_coord (t : ℝ) : N.affineChart 0 (coord t) = fun _ => t := by
  have hcompat : N.StoichCompatible 0 (fun _ => t) := by
    rw [StoichCompatible, stoichSubspace_eq_top]
    exact Submodule.mem_top
  rw [coord]
  exact affineChart_chartCoord N hcompat

theorem mem_steadyStateMap_zero_iff (y : ClassCoord N) :
    N.steadyStateMap rates 0 y = 0 ↔ y = coord 1 ∨ y = coord 2 ∨ y = coord 3 := by
  constructor
  · intro hz
    have hz' : N.stoichProj (N.massActionVectorField rates (N.affineChart 0 y)) = N.stoichProj 0 := by
      rw [steadyStateMap, reducedField] at hz
      exact hz.trans (map_zero N.stoichProj).symm
    have hF : N.massActionVectorField rates (N.affineChart 0 y) = 0 :=
      stoichProj_injective_of_stoichSubspace_eq_top N stoichSubspace_eq_top hz'
    have hval : (N.affineChart 0 y) 0 = 1 ∨ (N.affineChart 0 y) 0 = 2 ∨ (N.affineChart 0 y) 0 = 3 :=
      (massActionVectorField_eq_zero_iff (N.affineChart 0 y)).mp hF
    have heq : N.affineChart 0 y = fun _ => (N.affineChart 0 y) 0 := by
      funext s
      have hs : s = 0 := Fin.ext (Nat.lt_one_iff.mp s.isLt)
      rw [hs]
    have hcoord : y = N.chartCoord 0 (N.affineChart 0 y) := (chartCoord_affineChart N 0 y).symm
    rcases hval with h | h | h
    · left
      have hfun : N.affineChart 0 y = fun _ => (1 : ℝ) := by rw [heq, h]
      rw [hfun] at hcoord
      exact hcoord
    · right; left
      have hfun : N.affineChart 0 y = fun _ => (2 : ℝ) := by rw [heq, h]
      rw [hfun] at hcoord
      exact hcoord
    · right; right
      have hfun : N.affineChart 0 y = fun _ => (3 : ℝ) := by rw [heq, h]
      rw [hfun] at hcoord
      exact hcoord
  · rintro (h | h | h)
    · subst h
      have hz : N.massActionVectorField rates (fun _ => (1 : ℝ)) = 0 :=
        (massActionVectorField_eq_zero_iff (fun _ => (1 : ℝ))).mpr (Or.inl rfl)
      rw [steadyStateMap, reducedField, affineChart_coord, hz, map_zero]
    · subst h
      have hz : N.massActionVectorField rates (fun _ => (2 : ℝ)) = 0 :=
        (massActionVectorField_eq_zero_iff (fun _ => (2 : ℝ))).mpr (Or.inr (Or.inl rfl))
      rw [steadyStateMap, reducedField, affineChart_coord, hz, map_zero]
    · subst h
      have hz : N.massActionVectorField rates (fun _ => (3 : ℝ)) = 0 :=
        (massActionVectorField_eq_zero_iff (fun _ => (3 : ℝ))).mpr (Or.inr (Or.inr rfl))
      rw [steadyStateMap, reducedField, affineChart_coord, hz, map_zero]

theorem mem_positiveSteadyStates_coord_iff (t : ℝ) :
    coord t ∈ N.positiveSteadyStates_in_class rates 0 ↔ t = 1 ∨ t = 2 ∨ t = 3 := by
  rw [Network.mem_positiveSteadyStates_in_class_iff]
  constructor
  · rintro ⟨hpos, hsteady⟩
    have hz : N.steadyStateMap rates 0 (coord t) = 0 := by
      have hF : N.massActionVectorField rates (N.affineChart 0 (coord t)) = 0 := by
        funext s
        exact hsteady s
      rw [steadyStateMap, reducedField, hF, map_zero]
    rcases (mem_steadyStateMap_zero_iff (coord t)).mp hz with h | h | h
    · left; exact coord_injective h
    · right; left; exact coord_injective h
    · right; right; exact coord_injective h
  · rintro (h | h | h)
    · subst h
      refine ⟨?_, ?_⟩
      · rw [affineChart_coord]
        intro s
        have hs : s = 0 := Fin.ext (Nat.lt_one_iff.mp s.isLt)
        rw [hs]
        norm_num
      · rw [affineChart_coord]
        intro s
        rw [massActionVectorField_eq]
        norm_num
    · subst h
      refine ⟨?_, ?_⟩
      · rw [affineChart_coord]
        intro s
        have hs : s = 0 := Fin.ext (Nat.lt_one_iff.mp s.isLt)
        rw [hs]
        norm_num
      · rw [affineChart_coord]
        intro s
        rw [massActionVectorField_eq]
        norm_num
    · subst h
      refine ⟨?_, ?_⟩
      · rw [affineChart_coord]
        intro s
        have hs : s = 0 := Fin.ext (Nat.lt_one_iff.mp s.isLt)
        rw [hs]
        norm_num
      · rw [affineChart_coord]
        intro s
        rw [massActionVectorField_eq]
        norm_num

theorem mem_positiveSteadyStates_iff (y : ClassCoord N) :
    y ∈ N.positiveSteadyStates_in_class rates 0 ↔ y = coord 1 ∨ y = coord 2 ∨ y = coord 3 := by
  constructor
  · intro hy
    exact (mem_steadyStateMap_zero_iff y).mp hy.1
  · rintro (h | h | h)
    · rw [h]; exact (mem_positiveSteadyStates_coord_iff 1).mpr (Or.inl rfl)
    · rw [h]; exact (mem_positiveSteadyStates_coord_iff 2).mpr (Or.inr (Or.inl rfl))
    · rw [h]; exact (mem_positiveSteadyStates_coord_iff 3).mpr (Or.inr (Or.inr rfl))

/-- The three chart coordinates of the three positive steady states. -/
noncomputable def threeCoords : Finset (ClassCoord N) :=
  insert (coord 1) (insert (coord 2) (insert (coord 3) ∅))

theorem mem_threeCoords (y : ClassCoord N) :
    y ∈ threeCoords ↔ y = coord 1 ∨ y = coord 2 ∨ y = coord 3 := by
  simp [threeCoords]

theorem hfinP : (N.positiveSteadyStates_in_class rates 0).Finite := by
  have hset : N.positiveSteadyStates_in_class rates 0 = (↑threeCoords : Set (ClassCoord N)) := by
    ext y
    constructor
    · intro hy
      exact (mem_threeCoords y).mpr ((mem_positiveSteadyStates_iff y).mp hy)
    · intro hy
      exact (mem_positiveSteadyStates_iff y).mpr ((mem_threeCoords y).mp hy)
  rw [hset]
  exact Finset.finite_toSet threeCoords

theorem toFinset_eq_threeCoords (h : (N.positiveSteadyStates_in_class rates 0).Finite) :
    h.toFinset = threeCoords := by
  ext y
  rw [Set.Finite.mem_toFinset]
  constructor
  · intro hy
    exact (mem_threeCoords y).mpr ((mem_positiveSteadyStates_iff y).mp hy)
  · intro hy
    exact (mem_positiveSteadyStates_iff y).mpr ((mem_threeCoords y).mp hy)

/-- **The reduced Jacobian determinant at the chart coordinate of the concentration `t`** is the
derivative of the scalar field along the class, `-11 + 12 t - 3 t²`. -/
theorem reducedJacobian_det (t : ℝ) :
    (N.reducedJacobian rates 0 (coord t)).det = -11 + 12 * t - 3 * t ^ 2 := by
  have hcard : N.stoichRank = 1 := stoichRank_eq
  have hspan : N.stoichSubspace = Submodule.span ℝ {e₀} := stoichSubspace_eq_span
  have hi₀ : e₀ (0 : Fin 1) ≠ 0 := by simp [e₀]
  have hconc : (0 : Concentration (Fin 1)) + t • e₀ = (fun _ => t) := by
    funext s
    simp [e₀, Pi.smul_apply, smul_eq_mul, zero_add]
  have hchart : N.chartCoord 0 (0 + t • e₀) = coord t := by
    rw [hconc, coord]
  have hline : N.lineField rates 0 e₀ 0
      = (fun u : ℝ => 6 - 11 * u + 6 * u ^ 2 - u ^ 3) := by
    funext u
    have h1 : (0 : Concentration (Fin 1)) + u • e₀ = (fun _ => u) := by
      funext s
      simp [e₀, Pi.smul_apply, smul_eq_mul, zero_add]
    rw [lineField, h1, massActionVectorField_eq]
    have he₀ : e₀ (0 : Fin 1) = 1 := by simp [e₀]
    rw [he₀]
    simp
  have hderiv : HasDerivAt (fun u : ℝ => 6 - 11 * u + 6 * u ^ 2 - u ^ 3)
      (-11 + 12 * t - 3 * t ^ 2) t := by
    have hid : HasDerivAt (fun u : ℝ => u) 1 t := hasDerivAt_id t
    have hmul := (hasDerivAt_const t 11).mul hid
    have hp2 := hid.pow 2
    have hp3 := hid.pow 3
    have h6p2 := (hasDerivAt_const t 6).mul hp2
    have hA := ((hasDerivAt_const t 6).sub hmul).add h6p2
    have hB := hA.sub hp3
    convert hB using 1
    ring
  rw [← hchart]
  rw [reducedJacobian_det_eq_deriv N rates hcard hspan hi₀ 0 t]
  rw [hline]
  exact hderiv.deriv

theorem mem_nonnegativeClassRegion_zero_iff (y : ClassCoord N) :
    (y ∈ N.steadyStateMap rates 0 ⁻¹' {0} ∩ N.nonnegativeClassRegion 0) ↔
      y = coord 1 ∨ y = coord 2 ∨ y = coord 3 := by
  rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
    mem_nonnegativeClassRegion_iff]
  constructor
  · rintro ⟨hz, _⟩
    exact (mem_steadyStateMap_zero_iff y).mp hz
  · rintro (h | h | h)
    · refine ⟨?_, ?_⟩
      · rw [h]; exact (mem_steadyStateMap_zero_iff (coord 1)).mpr (Or.inl rfl)
      · rw [h, affineChart_coord]
        intro s
        have hs : s = 0 := Fin.ext (Nat.lt_one_iff.mp s.isLt)
        rw [hs]
        norm_num
    · refine ⟨?_, ?_⟩
      · rw [h]; exact (mem_steadyStateMap_zero_iff (coord 2)).mpr (Or.inr (Or.inl rfl))
      · rw [h, affineChart_coord]
        intro s
        have hs : s = 0 := Fin.ext (Nat.lt_one_iff.mp s.isLt)
        rw [hs]
        norm_num
    · refine ⟨?_, ?_⟩
      · rw [h]; exact (mem_steadyStateMap_zero_iff (coord 3)).mpr (Or.inr (Or.inr rfl))
      · rw [h, affineChart_coord]
        intro s
        have hs : s = 0 := Fin.ext (Nat.lt_one_iff.mp s.isLt)
        rw [hs]
        norm_num

theorem hfinN : (N.steadyStateMap rates 0 ⁻¹' {0} ∩ N.nonnegativeClassRegion 0).Finite := by
  have h1 : N.steadyStateMap rates 0 ⁻¹' {0} ∩ N.nonnegativeClassRegion 0
      ⊆ (↑threeCoords : Set (ClassCoord N)) := by
    intro y hy
    exact (mem_threeCoords y).mpr ((mem_nonnegativeClassRegion_zero_iff y).mp hy)
  exact (Finset.finite_toSet threeCoords).subset h1

theorem toFinset_eq_threeCoordsN
    (h : (N.steadyStateMap rates 0 ⁻¹' {0} ∩ N.nonnegativeClassRegion 0).Finite) :
    h.toFinset = threeCoords := by
  ext y
  rw [Set.Finite.mem_toFinset]
  constructor
  · intro hy
    exact (mem_threeCoords y).mpr ((mem_nonnegativeClassRegion_zero_iff y).mp hy)
  · intro hy
    exact (mem_nonnegativeClassRegion_zero_iff y).mpr ((mem_threeCoords y).mp hy)

theorem coord_ne_12 : coord 1 ≠ coord 2 := fun h => absurd (coord_injective h) (by norm_num)

theorem coord_ne_13 : coord 1 ≠ coord 3 := fun h => absurd (coord_injective h) (by norm_num)

theorem coord_ne_23 : coord 2 ≠ coord 3 := fun h => absurd (coord_injective h) (by norm_num)

theorem not_mem_1 : coord 1 ∉ insert (coord 2) (insert (coord 3) (∅ : Finset (ClassCoord N))) := by
  simp [coord_ne_12, coord_ne_13]

theorem not_mem_2 : coord 2 ∉ insert (coord 3) (∅ : Finset (ClassCoord N)) := by
  simp [coord_ne_23]

theorem not_mem_3 : coord 3 ∉ (∅ : Finset (ClassCoord N)) := by simp

theorem card_threeCoords : threeCoords.card = 3 := by
  rw [threeCoords, Finset.card_insert_of_notMem not_mem_1,
    Finset.card_insert_of_notMem not_mem_2, Finset.card_insert_of_notMem not_mem_3]
  norm_num

theorem card_positiveSteadyStates_eq_three :
    N.card_positiveSteadyStates_in_class rates 0 hfinP = 3 := by
  have h : N.card_positiveSteadyStates_in_class rates 0 hfinP = hfinP.toFinset.card := rfl
  rw [h, toFinset_eq_threeCoords hfinP]
  exact card_threeCoords

theorem classDegree_eq_neg_one
    (hfinN : (N.steadyStateMap rates 0 ⁻¹' {0} ∩ N.nonnegativeClassRegion 0).Finite) :
    N.nonnegativeClassDegree rates 0 hfinN = -1 := by
  have hset := toFinset_eq_threeCoordsN hfinN
  unfold nonnegativeClassDegree localDegreeOn
  rw [hset]
  simp only [threeCoords]
  rw [Finset.sum_insert not_mem_1, Finset.sum_insert not_mem_2, Finset.sum_insert not_mem_3]
  simp
  have g1 : ((SignType.sign (LinearMap.det
      (fderiv ℝ (N.steadyStateMap rates 0) (coord 1)).toLinearMap) : SignType) : ℤ) = -1 := by
    rw [N.det_fderiv_steadyStateMap_eq_reducedJacobian_det, reducedJacobian_det 1]
    rw [sign_neg (by norm_num)]
    rw [SignType.coe_neg_one]
  have g2 : ((SignType.sign (LinearMap.det
      (fderiv ℝ (N.steadyStateMap rates 0) (coord 2)).toLinearMap) : SignType) : ℤ) = 1 := by
    rw [N.det_fderiv_steadyStateMap_eq_reducedJacobian_det, reducedJacobian_det 2]
    rw [sign_pos (by norm_num)]
    rw [SignType.coe_one]
  have g3 : ((SignType.sign (LinearMap.det
      (fderiv ℝ (N.steadyStateMap rates 0) (coord 3)).toLinearMap) : SignType) : ℤ) = -1 := by
    rw [N.det_fderiv_steadyStateMap_eq_reducedJacobian_det, reducedJacobian_det 3]
    rw [sign_neg (by norm_num)]
    rw [SignType.coe_neg_one]
  rw [g1, g2, g3]
  ring

theorem odd_count_with_two_opposite_signs :
    (∃ y₁ y₂ : ClassCoord N, y₁ ∈ N.positiveSteadyStates_in_class rates 0 ∧
      y₂ ∈ N.positiveSteadyStates_in_class rates 0 ∧ y₁ ≠ y₂ ∧
      0 < (N.reducedJacobian rates 0 y₁).det ∧
        (N.reducedJacobian rates 0 y₂).det < 0) ∧
      Odd (N.card_positiveSteadyStates_in_class rates 0 hfinP : ℤ) := by
  refine ⟨⟨coord 2, coord 1, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (mem_positiveSteadyStates_coord_iff 2).mpr (Or.inr (Or.inl rfl))
  · exact (mem_positiveSteadyStates_coord_iff 1).mpr (Or.inl rfl)
  · exact coord_ne_12.symm
  · rw [reducedJacobian_det 2]; norm_num
  · rw [reducedJacobian_det 1]; norm_num
  · rw [card_positiveSteadyStates_eq_three]
    exact ⟨1, by norm_num⟩

end OppositeSignsCounterexample

#print axioms CRNT.Network.card_positiveSteadyStates_odd_iff_classDegree_odd
#print axioms CRNT.Network.card_positiveSteadyStates_even_iff_classDegree_even
#print axioms CRNT.Network.weightedCount_eq_classDegree
#print axioms CRNT.Network.classDegree_eq_card_nondeg_sub_two_mul_negCount
#print axioms CRNT.Network.card_nondegenerate_positiveSteadyStates_odd_iff_classDegree_odd
#print axioms CRNT.Network.classDegree_eq_sum_erase_two_opposite_signs
#print axioms CRNT.Network.card_positiveSteadyStates_odd_of_two_opposite_signs_of_odd_classDegree
#print axioms CRNT.Network.OppositeSignsCounterexample.mem_steadyStateMap_zero_iff
#print axioms CRNT.Network.OppositeSignsCounterexample.mem_positiveSteadyStates_iff
#print axioms CRNT.Network.OppositeSignsCounterexample.reducedJacobian_det
#print axioms CRNT.Network.OppositeSignsCounterexample.card_positiveSteadyStates_eq_three
#print axioms CRNT.Network.OppositeSignsCounterexample.classDegree_eq_neg_one
#print axioms CRNT.Network.OppositeSignsCounterexample.odd_count_with_two_opposite_signs

end Network

end CRNT

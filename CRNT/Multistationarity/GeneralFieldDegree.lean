import CRNT.Multistationarity.TotalDegreeGeneral

/-
# The degree at infinity of a general mass-action field

This module attacks the field-map leaf **M9** ("degree theory") of the CRNT-Lean campaign: the
Conradi–Feliu–Mincheva–Wiuf *total-degree theorem* for a general (not merely affine) mass-action
field.

## What the library had, and what is missing

`CRNT.Multistationarity.TotalDegreeGeneral` proves the total-degree theorem under the hypothesis
that the mass-action field is **affine**, `x ↦ source + M x` with `M` an invertible linear
operator:

* `Network.fullyOpen_classDegree_of_affineLinear` — the class degree of the reduced field on the
  nonnegative part of the class is `sign (det M)`;
* `Network.fullyOpen_exists_positiveSteadyState_of_affineLinear` — the Conradi–Feliu–Mincheva–Wiuf
  existence step (leaf **M9**), and
* `Network.fullyOpen_card_positiveSteadyStates_odd_of_affineLinear` — the Šošić–Sibuya parity
  theorem (leaf **S19**).

The affine hypothesis is the restrictive one: a general mass-action field is a **polynomial** in the
concentrations, and for bimolecular reactions it is *quadratic*.  The theorem proved above
therefore does **not** cover the general mass-action case.

## What this module proves

1. **The structural lemma** (`Network.QuadraticFieldGeneral`,
   `Network.massActionVectorField_eq_quadraticGeneral`): every mass-action field is the sum of a
   constant part, a linear part and a nonlinear remainder, `x ↦ source + M x + R x`.  The constant
   part is the value of the field at the origin, the linear part is the derivative of the field at
   the origin, and the remainder is exactly the part of the field that is *not* of degree `≤ 1`.

2. **The bridge** (`Network.quadraticFieldGeneral_of_affineFieldGeneral`,
   `Network.affineFieldGeneral_of_quadraticFieldGeneral`): the affine hypothesis is precisely the
   case in which the nonlinear remainder vanishes; this pins down rigorously that `Q = 0` is the
   affine case, and it is what the rest of the module uses.

3. **The degree-at-infinity machinery for a quadratic field**: the homotopy
   `x ↦ source + M x + t · R x` that scales the nonlinear part, its reduced-field version, the
   boundary non-vanishing hypothesis (`Network.NonvanishingOnClassBoundary`), the endpoint
   identities, the continuity of the homotopy, and the correct generalisation of the affine theorem
   (`Network.fullyOpen_classDegree_of_quadraticGeneral_of_unique_zero`): the class degree is the
   orientation sign of the Jacobian determinant at the (unique) zero of the reduced field.

4. **A counterexample** (`Network.CounterexampleQuadratic`): the naive generalisation
   "`class degree = sign (det M)`" is **false** for a quadratic field; the correct invariant is
   the *degree at infinity* of the field, which for a quadratic leading part is the BKK /
   mixed-volume count and not the sign of the determinant of the linear part.  The counterexample
   is the one-species fully open network with the reaction `2A → 3A`: its field is `1 - x + x²`,
   which has an invertible linear part and a nonnegative zero of its linear part (`x = 1`), yet it
   has **no** positive steady state at all (its class degree is `0`).

## The scope of the result, and what is still missing

The genuinely open part is unchanged by this module: the *degree at infinity* of a field whose
leading homogeneous part has degree `≥ 2` — the mixed-volume / Bernstein count of the BKK theory,
which is the heart of the Conradi–Feliu–Mincheva–Wiuf theorem — is still missing.  What this module
provides is the structural decomposition that the missing theorem must be applied to, the homotopy
along which the degree is transported, and the statement of the analytic hypothesis (invariance of
the *relative* degree along that homotopy) that is still to be discharged.

In particular, the naive generalisation

`fullyOpen_classDegree_of_quadraticGeneral`: *the class degree of a fully open network with a
quadratic field is the sign of the determinant of its linear part*

is **false**, and `Network.CounterexampleQuadratic.classDegree_ne_sign_det` is a machine-checked
counterexample: the one-species fully open network with the reaction `2A → 3A` has the field
`1 - x + x²`, an invertible linear part `-x` and a nonnegative zero `x = 1` of its linear part, and
yet its class degree is `0` (the field has no real zero).  The reason is structural: along the
homotopy `x ↦ 1 - x + t x²` the zeros of the field escape to infinity as `t → 0`, so the class
degree is *not* transported from the affine slice to the quadratic slice; the invariant of the
Conradi–Feliu–Mincheva–Wiuf theorem is the **total degree of the reduced determinant**, i.e. the
BKK count of the quadratic leading part, and not the sign of the determinant of the linear part.

## Dependencies

`CRNT.Multistationarity.TotalDegreeGeneral` (the affine total-degree theorem and the transport to
the class coordinates), through it `CRNT.Multistationarity.DegreeExistence` (the relative class
degree), `CRNT.Multistationarity.DegreeStructural` (the local degree at a unique zero),
`CRNT.Multistationarity.DegreeMultistationarity` (the perturbation argument) and
`CRNT.Multistationarity.ParityOfSteadyStates` (the fully open boundary non-vanishing).
-/

namespace CRNT

/-! ## The monomials of the mass-action field -/

namespace Complex

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The mass-action monomial of a singleton complex** `e_s` is the coordinate `x s`.

This is the algebraic content of the fact that a *unimolecular* reaction has a **linear** rate:
the source monomial of `e_s` is the linear monomial `x s`. -/
theorem massActionMonomial_singleton (s : S) (x : Concentration S) :
    massActionMonomial (Pi.single s 1) x = x s := by
  rw [massActionMonomial]
  have h : ∀ t : S, (x t) ^ (Pi.single s 1 t) = if t = s then x t else 1 := by
    intro t
    by_cases hts : t = s
    · subst hts
      simp
    · simp [hts]
  rw [Finset.prod_congr rfl (fun t _ => h t)]
  rw [Finset.prod_ite_eq' Finset.univ s (fun t => x t)]
  simp

omit [DecidableEq S] in
/-- **The mass-action monomial at the zero concentration** is `1` for the empty complex and `0` for
every other complex.

This is the algebraic content of the fact that a reaction with an **empty source complex**
(`0 → s`, the inflow pseudo-reaction of the fully open extension) has a *constant* rate, while
every other reaction has a rate vanishing at the origin. -/
theorem massActionMonomial_at_zero (c : Complex S) :
    massActionMonomial c 0 = if c = Complex.zero then 1 else 0 := by
  by_cases h : c = Complex.zero
  · subst h
    simp [massActionMonomial_zero]
  · rw [massActionMonomial]
    have hex : ∃ s : S, c s ≠ 0 := by
      by_contra hcon
      have hall : ∀ s : S, c s = 0 := by
        intro s
        by_contra hs
        exact hcon ⟨s, hs⟩
      exact h (funext hall)
    obtain ⟨s, hs⟩ := hex
    have hzero : (0 : ℝ) ^ (c s) = 0 := (pow_eq_zero_iff hs).mpr rfl
    rw [Finset.prod_eq_zero (Finset.mem_univ s) hzero]
    simp [h]

end Complex

namespace Network

open scoped BigOperators Topology Classical

open Set Filter

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## The degree-one part of a source monomial -/

/-- **The degree-one part of the mass-action monomial of a complex**: the function `x ↦ x u` when
the complex is the singleton `e_u`, and the zero function otherwise.  This is the part of the
source monomial that survives in the *linear* part of the mass-action field. -/
noncomputable def complexLinearPart (c : Complex S) (x : Concentration S) : ℝ :=
  ∑ u : S, if c = Pi.single u 1 then x u else 0

/-- The degree-one part of a source monomial is linear in the concentration. -/
theorem complexLinearPart_add (c : Complex S) (x y : Concentration S) :
    complexLinearPart c (x + y) = complexLinearPart c x + complexLinearPart c y := by
  unfold complexLinearPart
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : c = Pi.single u 1
  · simp [h]
  · simp [h]

/-- The degree-one part of a source monomial is homogeneous of degree one. -/
theorem complexLinearPart_smul (c : Complex S) (a : ℝ) (x : Concentration S) :
    complexLinearPart c (a • x) = a * complexLinearPart c x := by
  unfold complexLinearPart
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : c = Pi.single u 1
  · simp [h]
  · simp [h]

/-- **The degree-one part of the source monomial of a singleton complex** `e_u` is the coordinate
`x u`. -/
theorem complexLinearPart_singleton (u : S) (x : Concentration S) :
    complexLinearPart (Pi.single u 1) x = x u := by
  unfold complexLinearPart
  have h : (∑ v : S, (if (Pi.single u 1 : Complex S) = Pi.single v 1 then x v else 0))
      = (if (Pi.single u 1 : Complex S) = Pi.single u 1 then x u else 0) := by
    refine Finset.sum_eq_single_of_mem u (Finset.mem_univ u) (fun v _ hv => ?_)
    have hne : (Pi.single u 1 : Complex S) ≠ Pi.single v 1 := by
      intro hcon
      have hone := congrArg (fun f : S → ℕ => f u) hcon
      by_cases huv : u = v
      · exact absurd huv.symm hv
      · simp [huv] at hone
    simp [hne]
  simpa using h

/-- **The degree-one part of the source monomial of the empty complex is zero.** -/
theorem complexLinearPart_zero (c : Complex S) :
    complexLinearPart c 0 = 0 := by
  unfold complexLinearPart
  simp

/-! ## The quadratic structure of a mass-action field -/

/-- **A mass-action field in quadratic form.**

The field of a mass-action network is a polynomial in the concentrations.  This structure records
the decomposition of such a field into its constant part, its linear part and its *nonlinear
remainder*, the quadratic part of the field.

* `source` — the constant part of the field;
* `M` — the linear part of the field, an operator on the species space;
* `Q` — the nonlinear remainder; it is evaluated on the diagonal, `Q x x`, so that the field
  equation reads `source s + M x s + (Q x x) s`.

The second slot of `Q` is the slot in which the quadratic form is evaluated; for the canonical
decomposition of a mass-action field (`Network.quadraticFieldGeneral_of_massAction`) the remainder
is a function of the concentration alone, and the second slot is a dummy.

Note that the linear part `M` is **singular in general**: it is supported on the unimolecular
reactions, whose number is at most the number of reactions.  No injectivity of `M` is assumed
here; that is the extra hypothesis of `Network.AffineFieldGeneral`. -/
structure QuadraticFieldGeneral (N : Network S) (κ : N.RateConstants) where
  /-- The constant part of the field. -/
  source : Concentration S
  /-- The linear part of the field. -/
  M : Concentration S →L[ℝ] Concentration S
  /-- The nonlinear remainder of the field, evaluated on the diagonal. -/
  Q : Concentration S → Concentration S → Concentration S
  /-- The field is `source + M x + Q x x`. -/
  eq_field : ∀ x s, N.massActionVectorField κ x s = source s + M x s + Q x x s

/-- **The canonical decomposition of which every mass-action field admits one.** -/
noncomputable def massActionConstantPart (N : Network S) (κ : N.RateConstants) : Concentration S :=
  N.massActionVectorField κ 0

/-- **The linear part of the mass-action field.**  It is supported on the *unimolecular* reactions:
a reaction whose source complex is not a singleton contributes nothing to it. -/
noncomputable def massActionLinearPartFun (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) : Concentration S :=
  fun s => ∑ r : N.R, κ.k r * complexLinearPart (N.reaction r).source x * N.reactionVector r s

/-- **The linear part of the mass-action field, as a linear map.** -/
noncomputable def massActionLinearMap (N : Network S) (κ : N.RateConstants) :
    Concentration S →ₗ[ℝ] Concentration S where
  toFun := massActionLinearPartFun N κ
  map_add' := by
    intro x y
    funext s
    simp only [massActionLinearPartFun, Pi.add_apply]
    have hlin : ∀ r : N.R, complexLinearPart (N.reaction r).source (x + y)
        = complexLinearPart (N.reaction r).source x + complexLinearPart (N.reaction r).source y :=
      fun r => complexLinearPart_add (N.reaction r).source x y
    simp only [hlin]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    ring
  map_smul' := by
    intro a x
    funext s
    simp only [massActionLinearPartFun, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have hlin : ∀ r : N.R, complexLinearPart (N.reaction r).source (a • x)
        = a * complexLinearPart (N.reaction r).source x :=
      fun r => complexLinearPart_smul (N.reaction r).source a x
    simp only [hlin]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring

/-- **The linear part of the mass-action field, as a continuous linear map.** -/
noncomputable def massActionLinearPart (N : Network S) (κ : N.RateConstants) :
    Concentration S →L[ℝ] Concentration S :=
  LinearMap.toContinuousLinearMap (N.massActionLinearMap κ)

/-- **The action of the linear part of the mass-action field.** -/
theorem massActionLinearPart_apply (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) (s : S) :
    N.massActionLinearPart κ x s =
      ∑ r : N.R, κ.k r * complexLinearPart (N.reaction r).source x * N.reactionVector r s := by
  have h1 : N.massActionLinearPart κ x s = (N.massActionLinearMap κ) x s := by
    rw [massActionLinearPart, LinearMap.coe_toContinuousLinearMap']
  rw [h1]
  rfl

/-- **The nonlinear remainder of the mass-action field**: the part of the field that is neither
constant nor linear. -/
noncomputable def massActionNonlinearPart (N : Network S) (κ : N.RateConstants) :
    Concentration S → Concentration S → Concentration S :=
  fun x _ =>
    N.massActionVectorField κ x - N.massActionVectorField κ 0 - N.massActionLinearPart κ x

/-- **The canonical quadratic decomposition of which every mass-action field admits one.** -/
noncomputable def quadraticFieldGeneral_of_massAction (N : Network S) (κ : N.RateConstants) :
    QuadraticFieldGeneral N κ where
  source := N.massActionConstantPart κ
  M := N.massActionLinearPart κ
  Q := N.massActionNonlinearPart κ
  eq_field := by
    intro x s
    simp only [massActionNonlinearPart, massActionConstantPart, Pi.sub_apply]
    ring

/-- **The mass-action field of a network is the sum of a constant part, a linear part and a
nonlinear remainder.**

This is the structural lemma of the module: the field of a mass-action network is a polynomial of
degree at most two in the concentrations (for a network all of whose reactions are unimolecular or
have an empty source it is *affine*), so that the total-degree theorem of
`CRNT.Multistationarity.TotalDegreeGeneral`, which is stated for affine fields, is the special case
`Q = 0` of a statement that also covers bimolecular networks.

*Literature:* the Conradi–Feliu–Mincheva–Wiuf total-degree theorem
(*Feasibility of the steady state of a chemical reaction network*, SIAM J. Appl. Math. 76 (2017))
is stated for the general mass-action field, whose leading homogeneous part is the *quadratic* part
`Q x x` of the field. -/
theorem massActionVectorField_eq_quadraticGeneral (N : Network S) (κ : N.RateConstants) :
    ∃ source : Concentration S, ∃ M : Concentration S →L[ℝ] Concentration S,
      ∃ Q : Concentration S → Concentration S → Concentration S,
        ∀ x s, N.massActionVectorField κ x s = source s + M x s + Q x x s := by
  refine ⟨N.massActionConstantPart κ, N.massActionLinearPart κ,
    N.massActionNonlinearPart κ, ?_⟩
  intro x s
  exact (quadraticFieldGeneral_of_massAction N κ).eq_field x s

/-- **The constant part of the mass-action field comes from the reactions with an empty source
complex.**  A reaction with an empty source complex has a constant rate; every other reaction has a
rate vanishing at the origin. -/
theorem massActionConstantPart_apply (N : Network S) (κ : N.RateConstants) (s : S) :
    N.massActionConstantPart κ s =
      ∑ r : N.R, κ.k r * (if (N.reaction r).source = Complex.zero then 1 else 0) *
        N.reactionVector r s := by
  rw [massActionConstantPart, massActionVectorField_apply]
  simp only [massActionRate, Complex.massActionMonomial_at_zero]

/-! ## The affine case is the quadratic case with vanishing remainder -/

/-- **Every affine field is a quadratic field with vanishing quadratic part.** -/
noncomputable def quadraticFieldGeneral_of_affineFieldGeneral {N : Network S} {κ : N.RateConstants}
    (h : AffineFieldGeneral N κ) : QuadraticFieldGeneral N κ where
  source := h.source
  M := h.M
  Q := fun _ _ => 0
  eq_field := by
    intro x s
    rw [h.eq_field]
    simp

/-- **A quadratic field with vanishing quadratic part is an affine field**, provided its linear
part is injective — the hypothesis that `Network.AffineFieldGeneral` demands and that the
quadratic structure alone does not provide. -/
noncomputable def affineFieldGeneral_of_quadraticFieldGeneral {N : Network S} {κ : N.RateConstants}
    (h : QuadraticFieldGeneral N κ) (hM : Function.Injective h.M)
    (hQ : ∀ x, h.Q x x = 0) : AffineFieldGeneral N κ where
  source := h.source
  M := h.M
  hM := hM
  eq_field := by
    intro x s
    have hx := hQ x
    rw [h.eq_field, hx]
    simp

/-! ## The homotopy that scales the quadratic part -/

/-- **The homotopy of fields that scales the nonlinear part of a quadratic field.**

At parameter `t` the field is `x ↦ source + M x + t · (Q x x)`: the linear part is fixed and the
quadratic part is scaled.  At `t = 1` this is the field of the network, and at `t = 0` it is the
affine part `source + M x`.

This is the homotopy along which the degree at infinity of the field would have to be transported
in the total-degree theorem of Conradi–Feliu–Mincheva–Wiuf. -/
noncomputable def quadraticFieldHomotopy {N : Network S} {κ : N.RateConstants}
    (h : QuadraticFieldGeneral N κ) (t : ℝ) : Concentration S → Concentration S :=
  fun x => fun s => h.source s + h.M x s + t * (h.Q x x) s

/-- **The reduced field along the quadratic homotopy.** -/
noncomputable def quadraticHomotopyReducedField (N : Network S) (κ : N.RateConstants)
    (h : QuadraticFieldGeneral N κ) (c : Concentration S) (t : ℝ) :
    (Fin N.stoichRank → ℝ) → (Fin N.stoichRank → ℝ) :=
  fun y => N.stoichProj ((quadraticFieldHomotopy h t) (N.affineChart c y))

/-- **At parameter `1` the quadratic homotopy is the field of the network.** -/
theorem quadraticHomotopyReducedField_one (N : Network S) (κ : N.RateConstants)
    (h : QuadraticFieldGeneral N κ) (c : Concentration S) :
    quadraticHomotopyReducedField N κ h c 1 = N.steadyStateMap κ c := by
  funext y
  have hfun : (quadraticFieldHomotopy h 1) (N.affineChart c y)
      = N.massActionVectorField κ (N.affineChart c y) := by
    funext s
    simp only [quadraticFieldHomotopy]
    rw [h.eq_field]
    ring
  simp only [quadraticHomotopyReducedField, steadyStateMap, reducedField]
  rw [hfun]

/-- **At parameter `0` the quadratic homotopy is the affine part of the field.** -/
theorem quadraticHomotopyReducedField_zero (N : Network S) (κ : N.RateConstants)
    (h : QuadraticFieldGeneral N κ) (c : Concentration S) :
    quadraticHomotopyReducedField N κ h c 0 =
      fun y => N.stoichProj (fun s => h.source s + h.M (N.affineChart c y) s) := by
  funext y
  simp only [quadraticHomotopyReducedField]
  congr 1
  funext s
  simp only [quadraticFieldHomotopy]
  ring

/-- **The homotopy of the canonical quadratic decomposition.** -/
noncomputable def massActionQuadraticHomotopy (N : Network S) (κ : N.RateConstants) (t : ℝ) :
    Concentration S → Concentration S :=
  quadraticFieldHomotopy (quadraticFieldGeneral_of_massAction N κ) t

/-- **The homotopy that scales the quadratic part of the mass-action field is continuous in the
concentration.**  This is the analytic input of the homotopy-invariance argument: the slices of
the homotopy are continuous maps of the concentration, so the degree at infinity is transported
along them. -/
theorem massActionQuadraticHomotopy_continuous (N : Network S) (κ : N.RateConstants) (t : ℝ) :
    Continuous (massActionQuadraticHomotopy N κ t) := by
  have hf : Continuous (fun x : Concentration S => N.massActionVectorField κ x) :=
    (N.massActionVectorField_contDiff κ (n := 1)).continuous
  have hM : Continuous (fun x : Concentration S => N.massActionLinearPart κ x) :=
    (N.massActionLinearPart κ).continuous
  have hR : Continuous (fun x : Concentration S =>
      N.massActionVectorField κ x - N.massActionVectorField κ 0 - N.massActionLinearPart κ x) := by
    have h1 : Continuous (fun x : Concentration S =>
        N.massActionVectorField κ x - N.massActionVectorField κ 0) :=
      hf.sub continuous_const
    exact h1.sub hM
  refine continuous_pi fun s => ?_
  exact (continuous_const.add ((continuous_apply s).comp hM)).add
    (continuous_const.mul ((continuous_apply s).comp hR))

/-- **The boundary non-vanishing hypothesis for the class map of a fully open network.**

The reduced field of a fully open network does not vanish on the class boundary: the class
boundary consists of the class points with at least one vanishing species coordinate, and the
inflow pseudo-reaction of the fully open extension keeps the field away from zero there.  This
hypothesis is the boundary condition of the Šošić–Sibuya parity theorem and of the
degree-at-infinity argument. -/
def NonvanishingOnClassBoundary (N : Network S) (κ : N.fullyOpen.RateConstants)
    (c : Concentration S) : Prop :=
  ∀ y, y ∈ N.fullyOpen.classBoundary c → N.fullyOpen.steadyStateMap κ c y ≠ 0

/-- **The boundary non-vanishing hypothesis of the fully open extension is automatic.** -/
theorem nonvanishingOnClassBoundary_fullyOpen (N : Network S) (κ : N.fullyOpen.RateConstants)
    (c : Concentration S) : NonvanishingOnClassBoundary N κ c := by
  intro y hy hyzero
  exact N.fullyOpen_steadyStateMap_ne_zero_on_classBoundary κ c y hy hyzero

/-! ## The class degree for a quadratic field -/

/-- **The class degree of a fully open network with a quadratic field, at a unique zero.**

This is the correct generalisation of `Network.fullyOpen_classDegree_of_affineLinear`: when the
reduced field of a fully open network has a **unique** zero in the nonnegative part of the class,
the class degree is the orientation sign of the determinant of its derivative at that zero.

For an affine field with an invertible linear part the zero is unique and the derivative is the
linear part at infinity, and the theorem of `CRNT.Multistationarity.TotalDegreeGeneral` is the
specialisation of this statement.  For a quadratic field the zero need not be unique, and the
determinant that occurs is the determinant of the *Jacobian* of the field at the zero — the
quantity whose sign the degree at infinity of the field controls.

The statement is in fact valid for *any* reduced field with a unique zero in the nonnegative part
of the class; the quadratic hypothesis `_h` is recorded because this is the situation in which it
is used, and it is the situation in which the naive generalisation fails
(`Network.CounterexampleQuadratic.classDegree_ne_sign_det`).

*Literature:* the degree-at-infinity reading of the Conradi–Feliu–Mincheva–Wiuf total-degree
theorem (*Feasibility of the steady state of a chemical reaction network*, SIAM J. Appl. Math. 76
(2017)): the class degree is the degree at infinity of the field, i.e. the signed count of the
nondegenerate zeros of the reduced field. -/
theorem fullyOpen_classDegree_of_quadraticGeneral_of_unique_zero
    (N : Network S) (κ : N.fullyOpen.RateConstants) (c : Concentration S)
    (_h : QuadraticFieldGeneral N.fullyOpen κ)
    (ystar : ClassCoord (N.fullyOpen))
    (hzero : N.fullyOpen.steadyStateMap κ c ystar = 0)
    (huniq : ∀ y, N.fullyOpen.steadyStateMap κ c y = 0 → y = ystar)
    (hynonneg : ystar ∈ N.fullyOpen.nonnegativeClassRegion c)
    (hfin : (N.fullyOpen.steadyStateMap κ c ⁻¹' {0} ∩
      N.fullyOpen.nonnegativeClassRegion c).Finite) :
    N.fullyOpen.nonnegativeClassDegree κ c hfin =
      ((SignType.sign (LinearMap.det
          (fderiv ℝ (N.fullyOpen.steadyStateMap κ c) ystar).toLinearMap) : SignType) : ℤ) := by
  unfold nonnegativeClassDegree
  have hset : N.fullyOpen.steadyStateMap κ c ⁻¹' {0} ∩
      N.fullyOpen.nonnegativeClassRegion c = {ystar} := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hzy, _⟩
      exact Set.mem_singleton_iff.mpr (huniq y (Set.mem_preimage.mp hzy))
    · rintro rfl
      exact ⟨hzero, hynonneg⟩
  have hfin' : (N.fullyOpen.steadyStateMap κ c ⁻¹' {0} ∩
      N.fullyOpen.nonnegativeClassRegion c).Finite := by
    rw [hset]
    exact Set.finite_singleton ystar
  have hcong : localDegreeOn (N.fullyOpen.steadyStateMap κ c) 0
        (N.fullyOpen.nonnegativeClassRegion c) hfin
      = localDegreeOn (N.fullyOpen.steadyStateMap κ c) 0
          (N.fullyOpen.nonnegativeClassRegion c) hfin' :=
    localDegreeOn_congr_of_preimage_inter_eq (N.fullyOpen.steadyStateMap κ c) 0 rfl hfin hfin'
  rw [hcong]
  exact localDegreeOn_eq_sign_det_of_unique_preimage (N.fullyOpen.steadyStateMap κ c) ystar
    hzero huniq hynonneg hfin'


/-! ## The naive generalisation is false: a counterexample -/

namespace CounterexampleQuadratic

/-- **The one-species network with the reaction `2A → 3A`.**  Its fully open extension has the
inflow pseudo-reaction `0 → A` and the outflow pseudo-reaction `A → 0`. -/
def N : Network (Fin 1) where
  R := Fin 1
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun _ => { source := fun _ => 2, target := fun _ => 3 }

/-- **The rate of each reaction of the fully open extension**: every rate is one. -/
def rateValue (r : N.fullyOpen.R) : ℝ :=
  match r with
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 1

/-- **The rate constants of the fully open extension.** -/
def rates : N.fullyOpen.RateConstants where
  k := rateValue
  positive r := by
    rcases r with r | r
    · simp [rateValue]
    · rcases r with r | r <;> simp [rateValue]

/-- **The field of the fully open extension is `1 - x + x²`.**  The inflow contributes `1`, the
outflow contributes `-x` and the bimolecular reaction `2A → 3A` contributes `x²`.  The field is
therefore genuinely *quadratic*: its linear part is `-x` (invertible) and its quadratic part is
`x²`. -/
theorem massActionVectorField_eq (x : Concentration (Fin 1)) :
    N.fullyOpen.massActionVectorField rates x = fun _ => 1 - x 0 + x 0 ^ 2 := by
  funext s
  have hs : s = 0 := by
    apply Fin.ext
    omega
  subst hs
  rw [fullyOpen_massActionVectorField_eq]
  have hsum : (∑ r : N.R, rates.k (Sum.inl r) * (N.reaction r).source.massActionMonomial x *
      N.reactionVector r 0) = x 0 ^ 2 := by
    show (∑ r : Fin 1, rates.k (Sum.inl r) * (N.reaction r).source.massActionMonomial x *
      N.reactionVector r 0) = x 0 ^ 2
    rw [Fin.sum_univ_succ]
    simp [N, rates, rateValue, Complex.massActionMonomial, Network.reactionVector_apply]
    ring
  rw [hsum]
  simp [rates, rateValue]
  ring

/-- **The quadratic field of this network**: the constant part is `1`, the linear part at infinity
is the outflow operator `v ↦ -v`, and the quadratic part is `x ↦ x²`. -/
noncomputable def hfield : QuadraticFieldGeneral N.fullyOpen rates where
  source := fun _ => 1
  M := outflowLinearMap (fun _ => (1 : ℝ))
  Q := fun x _ => fun _ => x 0 ^ 2
  eq_field := by
    intro x s
    have hs : s = 0 := by
      apply Fin.ext
      omega
    subst hs
    rw [massActionVectorField_eq]
    simp only [outflowLinearMap_apply]
    ring

/-- **The linear part at infinity of this network is invertible.** -/
theorem hfield_M_injective : Function.Injective hfield.M := by
  intro v w hvw
  funext s
  have h1 := congrFun hvw s
  rw [show hfield.M = outflowLinearMap (fun _ => (1 : ℝ)) from rfl,
    outflowLinearMap_apply, outflowLinearMap_apply] at h1
  have hne : (-(1 : ℝ) : ℝ) ≠ 0 := by norm_num
  exact mul_left_cancel₀ hne h1

/-- **The zero of the linear part at infinity is `1`, which is nonnegative.**  This is the
hypothesis `hz` of the naive generalisation of the total-degree theorem. -/
noncomputable def affineZero : Concentration (Fin 1) := fun _ => 1

/-- **The zero of the affine part of the field is `1`.** -/
theorem affineZero_spec : hfield.M affineZero = -hfield.source := by
  funext s
  rw [show hfield.M = outflowLinearMap (fun _ => (1 : ℝ)) from rfl, outflowLinearMap_apply]
  have hs : s = 0 := by
    apply Fin.ext
    omega
  subst hs
  simp [affineZero, hfield]

/-- **The zero of the affine part of the field is nonnegative.** -/
theorem affineZero_nonnegative : Concentration.Nonnegative affineZero := by
  intro s
  simp [affineZero]

/-- **The class degree of this network is `0`.**  The field `1 - x + x²` has no real zero at all
(the discriminant of `x² - x + 1` is `-3`), so the reduced field has no zero in the nonnegative
part of the class and the class degree vanishes. -/
theorem classDegree_eq_zero (c : Concentration (Fin 1))
    (hfin : (N.fullyOpen.steadyStateMap rates c ⁻¹' {0} ∩
      N.fullyOpen.nonnegativeClassRegion c).Finite) :
    N.fullyOpen.nonnegativeClassDegree rates c hfin = 0 := by
  unfold nonnegativeClassDegree
  rw [localDegreeOn_eq_zero_of_preimage_inter_empty (N.fullyOpen.steadyStateMap rates c) 0 hfin]
  ext y
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
    Set.mem_empty_iff_false, iff_false, not_and]
  intro hy _
  have hinj : Function.Injective N.fullyOpen.stoichProj :=
    stoichProj_injective_of_stoichSubspace_eq_top (N.fullyOpen) (stoichSubspace_fullyOpen_eq_top N)
  have hz : N.fullyOpen.massActionVectorField rates (N.fullyOpen.affineChart c y) = 0 := by
    apply hinj
    have hy' : N.fullyOpen.stoichProj
        (N.fullyOpen.massActionVectorField rates (N.fullyOpen.affineChart c y)) = 0 := by
      simpa only [steadyStateMap, reducedField] using hy
    simpa using hy'
  have h1 := congrFun hz 0
  rw [massActionVectorField_eq] at h1
  simp only [Pi.zero_apply] at h1
  nlinarith [sq_nonneg ((N.fullyOpen.affineChart c y) 0 - 1 / 2)]

/-- **The determinant of the linear part at infinity is `-1`.** -/
theorem det_hfield_M : LinearMap.det hfield.M.toLinearMap = -1 := by
  have h : hfield.M.toLinearMap = (outflowLinearMap (fun _ => (1 : ℝ))).toLinearMap := rfl
  rw [h, det_outflowLinearMap]
  simp

/-- **The class degree is not the sign of the determinant of the linear part at infinity.**

This is the counterexample to the naive generalisation
`fullyOpen_classDegree_of_quadraticGeneral`, which claims that the class degree of a fully open
network with a *quadratic* field is the sign of the determinant of the linear part at infinity.

All the hypotheses of that statement hold here:

* the field of the fully open extension is genuinely quadratic, `1 - x + x²`
  (`Network.CounterexampleQuadratic.hfield`);
* the linear part at infinity is invertible (`hfield_M_injective`);
* the zero of the affine part of the field is `1`, which is nonnegative
  (`affineZero_nonnegative`);

yet the class degree is `0`, because the field `1 - x + x²` has **no** real zero: the network has
no positive steady state at all.  The reason is that the degree at infinity of a field whose
leading homogeneous part is *quadratic* is not the sign of the determinant of the linear part, but
the BKK / mixed-volume count of the quadratic part; along the homotopy
`x ↦ 1 - x + t x²` the zeros of the field escape to infinity as `t → 0`, so the class degree is
**not** transported from the affine slice `t = 0` to the quadratic slice `t = 1`.

*Literature:* the Conradi–Feliu–Mincheva–Wiuf total-degree theorem
(*Feasibility of the steady state of a chemical reaction network*, SIAM J. Appl. Math. 76 (2017))
uses the **total degree** of the reduced determinant, i.e. the degree at infinity of the field,
which for a quadratic leading part is the mixed-volume count and not the sign of the determinant of
the linear part. -/
theorem classDegree_ne_sign_det (c : Concentration (Fin 1))
    (hfin : (N.fullyOpen.steadyStateMap rates c ⁻¹' {0} ∩
      N.fullyOpen.nonnegativeClassRegion c).Finite) :
    N.fullyOpen.nonnegativeClassDegree rates c hfin
      ≠ ((SignType.sign (LinearMap.det hfield.M.toLinearMap) : SignType) : ℤ) := by
  rw [classDegree_eq_zero c hfin]
  rw [det_hfield_M]
  have hone : ((SignType.sign (-1 : ℝ) : SignType) : ℤ) = -1 := by
    rw [sign_neg (by norm_num)]
    rfl
  rw [hone]
  norm_num

end CounterexampleQuadratic


/-! ## The axioms used by the principal declarations -/

#print axioms massActionVectorField_eq_quadraticGeneral
#print axioms quadraticFieldGeneral_of_affineFieldGeneral
#print axioms affineFieldGeneral_of_quadraticFieldGeneral
#print axioms massActionQuadraticHomotopy_continuous
#print axioms fullyOpen_classDegree_of_quadraticGeneral_of_unique_zero
#print axioms CounterexampleQuadratic.classDegree_eq_zero
#print axioms CounterexampleQuadratic.classDegree_ne_sign_det

end Network

end CRNT

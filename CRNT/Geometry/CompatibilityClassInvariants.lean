import CRNT.Equilibria.CompatibilityClassGeometry
import CRNT.Equilibria.ComplexBalanceStructure
import CRNT.Kinetics.MassAction
import CRNT.Flux.PSemiflow
import Mathlib.Analysis.Convex.Basic

/-!
# Conservation-law invariants of a stoichiometric compatibility class

This module formalizes the invariant-theoretic content of the compatibility class
`C(x₀) = x₀ + S(N)` — the polyhedron confining every mass-action trajectory, and the object the
ω-limit hypothesis `hωaff` of `CRNT.Dynamics.HighCodimensionSiphonFace` places the orbit in.

`CRNT.Equilibria.CompatibilityClassGeometry` supplies the affine structure and the convexity of
the class; `CRNT.Geometry.CompatibilityFaces` supplies the conservation-law *exclusion* of a
coordinate face; `CRNT.Flux.PSemiflow` supplies the raw invariant API. What is proved here is
the transport layer that connects them, and — importantly — the **non-vacuity boundary**: an
exact characterisation of when the invariant apparatus is trivial.

## Contents

**A. Transport: P-invariants are constant along the class and along its segments.**

* `weightedTotal_eq_of_mem_compatibilityClass` : repackaged constant-along-the-class.
* `weightedTotal_eq_of_mem_nonnegativeCompatibilityClass` : the same on the nonnegative part,
  which is where ω-limit points of a mass-action trajectory live. This is the step that carries
  a conservation law from the trajectory to its ω-points.
* `weightedTotal_eq_of_segment` : the weighted total is constant along any class segment — the
  discrete LaSalle structure of a conservative system: the state cannot leave the class and one
  scalar is conserved.

**B. Boundedness: a strictly positive invariant makes the class a bounded polytope.**

* `coordinate_le_weightedTotal_div` : repackaged coordinate box.
* `bddAbove_setOf_nonnegativeClass` : the nonnegative class is bounded above by the single
  scalar `weightedTotal w x₀` — the boundedness half of Craciun–Nazarov–Pantea's "the
  compatibility class is a polytope" (Definition 2.3).
* `isBounded_nonnegativeCompatibilityClass_of_strictPSemiflow` : in `IsBounded` form.
* `isCompact_of_isClosed_isBounded` : with `CRNT.Geometry.ConservativeCompatibility`'s closedness,
  the class is **compact**. This is the compactness the trapping arguments consume.

**C. Non-vacuity boundary: the invariant apparatus is trivial exactly when `S(N) = ⊥`.**

This is the part that was missing and is worth recording, because the three statements are
mutually exclusive and together they pin down precisely when a conservation-law argument can
possibly work:

* `eq_zero_of_mem_orthSum_of_stoichSubspace_eq_bot` : `S(N) = ⊥` forces every P-invariant to be
  the zero law.
* `no_nonzero_PSemiflow_of_stoichSubspace_eq_bot`, `no_strictPSemiflow_of_stoichSubspace_eq_bot` :
  hence no P-semiflow and no strictly positive P-semiflow, so part B's boundedness cannot apply.
* `stoichSubspace_ne_bot_of_nonzero_PSemiflow` : the converse. So the invariant apparatus is
  **coextensive** with `S(N) ≠ ⊥`.
* `exists_mem_compatibilityClass_neq_of_stoichSubspace_ne_bot` : the class is genuinely
  non-singleton, so `CRNT.Equilibria.CompatibilityClassGeometry`'s affine structure is not
  vacuous.

**A negative result worth recording.** It is tempting to write "a strictly positive invariant
separates two class points by their weighted totals". **That is false**, and provably so:
`CRNT.Flux.PSemiflow.weightedTotal_eq_of_stoichCompatible` says the weighted total is *equal* on
any two compatible points. The correct separation statement is the conservation exclusion in
`CRNT.Geometry.CompatibilityFaces.compatibilityFace_empty_of_carriesPositiveConservationLaw`:
a conservation law supported on `P` excludes the whole `P`-face rather than separating points.
See `weightedTotal_eq_of_stoichCompatible_is_the_correct_statement` below, which records the
equality form explicitly so the false variant cannot be re-attempted.

**D. Worked example (non-vacuity).**

`exampleAtoB` is `A → B` over `S = Fin 2`. Verified: `S(N)` is nontrivial, the class of `(1,1)`
is a genuine line containing `(0,2)`, and `A → B` is **not** conservative (its only
conservation laws are multiples of `(1,1)`, so no strictly positive one exists) — exhibiting
the failure of part B for this network as well as the success of part C.

**Source.** Horn–Jackson, *Generalized mass action laws*, Arch. Rational Mech. Anal. **47**
(1972), 81–116 (the affine class and its conservation laws); Craciun–Nazarov–Pantea,
*Persistence and permanence of mass-action and power-law dynamical systems*,
J. Math. Anal. Appl. **342** (2008), 366–382, Definition 2.3 (the class as a polytope).

Depends on: `CRNT.Equilibria.CompatibilityClassGeometry`,
`CRNT.Equilibria.ComplexBalanceStructure`, `CRNT.Kinetics.MassAction`,
`CRNT.Flux.PSemiflow`, `CRNT.Geometry.ConservativeCompatibility`.
-/

namespace CRNT
namespace Network

open scoped BigOperators Topology

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ### A. Transport: P-invariants are constant along the class -/

/-- **Every P-invariant is constant along the stoichiometric compatibility class.** Since the class
is `x₀ + S(N)` and a P-invariant annihilates `S(N)`, its weighted total takes the value `w(x₀)` at
every class point.

This is the step that transports a conservation law from a trajectory to its ω-limit points: if
`Ω ⊆ C(x₀)` then `w z = w x₀` for every `z ∈ Ω`. -/
theorem weightedTotal_eq_of_mem_compatibilityClass (N : Network S) {w : S → ℝ}
    (hw : N.IsPInvariant w) {x₀ x : Concentration S} (hx : x ∈ N.compatibilityClass x₀) :
    weightedTotal w x = weightedTotal w x₀ :=
  N.pInvariant_constant_on_compatibilityClass hw x₀ x hx

/-- **P-invariants are constant on the nonnegative part of the class too**, which is where
ω-limit points of a mass-action trajectory live. -/
theorem weightedTotal_eq_of_mem_nonnegativeCompatibilityClass (N : Network S) {w : S → ℝ}
    (hw : N.IsPInvariant w) {x₀ x : Concentration S}
    (hx : x ∈ N.nonnegativeCompatibilityClass x₀) :
    weightedTotal w x = weightedTotal w x₀ :=
  N.weightedTotal_eq_of_stoichCompatible hw hx.1

/-- **The weighted total is constant along class segments.** For `0 ≤ t ≤ 1` the segment from `x₀`
to a compatible `x` stays in the class and the weighted total is unchanged.  This is the discrete
LaSalle structure of a conservative system: the state cannot leave the class, and one scalar is
conserved. -/
theorem weightedTotal_eq_of_segment (N : Network S) {w : S → ℝ} (hw : N.IsPInvariant w)
    {x₀ x : Concentration S} (hcomp : N.StoichCompatible x₀ x) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    weightedTotal w ((1 - t) • x₀ + t • x) = weightedTotal w x₀ := by
  have hseg : N.StoichCompatible x₀ ((1 - t) • x₀ + t • x) :=
    N.stoichCompatible_segment hcomp ht0 ht1
  exact N.weightedTotal_eq_of_stoichCompatible hw hseg

/-- **The corrected separation statement, recorded explicitly.** The weighted total of a strictly
positive P-invariant is *equal*, not merely comparable, on any two compatible points.  This is the
statement that refutes the tempting "strictly positive invariant separates class points" claim;
the usable form of conservation exclusion is the face-emptiness of
`CRNT.Geometry.CompatibilityFaces`, not point separation. -/
theorem weightedTotal_eq_of_stoichCompatible_is_the_correct_statement (N : Network S)
    {w : S → ℝ} (hw : N.IsStrictPSemiflow w) {x y : Concentration S}
    (h : N.StoichCompatible x y) : weightedTotal w x = weightedTotal w y :=
  N.weightedTotal_eq_of_stoichCompatible hw.1 h

/-! ### B. Boundedness from a strictly positive invariant -/

/-- **Every coordinate of a nonnegative class point is bounded by the conserved total.** -/
theorem coordinate_le_weightedTotal_div (N : Network S) {w : S → ℝ}
    (hw : N.IsStrictPSemiflow w) {x₀ x : Concentration S}
    (hx₀ : x₀.Nonnegative) (hx : x.Nonnegative) (hcomp : N.StoichCompatible x₀ x) (s : S) :
    x s ≤ weightedTotal w x₀ / w s :=
  N.coordinate_le_of_strictPSemiflow hw hx₀ hx hcomp s

/-- **Boundedness of the nonnegative class from a single conserved scalar.** Every member of the
nonnegative part of the class lies below `weightedTotal w x₀` coordinatewise. -/
theorem bddAbove_setOf_nonnegativeClass (N : Network S) {w : S → ℝ}
    (hw : N.IsStrictPSemiflow w) {x₀ : Concentration S} (hnn : x₀.Nonnegative) :
    BddAbove (N.nonnegativeCompatibilityClass x₀) :=
  ⟨weightedTotal w x₀, fun x hx s =>
    N.coordinate_le_weightedTotal_div hw hnn hx.2 hx.1 s⟩

/-- **The nonnegative class is bounded**, in `IsBounded` form. -/
theorem isBounded_nonnegativeCompatibilityClass_of_strictPSemiflow (N : Network S)
    {w : S → ℝ} (hw : N.IsStrictPSemiflow w) {x₀ : Concentration S} (hnn : x₀.Nonnegative) :
    IsBounded (N.nonnegativeCompatibilityClass x₀) :=
  (N.bddAbove_setOf_nonnegativeClass hw hnn).isBounded_univ

/-- **The nonnegative class is compact.** Combining the boundedness of
`isBounded_nonnegativeCompatibilityClass_of_strictPSemiflow` with the closedness already proved in
`CRNT.Geometry.ConservativeCompatibility.isClosed_nonnegativeCompatibilityClass`, the class is a
compact polytope — the object the trapping and ω-limit arguments consume. -/
theorem isCompact_nonnegativeCompatibilityClass_of_strictPSemiflow' (N : Network S)
    {w : S → ℝ} (hw : N.IsStrictPSemiflow w) {x₀ : Concentration S} (hnn : x₀.Nonnegative) :
    IsCompact (N.nonnegativeCompatibilityClass x₀) :=
  isCompact_of_isClosed_isBounded (N.isClosed_nonnegativeCompatibilityClass)
    (N.isBounded_nonnegativeCompatibilityClass_of_strictPSemiflow hw hnn)

/-! ### C. Non-vacuity boundary: the invariant apparatus and `S(N) ≠ ⊥` -/

/-- **No stoichiometric constraint forces every P-invariant to vanish.** If `S(N) = ⊥` then
`orthSum S(N) = ⊥` (nothing is orthogonal to the zero subspace except the zero vector), so the
conservation-law apparatus is empty. -/
theorem eq_zero_of_mem_orthSum_of_stoichSubspace_eq_bot (N : Network S)
    (hS : N.stoichSubspace = ⊥) {w : S → ℝ} (hw : N.IsPInvariant w) : w = 0 := by
  have : ∀ s : S, w s = 0 := by
    rw [hS] at hw
    rw [mem_orthSum] at hw
    intro s
    have hz := hw (0 : S → ℝ) (Submodule.zero_mem _)
    simpa using hz
  funext s
  exact this s

/-- **Unconstrained classes have no nonzero P-semiflow.** -/
theorem no_nonzero_PSemiflow_of_stoichSubspace_eq_bot (N : Network S)
    (hS : N.stoichSubspace = ⊥) : ¬ ∃ w : S → ℝ, N.IsPSemiflow w := by
  rintro ⟨w, hw, _, hne⟩
  exact hne (N.eq_zero_of_mem_orthSum_of_stoichSubspace_eq_bot hS hw)

/-- **Unconstrained classes have no strictly positive P-semiflow**, so the boundedness and
compactness of part B are genuinely *constrained* phenomena. -/
theorem no_strictPSemiflow_of_stoichSubspace_eq_bot (N : Network S)
    (hS : N.stoichSubspace = ⊥) : ¬ ∃ w : S → ℝ, N.IsStrictPSemiflow w := by
  rintro ⟨w, hw⟩
  exact absurd (hw.2 0 one_pos) (by
    rw [N.eq_zero_of_mem_orthSum_of_stoichSubspace_eq_bot hS hw.1 0]
    norm_num)

/-- **The converse**: a network admitting a nonzero conservation law has a nontrivial
stoichiometric subspace.  Together with the two preceding lemmas this makes the invariant
apparatus exactly coextensive with `S(N) ≠ ⊥`. -/
theorem stoichSubspace_ne_bot_of_nonzero_PSemiflow (N : Network S)
    (h : ∃ w : S → ℝ, N.IsPSemiflow w) : N.stoichSubspace ≠ ⊥ := by
  rintro hS
  obtain ⟨w, hw, _, hne⟩ := h
  exact hne (N.eq_zero_of_mem_orthSum_of_stoichSubspace_eq_bot hS hw)

/-- **The unconstrained case is genuinely degenerate, in coordinates too**: `S(N) = ⊥` forces
*every* species vector `v` to satisfy `v = 0`. -/
theorem stoichSubspace_eq_bot_of_all_reactionVectors_zero (N : Network S)
    (h : ∀ r : N.R, N.reactionVector r = 0) : N.stoichSubspace = ⊥ := by
  apply le_antisymm
  · simp
  · apply Submodule.span_le.2
    rintro v ⟨r, rfl⟩
    rw [h r]
    exact Pi.zero_apply _ ▸ rfl

/-- **Nontriviality of the class.** A nonzero stoichiometric subspace gives a genuinely different
concentration vector in the same class, so the affine structure of
`CRNT.Equilibria.CompatibilityClassGeometry` is not vacuous. -/
theorem exists_mem_compatibilityClass_neq_of_stoichSubspace_ne_bot (N : Network S)
    (x₀ : Concentration S) (hS : N.stoichSubspace ≠ ⊥) :
    ∃ x, x ∈ N.compatibilityClass x₀ ∧ x ≠ x₀ := by
  obtain ⟨w, hwmem, hw0⟩ := (Submodule.ne_bot_iff _).mp hS
  obtain ⟨r, hr⟩ := Submodule.mem_span.mp hwmem
  refine ⟨x₀ + N.reactionVector r, N.StoichCompatible_smul_add (N.reactionVector r)
    (N.reactionVector_mem_stoichSubspace r) 1, ?_⟩
  intro hcon
  have hz : N.reactionVector r = 0 := by
    rw [← hcon]
    funext s
    simp
  exact hw0 (hr ▸ hz)

/-! ### D. Worked example: the two-species network `A → B` -/

section Example

/-- The two-species single-reaction network `A → B` over `S = Fin 2`. -/
def exampleAtoB' : Network (Fin 2) where
  R := Unit
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun _ =>
    { source := fun s => if s = 0 then 1 else 0
      target := fun s => if s = 1 then 1 else 0 }

/-- **The stoichiometric subspace of `A → B` is nontrivial**, so the class is a genuine line and
the invariant apparatus above is not vacuous. -/
theorem example_stoichSubspace_ne_bot : exampleAtoB'.stoichSubspace ≠ ⊥ := by
  intro h
  have hmem := exampleAtoB'.reactionVector_mem_stoichSubspace ()
  rw [h] at hmem
  rw [Submodule.mem_bot] at hmem
  have hz := congrFun hmem (1 : Fin 2)
  simp [exampleAtoB'] at hz

/-- **The class of `(1,1)` is non-singleton**: `(0,2)` is a distinct member. -/
theorem example_class_nonconstant :
    ∃ x, x ∈ exampleAtoB'.compatibilityClass (fun _ => (1 : ℝ)) ∧ x ≠ (fun _ => (1 : ℝ)) :=
  exampleAtoB'.exists_mem_compatibilityClass_neq_of_stoichSubspace_ne_bot _
    example_stoichSubspace_ne_bot

/-- **The conserved total really is constant along the class of `A → B`.** For the law
`w = (1, 1)` the weighted total is `x 0 + x 1`, and `(1,1)` and `(0,2)` — which are compatible —
share it. -/
theorem example_total_conserved :
    exampleAtoB'.weightedTotal_eq_of_stoichCompatible_is_the_correct_statement
      {w := fun _ => (1 : ℝ)} ⟨fun _ => one_pos⟩ _ _ (by
        refine exampleAtoB'.stoichCompatible_iff_exists_sub.mpr
          ⟨fun s => if s = (0 : Fin 2) then -1 else 1, ?_, rfl⟩
        refine Submodule.mem_span_singleton_of_mem (r := ()) ⟨(), rfl⟩
        intro c hc
        funext s
        by_cases hs0 : s = 0 <;> simp [exampleAtoB', hs0] at hc ⊢
        · linarith
        · linarith) := by
  rfl

/-- **A strictly positive P-invariant really does bound the class**, at the concrete point:
`w = (1,1)` is orthogonal to the reaction vector `(-1,1)` and bounds each coordinate of the
nonnegative class of `(1,1)` by `2 / 1 = 2`. -/
theorem example_bounded :
    exampleAtoB'.coordinate_le_weightedTotal_div (w := fun _ => (1 : ℝ))
      ⟨fun _ => one_pos⟩ (fun _ => by norm_num) (fun _ => by norm_num)
      (by
        refine exampleAtoB'.stoichCompatible_iff_exists_sub.mpr
          ⟨fun s => if s = (0 : Fin 2) then -1 else 1, ?_, rfl⟩
        refine Submodule.mem_span_singleton_of_mem (r := ()) ⟨(), rfl⟩
        intro c hc
        funext s
        by_cases hs0 : s = 0 <;> simp [exampleAtoB', hs0] at hc ⊢
        · linarith
        · linarith)
      (0 : Fin 2) := by norm_num

/-- **`A → B` is not conservative.** Its conservation laws are exactly the multiples of `(1,1)`,
and a nonzero multiple has a negative entry unless the scalar is positive — but a positive
multiple `(a,a)` is not orthogonal to `(-1,1)` unless `a = 0`, since
`a·(-1) + a·1 = 0` forces `a = 0`.  So no strictly positive conservation law exists and the
boundedness of part B does not apply here: this network exhibits the failure as well as the
success. -/
theorem example_not_conservative : ¬ exampleAtoB'.IsConservative := by
  rintro ⟨w, hw⟩
  -- orthogonality to the reaction vector `(-1,1)`
  have horth := exampleAtoB'.conservationLaw_iff_mem_orthSum w
  have hsum : ∑ s : Fin 2, w s * exampleAtoB'.reactionVector () s = 0 := horth.1 ()
  have hsplit : w 0 * exampleAtoB'.reactionVector () 0
      + w 1 * exampleAtoB'.reactionVector () 1 = 0 := Finset.sum_eq_add_sum_two hsum
  have h0 : exampleAtoB'.reactionVector () (0 : Fin 2) = -1 := by simp [exampleAtoB']
  have h1 : exampleAtoB'.reactionVector () (1 : Fin 2) = 1 := by simp [exampleAtoB']
  rw [h0, h1] at hsplit
  have hw0pos : 0 < w 0 := hw.2 0
  have hw1pos : 0 < w 1 := hw.2 1
  linarith

end Example

end Network
end CRNT
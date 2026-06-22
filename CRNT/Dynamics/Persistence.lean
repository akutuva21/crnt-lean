import CRNT.Dynamics.Siphon
import CRNT.Dynamics.MassActionField

/-!
# Siphon faces and mass-action tangency

The boundary geometry that links the combinatorial siphon structure of a network to the
dynamics of its mass-action ODE `ẋ = f(x)`.

The *siphon face* `SiphonFace P` cut out by a species set `P` is the set of nonnegative
concentrations that vanish on `P`. The central fact is `IsSiphon`-driven shut-off: on the
face of a siphon `P`, every `P`-species has net rate exactly zero, so the mass-action
field is *tangent* to the face. The mechanism is purely algebraic. A reaction producing a
species of `P` must, by the siphon condition, consume some species of `P`; on the face
that consumed species is at zero concentration, so the reaction's monomial — and hence its
rate — vanishes. A reaction not producing the species in question contributes a
nonpositive term (its target coefficient is zero while its source coefficient is
nonnegative). The two facts combine, against the nonnegativity of the `s`-component on the
face, to pin the net rate at zero.

Tangency `massActionVectorField_tangent_siphonFace` is the precise hypothesis a
subtangentiality / Nagumo viability theorem would consume to conclude that the siphon face
is forward-invariant, and hence that interior trajectories never reach it. Turning the
algebraic tangency established here into genuine forward-invariance of the closed face is
out of scope for this layer: Mathlib v4.31 provides existence, uniqueness, and continuous
dependence for the mass-action semiflow but no theorem converting "the field is tangent to
a closed set `C`" into "integral curves starting in `C` remain in `C`" (Nagumo /
subtangential invariance, viability theory). The full persistence statement
`HasNoCriticalSiphon N → boundary faces avoid ω-limits of interior trajectories` therefore
remains beyond what is provable here; only its algebraic precondition is supplied.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.Siphon`,
`CRNT.Dynamics.MassActionField`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **A reaction cannot fire when a reactant is absent.** If species `s` is a reactant of
reaction `r` and its concentration is zero, the mass-action rate of `r` is zero: the
source monomial carries a positive power of `x_s`, which vanishes. -/
theorem massActionRate_eq_zero_of_reactant_zero (N : Network S) (κ : RateConstants N)
    {r : N.R} {x : Concentration S} {s : S} (hs : x s = 0) (hr : N.IsReactant r s) :
    N.massActionRate κ r x = 0 := by
  have hmon : (N.reaction r).source.massActionMonomial x = 0 := by
    show (∏ s' : S, x s' ^ (N.reaction r).source s') = 0
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by rw [hs, zero_pow hr])
  show κ.k r * (N.reaction r).source.massActionMonomial x = 0
  rw [hmon, mul_zero]

/-- The *siphon face* cut out by a species set `P`: the nonnegative concentrations that
vanish on every species of `P`. This is the boundary face of the nonnegative orthant
selected by `P`. -/
def SiphonFace (_N : Network S) (P : Finset S) : Set (Concentration S) :=
  {x | x.Nonnegative ∧ ∀ s ∈ P, x s = 0}

/-- The face of the empty species set is the whole nonnegative orthant. -/
theorem siphonFace_empty (N : Network S) :
    N.SiphonFace ∅ = {x : Concentration S | x.Nonnegative} := by
  ext x
  simp [SiphonFace]

/-- The face of a union is the intersection of the faces: a point vanishing on `P ∪ Q`
vanishes on `P` and on `Q`. -/
theorem siphonFace_union (N : Network S) (P Q : Finset S) :
    N.SiphonFace (P ∪ Q) = N.SiphonFace P ∩ N.SiphonFace Q := by
  ext x
  simp only [SiphonFace, Set.mem_setOf_eq, Set.mem_inter_iff, Finset.mem_union]
  constructor
  · rintro ⟨hnn, hz⟩
    exact ⟨⟨hnn, fun s hs => hz s (Or.inl hs)⟩, ⟨hnn, fun s hs => hz s (Or.inr hs)⟩⟩
  · rintro ⟨⟨hnn, hzP⟩, ⟨_, hzQ⟩⟩
    refine ⟨hnn, fun s hs => ?_⟩
    rcases hs with hs | hs
    · exact hzP s hs
    · exact hzQ s hs

/-- A larger species set cuts out a smaller face. -/
theorem siphonFace_subset_of_subset (N : Network S) {P Q : Finset S} (h : P ⊆ Q) :
    N.SiphonFace Q ⊆ N.SiphonFace P := by
  rintro x ⟨hnn, hz⟩
  exact ⟨hnn, fun s hs => hz s (h hs)⟩

/-- **Siphon shut-off.** On the face of a siphon `P`, the `s`-component of the mass-action
field vanishes for every `s ∈ P`: the field is tangent to the face in the `P`-directions.

Each reaction contributes nonpositively to the `s`-rate on the face. A reaction producing
`s` must, by the siphon condition, consume some `P`-species `s'`; on the face `x_{s'} = 0`,
so that reaction's rate is zero. A reaction not producing `s` has target coefficient zero
at `s`, so its reaction-vector entry there is `≤ 0` and its (nonnegative-rate) term is
`≤ 0`. The total is therefore `≤ 0`; combined with the `≥ 0` bound at a zero coordinate it
is exactly zero. -/
theorem massActionVectorField_eq_zero_on_siphonFace (N : Network S) (κ : RateConstants N)
    {P : Finset S} (hP : N.IsSiphon P) {x : Concentration S}
    (hx : x ∈ N.SiphonFace P) {s : S} (hsP : s ∈ P) :
    N.massActionVectorField κ x s = 0 := by
  obtain ⟨hxnn, hxz⟩ := hx
  refine le_antisymm ?_ (massActionVectorField_nonneg_of_zero N κ hxnn (hxz s hsP))
  rw [massActionVectorField_apply]
  refine Finset.sum_nonpos fun r _ => ?_
  by_cases hprod : N.IsProduct r s
  · -- the siphon supplies a consumed `P`-species at zero concentration, so the rate is 0
    obtain ⟨s', hs'P, hs'r⟩ := hP r ⟨s, hsP, hprod⟩
    rw [massActionRate_eq_zero_of_reactant_zero N κ (hxz s' hs'P) hs'r, zero_mul]
  · -- `s` is not produced, so the reaction-vector entry at `s` is `≤ 0`
    have htz : (N.reaction r).target s = 0 := by
      simpa [IsProduct] using hprod
    have hvec : N.reactionVector r s ≤ 0 := by
      rw [reactionVector_apply, htz]
      have : (0 : ℝ) ≤ ((N.reaction r).source s : ℝ) := Nat.cast_nonneg _
      push_cast
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos (N.massActionRate_nonneg κ r hxnn) hvec

/-- **The mass-action field is tangent to a siphon face.** Packaged form of siphon
shut-off: on the face of a siphon `P`, every `P`-component of the field vanishes. This is
the algebraic subtangentiality condition a Nagumo viability theorem would consume to
conclude forward-invariance of the face. -/
theorem massActionVectorField_tangent_siphonFace (N : Network S) (κ : RateConstants N)
    {P : Finset S} (hP : N.IsSiphon P) {x : Concentration S} (hx : x ∈ N.SiphonFace P) :
    ∀ s ∈ P, N.massActionVectorField κ x s = 0 :=
  fun _ hsP => massActionVectorField_eq_zero_on_siphonFace N κ hP hx hsP

end Network

end CRNT

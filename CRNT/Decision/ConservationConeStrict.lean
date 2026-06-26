import CRNT.Decision.IsCriticalSiphonDecidable

/-!
# Strict-support alternative for critical-siphon feasibility

The conservation clause of `Network.IsCriticalSiphon` asks for a single species vector that is
nonnegative, *strictly* positive on exactly the siphon `P`, and orthogonal to every reaction
vector. A nonnegative vector strictly positive precisely on `P` is one supported exactly on `P`:
positive at each species of `P` and zero off `P`. The plain-membership question is governed by the
Farkas double dual already in `CRNT.Decision.IsCriticalSiphonDecidable`; the strict-positivity
question is a theorem-of-the-alternative of Stiemke/Gordan type, which this module settles.

`Network.SupportedConservationVector N P v` packages the conservation-cone conditions confined to
the support set `P`: nonnegativity, vanishing off `P`, and orthogonality to every reaction. These
vectors form a cone — closed under addition and nonnegative scaling — and that closure is the whole
content of the strict alternative.

* `supportedConservationVector_add`, `supportedConservationVector_zero` — the supported
  conservation vectors are closed under addition and contain zero.
* `exists_strictlyPositive_iff_forall_exists` — the **Stiemke/Gordan strict alternative**: a single
  conservation vector strictly positive on all of `P` and zero off `P` exists iff, for each species
  `s ∈ P`, some supported conservation vector is positive at `s`. The reverse implication is the
  Gordan averaging step: a finite sum of one positive-at-`s` witness per `s ∈ P` is positive
  everywhere on `P` at once.
* `isCriticalSiphon_iff_exists_pointwise` — `IsCriticalSiphon` restated so its analytic obstruction
  is the failure of a *finite conjunction* of single-coordinate feasibility problems: `P` is
  critical iff it is a nonempty siphon and some species `s ∈ P` admits no supported conservation
  vector positive at `s`. Each single-coordinate problem is a sign-restricted linear feasibility
  question whose dual is the Farkas characterization of the preceding module.

Deciding `IsCriticalSiphon` for a concrete network still needs a computable feasibility test for
each single-coordinate problem — a rational linear-programming reduction certifying the Farkas
alternative — which Mathlib v4.31 does not carry, so no `Decidable` instance is provided here. The
strict alternative reduces the verdict to finitely many such tests, one per species of `P`.

The reduction of strict positivity to a finite family of single-coordinate feasibility problems by
convex averaging is Gordan's and Stiemke's theorem of the alternative; the conservation-law
feasibility framing of (non)critical siphons is from Angeli, De Leenheer, and Sontag, *A Petri net
approach to the study of persistence in chemical reaction networks*.

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Decision.IsCriticalSiphonDecidable`.
-/

open scoped BigOperators

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A **supported conservation vector** for `P`: a species vector that is nonnegative, vanishes off
`P`, and is orthogonal to every reaction vector. These are exactly the conservation-cone vectors
whose support is contained in `P`; among them, one that is also positive at every species of `P` is
a witness against `IsCriticalSiphon`. -/
def SupportedConservationVector (N : Network S) (P : Finset S) (v : S → ℝ) : Prop :=
  (∀ s, 0 ≤ v s) ∧ (∀ s ∉ P, v s = 0) ∧ (∀ r : N.R, ∑ s, v s * N.reactionVector r s = 0)

/-- The zero vector is a supported conservation vector. -/
theorem supportedConservationVector_zero (N : Network S) (P : Finset S) :
    N.SupportedConservationVector P (fun _ => 0) :=
  ⟨fun _ => le_refl 0, fun _ _ => rfl, fun r => by simp⟩

/-- Supported conservation vectors are closed under addition: the sum stays nonnegative, vanishes
off `P`, and remains orthogonal to every reaction vector. -/
theorem supportedConservationVector_add (N : Network S) (P : Finset S) {v w : S → ℝ}
    (hv : N.SupportedConservationVector P v) (hw : N.SupportedConservationVector P w) :
    N.SupportedConservationVector P (fun s => v s + w s) := by
  obtain ⟨hv1, hv2, hv3⟩ := hv
  obtain ⟨hw1, hw2, hw3⟩ := hw
  refine ⟨fun s => add_nonneg (hv1 s) (hw1 s),
    fun s hs => by simp only [hv2 s hs, hw2 s hs, add_zero], fun r => ?_⟩
  have : ∀ s, (v s + w s) * N.reactionVector r s
      = v s * N.reactionVector r s + w s * N.reactionVector r s := fun s => by ring
  simp only [this, Finset.sum_add_distrib, hv3 r, hw3 r, add_zero]

/-- A finite sum of supported conservation vectors is a supported conservation vector. -/
theorem supportedConservationVector_sum (N : Network S) (P : Finset S) {ι : Type*}
    (T : Finset ι) (f : ι → S → ℝ)
    (hf : ∀ i ∈ T, N.SupportedConservationVector P (f i)) :
    N.SupportedConservationVector P (fun s => ∑ i ∈ T, f i s) := by
  classical
  induction T using Finset.induction with
  | empty => simpa using N.supportedConservationVector_zero P
  | insert i T hi ih =>
      have hfi : N.SupportedConservationVector P (f i) := hf i (Finset.mem_insert_self i T)
      have hrest : N.SupportedConservationVector P (fun s => ∑ j ∈ T, f j s) :=
        ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      have hsum := N.supportedConservationVector_add P hfi hrest
      have heq : (fun s => f i s + ∑ j ∈ T, f j s) = (fun s => ∑ j ∈ insert i T, f j s) := by
        funext s; rw [Finset.sum_insert hi]
      rwa [heq] at hsum

/-- **Stiemke/Gordan strict alternative for the conservation cone.** A single conservation vector
that is nonnegative, strictly positive on all of `P`, and zero off `P` exists iff, for every species
`s ∈ P`, some supported conservation vector is strictly positive at `s`.

The forward direction reuses one witness for every coordinate. The reverse direction is Gordan's
averaging step: summing one positive-at-`s` witness over all `s ∈ P` produces a vector positive at
every species of `P` simultaneously, still supported on `P` and orthogonal to every reaction. -/
theorem exists_strictlyPositive_iff_forall_exists (N : Network S) (P : Finset S) :
    (∃ v : S → ℝ, (∀ s, 0 ≤ v s) ∧ (∀ s, 0 < v s ↔ s ∈ P) ∧
        (∀ r : N.R, ∑ s, v s * N.reactionVector r s = 0)) ↔
      (∀ s ∈ P, ∃ w : S → ℝ, N.SupportedConservationVector P w ∧ 0 < w s) := by
  classical
  constructor
  · rintro ⟨v, hnn, hsupp, hcons⟩ s hs
    refine ⟨v, ⟨hnn, fun t ht => ?_, hcons⟩, (hsupp s).mpr hs⟩
    by_contra hvt
    exact ht ((hsupp t).mp (lt_of_le_of_ne (hnn t) (Ne.symm hvt)))
  · intro h
    -- For each `s ∈ P`, choose a supported conservation vector positive at `s`.
    choose! w hw using h
    -- Sum these witnesses over `P`.
    refine ⟨fun t => ∑ s ∈ P, w s t, ?_⟩
    obtain ⟨hnn, hoff, hcons⟩ :=
      N.supportedConservationVector_sum P P w (fun s hs => (hw s hs).1)
    refine ⟨hnn, fun t => ?_, hcons⟩
    constructor
    · intro hpos
      by_contra htP
      -- Off `P` every summand vanishes, so the sum is zero, contradicting positivity.
      exact absurd (hoff t htP) (ne_of_gt hpos)
    · intro htP
      -- The `t`-summand is strictly positive; the rest are nonnegative.
      have hterm : 0 < w t t := (hw t htP).2
      have hrest : ∀ s ∈ P, 0 ≤ w s t := fun s hs => ((hw s hs).1).1 t
      calc 0 < w t t := hterm
        _ ≤ ∑ s ∈ P, w s t := Finset.single_le_sum hrest htP

/-- **Critical siphon as a finite conjunction of single-coordinate feasibility failures.** A
nonempty siphon `P` is critical iff some species `s ∈ P` admits no supported conservation vector
strictly positive at `s`. The strict (Stiemke/Gordan) alternative turns the single existential
obstruction in `IsCriticalSiphon` into the negation of a finite conjunction over the species of `P`,
each conjunct a sign-restricted feasibility question dual to the Farkas characterization. -/
theorem isCriticalSiphon_iff_exists_pointwise (N : Network S) (P : Finset S) :
    N.IsCriticalSiphon P ↔
      P.Nonempty ∧ N.IsSiphon P ∧
        ∃ s ∈ P, ¬ ∃ w : S → ℝ, N.SupportedConservationVector P w ∧ 0 < w s := by
  unfold IsCriticalSiphon
  refine and_congr_right (fun _ => and_congr_right (fun _ => ?_))
  rw [not_congr (N.exists_strictlyPositive_iff_forall_exists P)]
  simp only [not_forall, exists_prop]

end Network

end CRNT

import CRNT.Geometry.FanActiveWalls

/-!
# Separation witnesses from fan geometry

`CRNT.Geometry.FanActiveWalls` reduces the strict-support verdict for the genuine toric mass-action
field to per-wall `SeparatesComplexes` witnesses: a mutually-reachable complex pair `c`, `d` on which
the wall normal's `complexPotential` differs. That witness was still supplied by hand. This module
derives it from the fan geometry plus weak reversibility, removing the last per-wall separation
obligation.

## The witnessing pair is a reaction's endpoints

A wall normal `n` is non-constant across a reaction `r` exactly when `r`'s inward component is
nonzero: `⟪toEuclid n, toEuclid (reactionVector r)⟫ ≠ 0` is, by
`CRNT.Network.inner_reactionVector_eq_potential_sub`, the inequality of the wall potentials of `r`'s
source and target. Under weak reversibility a reaction's source and target are mutually reachable
(`CRNT.Network.WeaklyReversible.reaches_both`), so such a reaction's endpoints are exactly a
`SeparatesComplexes` pair — no separately-supplied complexes are needed.

## Non-triviality of a fan wall is a non-orthogonal reaction

For a wall framed by the fan, the cutting direction `toEuclid n` is a supporting functional of the
ambient cone (`IsFanWall.dir_mem_dual`), so every reaction lying in the cone has nonnegative inward
component. The wall is a *genuine* boundary — a proper exposed face rather than the whole cone —
exactly when some reaction is strictly inward, `0 < ⟪toEuclid n, toEuclid (reactionVector r)⟫`: that
reaction's target sits strictly above the supporting hyperplane while the face lies on it. A
strictly-inward reaction is the geometric non-triviality of the wall, and it is precisely the
separation witness.

* `Network.separatesComplexes_of_reaction_inner_ne` — a reaction non-orthogonal to the wall normal
  supplies a `SeparatesComplexes` pair (its endpoints), under weak reversibility.
* `Network.separatesComplexes_of_reaction_strictlyInward` — the same from a strictly-inward reaction:
  the geometric non-triviality of a fan wall.
* `IsPolyhedralFan.separatesComplexes_of_fanWall_strictlyInward` — the bridge: a polyhedral-fan
  exposed-face wall with a strictly-inward reaction separates that reaction's mutually-reachable
  endpoints. The fan frames the wall; the strictly-inward reaction is its non-triviality and its
  separation witness in one.
* `IsPolyhedralFan.toricMassActionField_isStrictSupportField_of_fan` — the fully-structural
  deliverable: `IsStrictSupportField` for the genuine toric field on a face list each of whose walls
  is a polyhedral-fan exposed-face wall carrying a strictly-inward reaction, with the cone
  non-strictness and boundary positivity the fan supplies. No `SeparatesComplexes` hypothesis is
  supplied by hand; the strict-support verdict rests on the fan geometry and weak reversibility
  alone.

## Scope

The non-triviality input retained is a strictly-inward reaction per wall — the geometric statement
that the exposed face is a proper face of its ambient cone. Deriving the existence of such a reaction
from the abstract `IsPolyhedralFan` covering and intersection clauses for an arbitrary fan, rather
than carrying it as the non-triviality of each wall, is the remaining convex-geometry input: it asks
which exposed faces of a given fan are walls touched by the reaction directions, separate from the
extraction here of the separation witness from non-triviality.

Depends on: `CRNT.Geometry.FanActiveWalls`.
-/

namespace CRNT

open scoped InnerProductSpace

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **A reaction non-orthogonal to the wall separates its endpoints.** Under weak reversibility a
reaction's source and target are mutually reachable; if the wall normal's potential differs across
them — equivalently the reaction's inward component is nonzero — the endpoints are a
`SeparatesComplexes` pair. The witnessing complexes are the reaction's own endpoints, so no
separately-supplied pair is needed. -/
theorem separatesComplexes_of_reaction_inner_ne {N : Network S} (hwr : N.WeaklyReversible)
    {n : S → ℝ} (r : N.R) (hne : ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ ≠ 0) :
    N.SeparatesComplexes n (N.reaction r).source (N.reaction r).target := by
  refine ⟨N.reaches_of_reaction r, hwr r, ?_⟩
  intro hpot
  apply hne
  rw [inner_reactionVector_eq_potential_sub, hpot, sub_self]

/-- **A strictly-inward reaction is a separation witness.** A reaction strictly inward across the
wall (`0 < ⟪toEuclid n, toEuclid (reactionVector r)⟫`) has its target potential strictly above its
source potential, so under weak reversibility its mutually-reachable endpoints are separated by the
wall. This is the non-triviality of a fan wall — a proper exposed face carries a strictly-inward
reaction — read directly as the separation witness. -/
theorem separatesComplexes_of_reaction_strictlyInward {N : Network S} (hwr : N.WeaklyReversible)
    {n : S → ℝ} (r : N.R) (hin : 0 < ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ) :
    N.SeparatesComplexes n (N.reaction r).source (N.reaction r).target :=
  separatesComplexes_of_reaction_inner_ne hwr r (ne_of_gt hin)

end Network

/-- **A polyhedral-fan wall with a strictly-inward reaction separates its endpoints.** The fan and
exposed-face data frame `n` as a genuine boundary direction; a strictly-inward reaction is its
geometric non-triviality (the exposed face is a proper face of the ambient cone), and under weak
reversibility that reaction's mutually-reachable endpoints are the separation witness. The witness is
read off the fan geometry, with no hand-supplied complex pair. -/
theorem IsPolyhedralFan.separatesComplexes_of_fanWall_strictlyInward {S : Type} [DecidableEq S]
    [Fintype S] {N : Network S} (hwr : N.WeaklyReversible) {F : Fan (EuclideanSpace ℝ S)}
    (_hF : IsPolyhedralFan F) {D C : ProperCone ℝ (EuclideanSpace ℝ S)} {n : S → ℝ}
    (_hwall : N.IsFanWall F D C n) {r : N.R}
    (hin : 0 < ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ) :
    N.SeparatesComplexes n (N.reaction r).source (N.reaction r).target :=
  Network.separatesComplexes_of_reaction_strictlyInward hwr r hin

/-- **The genuine toric field is a strict support field — from fan geometry and weak reversibility
alone.** For a polyhedral fan and a weakly-reversible network, if every face of the angular face list
is an exposed-face wall of the fan that carries a strictly-inward reaction (its geometric
non-triviality), is non-strictly inward across every reaction (the cone condition the fan supplies),
and has strictly-positive boundary concentrations, then the genuine toric mass-action field is a
strict support field for the faces. The per-wall `SeparatesComplexes` obligation of
`IsPolyhedralFan.toricMassActionField_isStrictSupportField_of_separatingWalls` is discharged here:
the strictly-inward reaction's mutually-reachable endpoints are the separation witness. The
strict-support verdict rests on the fan geometry and weak reversibility, with no separation
hypothesis supplied by hand. -/
theorem IsPolyhedralFan.toricMassActionField_isStrictSupportField_of_fan {S : Type} [DecidableEq S]
    [Fintype S] {N : Network S} (hwr : N.WeaklyReversible) {F : Fan (EuclideanSpace ℝ S)}
    (hF : IsPolyhedralFan F) (κ : N.RateConstants) {faces : List (EuclideanSpace ℝ S × ℝ)}
    (hfaces : ∀ nf ∈ faces, ∃ (n₀ : S → ℝ) (D C : ProperCone ℝ (EuclideanSpace ℝ S)) (r : N.R),
      nf.1 = toEuclid n₀ ∧
      N.IsFanWall F D C n₀ ∧ 0 < ⟪toEuclid n₀, toEuclid (N.reactionVector r)⟫_ℝ ∧
      (∀ r : N.R, 0 ≤ ⟪toEuclid n₀, toEuclid (N.reactionVector r)⟫_ℝ) ∧
      (∀ p : EuclideanSpace ℝ S,
        ZeroSeparatingCurve2D.OnFaceBoundary faces (toEuclid n₀) nf.2 p →
          Concentration.Positive (toEuclid.symm p))) :
    ZeroSeparatingCurve2D.IsStrictSupportField (N.toricMassActionField κ) faces := by
  refine hF.toricMassActionField_isStrictSupportField_of_separatingWalls hwr κ ?_
  intro nf hnf
  obtain ⟨n₀, D, C, r, hn₀, hwall, hin, hinward, hpos⟩ := hfaces nf hnf
  exact ⟨n₀, D, C, (N.reaction r).source, (N.reaction r).target, hn₀, hwall,
    hF.separatesComplexes_of_fanWall_strictlyInward hwr hwall hin, hinward, hpos⟩

end CRNT

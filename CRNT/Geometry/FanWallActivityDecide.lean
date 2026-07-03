import CRNT.Geometry.FanSeparationWitness
import CRNT.Decision.DirectedReachability

/-!
# A finite inward-reaction witness for fan-wall activity

`CRNT.Geometry.FanActiveWalls` reduces the strict-support verdict for the genuine toric mass-action
field of Craciun, _Toric differential inclusions and a proof of the global attractor conjecture_, to
a per-wall `SeparatesComplexes` obligation: a mutually-reachable complex pair on which the wall
normal's `complexPotential` differs. `CRNT.Geometry.FanSeparationWitness` supplies that pair from a
*hand-named* reaction strictly inward across the wall. This module replaces the hand-named reaction
with a **finite search over the reaction index type**: the wall normal `n` admits an inward reaction
when some `r : N.R` raises the wall potential from its source to its target, and the witnessing
complexes are read off that reaction's endpoints under weak reversibility.

## The inward-reaction predicate

A reaction `r` is *inward* across the wall `n` when the wall potential strictly increases along it,
`complexPotential n (source r) < complexPotential n (target r)` — equivalently the inner product
`0 < ⟪toEuclid n, toEuclid (reactionVector r)⟫` (`CRNT.Network.reaction_strictlyInward_iff_potential_lt`).
The wall `n` *has an inward reaction* when some `r : N.R` is inward across it. Because `N.R` is a
`Fintype`, this is a finite existential — a `Finset`-witness whose search ranges over the reaction
index type, not over the infinite complex space.

The inward-reaction predicate is exactly the wall-crossing predicate `WallCrossedByPath` with the
threshold collapsed: taking the offset `a = complexPotential n (source r)`, the directed step
`source r ⇝ target r` straddles it (`hasInwardReaction_imp_wallCrossedByPath`).

## From the finite witness to the separation obligation

Under weak reversibility a reaction's source and target are mutually reachable
(`CRNT.Network.reaches_of_reaction`, `CRNT.Network.WeaklyReversible.reaches_symm`), so an inward
reaction's endpoints are a `SeparatesComplexes` pair: their potentials differ, and each reaches the
other (`separatesComplexes_of_hasInwardReaction`). This discharges the per-wall `SeparatesComplexes`
hypothesis of `IsPolyhedralFan.toricMassActionField_isStrictSupportField_of_separatingWalls` from the
finite inward search, with no hand-named complex pair.

## What is decidable

The reachability half of the obligation is fully decidable: directed reachability among the
network's complexes is decided by a forward closure on `Finset`s
(`CRNT.Network.decidableReachesV`), and weak reversibility itself is decidable
(`instance : Decidable N.WeaklyReversible`). The inward search `HasInwardReaction n` is a finite
existential over `N.R`, hence decidable **once the per-reaction comparison `InwardReaction n r` is**
— a strict inequality of the reals `complexPotential n y = ∑ s, n s · (y s : ℝ)`. Real comparison
carries no computable `Decidable` instance, so for an arbitrary real wall normal the inward search is
not closed by `decide`; the decidability is supplied as the typeclass hypothesis
`DecidablePred (N.InwardReaction n)`, which a rational wall normal discharges. The reachability
skeleton, by contrast, is `decide`-closed unconditionally.

* `InwardReaction`, `HasInwardReaction` — the per-reaction inward predicate and its finite
  existential over the reaction index type.
* `decidableHasInwardReaction` — the inward search is decidable given a decision for the per-reaction
  real comparison.
* `hasInwardReaction_of_decide` — the `decide`-driven entry point for the inward search, under that
  decision hypothesis.
* `separatesComplexes_of_hasInwardReaction` — an inward reaction's endpoints separate the wall, under
  weak reversibility.
* `IsPolyhedralFan.toricMassActionField_isStrictSupportField_of_inwardReactions` — the deliverable:
  `IsStrictSupportField` for the genuine toric field on a face list each of whose walls is a
  polyhedral-fan exposed-face wall carrying an inward reaction (found by the finite search), with the
  cone non-strictness and boundary positivity the fan supplies. The per-wall `SeparatesComplexes`
  obligation is discharged from the finite inward search and weak reversibility, with no hand-named
  complex pair.

## Scope

This removes the hand-named separation witness on the toric route, replacing it with a finite search
over the reaction index type plus weak reversibility. It does **not** by itself prove the global
attractor conjecture past critical siphons: that route remains gated on the `IsPolyhedralFan`
covering and intersection axioms and the set-valued Nagumo invariance, which decide *which* exposed
faces of a given fan are the walls touched by the reaction directions. The finite witness here closes
the per-wall separation obligation once such a wall and its inward reaction are in hand; it does not
manufacture the fan walls.

Depends on: `CRNT.Geometry.FanSeparationWitness`,
`CRNT.Decision.DirectedReachability`.
-/

namespace CRNT

open scoped InnerProductSpace

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **An inward reaction.** The reaction `r` is inward across the wall `n` when the wall potential
strictly increases along it: `complexPotential n (source r) < complexPotential n (target r)`. By
`reaction_strictlyInward_iff_potential_lt` this is the strictly-inward inner-product condition
`0 < ⟪toEuclid n, toEuclid (reactionVector r)⟫`. -/
def InwardReaction (N : Network S) (n : S → ℝ) (r : N.R) : Prop :=
  complexPotential n (N.reaction r).source < complexPotential n (N.reaction r).target

/-- An inward reaction is strictly inward in the inner-product sense: its reaction vector has
positive component along the wall normal. -/
theorem inwardReaction_iff_strictlyInward (N : Network S) (n : S → ℝ) (r : N.R) :
    N.InwardReaction n r ↔ 0 < ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ :=
  (reaction_strictlyInward_iff_potential_lt N n r).symm

/-- **The wall has an inward reaction.** Some reaction of the network is inward across the wall `n`.
This is a finite existential over the reaction index type `N.R`: the search ranges over the finitely
many reactions, not over the infinite complex space. It is `WallCrossedByPath n` with the threshold
collapsed to the inward reaction's source potential. -/
def HasInwardReaction (N : Network S) (n : S → ℝ) : Prop :=
  ∃ r : N.R, N.InwardReaction n r

/-- The inward search is decidable once the per-reaction inward comparison is. The comparison is a
strict inequality of the reals `complexPotential n y`; a rational wall normal supplies its decision,
after which the finite existential over `N.R` is decided by ranging over the reaction index type. -/
instance decidableHasInwardReaction (N : Network S) (n : S → ℝ)
    [DecidablePred (N.InwardReaction n)] : Decidable (N.HasInwardReaction n) :=
  Fintype.decidableExistsFintype

/-- **The `decide`-driven inward search.** When the inward search returns `true` — under a decision
for the per-reaction real comparison — the wall `n` has an inward reaction. The reachability skeleton
needed to turn this into a separation witness is itself `decide`-closed (weak reversibility is
decidable); the residual decision is exactly the strict comparison of wall potentials. -/
theorem hasInwardReaction_of_decide (N : Network S) (n : S → ℝ)
    [DecidablePred (N.InwardReaction n)] (h : decide (N.HasInwardReaction n) = true) :
    N.HasInwardReaction n :=
  of_decide_eq_true h

/-- **The collapsed crossing.** A wall with an inward reaction is crossed by a directed path: the
single inward step `source r ⇝ target r` straddles the threshold `complexPotential n (source r)`, so
the `∃ a` of `WallCrossedByPath` collapses to that source potential. -/
theorem hasInwardReaction_imp_wallCrossedByPath (N : Network S) {n : S → ℝ}
    (h : N.HasInwardReaction n) : N.WallCrossedByPath n := by
  obtain ⟨r, hr⟩ := h
  exact ⟨(N.reaction r).source, (N.reaction r).target, complexPotential n (N.reaction r).source,
    N.reaches_of_reaction r, le_rfl, hr⟩

/-- **An inward reaction supplies a separation witness.** Under weak reversibility an inward
reaction's source and target are mutually reachable, and the inward condition is exactly the
inequality of their wall potentials, so the endpoints are a `SeparatesComplexes` pair. The witnessing
complexes are read off the reaction found by the finite search — no hand-named pair is supplied. -/
theorem separatesComplexes_of_hasInwardReaction {N : Network S} (hwr : N.WeaklyReversible)
    {n : S → ℝ} (r : N.R) (hr : N.InwardReaction n r) :
    N.SeparatesComplexes n (N.reaction r).source (N.reaction r).target :=
  separatesComplexes_of_reaction_strictlyInward hwr r
    ((N.inwardReaction_iff_strictlyInward n r).mp hr)

end Network

/-- **A polyhedral-fan wall with an inward reaction separates its endpoints.** The fan and
exposed-face data frame `n` as a genuine boundary direction; an inward reaction (found by the finite
search over the reaction index type) is its geometric non-triviality, and under weak reversibility
that reaction's mutually-reachable endpoints are the separation witness. -/
theorem IsPolyhedralFan.separatesComplexes_of_fanWall_hasInwardReaction {S : Type} [DecidableEq S]
    [Fintype S] {N : Network S} (hwr : N.WeaklyReversible) {F : Fan (EuclideanSpace ℝ S)}
    (_hF : IsPolyhedralFan F) {D C : ProperCone ℝ (EuclideanSpace ℝ S)} {n : S → ℝ}
    (_hwall : N.IsFanWall F D C n) {r : N.R} (hr : N.InwardReaction n r) :
    N.SeparatesComplexes n (N.reaction r).source (N.reaction r).target :=
  Network.separatesComplexes_of_hasInwardReaction hwr r hr

/-- **The genuine toric field is a strict support field — separation from the finite inward search.**
For a polyhedral fan and a weakly-reversible network, if every face of the angular face list is an
exposed-face wall of the fan that carries an inward reaction (found by the finite search over the
reaction index type), is non-strictly inward across every reaction (the cone condition the fan
supplies), and has strictly-positive boundary concentrations, then the genuine toric mass-action
field is a strict support field for the faces. The per-wall `SeparatesComplexes` obligation of
`IsPolyhedralFan.toricMassActionField_isStrictSupportField_of_separatingWalls` is discharged here from
the finite inward search and weak reversibility: the inward reaction's mutually-reachable endpoints
are the separation witness, with no hand-named complex pair. -/
theorem IsPolyhedralFan.toricMassActionField_isStrictSupportField_of_inwardReactions {S : Type}
    [DecidableEq S] [Fintype S] {N : Network S} (hwr : N.WeaklyReversible)
    {F : Fan (EuclideanSpace ℝ S)} (hF : IsPolyhedralFan F) (κ : N.RateConstants)
    {faces : List (EuclideanSpace ℝ S × ℝ)}
    (hfaces : ∀ nf ∈ faces, ∃ (n₀ : S → ℝ) (D C : ProperCone ℝ (EuclideanSpace ℝ S)) (r : N.R),
      nf.1 = toEuclid n₀ ∧
      N.IsFanWall F D C n₀ ∧ N.InwardReaction n₀ r ∧
      (∀ r : N.R, 0 ≤ ⟪toEuclid n₀, toEuclid (N.reactionVector r)⟫_ℝ) ∧
      (∀ p : EuclideanSpace ℝ S,
        ZeroSeparatingCurve2D.OnFaceBoundary faces (toEuclid n₀) nf.2 p →
          Concentration.Positive (toEuclid.symm p))) :
    ZeroSeparatingCurve2D.IsStrictSupportField (N.toricMassActionField κ) faces := by
  refine hF.toricMassActionField_isStrictSupportField_of_separatingWalls hwr κ ?_
  intro nf hnf
  obtain ⟨n₀, D, C, r, hn₀, hwall, hr, hinward, hpos⟩ := hfaces nf hnf
  exact ⟨n₀, D, C, (N.reaction r).source, (N.reaction r).target, hn₀, hwall,
    hF.separatesComplexes_of_fanWall_hasInwardReaction hwr hwall hr, hinward, hpos⟩

end CRNT

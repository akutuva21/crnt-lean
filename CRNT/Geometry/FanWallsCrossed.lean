import CRNT.Geometry.ToricWRStrictInward

/-!
# Active fan walls are crossed by weakly-reversible paths

`CRNT.Geometry.ToricWRStrictInward` discharges the strictly-inward part of
`IsStrictSupportField` for the genuine toric mass-action field of Craciun, _Toric differential
inclusions and a proof of the global attractor conjecture_, from the *crossing* hypothesis
`WallCrossedByPath`: a wall whose complex potential is straddled by a directed reaction path has a
strictly-inward reaction. That left the crossing hypothesis itself as input. This module supplies
the crossing for a **weakly-reversible** network from the structure of the reaction graph, with no
two-dimensional or single-fan restriction.

## The active wall

A wall normal `n : S → ℝ` is *active* on a strongly-connected piece of the reaction graph when it
fails to be constant on the complexes there: two mutually-reachable complexes `c`, `d` have distinct
complex potentials, `complexPotential n c ≠ complexPotential n d`. An inactive wall — constant
potential on the component — separates nothing, so only active walls carry geometric content. The
active condition is exactly the "the wall normal is non-constant on the reaction complexes" clause:
an active boundary wall genuinely separates the complexes it touches.

## From active to crossed, under weak reversibility

Weak reversibility makes directed reachability symmetric (`WeaklyReversible.reaches_comm`): every
connected component of the reaction graph is strongly connected. So if `c` and `d` are mutually
reachable and their potentials differ, the complex of *lower* potential reaches the complex of
*higher* potential along a directed path — a directed crossing of any threshold strictly between the
two potentials. That is `WallCrossedByPath`:

* `ActiveWall` — the active-wall predicate: two reachable complexes with distinct wall potential.
* `WeaklyReversible.wallCrossedByPath_of_activeWall` — the core fact: under weak reversibility an
  active wall is crossed by a directed path. A WR cycle through the wall is exactly such a path; the
  symmetric reachability of weak reversibility removes any orientation assumption on the witnessing
  pair.
* `WeaklyReversible.wallCrossedByPath_of_directlyReacts` — the same conclusion from a single reaction
  straddling the wall (`complexPotential n` differs across one reaction's source and target): such a
  reaction is itself a directed crossing, no symmetry needed.
* `WeaklyReversible.exists_strictlyInward_of_activeWall` — chaining the crossing into the strictly-
  inward extraction of `ToricWRStrictInward`: an active wall of a weakly-reversible network has a
  strictly-inward reaction.

## The strict support field with the crossing discharged

Chaining the per-wall crossing across a face list whose walls are all active gives the genuine toric
field as a strict support field with the `WallCrossedByPath` clause of
`toricMassActionField_isStrictSupportField_of_wallsCrossed` discharged from weak reversibility and
the per-wall activity:

* `WeaklyReversible.toricMassActionField_isStrictSupportField_of_activeWalls` — the deliverable:
  `IsStrictSupportField` for the genuine toric field on a face list every wall of which is active,
  for a weakly-reversible network. The only per-wall geometric inputs retained are the cone
  non-strictness `0 ≤ ⟪n, reactionVector r⟫` (the fan supplies this) and strict positivity of the
  boundary concentration (the enabling input); the *crossing* is no longer assumed.

## Scope

The deliverable is: active boundary wall + weak reversibility ⟹ the wall is crossed by a directed
path ⟹ strictly-inward reaction ⟹ the strict support field with the crossing clause discharged. The
crossing argument is dimension-free — it consumes only the symmetric reachability of weak
reversibility and the potential identity of `ToricWRStrictInward`.

What is carried as an explicit hypothesis rather than derived is that the genuinely-active boundary
walls of a *concrete* polyhedral fan are exactly the walls whose normals are non-constant across the
reaction complexes (`ActiveWall`). Identifying `IsPolyhedralFan`'s exposed-face walls with this
potential-non-constancy condition for an arbitrary fan is the per-wall normal geometry of the fan,
separate from this graph-theoretic crossing extraction.

Depends on: `CRNT.Geometry.ToricWRStrictInward`.
-/

namespace CRNT

namespace Network

open scoped InnerProductSpace

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **An active wall.** The wall normal `n` is active when it is non-constant on a strongly-connected
piece of the reaction graph: two mutually-reachable complexes `c ⇝ d ⇝ c` have distinct wall
potentials. An inactive wall has constant potential on the component, so it separates none of the
complexes it touches; only active walls carry the separating geometry of a genuine boundary wall. -/
def ActiveWall (N : Network S) (n : S → ℝ) : Prop :=
  ∃ c d : Complex S, N.Reaches c d ∧ N.Reaches d c ∧
    complexPotential n c ≠ complexPotential n d

/-- An active wall is symmetric in its witnessing complexes: swapping `c` and `d` exchanges the two
reachability directions and negates the potential gap, which is still nonzero. -/
theorem ActiveWall.symm {N : Network S} {n : S → ℝ} (h : N.ActiveWall n) :
    ∃ c d : Complex S, N.Reaches c d ∧ N.Reaches d c ∧ complexPotential n c < complexPotential n d := by
  obtain ⟨c, d, hcd, hdc, hne⟩ := h
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨c, d, hcd, hdc, hlt⟩
  · exact ⟨d, c, hdc, hcd, hgt⟩

/-- **Core fact — an active wall of a weakly-reversible network is crossed.** Under weak
reversibility every component is strongly connected, so the witnessing pair of an active wall is
mutually reachable for free; orienting it so the lower potential reaches the higher one exhibits a
directed path whose endpoints straddle any threshold strictly between the two potentials. That is
`WallCrossedByPath`. A WR cycle through the wall is exactly such a path. -/
theorem WeaklyReversible.wallCrossedByPath_of_activeWall {N : Network S}
    (_hwr : N.WeaklyReversible) {n : S → ℝ} (h : N.ActiveWall n) :
    N.WallCrossedByPath n := by
  obtain ⟨c, d, hcd, _hdc, hlt⟩ := h.symm
  exact ⟨c, d, complexPotential n c, hcd, le_rfl, hlt⟩

/-- **A single straddling reaction crosses the wall.** If one reaction's source and target have
distinct wall potentials, the wall is crossed: the reaction (or its weak-reversibility return path,
whichever runs uphill) is a directed crossing. No strong-connectivity input beyond weak reversibility
is needed — the reaction itself supplies the directed step. -/
theorem WeaklyReversible.wallCrossedByPath_of_directlyReacts {N : Network S}
    (hwr : N.WeaklyReversible) {n : S → ℝ} (r : N.R)
    (hne : complexPotential n (N.reaction r).source ≠ complexPotential n (N.reaction r).target) :
    N.WallCrossedByPath n := by
  refine hwr.wallCrossedByPath_of_activeWall ⟨(N.reaction r).source, (N.reaction r).target, ?_, ?_, hne⟩
  · exact N.reaches_of_reaction r
  · exact hwr r

/-- **An active wall of a weakly-reversible network has a strictly-inward reaction.** Chains the
crossing of `wallCrossedByPath_of_activeWall` into the strictly-inward extraction
`exists_strictlyInward_of_wallCrossed` of `CRNT.Geometry.ToricWRStrictInward`. -/
theorem WeaklyReversible.exists_strictlyInward_of_activeWall {N : Network S}
    (hwr : N.WeaklyReversible) {n : S → ℝ} (h : N.ActiveWall n) :
    ∃ r : N.R, 0 < ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ :=
  N.exists_strictlyInward_of_wallCrossed (hwr.wallCrossedByPath_of_activeWall h)

/-- **An active wall is an enabled strictly-inward face, under weak reversibility.** With the wall
active, every reaction non-strictly inward across it (the fan cone condition), and every boundary
point a strictly-positive concentration (the enabling input), the face is
`EnabledStrictlyInwardFace`: the crossing is supplied by weak reversibility plus activity rather than
assumed. -/
theorem WeaklyReversible.enabledStrictlyInwardFace_of_activeWall {N : Network S}
    (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {faces : List (EuclideanSpace ℝ S × ℝ)} {n : S → ℝ} {a : ℝ}
    (hactive : N.ActiveWall n)
    (hinward : ∀ r : N.R, 0 ≤ ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ)
    (hpos : ∀ p : EuclideanSpace ℝ S, ZeroSeparatingCurve2D.OnFaceBoundary faces (toEuclid n) a p →
      Concentration.Positive (toEuclid.symm p)) :
    N.EnabledStrictlyInwardFace κ faces n a :=
  N.enabledStrictlyInwardFace_of_wallCrossed κ (hwr.wallCrossedByPath_of_activeWall hactive) hinward
    hpos

/-- **The genuine toric field is a strict support field — crossing discharged from weak
reversibility.** If every face's wall normal is active and (the fan-supplied) non-strictly inward,
and every boundary point is a strictly-positive concentration, then the genuine toric mass-action
field of a weakly-reversible network is a strict support field for `faces`. The `WallCrossedByPath`
clause of `toricMassActionField_isStrictSupportField_of_wallsCrossed` is discharged here from weak
reversibility plus per-wall activity; the only retained per-wall geometric inputs are the cone
non-strictness and the boundary positivity. -/
theorem WeaklyReversible.toricMassActionField_isStrictSupportField_of_activeWalls {N : Network S}
    (hwr : N.WeaklyReversible) (κ : N.RateConstants) {faces : List (EuclideanSpace ℝ S × ℝ)}
    (hfaces : ∀ nf ∈ faces, ∃ n₀ : S → ℝ, nf.1 = toEuclid n₀ ∧
      N.ActiveWall n₀ ∧
      (∀ r : N.R, 0 ≤ ⟪toEuclid n₀, toEuclid (N.reactionVector r)⟫_ℝ) ∧
      (∀ p : EuclideanSpace ℝ S,
        ZeroSeparatingCurve2D.OnFaceBoundary faces (toEuclid n₀) nf.2 p →
          Concentration.Positive (toEuclid.symm p))) :
    ZeroSeparatingCurve2D.IsStrictSupportField (N.toricMassActionField κ) faces := by
  refine N.toricMassActionField_isStrictSupportField_of_wallsCrossed κ ?_
  intro nf hnf
  obtain ⟨n₀, hn₀, hactive, hinward, hpos⟩ := hfaces nf hnf
  exact ⟨n₀, hn₀, hwr.wallCrossedByPath_of_activeWall hactive, hinward, hpos⟩

end Network

end CRNT

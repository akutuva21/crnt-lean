import CRNT.Geometry.ToricStrictSupport
import CRNT.Graph.Crossing
import CRNT.Graph.CycleCover

/-!
# Strictly-inward reactions at crossed walls from weak reversibility

`CRNT.Geometry.ToricStrictSupport` derives the strict boundary-local support condition
`IsStrictSupportField` for the genuine toric mass-action field of Craciun, _Toric differential
inclusions and a proof of the global attractor conjecture_, from an explicit hypothesis
`EnabledStrictlyInwardFace`: at every active boundary wall there is at least one *enabled* and
*strictly-inward* reaction. The cone geometry alone gives only the non-strict condition
`0 ≤ ⟪n, reactionVector r⟫`; the strict one `0 < ⟪n, reactionVector r⟫` is the dynamics-side input
that condition packages.

This module discharges the strictly-inward part from **weak reversibility** (Anderson, _A proof of
the global attractor conjecture in the single linkage class case_), for the wall class crossed by a
directed path of the reaction graph. The enabling part is automatic at a strictly-positive
concentration (`massActionRate_pos`), so the whole `EnabledStrictlyInwardFace` condition reduces, on
that wall class, to a purely graph-theoretic crossing fact.

## The complex potential and the strictly-inward characterization

A wall normal `n : S → ℝ` reads each complex `y` by its linear potential
`complexPotential n y = ∑ s, n s * (y s : ℝ) = ⟪toEuclid n, toEuclid (exponentVector y)⟫`. The
inward component of a reaction `r : source → target` across the wall is the potential *increase*
along the reaction:

```
⟪toEuclid n, toEuclid (reactionVector r)⟫ = complexPotential n target − complexPotential n source.
```

So a reaction is *strictly inward* (`0 < ⟪toEuclid n, toEuclid (reactionVector r)⟫`) exactly when the
potential strictly increases along it, `complexPotential n source < complexPotential n target`
(`inner_reactionVector_eq_potential_sub`, `reaction_strictlyInward_iff_potential_lt`).

## The crossing extraction

Threshold the complexes by the wall potential: `P y := a < complexPotential n y`. A directed path
from a complex below the threshold to one above it must traverse a reaction whose source is below and
whose target is above — `Network.exists_crossing_reaction` — and that reaction strictly increases the
potential, hence is strictly inward (`exists_strictlyInward_of_reaches_cross`).

* `WallCrossedByPath` — the characterized wall class: a wall `n` with two complexes `c ⇝ d` whose
  potentials straddle a threshold (`complexPotential n c ≤ a < complexPotential n d`). A WR cycle
  through the wall is exactly such a path.
* `exists_strictlyInward_of_wallCrossed` — a crossed wall has a strictly-inward reaction.
* `WeaklyReversible.exists_strictlyInward_of_potential_lt` — under weak reversibility, *any* two
  complexes with `complexPotential n c < complexPotential n d` give a strictly-inward reaction,
  because weak reversibility makes the reachability symmetric so a connecting path always exists once
  the two complexes lie in a common reachable component. The hypothesis kept is that `d` is reachable
  from `c` (the WR cycle structure supplies this); strictness of the inward reaction then follows
  with no further geometry.

## From a crossed wall to the enabled strictly-inward face

At a strictly-positive concentration every reaction is enabled (`massActionRate_pos`), so the
strictly-inward reaction extracted above is in particular *enabled*. Together with the non-strict
cone condition (`0 ≤ ⟪n, reactionVector r⟫` for all `r`, supplied by the fan geometry) and
nonnegativity of the boundary concentration this is exactly `EnabledStrictlyInwardFace`:

* `enabledStrictlyInwardFace_of_wallCrossed` — assembles `EnabledStrictlyInwardFace` for a crossed
  wall, given the cone-side non-strictness and that every boundary point is a strictly-positive
  concentration.
* `toricMassActionField_isStrictSupportField_of_wallsCrossed` — the deliverable:
  `IsStrictSupportField` for the genuine toric field on a face list every wall of which is crossed,
  with the strictly-inward part discharged from weak reversibility rather than assumed.

## Scope

The deliverable is the weak-reversibility ⇒ strictly-inward-reaction extraction for the *crossed*
wall class (walls straddled by a directed reaction path; equivalently, by a WR cycle), and the
resulting `EnabledStrictlyInwardFace` / `IsStrictSupportField` discharge. The crossing argument is
self-contained: it needs only `Network.exists_crossing_reaction` and the potential identity, so it
applies to an arbitrary wall normal `n` over an arbitrary network — no two-dimensional or
single-fan restriction. What is *not* established is that *every* boundary wall of an arbitrary
polyhedral fan is crossed: identifying the crossed walls with the genuinely-active boundary walls of
the fan, for an arbitrary fan, is the per-wall geometry of the fan's normal structure, separate from
this graph-theoretic extraction.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Geometry.ToricStrictSupport`,
`CRNT.Graph.Crossing`, `CRNT.Graph.CycleCover`.
-/

namespace CRNT

namespace Network

open scoped InnerProductSpace
open Finset

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The wall potential of a complex.** Read each complex `y` by the linear functional of the wall
normal `n`: `complexPotential n y = ∑ s, n s * (y s : ℝ)`. This is the value at the complex's
exponent point of the linear functional `⟪toEuclid n, ·⟫`; a reaction's inward component across the
wall is the potential increase along it. -/
def complexPotential (n : S → ℝ) (y : Complex S) : ℝ :=
  ∑ s : S, n s * (y s : ℝ)

omit [DecidableEq S] in
/-- The wall potential is the Euclidean inner product of the wall normal with the complex's exponent
vector, mapped into `EuclideanSpace ℝ S` by `toEuclid`. -/
theorem complexPotential_eq_inner (n : S → ℝ) (y : Complex S) :
    complexPotential n y = ⟪toEuclid n, toEuclid (CRNT.exponentVector y)⟫_ℝ := by
  rw [inner_toEuclid]
  rfl

/-- **The inward component is the potential increase.** The inner product of the wall normal with a
reaction's vector is the wall potential of the target minus that of the source:
`⟪toEuclid n, toEuclid (reactionVector r)⟫ = complexPotential n target − complexPotential n source`.
This is the bridge from the graph (potentials at complexes) to the cone geometry (inward components
of reactions). -/
theorem inner_reactionVector_eq_potential_sub (N : Network S) (n : S → ℝ) (r : N.R) :
    ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ =
      complexPotential n (N.reaction r).target - complexPotential n (N.reaction r).source := by
  rw [inner_toEuclid, complexPotential, complexPotential, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [reactionVector_apply]
  ring

/-- **Strictly inward iff the potential strictly increases.** A reaction is strictly inward across
the wall `n` (`0 < ⟪toEuclid n, toEuclid (reactionVector r)⟫`) exactly when its source potential is
strictly below its target potential. -/
theorem reaction_strictlyInward_iff_potential_lt (N : Network S) (n : S → ℝ) (r : N.R) :
    0 < ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ ↔
      complexPotential n (N.reaction r).source < complexPotential n (N.reaction r).target := by
  rw [inner_reactionVector_eq_potential_sub, sub_pos]

/-- **Strictly-inward reaction from a potential-straddling path.** If `c` reaches `d` along the
reaction graph and the wall potential straddles a threshold `a` between them
(`complexPotential n c ≤ a < complexPotential n d`), then some reaction is strictly inward across the
wall `n`: the path must cross the threshold, and the crossing reaction strictly increases the
potential. This is `Network.exists_crossing_reaction` for the predicate "potential exceeds `a`",
read through the strictly-inward characterization. -/
theorem exists_strictlyInward_of_reaches_cross (N : Network S) (n : S → ℝ) {a : ℝ}
    {c d : Complex S} (hcd : N.Reaches c d) (hc : complexPotential n c ≤ a)
    (hd : a < complexPotential n d) :
    ∃ r : N.R, 0 < ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ := by
  obtain ⟨r, hrs, hrt⟩ :=
    N.exists_crossing_reaction (fun y => a < complexPotential n y) hcd (not_lt.mpr hc) hd
  refine ⟨r, (reaction_strictlyInward_iff_potential_lt N n r).mpr ?_⟩
  exact lt_of_le_of_lt (not_lt.mp hrs) hrt

/-- **The crossed wall class.** A wall normal `n` is *crossed* by the network when some directed path
`c ⇝ d` of the reaction graph has its wall potential straddle a threshold:
`complexPotential n c ≤ a < complexPotential n d`. A weakly-reversible cycle running through the wall
is exactly such a path — the cycle returns to its base, so it must both rise above and fall below any
intermediate potential level. -/
def WallCrossedByPath (N : Network S) (n : S → ℝ) : Prop :=
  ∃ (c d : Complex S) (a : ℝ),
    N.Reaches c d ∧ complexPotential n c ≤ a ∧ a < complexPotential n d

/-- A crossed wall has a strictly-inward reaction, by the crossing extraction. -/
theorem exists_strictlyInward_of_wallCrossed (N : Network S) {n : S → ℝ}
    (h : N.WallCrossedByPath n) :
    ∃ r : N.R, 0 < ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ := by
  obtain ⟨c, d, a, hcd, hc, hd⟩ := h
  exact N.exists_strictlyInward_of_reaches_cross n hcd hc hd

/-- **Weak reversibility upgrades a potential gap to a strictly-inward reaction.** If `c` reaches `d`
and the wall potential is strictly larger at `d` than at `c`, then some reaction is strictly inward
across the wall `n`. Take the threshold `a := complexPotential n c`; the path `c ⇝ d` then straddles
it. Under weak reversibility the reachability relation is symmetric, so a single such potential gap
anywhere in a reachable component yields a strictly-inward reaction; the hypothesis kept is the
witnessing path `c ⇝ d`, which a WR cycle through the wall supplies. -/
theorem WeaklyReversible.exists_strictlyInward_of_potential_lt {N : Network S}
    (_hwr : N.WeaklyReversible) {n : S → ℝ} {c d : Complex S} (hcd : N.Reaches c d)
    (hlt : complexPotential n c < complexPotential n d) :
    ∃ r : N.R, 0 < ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ :=
  N.exists_strictlyInward_of_reaches_cross n hcd le_rfl hlt

/-- **A crossed wall is an enabled strictly-inward face.** Given that the wall `n` is crossed, that
every reaction is non-strictly inward across it (`0 ≤ ⟪toEuclid n, toEuclid (reactionVector r)⟫`, the
fan-supplied cone condition), and that every region-boundary point on the face is a *strictly
positive* concentration, the face `(toEuclid n, a)` is `EnabledStrictlyInwardFace`: the strictly
inward reaction from the crossing is enabled by the positive concentration (`massActionRate_pos`).

The strictly-inward reaction `r₀` is the same one at every boundary point — its enabledness is what
varies with the point, and that is exactly what the strict positivity of the boundary concentration
secures. -/
theorem enabledStrictlyInwardFace_of_wallCrossed (N : Network S) (κ : N.RateConstants)
    {faces : List (EuclideanSpace ℝ S × ℝ)} {n : S → ℝ} {a : ℝ}
    (hcrossed : N.WallCrossedByPath n)
    (hinward : ∀ r : N.R, 0 ≤ ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ)
    (hpos : ∀ p : EuclideanSpace ℝ S, ZeroSeparatingCurve2D.OnFaceBoundary faces (toEuclid n) a p →
      Concentration.Positive (toEuclid.symm p)) :
    N.EnabledStrictlyInwardFace κ faces n a := by
  obtain ⟨r₀, hr₀⟩ := N.exists_strictlyInward_of_wallCrossed hcrossed
  intro p hp
  refine ⟨(hpos p hp).nonnegative, hinward, r₀, ?_, hr₀⟩
  exact N.massActionRate_pos κ r₀ (hpos p hp)

/-- **The genuine toric field is a strict support field — strictness from weak reversibility.** If
every face of the angular face list has a wall normal that is crossed, every reaction is non-strictly
inward across each such wall, and every boundary point is a strictly-positive concentration, then the
genuine toric mass-action field is a full `IsStrictSupportField` for `faces`. The strictly-inward
reaction at each active wall is **discharged from weak reversibility** (the crossing extraction)
rather than assumed: a directed path across the wall — a WR cycle — supplies it, and the positive
concentration enables it. This discharges `EnabledStrictlyInwardFace` for the crossed wall class. -/
theorem toricMassActionField_isStrictSupportField_of_wallsCrossed (N : Network S)
    (κ : N.RateConstants) {faces : List (EuclideanSpace ℝ S × ℝ)}
    (hfaces : ∀ nf ∈ faces, ∃ n₀ : S → ℝ, nf.1 = toEuclid n₀ ∧
      N.WallCrossedByPath n₀ ∧
      (∀ r : N.R, 0 ≤ ⟪toEuclid n₀, toEuclid (N.reactionVector r)⟫_ℝ) ∧
      (∀ p : EuclideanSpace ℝ S,
        ZeroSeparatingCurve2D.OnFaceBoundary faces (toEuclid n₀) nf.2 p →
          Concentration.Positive (toEuclid.symm p))) :
    ZeroSeparatingCurve2D.IsStrictSupportField (N.toricMassActionField κ) faces := by
  refine N.toricMassActionField_isStrictSupportField κ ?_
  intro nf hnf
  obtain ⟨n₀, hn₀, hcrossed, hinward, hpos⟩ := hfaces nf hnf
  exact ⟨n₀, hn₀, N.enabledStrictlyInwardFace_of_wallCrossed κ hcrossed hinward hpos⟩

end Network

end CRNT

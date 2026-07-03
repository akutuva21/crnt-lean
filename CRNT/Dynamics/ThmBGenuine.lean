import CRNT.Dynamics.SublevelNagumo
import CRNT.Dynamics.ZeroSeparating
import CRNT.Kinetics.MassAction
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Zero-separating away-from-origin invariance for the genuine flow in dimension `≥ 2`

This assembles the viability results into a zero-separating, away-from-origin invariant region for
the **genuine (single-valued) flow** `ẋ = f x`, extending the zero-separating-region result of
Craciun, _Toric differential inclusions and a proof of the global attractor conjecture_, from the
1-D base case of `ZeroSeparating.lean` to all dimensions for the genuine dynamics. The persistence
consequence of the Global Attractor Conjecture needs only the genuine mass-action trajectory to
stay in the region — *not* set-valued Filippov viability of the whole inclusion.

## Contents

* `genuine_sublevel_invariant` — **genuine-flow sublevel zero-separating region.** A direct wrap of
  `sublevel_invariant_of_neighborhood_descent`: for a curve `γ` continuous on `[0, ∞)` and solving
  `HasDerivAt γ (f (γ t)) t` there, a `C¹` function `g` with neighborhood descent
  `g' y (f y) ≤ 0` on the band `{c − δ ≤ g y ≤ c + δ}`, and `g (γ 0) ≤ c`, the curve stays in the
  sublevel set: `g (γ t) ≤ c` for all `t ≥ 0`.

* `genuine_away_from_origin` — **away-from-origin (persistence) consequence.** Adding a separation
  hypothesis that the sublevel set `{g ≤ c}` misses the open ball `Metric.ball 0 r` (`r > 0`), the
  genuine trajectory keeps a hard distance `r` from the origin: `r ≤ dist (γ t) 0` for all
  `t ≥ 0`. The origin is therefore not an `ω`-limit point of `γ`.

* `GenuineZeroSeparating` — a `ZeroSeparating.ZeroSeparatingRegion`-style bundle specialized to a
  single genuine curve `γ`: the sublevel region `{g ≤ c}` carries a strictly positive margin `r`,
  is forward-invariant *along `γ`*, contains `γ 0`, and excludes the `r`-ball about `0`. Its
  consequences `zero_not_mem`, `notMem_ball`, `mem_of_le`, `margin_le_dist`, `dist_pos` mirror the
  inclusion-level interface for the genuine flow.

* `massAction_genuine_away_from_origin` — **mass-action specialization.** Instantiating
  `f := N.massActionVectorField κ` over `E := Concentration S` (a finite-dimensional normed space),
  the genuine mass-action trajectory stays a distance `r` from the origin. The genuine field is
  locally Lipschitz (polynomial), so such a `γ` exists and is unique by Picard–Lindelöf; existence
  is not the point — the invariance is — so `γ` and its derivative are taken as hypotheses.

## Scope

What is **assembled here** is the genuine-flow invariance + away-from-origin conclusion, obtained
from the neighborhood-descent Nagumo lemma. The zero-separating-surface construction —
producing the function `g`, its descent band, and its separation from the origin out of the
dimension induction — is not constructed here; the function `g`, its descent band, and the
separation are supplied as hypotheses.

Depends on: `CRNT.Dynamics.SublevelNagumo`,
`CRNT.Dynamics.ZeroSeparating`, `CRNT.Kinetics.MassAction`,
`Mathlib.Analysis.InnerProductSpace.PiL2`.
-/

namespace CRNT

namespace DifferentialInclusion

open Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Genuine-flow sublevel zero-separating region.** For a curve `γ` continuous on `[0, ∞)` and
solving `HasDerivAt γ (f (γ t)) t` there, a `C¹` function `g` (derivative field `g'`) whose
neighborhood descent `g' y (f y) ≤ 0` holds on the two-sided band `{y | c − δ ≤ g y ≤ c + δ}` for
some `δ > 0`, with `g (γ 0) ≤ c`, the genuine trajectory stays in the sublevel set `{g ≤ c}`:
`g (γ t) ≤ c` for all `t ≥ 0`. A direct wrap of `sublevel_invariant_of_neighborhood_descent`. -/
theorem genuine_sublevel_invariant
    {f : E → E} {γ : ℝ → E} {g : E → ℝ} {g' : E → (E →L[ℝ] ℝ)} {c δ : ℝ}
    (hgc : Continuous g) (hg : ∀ y, HasFDerivAt g (g' y) y)
    (hγcont : Continuous γ)
    (hγderiv : ∀ t, 0 ≤ t → HasDerivAt γ (f (γ t)) t)
    (hδ : 0 < δ)
    (hdescent : ∀ y, c - δ ≤ g y → g y ≤ c + δ → g' y (f y) ≤ 0)
    (h0 : g (γ 0) ≤ c) :
    ∀ t, 0 ≤ t → g (γ t) ≤ c :=
  sublevel_invariant_of_neighborhood_descent hgc hg hγcont hγderiv hδ hdescent h0

/-- **Away-from-origin (persistence) consequence.** Under the hypotheses of
`genuine_sublevel_invariant`, add the separation that the sublevel set `{g ≤ c}` is disjoint from
the open ball `Metric.ball 0 r` (`r > 0`), i.e. `{g ≤ c} ⊆ (Metric.ball 0 r)ᶜ`. Then the genuine
trajectory keeps a hard distance `r` from the origin: `r ≤ dist (γ t) 0` for all `t ≥ 0`. Hence the
origin is not an `ω`-limit point of `γ`. -/
theorem genuine_away_from_origin
    {f : E → E} {γ : ℝ → E} {g : E → ℝ} {g' : E → (E →L[ℝ] ℝ)} {c δ r : ℝ}
    (hgc : Continuous g) (hg : ∀ y, HasFDerivAt g (g' y) y)
    (hγcont : Continuous γ)
    (hγderiv : ∀ t, 0 ≤ t → HasDerivAt γ (f (γ t)) t)
    (hδ : 0 < δ)
    (hdescent : ∀ y, c - δ ≤ g y → g y ≤ c + δ → g' y (f y) ≤ 0)
    (h0 : g (γ 0) ≤ c)
    (hsep : {y : E | g y ≤ c} ⊆ (Metric.ball (0 : E) r)ᶜ) :
    ∀ t, 0 ≤ t → r ≤ dist (γ t) 0 := by
  intro t ht
  have hmem : g (γ t) ≤ c :=
    genuine_sublevel_invariant hgc hg hγcont hγderiv hδ hdescent h0 t ht
  have hnotball : γ t ∉ Metric.ball (0 : E) r := hsep hmem
  rw [Metric.mem_ball] at hnotball
  exact not_lt.mp hnotball

/-- **Genuine zero-separating region (single-curve bundle).** Packages, for one genuine curve `γ`,
the data of `ZeroSeparating.ZeroSeparatingRegion` specialized to the genuine flow: the sublevel set
`{g ≤ c}` carries a strictly positive margin `r`, the trajectory stays inside it forward, `γ 0`
lies inside, and the `r`-ball about `0` is excluded. -/
structure GenuineZeroSeparating
    (f : E → E) (γ : ℝ → E) (g : E → ℝ) (c r : ℝ) : Prop where
  /-- The separating margin is strictly positive. -/
  margin_pos : 0 < r
  /-- The genuine trajectory stays in the sublevel region forward in time. -/
  invariant : ∀ t, 0 ≤ t → g (γ t) ≤ c
  /-- The initial point lies in the region. -/
  mem_start : g (γ 0) ≤ c
  /-- The sublevel region keeps a distance `r` from the origin: the `r`-ball about `0` is
  excluded. -/
  ball_subset_compl : Metric.ball (0 : E) r ⊆ {y : E | g y ≤ c}ᶜ

/-- Assemble a `GenuineZeroSeparating` bundle from the neighborhood-descent hypotheses and the
ball-separation hypothesis. The invariance is `genuine_sublevel_invariant`; the margin and exclusion
come from the separation hypothesis. -/
theorem genuineZeroSeparating_of_descent
    {f : E → E} {γ : ℝ → E} {g : E → ℝ} {g' : E → (E →L[ℝ] ℝ)} {c δ r : ℝ}
    (hgc : Continuous g) (hg : ∀ y, HasFDerivAt g (g' y) y)
    (hγcont : Continuous γ)
    (hγderiv : ∀ t, 0 ≤ t → HasDerivAt γ (f (γ t)) t)
    (hδ : 0 < δ)
    (hdescent : ∀ y, c - δ ≤ g y → g y ≤ c + δ → g' y (f y) ≤ 0)
    (h0 : g (γ 0) ≤ c)
    (hr : 0 < r)
    (hsep : Metric.ball (0 : E) r ⊆ {y : E | g y ≤ c}ᶜ) :
    GenuineZeroSeparating f γ g c r where
  margin_pos := hr
  invariant := genuine_sublevel_invariant hgc hg hγcont hγderiv hδ hdescent h0
  mem_start := h0
  ball_subset_compl := hsep

omit [NormedSpace ℝ E] in
/-- No point within distance `r` of the origin lies in the sublevel region of a genuine
zero-separating bundle. -/
theorem GenuineZeroSeparating.notMem_ball
    {f : E → E} {γ : ℝ → E} {g : E → ℝ} {c r : ℝ}
    (h : GenuineZeroSeparating f γ g c r) {x : E} (hx : dist x 0 < r) :
    ¬ g x ≤ c :=
  h.ball_subset_compl (Metric.mem_ball.mpr hx)

omit [NormedSpace ℝ E] in
/-- The origin is not in the sublevel region of a genuine zero-separating bundle. -/
theorem GenuineZeroSeparating.zero_not_mem
    {f : E → E} {γ : ℝ → E} {g : E → ℝ} {c r : ℝ}
    (h : GenuineZeroSeparating f γ g c r) : ¬ g (0 : E) ≤ c :=
  h.ball_subset_compl (Metric.mem_ball_self h.margin_pos)

omit [NormedSpace ℝ E] in
/-- The genuine trajectory of a zero-separating bundle stays at least the margin `r` from the
origin for all forward times. -/
theorem GenuineZeroSeparating.margin_le_dist
    {f : E → E} {γ : ℝ → E} {g : E → ℝ} {c r : ℝ}
    (h : GenuineZeroSeparating f γ g c r) :
    ∀ t, 0 ≤ t → r ≤ dist (γ t) 0 := by
  intro t ht
  have hmem : g (γ t) ≤ c := h.invariant t ht
  by_contra hlt
  exact h.notMem_ball (not_le.mp hlt) hmem

omit [NormedSpace ℝ E] in
/-- The genuine trajectory of a zero-separating bundle keeps a strictly positive distance from the
origin for all forward times: `0` is not an `ω`-limit point. -/
theorem GenuineZeroSeparating.dist_pos
    {f : E → E} {γ : ℝ → E} {g : E → ℝ} {c r : ℝ}
    (h : GenuineZeroSeparating f γ g c r) :
    ∀ t, 0 ≤ t → 0 < dist (γ t) 0 :=
  fun t ht => lt_of_lt_of_le h.margin_pos (h.margin_le_dist t ht)

end DifferentialInclusion

/-! ## Mass-action specialization

`Concentration S = S → ℝ` is, for a finite species set `S`, a finite-dimensional normed space over
`ℝ`, and `N.massActionVectorField κ : Concentration S → Concentration S` has exactly the field
shape the assembly needs. Instantiating `f` at it yields the away-from-origin conclusion for the
genuine mass-action trajectory. The genuine field is locally Lipschitz (polynomial), so such a `γ`
exists and is unique by Picard–Lindelöf; existence is not the point here, so `γ` and its derivative
are taken as hypotheses. -/

namespace Network

open DifferentialInclusion

variable {S : Type} [Fintype S] [DecidableEq S]

/-- **Away-from-origin for the genuine mass-action trajectory.** For a curve `γ` in concentration
space continuous on `[0, ∞)` and solving the genuine mass-action ODE
`HasDerivAt γ (N.massActionVectorField κ (γ t)) t` there, a `C¹` function `g` with neighborhood
descent along the mass-action field on the band `{c − δ ≤ g y ≤ c + δ}`, `g (γ 0) ≤ c`, and the
sublevel set `{g ≤ c}` separated from the `r`-ball about `0` (`r > 0`), the genuine mass-action
trajectory keeps a hard distance `r` from the origin: `r ≤ dist (γ t) 0` for all `t ≥ 0`. -/
theorem massAction_genuine_away_from_origin
    (N : Network S) (κ : RateConstants N)
    {γ : ℝ → Concentration S} {g : Concentration S → ℝ}
    {g' : Concentration S → (Concentration S →L[ℝ] ℝ)} {c δ r : ℝ}
    (hgc : Continuous g) (hg : ∀ y, HasFDerivAt g (g' y) y)
    (hγcont : Continuous γ)
    (hγderiv : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hδ : 0 < δ)
    (hdescent : ∀ y, c - δ ≤ g y → g y ≤ c + δ → g' y (N.massActionVectorField κ y) ≤ 0)
    (h0 : g (γ 0) ≤ c)
    (hsep : {y : Concentration S | g y ≤ c} ⊆ (Metric.ball (0 : Concentration S) r)ᶜ) :
    ∀ t, 0 ≤ t → r ≤ dist (γ t) 0 :=
  genuine_away_from_origin hgc hg hγcont hγderiv hδ hdescent h0 hsep

end Network

end CRNT

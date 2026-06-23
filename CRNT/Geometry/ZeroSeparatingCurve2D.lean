import CRNT.Dynamics.ClosedSetNagumo
import CRNT.Geometry.ToricFan
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The 2-D polygonal zero-separating curve

In the plane a toric differential inclusion is *constant* — equal to a polar cone — on the
interior of each exponential cone of the fan, and a half-plane field across the thin
"uncertainty region" straddling each fan line. Following Craciun, _Toric differential inclusions
and a proof of the global attractor conjecture_, the planar **zero-separating curve** is a
polygonal line running from the positive `x`-axis to the positive `y`-axis, with one vertex per
bounded exp-cone, each edge crossing an uncertainty region in that region's *attracting
direction* — the direction orthogonal to the corresponding third-quadrant half-line. The side of
the curve away from the origin is forward-invariant for the inclusion and its closure misses `0`,
separating every persistent trajectory from extinction.

Craciun's curve is **piecewise-linear**, so the boundary of its region is only Lipschitz, never
`C¹`. The connection to invariance is therefore the *distance-based* closed-set Nagumo rung
`CRNT.invariant_of_infDist_antitoneOn` (and the first-exit form
`invariant_of_no_infDist_increase_at_exit`) of `ClosedSetNagumo.lean`, which handles closed
regions without any `C¹` boundary — **not** the `C¹` sublevel form used by
`ZeroSeparatingSurface.lean`.

The ambient space here is a real inner-product space `E` (the worked example specializes to the
plane `EuclideanSpace ℝ (Fin 2)`); the half-plane normal is paired with velocities through the
real inner product `⟪·,·⟫_ℝ`, whose Cauchy–Schwarz inequality drives the separation lemma and
whose induced norm is the genuine Euclidean metric used by `infDist`/Nagumo.

## What this module formalizes (sorry-free)

* `dotHalfPlane` — the closed half-plane `{p | a ≤ ⟪n, p⟫_ℝ}` with inward normal `n`, the region
  side of an oriented edge; `isClosed_dotHalfPlane`, and `dotHalfPlane_subset_compl_ball`
  (a half-plane with unit normal and offset `a ≥ r > 0` excludes the open `r`-ball, by
  Cauchy–Schwarz).

* `polyRegion` — the closed "upper" region cut out by a finite list of oriented half-planes
  `faces : List (E × ℝ)` (normal/offset pairs), namely their intersection: `isClosed_polyRegion`,
  `polyRegion_subset_compl_ball` (it excludes `Metric.ball 0 r` once one face does, realizing the
  `ball_subset_compl` separation), and `mem_polyRegion` for membership of the start point.

* `IsSupportFace` / `IsSupportField` — the **subtangency interface**: a face `(n, a)` is a support
  face of a field `f` on the region when, at every region-boundary point `p` on that face's line
  (`⟪n, p⟫_ℝ = a`), the velocity points into the region side, `0 ≤ ⟪n, f p⟫_ℝ`.

* `attractingDirection_isSupport` — the clean **directional lemma**: when a constant field value
  `v` lies in the closed half-plane on the region side (`0 ≤ ⟪n, v⟫_ℝ`, the field along the
  attracting direction of the uncertainty region the edge crosses), `(n, a)` is a support face for
  the constant field `fun _ => v`. The fan-geometry hypothesis `0 ≤ ⟪n, v⟫_ℝ` is named, not
  derived.

* `stays_away_from_zero_of_support` — the **persistence wiring**: given the distance-nonincreasing
  fact for a genuine curve into `polyRegion` (the support ⇒ `infDist`-nonincreasing bridge,
  supplied as a hypothesis), the trajectory stays in the region for all forward time and hence a
  fixed distance `r` from `0`. A direct feed into `invariant_of_infDist_antitoneOn`.

## What is proved here, and what is taken as a hypothesis

Proved, sorry-free and axiom-clean:

* the half-plane / closed-region geometry and its closedness;
* the separation geometry — the region excludes a ball about `0`, the start lies in it;
* the subtangency *definitions* and the directional lemma `attractingDirection_isSupport`;
* the wiring from a supplied distance-nonincreasing hypothesis into the closed-set Nagumo rung.

Taken as hypotheses, not derived here:

* **Fan-geometry subtangency.** That for an *actual* toric inclusion's fan the support-face
  hypothesis `0 ≤ ⟪n, f p⟫_ℝ` holds at every boundary point with `n` the attracting direction
  orthogonal to the corresponding third-quadrant half-line — across both the constant exp-cone
  pieces and the half-plane uncertainty pieces. This is the per-fan-cell attracting-direction
  analysis; it needs the explicit polar-cone-of-each-exp-cone description of `toricField` and the
  uncertainty-region half-plane field.

* **Support ⇒ `infDist` nonincreasing.** The Lipschitz/Dini link from "the field lies in the
  region-side half-plane on each edge" to "`t ↦ Metric.infDist (γ t) polyRegion` is nonincreasing"
  along the genuine flow. For a polygonal (Lipschitz, non-`C¹`) boundary this is the
  proximal-normal / contingent-derivative-of-distance step recorded in `ClosedSetNagumo.lean`; it
  is supplied as a hypothesis to `stays_away_from_zero_of_support`, not discharged.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.ClosedSetNagumo`,
`CRNT.Geometry.ToricFan`, `Mathlib.Analysis.Convex.Segment`,
`Mathlib.Topology.MetricSpace.HausdorffDistance`.
-/

namespace CRNT

namespace ZeroSeparatingCurve2D

open Set Metric
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Closed half-planes -/

/-- The closed half-plane `{p | a ≤ ⟪n, p⟫_ℝ}` with inward normal `n` and offset `a`: the region
side of an oriented edge. -/
def dotHalfPlane (n : E) (a : ℝ) : Set E := {p | a ≤ ⟪n, p⟫_ℝ}

@[simp] theorem mem_dotHalfPlane {n : E} {a : ℝ} {p : E} :
    p ∈ dotHalfPlane n a ↔ a ≤ ⟪n, p⟫_ℝ := Iff.rfl

/-- A closed half-plane is closed: `p ↦ ⟪n, p⟫_ℝ` is continuous. -/
theorem isClosed_dotHalfPlane (n : E) (a : ℝ) : IsClosed (dotHalfPlane n a) :=
  isClosed_le continuous_const (continuous_const.inner continuous_id)

/-- **Separation of a half-plane from the origin.** A unit inward normal `n` (`‖n‖ = 1`) with
offset `a ≥ r > 0` gives a half-plane that misses the open `r`-ball: every `p` with
`a ≤ ⟪n, p⟫_ℝ` has `r ≤ ‖p‖`, by Cauchy–Schwarz `⟪n, p⟫_ℝ ≤ ‖n‖ * ‖p‖ = ‖p‖`. -/
theorem dotHalfPlane_subset_compl_ball {n : E} {a r : ℝ}
    (hn : ‖n‖ = 1) (har : r ≤ a) :
    dotHalfPlane n a ⊆ (Metric.ball (0 : E) r)ᶜ := by
  intro p hp
  rw [mem_dotHalfPlane] at hp
  rw [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt]
  have hcs : ⟪n, p⟫_ℝ ≤ ‖p‖ := by
    have := real_inner_le_norm n p
    rwa [hn, one_mul] at this
  calc r ≤ a := har
    _ ≤ ⟪n, p⟫_ℝ := hp
    _ ≤ ‖p‖ := hcs

/-! ## The closed polygonal region -/

/-- The closed "upper" region cut out by a finite list of oriented half-planes — each a
normal/offset pair `(n, a)` — namely the intersection of the closed half-planes `dotHalfPlane n a`
over the list. For Craciun's curve the half-planes are the region-side supporting half-planes of
the polygonal edges, so this is the side of the curve away from `0`. -/
def polyRegion (faces : List (E × ℝ)) : Set E :=
  {p | ∀ f ∈ faces, p ∈ dotHalfPlane f.1 f.2}

@[simp] theorem mem_polyRegion {faces : List (E × ℝ)} {p : E} :
    p ∈ polyRegion faces ↔ ∀ f ∈ faces, f.2 ≤ ⟪f.1, p⟫_ℝ := Iff.rfl

/-- The region of the empty face list is everything. -/
@[simp] theorem polyRegion_nil : polyRegion ([] : List (E × ℝ)) = Set.univ := by
  ext p; simp [polyRegion]

/-- **The polygonal region is closed**: it is a finite intersection of closed half-planes. -/
theorem isClosed_polyRegion (faces : List (E × ℝ)) : IsClosed (polyRegion faces) := by
  have : polyRegion faces = ⋂ f ∈ faces, dotHalfPlane f.1 f.2 := by
    ext p; simp [polyRegion, mem_dotHalfPlane]
  rw [this]
  exact isClosed_biInter (fun f _ => isClosed_dotHalfPlane f.1 f.2)

/-- **Separation of the polygonal region from the origin.** If some face `(n, a)` of the list has
a unit normal and offset `a ≥ r > 0`, the whole region — being contained in that face's
half-plane — excludes the open `r`-ball about `0`. This realizes the `ball_subset_compl`
separation: `Metric.ball 0 r ⊆ (polyRegion faces)ᶜ`. -/
theorem polyRegion_subset_compl_ball {faces : List (E × ℝ)} {n : E} {a r : ℝ}
    (hmem : (n, a) ∈ faces) (hn : ‖n‖ = 1) (har : r ≤ a) :
    polyRegion faces ⊆ (Metric.ball (0 : E) r)ᶜ := by
  intro p hp
  have hpf : p ∈ dotHalfPlane n a := by
    have := hp (n, a) hmem
    simpa [mem_dotHalfPlane] using this
  exact dotHalfPlane_subset_compl_ball hn har hpf

/-- The ball-exclusion stated in the `ball ⊆ compl` orientation, matching the separation
hypothesis shape consumed by the genuine-flow persistence layer. -/
theorem ball_subset_compl_polyRegion {faces : List (E × ℝ)} {n : E} {a r : ℝ}
    (hmem : (n, a) ∈ faces) (hn : ‖n‖ = 1) (har : r ≤ a) :
    Metric.ball (0 : E) r ⊆ (polyRegion faces)ᶜ :=
  subset_compl_comm.mp (polyRegion_subset_compl_ball hmem hn har)

/-! ## The polygonal curve from an ordered vertex list -/

/-- The edges of a polygonal curve through an ordered vertex list: the consecutive segments. The
curve runs from the first vertex (on the positive `x`-axis) to the last (on the positive
`y`-axis). -/
def polyEdges : List E → List (Set E)
  | [] => []
  | [_] => []
  | v :: w :: rest => segment ℝ v w :: polyEdges (w :: rest)

/-- The point set of the polygonal curve: the union of its edges. -/
def polyCurve (verts : List E) : Set E := ⋃ s ∈ polyEdges verts, s

/-- The curve stays a positive distance from `0`: every edge is contained in the complement of
the open `r`-ball. The vertices and segments of Craciun's curve are bounded away from the origin,
which is what keeps the region's closure off `0`. -/
def segmentBoundedAwayFromZero (verts : List E) (r : ℝ) : Prop :=
  ∀ s ∈ polyEdges verts, s ⊆ (Metric.ball (0 : E) r)ᶜ

/-- Under a positive bound, the whole curve avoids the open `r`-ball. -/
theorem polyCurve_subset_compl_ball {verts : List E} {r : ℝ}
    (h : segmentBoundedAwayFromZero verts r) :
    polyCurve verts ⊆ (Metric.ball (0 : E) r)ᶜ := by
  intro p hp
  rw [polyCurve, Set.mem_iUnion₂] at hp
  obtain ⟨s, hs, hps⟩ := hp
  exact h s hs hps

/-! ## The subtangency interface -/

/-- A point `p` is a **region-boundary point on the face `(n, a)`** when it lies in the region and
on that face's bounding line `⟪n, p⟫_ℝ = a`. -/
def OnFaceBoundary (faces : List (E × ℝ)) (n : E) (a : ℝ) (p : E) : Prop :=
  p ∈ polyRegion faces ∧ ⟪n, p⟫_ℝ = a

/-- **Support face.** A face `(n, a)` is a *support face* of the field `f` on the region cut out by
`faces` when, at every region-boundary point on that face's line, the velocity `f p` points into
the region side: `0 ≤ ⟪n, f p⟫_ℝ`. This is the per-edge subtangency condition — the field at each
region-boundary point lies in the closed half-plane on the region side. -/
def IsSupportFace (f : E → E) (faces : List (E × ℝ)) (n : E) (a : ℝ) : Prop :=
  ∀ p, OnFaceBoundary faces n a p → 0 ≤ ⟪n, f p⟫_ℝ

/-- **Support field.** The field `f` is *subtangent* to the region cut out by `faces` when every
face of the list is a support face. This is the planar support condition: along every edge of
the polygonal curve the field points into the region. -/
def IsSupportField (f : E → E) (faces : List (E × ℝ)) : Prop :=
  ∀ nf ∈ faces, IsSupportFace f faces nf.1 nf.2

/-- **The directional lemma (per-edge support segment).** When the locally-constant field value
`v` across an uncertainty region lies in the closed half-plane on the region side — `0 ≤ ⟪n, v⟫_ℝ`,
with `n` the edge's inward normal, the *attracting direction* orthogonal to the corresponding
third-quadrant half-line — the face `(n, a)` is a support face for the constant field `fun _ => v`.
This is the clean direction-level statement: a segment whose normal is the attracting direction of
the uncertainty region it crosses is a support segment. The fan-geometry fact that `0 ≤ ⟪n, v⟫_ℝ`
holds for an actual toric inclusion is taken as a hypothesis. -/
theorem attractingDirection_isSupport {v n : E} {a : ℝ} {faces : List (E × ℝ)}
    (hv : 0 ≤ ⟪n, v⟫_ℝ) :
    IsSupportFace (fun _ => v) faces n a :=
  fun _ _ => hv

/-- A constant field is a support field for `faces` as soon as its value lies in every face's
region-side half-plane. -/
theorem constField_isSupport {v : E} {faces : List (E × ℝ)}
    (hv : ∀ nf ∈ faces, 0 ≤ ⟪nf.1, v⟫_ℝ) :
    IsSupportField (fun _ => v) faces :=
  fun nf hnf => attractingDirection_isSupport (hv nf hnf)

/-! ## Persistence wiring into the closed-set Nagumo rung -/

/-- **Persistence of the polygonal region (away from `0`).** Let `γ` be a genuine curve with
`γ 0 ∈ polyRegion faces`, and suppose the support ⇒ distance-nonincreasing bridge has been
supplied: `t ↦ Metric.infDist (γ t) (polyRegion faces)` is antitone on `[0, ∞)`. Then `γ` stays in
the region for all forward time. If moreover some face `(n, a)` of the list has a unit normal and
offset `a ≥ r > 0`, the trajectory keeps a hard distance `r` from the origin.

The distance-nonincreasing hypothesis is exactly the support ⇒ `infDist`-nonincreasing
content (taken as a hypothesis, as in the module header and in `ClosedSetNagumo.lean`); given it,
this is a direct application of `invariant_of_infDist_antitoneOn` plus the half-plane separation. -/
theorem stays_away_from_zero_of_support {faces : List (E × ℝ)} {γ : ℝ → E}
    {n : E} {a r : ℝ}
    (hmem : (n, a) ∈ faces) (hn : ‖n‖ = 1) (har : r ≤ a) (_hr : 0 < r)
    (h0 : γ 0 ∈ polyRegion faces)
    (hanti : AntitoneOn (fun t => Metric.infDist (γ t) (polyRegion faces)) (Set.Ici 0))
    {t : ℝ} (ht : 0 ≤ t) :
    r ≤ dist (γ t) 0 := by
  have hne : (polyRegion faces).Nonempty := ⟨γ 0, h0⟩
  have hmemR : γ t ∈ polyRegion faces :=
    invariant_of_infDist_antitoneOn (isClosed_polyRegion faces) hne h0 hanti ht
  have hcompl : γ t ∈ (Metric.ball (0 : E) r)ᶜ :=
    polyRegion_subset_compl_ball hmem hn har hmemR
  rw [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] at hcompl
  rwa [dist_zero_right]

/-! ## A concrete worked two-segment example in the plane

A two-edge curve in `EuclideanSpace ℝ (Fin 2)` realizing the framework: two faces with the same
unit normal `(√2/2, √2/2)` (the symmetric attracting direction) and offset `1`, cutting out the
half-plane `x + y ≥ √2`. A constant field along the attracting direction is a support field, and
the region excludes the open ball of radius `1` about the origin. -/

section Worked

/-- The symmetric unit normal `(√2/2, √2/2)` in the plane: the attracting direction of the
diagonal third-quadrant half-line. -/
noncomputable def diagNormal : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![Real.sqrt 2 / 2, Real.sqrt 2 / 2]

@[simp] theorem diagNormal_apply (i : Fin 2) :
    diagNormal i = ![Real.sqrt 2 / 2, Real.sqrt 2 / 2] i := rfl

/-- The diagonal normal is a unit vector. -/
theorem norm_diagNormal : ‖diagNormal‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hs : Real.sqrt 2 / 2 * (Real.sqrt 2 / 2) = 1 / 2 := by
    rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]; norm_num
  simp only [Fin.sum_univ_two, diagNormal_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.norm_eq_abs, sq_abs]
  have hsum : (Real.sqrt 2 / 2) ^ 2 + (Real.sqrt 2 / 2) ^ 2 = 1 := by
    rw [pow_two, hs]; norm_num
  rw [hsum, Real.sqrt_one]

/-- The two-face list for the worked diagonal example: two copies of the same supporting
half-plane `x + y ≥ 1`. -/
noncomputable def diagFaces : List (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  [(diagNormal, 1), (diagNormal, 1)]

/-- The diagonal region excludes the open unit ball about the origin: the worked separation. -/
theorem diagRegion_subset_compl_ball :
    polyRegion diagFaces ⊆ (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ :=
  polyRegion_subset_compl_ball (n := diagNormal) (a := 1) (r := 1)
    (by simp [diagFaces]) norm_diagNormal le_rfl

/-- A constant field whose value points into the diagonal half-plane (`0 ≤ ⟪diagNormal, v⟫_ℝ`) is a
support field for the diagonal region: the worked directional realization. -/
theorem diagField_isSupport {v : EuclideanSpace ℝ (Fin 2)}
    (hv : 0 ≤ ⟪diagNormal, v⟫_ℝ) :
    IsSupportField (fun _ => v) diagFaces := by
  apply constField_isSupport
  intro nf hnf
  simp only [diagFaces, List.mem_cons, List.not_mem_nil, or_false] at hnf
  rcases hnf with h | h <;> (rw [h]; exact hv)

end Worked

end ZeroSeparatingCurve2D

end CRNT

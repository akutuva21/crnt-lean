import CRNT.Geometry.FaithfulCurve
import CRNT.Dynamics.PolyRegionInvariant

/-!
# Faithful-curve existence: the end-to-end §4.2 composition (Craciun §4.2)

The §4.2 zero-separating construction runs in three layers — *support* (the fan's attracting
direction points the toric field into a half-plane region), *invariance* (a genuine curve solving
the field cannot leave that region), and *separation* (the region misses a ball about `0`) —
which together deliver *persistence*: a genuine mass-action curve started in the region stays a
fixed distance from extinction for all forward time.

Each layer is proved in isolation upstream:

* support — `FaithfulCurveExample.crossField_subset_dualHalfPlane` /
  `crossField_isSupportFace`, driven by `Faithful.diagNormal_attractsTowardAll`;
* invariance — `ZeroSeparatingCurve2D.polyRegion_invariant_of_support`;
* separation — `ZeroSeparatingCurve2D.polyRegion_subset_compl_ball` /
  `ball_subset_compl_polyRegion`;
* the persistence wiring — `ZeroSeparatingCurve2D.stays_away_from_zero_of_support_invariant`.

This module **composes them in a single concrete case**: the worked two-cell fan
`FaithfulCurveExample.crossFan` (cells `coneDual {e₀}`, `coneDual {e₁}`, both containing the
diagonal attracting direction `diagNormal`), the single-face region
`polyRegion [(diagNormal, 1)]` = `{x | 1 ≤ ⟪diagNormal, x⟫_ℝ}`, and the toric field
`toricField crossFan δ`. The result `crossFan_genuine_persistent` shows the whole §4.2 chain
links from fan to persistence in a genuine instance.

## What this module formalizes (sorry-free)

* `crossFaces` / `crossField_support` — the single-face region for the worked fan and the support
  certificate that every value of `toricField crossFan δ` at every log-state points into the
  region side of its only face. Pure consequences of `crossField_subset_dualHalfPlane`.

* `crossFaces_separates` — the worked region excludes the open unit ball about `0`: a
  fully-evaluated `polyRegion_subset_compl_ball` with the unit normal `diagNormal` and offset `1`.

* `crossFan_genuine_persistent` — **the end-to-end concrete persistence theorem.** A genuine curve
  `γ` solving `ẋ = f(γ)` whose velocity field `f` is a selection of `toricField crossFan δ` at the
  log-state (`∀ x, f x ∈ toricField crossFan δ (logCoords x)`), continuous, started in the region
  `polyRegion crossFaces`, keeps a hard distance `1` from the origin for all `t ≥ 0`. The full
  §4.2 support → invariance → separation → persistence chain, composed on the worked fan via
  `stays_away_from_zero_of_support_invariant`.

* `supportFieldOfNormals` / `isSupportField_of_attractsAll_normals` — **the construction
  framework.** From an ordered list of attracting normals, each of which attracts toward all δ-near
  cells of a fan at a point `X`, the constant field of any value of `toricField F δ X` is a support
  field for the region those normals cut out. The clean generalization of the single-direction
  `crossField_support` to a list of per-segment attracting directions.

## Proven vs. residue — what composes end-to-end and what remains open

PROVEN here, sorry-free and axiom-clean:

* the **complete §4.2 composition on the worked `crossFan`**: support
  (`crossField_subset_dualHalfPlane`) → invariance (`polyRegion_invariant_of_support`) →
  separation (`polyRegion_subset_compl_ball`) → persistence
  (`stays_away_from_zero_of_support_invariant`), linked in `crossFan_genuine_persistent` for a
  genuine curve solving a selection of the toric field;
* the **list-of-normals construction framework**: `isSupportField_of_attractsAll_normals` turns a
  list of attracting directions, each in `⋂ᵢ Cᵢ`, into a support field for their cut-out region.

RESIDUE — the genuine §4.2 heart, named in prose, **not** stated as `theorem … : True` and
**never** `sorry`:

* **General arbitrary-fan faithful-curve existence.** That for an *arbitrary* 2-D toric fan there
  *exists* a faithful polygonal curve traversing every exponential cone — one vertex per bounded
  exp-cone, every segment's interior slope landing in the interior of the interval bounded by its
  adjacent attracting directions, simultaneously satisfying every cell's membership constraint,
  running from the positive `x`-axis to the positive `y`-axis and separating `0` from an arbitrary
  `x₀`. The simultaneous solvability of all the slope constraints — that the attracting-direction
  intervals chain together so a single monotone polygonal curve realizes them all — rests on the
  explicit fan-line/exp-cone slope ordering of the plane and is the genuine figure-driven §4.2
  content. The worked `crossFan` is the single-region degenerate instance where one attracting
  direction (`diagNormal`) serves every cell, so no chaining is needed; the general chaining is the
  open research crux.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Geometry.FaithfulCurve`,
`CRNT.Dynamics.PolyRegionInvariant`.
-/

namespace CRNT

namespace FaithfulCurveExistence

open scoped InnerProductSpace
open ZeroSeparatingCurve2D CRNT.Faithful FaithfulCurveExample

/-! ## The construction framework: a list of attracting normals yields a support field -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **The region cut out by a list of attracting normals**, each at offset `a`: the polygonal
region whose faces are the segments' inward normals. The construction framework turns the
per-segment attracting directions of a faithful curve into this region. -/
def supportFieldOfNormals (normals : List E) (a : ℝ) : List (E × ℝ) :=
  normals.map (fun n => (n, a))

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
@[simp] theorem mem_supportFieldOfNormals {normals : List E} {a : ℝ} {nf : E × ℝ} :
    nf ∈ supportFieldOfNormals normals a ↔ ∃ n ∈ normals, (n, a) = nf := by
  simp [supportFieldOfNormals]

/-- **Construction framework: a list of attracting directions yields a support field.** If every
normal in `normals` attracts toward all δ-near cells of `F` at `X` (`AttractsTowardAll`), then for
any value `v` of the toric field at `X`, the constant field `fun _ => v` is a support field for the
region `supportFieldOfNormals normals a` those normals cut out. Each face normal lies in `⋂ᵢ Cᵢ`,
so `crossField`-style subtangency (`isSupportFace_of_attractsAll`) fires on every segment. This is
the clean generalization of the single-direction worked support to an ordered list of per-segment
attracting directions. -/
theorem isSupportField_of_attractsAll_normals {F : Fan E} {δ : ℝ} {X v : E}
    (hv : v ∈ toricField F δ X) {normals : List E} {a : ℝ}
    (hatt : ∀ n ∈ normals, AttractsTowardAll F δ X n) :
    IsSupportField (fun _ => v) (supportFieldOfNormals normals a) := by
  intro nf hnf
  rw [mem_supportFieldOfNormals] at hnf
  obtain ⟨n, hn, hnf⟩ := hnf
  subst hnf
  exact isSupportFace_of_attractsAll (hatt n hn) hv

end FaithfulCurveExistence

/-! ## The end-to-end concrete §4.2 instance on the worked `crossFan` -/

namespace FaithfulCurveExistence

open scoped InnerProductSpace
open ZeroSeparatingCurve2D CRNT.Faithful FaithfulCurveExample

/-- The single-face region of the worked instance: the half-plane `{x | 1 ≤ ⟪diagNormal, x⟫_ℝ}`,
cut out by the lone face `(diagNormal, 1)`. Its only normal is the diagonal attracting direction
that both cells of `crossFan` contain. -/
noncomputable def crossFaces : List (Plane × ℝ) := [(diagNormal, 1)]

/-- The lone face `(diagNormal, 1)` belongs to `crossFaces`. -/
theorem diagNormal_one_mem_crossFaces : (diagNormal, (1 : ℝ)) ∈ crossFaces := by
  simp [crossFaces]

/-- **Support for the worked instance.** Every value `v` of `toricField crossFan δ X` (at any
log-state `X`) pairs nonnegatively with the only face normal of `crossFaces`, `diagNormal`: the
diagonal direction attracts toward both cells, so the field lands in the region-side half-plane.
A fully-evaluated `crossField_subset_dualHalfPlane`. -/
theorem crossField_support (δ : ℝ) (X : Plane) {v : Plane} (hv : v ∈ toricField crossFan δ X) :
    ∀ nf ∈ crossFaces, 0 ≤ ⟪nf.1, v⟫_ℝ := by
  intro nf hnf
  simp only [crossFaces, List.mem_singleton] at hnf
  subst hnf
  exact crossField_subset_dualHalfPlane δ X hv

/-- **Separation for the worked instance.** The region `polyRegion crossFaces` excludes the open
unit ball about `0`: the lone face has unit normal `diagNormal` and offset `1 ≥ 1 > 0`. A
fully-evaluated `polyRegion_subset_compl_ball`. -/
theorem crossFaces_separates :
    polyRegion crossFaces ⊆ (Metric.ball (0 : Plane) 1)ᶜ :=
  polyRegion_subset_compl_ball (n := diagNormal) (a := 1) (r := 1)
    diagNormal_one_mem_crossFaces norm_diagNormal le_rfl

/-- **The end-to-end concrete §4.2 persistence theorem.** Let `γ` be a *genuine* curve solving the
ODE `ẋ = f(γ)` whose velocity field `f` is a **selection** of the worked toric field at the
log-state — `f x ∈ toricField crossFan δ (logCoords x)` for every state `x` — continuous, and
started in the region `polyRegion crossFaces`. Then `γ` keeps a hard distance `1` from the origin
for all forward time `t ≥ 0`: it is persistent.

This composes the full §4.2 chain on the worked `crossFan`:

* **support** — `crossField_support` (from `crossField_subset_dualHalfPlane` /
  `diagNormal_attractsTowardAll`): the velocity `f (γ t) ∈ toricField crossFan δ (logCoords (γ t))`
  pairs nonnegatively with the face normal `diagNormal`;
* **invariance + separation + persistence** — `stays_away_from_zero_of_support_invariant`: that
  support, with the unit-normal/offset-`1` separating face, forces `γ` to stay in the region and so
  a distance `1` from `0`.

This is the proof-of-concept that the §4.2 machinery links from fan to persistence in a real
case. -/
theorem crossFan_genuine_persistent {δ : ℝ} {f : Plane → Plane} {γ : ℝ → Plane}
    (hsel : ∀ x : Plane, f x ∈ toricField crossFan δ (logCoords x))
    (hγcont : Continuous γ) (hγ : ∀ t > 0, HasDerivAt γ (f (γ t)) t)
    (h0 : γ 0 ∈ polyRegion crossFaces) {t : ℝ} (ht : 0 ≤ t) :
    (1 : ℝ) ≤ dist (γ t) 0 := by
  refine stays_away_from_zero_of_support_invariant (n := diagNormal) (a := 1) (r := 1)
    diagNormal_one_mem_crossFaces norm_diagNormal le_rfl hγcont hγ ?_ h0 ht
  intro na hna s hs
  exact crossField_support δ (logCoords (γ s)) (hsel (γ s)) na hna

end FaithfulCurveExistence

end CRNT

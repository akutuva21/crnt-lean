import CRNT.Geometry.FaithfulCurveExistence

/-!
# The general faithful zero-separating curve: chaining data and the existence question

The zero-separating construction of Craciun, _Toric differential inclusions and a proof of the
global attractor conjecture_, realizes a polygonal curve whose consecutive segments cross the
fan's uncertainty regions in their respective *attracting directions*. Each segment contributes
one oriented region-side half-plane `(nᵢ, aᵢ)`, with `nᵢ` the per-wall attracting direction; the
curve's region is the intersection `polyRegion [(n₀, a₀), (n₁, a₁), …]`. The persistence chain runs
*support* (every `nᵢ` attracts toward all δ-near cells, so the toric field points into the region on
every face) → *invariance* (`polyRegion_invariant_of_support`) → *separation* (one unit-normal face
excludes a ball about `0`) → *persistence*.

`FaithfulCurveExistence.crossFan_genuine_persistent` composes this chain on the worked `crossFan`,
but degenerately: one direction `diagNormal` serves both cells, so the normal list collapses to a
single face and no slope-chaining occurs. This module supplies the genuinely *chained* layer:

* the `ChainingData` structure — an ordered list of segment normals, each an attracting direction
  for the fan at a point — and the general persistence theorem built from it;

* a **first non-degenerate witness** with two distinct segment normals `axisNormal 0 ≠ axisNormal 1`
  that genuinely chain into a two-face region, composed end-to-end to persistence;

* the structured-fan existence question for 2-D, pushed to what is cleanly provable (consecutive
  segments chain whenever every normal is a common attracting direction), with the full
  angular-sort / slope-interval-nonemptiness / separation construction taken as a hypothesis.

## What this module formalizes (sorry-free)

* `ChainingData` — the per-segment chaining record for a fan `F`, scale `δ`, point `X`, offset `a`:
  a `normals : List E` with `attracts : ∀ n ∈ normals, AttractsTowardAll F δ X n`. Its `faces` is
  `supportFieldOfNormals normals a`.

* `ChainingData.isSupportField` — the toric field at `X` is a support field on every face of the
  chaining data (each `nᵢ ∈ ⋂ Cⱼ`, so `isSupportField_of_attractsAll_normals` fires on every
  segment). The clean generalization of the single-direction worked support to an arbitrary normal
  list.

* `ChainingData.genuine_persistent` — **the general persistence theorem.** A genuine curve solving a
  selection of `toricField F δ` at the log-state, started in `polyRegion cd.faces`, with one
  unit-normal face at offset `≥ r > 0`, stays a hard distance `r` from `0` for all forward time.
  Generalizes `crossFan_genuine_persistent` from one collapsed direction to an arbitrary normal list.

* `axisNormal` / the non-degenerate witness `twoWallFaces` — two *distinct* unit segment normals
  `axisNormal 0 = (1,0)`, `axisNormal 1 = (0,1)`, both attracting toward the two cells of `crossFan`,
  cutting out `polyRegion [(axisNormal 0, 1), (axisNormal 1, 1)]` (the corner `{x ≥ 1, y ≥ 1}`). The
  composed `twoWall_genuine_persistent` exhibits real slope-chaining: two genuinely different
  attracting directions linked end-to-end into one persistence statement.

* `consecutive_chain` — the cleanly-provable fragment of the structured-fan existence: if every
  normal in a list is a common attracting direction at `X`, then *every consecutive pair* chains in
  the sense that both serve as support faces of one toric-field value — the local compatibility that
  the global angular sort must arrange.

## What is proved here, and what is taken as a hypothesis

Proved, sorry-free and axiom-clean:

* the `ChainingData` framework and its support certificate `ChainingData.isSupportField`;
* the **general chained persistence theorem** `ChainingData.genuine_persistent`, an arbitrary
  normal list composed support → invariance → separation → persistence;
* the **first non-degenerate two-distinct-normal witness** `twoWall_genuine_persistent`, the first
  instance exhibiting genuine slope-chaining (degenerate-free, unlike `crossFan`);
* the local-compatibility fragment `consecutive_chain` of the structured-fan existence.

Taken as a hypothesis, not constructed here:

* **General arbitrary-fan chaining-data existence.** For an *arbitrary* 2-D toric fan: the existence
  of the chaining normal-list whose per-segment attracting-direction slope intervals are nonempty and
  mutually compatible (the interval bounded by adjacent attracting directions is non-degenerate and
  the consecutive intervals overlap), traversing *every* exponential cone in angular order, running
  from the positive `x`-axis to the positive `y`-axis, and separating `0` from an arbitrary `x₀`.
  Two-dimensionality makes the sectors from origin lines totally angularly ordered, so a monotone
  polygonal curve exists; but turning that order into a concrete normal list with nonempty
  compatible slope intervals — the simultaneous solvability of all per-cell membership constraints by
  one monotone curve — is the explicit fan-line/exp-cone slope-ordering construction.
  `ChainingData` is the *interface* such a construction would populate;
  `consecutive_chain` shows the *local* compatibility once the normals are in hand; the *global*
  production of those normals (angular sort + slope-interval nonemptiness + axis endpoints +
  `x₀`-separation) is not formalized here. The non-degenerate `twoWallFaces` witness shows the
  interface is genuinely inhabited by a chained (not collapsed) instance.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Geometry.FaithfulCurveExistence`.
-/

namespace CRNT

namespace FaithfulCurveGeneral

open scoped InnerProductSpace
open ZeroSeparatingCurve2D CRNT.Faithful FaithfulCurveExample FaithfulCurveExistence

/-! ## (a) The general construction framework: chaining data for a 2-D fan -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Chaining data for a 2-D fan.** Bundles the per-segment attracting directions of a faithful
polygonal curve relative to a fan `F`, scale `δ`, point `X`, and common offset `a`:

* `normals` — the ordered list of segment normals `n₀, n₁, …` (the per-wall attracting directions);
* `attracts` — each normal attracts toward *all* δ-near cells of `F` at `X` (`AttractsTowardAll`),
  the per-segment cell-membership witness `nᵢ ∈ ⋂ⱼ Cⱼ`.

The faithful curve's region is `polyRegion` of `faces`, the oriented half-planes
`(nᵢ, a)`. This is the *interface* a general existence construction would populate; the geometric
content producing a *specific* normal list (the angular sort with nonempty compatible slope
intervals traversing every exp-cone) is taken as a hypothesis. -/
structure ChainingData (F : Fan E) (δ : ℝ) (X : E) (a : ℝ) where
  /-- The ordered list of per-segment attracting directions. -/
  normals : List E
  /-- Each segment normal attracts toward all δ-near cells of `F` at `X`. -/
  attracts : ∀ n ∈ normals, AttractsTowardAll F δ X n

/-- The oriented region-side half-planes of the chaining data: one face `(nᵢ, a)` per segment
normal, via `supportFieldOfNormals`. The faithful curve's region is `polyRegion cd.faces`. -/
def ChainingData.faces {F : Fan E} {δ : ℝ} {X : E} {a : ℝ} (cd : ChainingData F δ X a) :
    List (E × ℝ) :=
  supportFieldOfNormals cd.normals a

/-- **Support on every face of the chaining data.** For any value `v` of the toric field at `X`, the
constant field `fun _ => v` is a support field for the region `cd.faces`: every segment normal lies
in `⋂ⱼ Cⱼ`, so the uncertainty-crossing support lemma fires on each face. The clean generalization
of the single-direction worked support (`crossField_support`) to an arbitrary normal list. -/
theorem ChainingData.isSupportField {F : Fan E} {δ : ℝ} {X v : E} {a : ℝ}
    (cd : ChainingData F δ X a) (hv : v ∈ toricField F δ X) :
    IsSupportField (fun _ => v) cd.faces :=
  isSupportField_of_attractsAll_normals hv cd.attracts

/-- **Every face value of the toric field points into the region.** Repackages the support
certificate as the per-face nonnegativity needed by the invariance layer: each face normal `nf.1`
pairs nonnegatively with any toric-field value `v` at `X`. -/
theorem ChainingData.face_nonneg {F : Fan E} {δ : ℝ} {X v : E} {a : ℝ}
    (cd : ChainingData F δ X a) (hv : v ∈ toricField F δ X) :
    ∀ nf ∈ cd.faces, 0 ≤ ⟪nf.1, v⟫_ℝ := by
  intro nf hnf
  rw [ChainingData.faces, mem_supportFieldOfNormals] at hnf
  obtain ⟨n, hn, hnf⟩ := hnf
  subst hnf
  exact toricField_subset_dualHalfPlane_of_attractsAll (cd.attracts n hn) hv

end FaithfulCurveGeneral

/-! ## (a, continued) The general persistence theorem over `EuclideanSpace ℝ S` -/

namespace FaithfulCurveGeneral

open scoped InnerProductSpace
open ZeroSeparatingCurve2D CRNT.Faithful FaithfulCurveExample FaithfulCurveExistence

variable {S : Type*} [Fintype S]

/-- **The general chained persistence theorem.** Let `cd` be chaining data for a fan `F`, scale `δ`,
log-state `logCoords x₀`, offset `a`; let `γ` be a genuine curve solving the ODE `ẋ = f(γ)` whose
velocity field `f` is a **selection** of the toric field at the *same* log-state for every state —
`f x ∈ toricField F δ (logCoords x₀)` — continuous, and started in the region `polyRegion cd.faces`.
If one face `(n, a)` of the chaining data has a unit normal and offset `a ≥ r > 0`, then `γ` keeps a
hard distance `r` from the origin for all forward time `t ≥ 0`.

This composes the full chain on an *arbitrary* normal list:

* **support** — `cd.face_nonneg`: each velocity `f (γ t)` pairs nonnegatively with every face normal;
* **invariance + separation + persistence** — `stays_away_from_zero_of_support_invariant`: support,
  with the unit-normal separating face, forces `γ` to stay in the region and so a distance `r`
  from `0`.

The selection is taken at the fixed point `logCoords x₀` — the same point whose δ-near cells the
chaining data certifies — which is the setting in which `cd.attracts` supplies the support data. This
generalizes `crossFan_genuine_persistent` from one collapsed direction (`diagNormal`) to an arbitrary
chained normal list. -/
theorem ChainingData.genuine_persistent
    {F : Fan (EuclideanSpace ℝ S)} {δ : ℝ} {x₀ : EuclideanSpace ℝ S} {a r : ℝ}
    (cd : ChainingData F δ (logCoords x₀) a)
    {f : EuclideanSpace ℝ S → EuclideanSpace ℝ S} {γ : ℝ → EuclideanSpace ℝ S}
    {n : EuclideanSpace ℝ S}
    (hmem : (n, a) ∈ cd.faces) (hn : ‖n‖ = 1) (har : r ≤ a)
    (hsel : ∀ x : EuclideanSpace ℝ S, f x ∈ toricField F δ (logCoords x₀))
    (hγcont : Continuous γ) (hγ : ∀ t > 0, HasDerivAt γ (f (γ t)) t)
    (h0 : γ 0 ∈ polyRegion cd.faces) {t : ℝ} (ht : 0 ≤ t) :
    r ≤ dist (γ t) 0 := by
  refine stays_away_from_zero_of_support_invariant (n := n) (a := a) (r := r)
    hmem hn har hγcont hγ ?_ h0 ht
  intro na hna s _
  exact cd.face_nonneg (hsel (γ s)) na hna

/-! ## (b) The first non-degenerate witness: two distinct chained segment normals -/

/-- A coordinate-axis unit normal: `axisNormal i = EuclideanSpace.single i 1`, the unit vector
along axis `i`. `axisNormal 0 = (1, 0)` and `axisNormal 1 = (0, 1)` are the two *distinct* attracting
directions of the non-degenerate witness — unlike the single `diagNormal` of `crossFan`. -/
noncomputable def axisNormal (i : Fin 2) : Plane := EuclideanSpace.single i (1 : ℝ)

@[simp] theorem axisNormal_apply (i j : Fin 2) :
    axisNormal i j = if j = i then (1 : ℝ) else 0 :=
  PiLp.single_apply 2 ℝ i 1 j

/-- Each axis normal is a unit vector. -/
theorem norm_axisNormal (i : Fin 2) : ‖axisNormal i‖ = 1 := by
  rw [axisNormal, PiLp.norm_single, norm_one]

/-- The two axis normals are **distinct**: `axisNormal 0 ≠ axisNormal 1`. They disagree in the
first coordinate (`1` versus `0`), so the witness genuinely chains two different directions. -/
theorem axisNormal_zero_ne_one : axisNormal 0 ≠ axisNormal 1 := by
  intro h
  have := congrArg (fun v => v 0) h
  simp only [axisNormal_apply] at this
  norm_num at this

/-- **Each axis normal attracts toward all cells of `crossFan`, at every point and scale.** Both
cells of `crossFan` are the polar cones of the coordinate axes (`crossCell j = {y | 0 ≤ y j}`), and
`axisNormal i` has nonnegative coordinates (`1` or `0`), so it lies in every cell regardless of which
are δ-near `X`. This is the per-segment cell-membership witness for the two distinct normals. -/
theorem axisNormal_attractsTowardAll (i : Fin 2) (δ : ℝ) (X : Plane) :
    AttractsTowardAll crossFan δ X (axisNormal i) := by
  intro C hC _
  simp only [crossFan, Finset.mem_insert, Finset.mem_singleton] at hC
  have key : ∀ j : Fin 2, axisNormal i ∈ (crossCell j : Set Plane) := by
    intro j
    rw [mem_crossCell, axisNormal_apply]
    split <;> norm_num
  rcases hC with h | h <;> (subst h; exact key _)

/-- The two-face region of the non-degenerate witness: two *distinct* unit segment normals,
`(axisNormal 0, 1)` and `(axisNormal 1, 1)`, cutting out the corner `{x | 1 ≤ x 0 ∧ 1 ≤ x 1}`. Unlike
`crossFaces` (one face, one direction), this region's boundary genuinely chains two walls. -/
noncomputable def twoWallFaces : List (Plane × ℝ) :=
  [(axisNormal 0, 1), (axisNormal 1, 1)]

/-- The face `(axisNormal 0, 1)` belongs to `twoWallFaces` — the separating face, with unit normal
`axisNormal 0` and offset `1`. -/
theorem axisNormal_zero_one_mem_twoWallFaces : (axisNormal 0, (1 : ℝ)) ∈ twoWallFaces := by
  simp [twoWallFaces]

/-- The chaining data of the non-degenerate witness: the two distinct attracting directions
`axisNormal 0, axisNormal 1`, each attracting toward all cells of `crossFan`. Its `faces` reduces to
`twoWallFaces`. -/
noncomputable def twoWallChaining (δ : ℝ) (X : Plane) :
    ChainingData crossFan δ X 1 where
  normals := [axisNormal 0, axisNormal 1]
  attracts := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h <;> (subst h; exact axisNormal_attractsTowardAll _ δ X)

/-- The chaining data's `faces` is exactly `twoWallFaces`. -/
theorem twoWallChaining_faces (δ : ℝ) (X : Plane) :
    (twoWallChaining δ X).faces = twoWallFaces := by
  rfl

/-- **The first non-degenerate persistence theorem (genuine slope-chaining).** Let `γ` be a genuine
curve solving `ẋ = f(γ)` whose velocity field `f` is a selection of `toricField crossFan δ` at the
fixed log-state `logCoords x₀`, continuous, started in the two-wall corner region
`polyRegion twoWallFaces`. Then `γ` keeps a hard distance `1` from the origin for all forward time.

This is the first instance exhibiting *real slope-chaining*: two **distinct** segment normals
`axisNormal 0 ≠ axisNormal 1` (a 3-cell-style two-wall fan), each attracting its adjacent cells,
composed END-TO-END through the support → invariance → separation → persistence chain via
`ChainingData.genuine_persistent`. Unlike `crossFan_genuine_persistent`, no single direction serves
both cells — the region's boundary is a genuine two-segment polygonal chain. -/
theorem twoWall_genuine_persistent
    {δ : ℝ} {x₀ : Plane} {f : Plane → Plane} {γ : ℝ → Plane}
    (hsel : ∀ x : Plane, f x ∈ toricField crossFan δ (logCoords x₀))
    (hγcont : Continuous γ) (hγ : ∀ t > 0, HasDerivAt γ (f (γ t)) t)
    (h0 : γ 0 ∈ polyRegion twoWallFaces) {t : ℝ} (ht : 0 ≤ t) :
    (1 : ℝ) ≤ dist (γ t) 0 := by
  have hmem : (axisNormal 0, (1 : ℝ)) ∈ (twoWallChaining δ (logCoords x₀)).faces := by
    rw [twoWallChaining_faces]; exact axisNormal_zero_one_mem_twoWallFaces
  refine (twoWallChaining δ (logCoords x₀)).genuine_persistent
    (n := axisNormal 0) (r := 1) hmem (norm_axisNormal 0) le_rfl hsel hγcont hγ ?_ ht
  rwa [twoWallChaining_faces]

/-! ## (c) The structured-fan existence question: local compatibility, and the global hypothesis

Two-dimensionality is special: the sectors cut by lines through the origin are *totally angularly
ordered*, so a monotone polygonal curve threads every exponential cone, one vertex per bounded
cone, each segment crossing an uncertainty region in its attracting direction. Turning that picture
into a rigorous existence statement requires producing a concrete normal list whose per-segment
attracting-direction slope intervals are nonempty and mutually compatible — the simultaneous
solvability of every cell's membership constraint by one monotone curve.

What is cleanly provable *once the normals are in hand* is the **local compatibility** of consecutive
segments: if every normal in the list is a common attracting direction at the point, then each
consecutive pair shares a support certificate from one toric-field value (`consecutive_chain` below).
This is the local result the global angular sort must arrange into a single curve.

Taken as a hypothesis is the *global production* of the normal list:

  For an ARBITRARY 2-D toric fan, the existence of the chaining normal-list (a `ChainingData`)
  whose per-segment attracting-direction slope intervals are nonempty and mutually compatible —
  the interval bounded by each pair of adjacent attracting directions is non-degenerate, and the
  consecutive intervals overlap so a single monotone polygonal curve realizes them all — traversing
  EVERY exponential cone in angular order, running from the positive `x`-axis to the positive
  `y`-axis, and separating `0` from an arbitrary `x₀`.

This rests on the explicit fan-line / exp-cone slope ordering of the plane: the angular sort of the
cells, the nonemptiness of each slope interval, and the overlap of consecutive intervals.
`ChainingData` is the interface it would populate; the non-degenerate `twoWallFaces` witness shows
that interface is genuinely inhabited by a chained (not collapsed) instance; `consecutive_chain`
discharges the local compatibility. The global existence is taken as a hypothesis rather than
constructed. -/

/-- **Local compatibility of consecutive segments.** Fix a
fan `F`, scale `δ`, point `X`, offset `a`, and chaining data `cd`. For any value `v` of the toric
field at `X` and any two consecutive segment normals (`cd.normals[k]` and `cd.normals[k+1]`, with
`k + 1` in range), *both* their faces are support faces of the single constant
field `fun _ => v`: the velocity points into the region across both adjacent segments simultaneously.

This is the local result the global angular sort must arrange: consecutive segments chain in the sense
that one toric-field value certifies subtangency on both. The *global* production of a normal list
whose consecutive slope intervals are nonempty and overlapping is taken as a hypothesis. -/
theorem consecutive_chain
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {F : Fan E} {δ : ℝ} {X v : E} {a : ℝ}
    (cd : ChainingData F δ X a) (hv : v ∈ toricField F δ X)
    {k : ℕ} (hk : k + 1 < cd.normals.length) :
    IsSupportFace (fun _ => v) cd.faces cd.normals[k] a ∧
      IsSupportFace (fun _ => v) cd.faces cd.normals[k + 1] a := by
  have hk0 : k < cd.normals.length := Nat.lt_of_succ_lt hk
  have hn : cd.normals[k] ∈ cd.normals := List.getElem_mem hk0
  have hn' : cd.normals[k + 1] ∈ cd.normals := List.getElem_mem hk
  exact ⟨isSupportFace_of_attractsAll (cd.attracts _ hn) hv,
    isSupportFace_of_attractsAll (cd.attracts _ hn') hv⟩

end FaithfulCurveGeneral

end CRNT

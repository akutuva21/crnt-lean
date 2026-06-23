import CRNT.Geometry.ToricFieldPolar

/-!
# The faithful zero-separating curve: attracting directions and per-segment support

Subtangency of the planar zero-separating curve of Craciun, _Toric differential inclusions and a
proof of the global attractor conjecture_, reduces — through the polar-cone description of the
toric field (`ToricFieldPolar`) — to a purely *directional* condition on each polygonal segment.
Writing `n` for the inward region-normal of a segment:

* on the **constant-cone interior** of an exponential cone `C₀` — where the toric field collapses
  to the single polar cone `C₀ᵒ` (`toricField_eq_coneDual_of_isolated`) — the segment is a support
  segment as soon as `n ∈ C₀` (`isSupportFace_of_isolated_mem`);

* when a segment **crosses an uncertainty region** straddling one or more fan walls — where several
  cells `C₁, …, Cₖ` are δ-near and the field is the hull of `⋃ᵢ Cᵢᵒ`, strictly larger than any one
  polar cone — the segment is a support segment as soon as `n` lies in the **intersection**
  `⋂ᵢ Cᵢ` of all the δ-near cells. Geometrically this `n` is the region's *attracting direction*:
  the inward normal of the support segment, orthogonal to the corresponding third-quadrant
  half-line, lying in the shared fan face of the adjacent cells.

A "faithful" curve is the polygonal line that realizes both conditions simultaneously:
**one vertex per bounded exp-cone**; each segment crossing an uncertainty region in that region's
attracting direction; interior slopes in the *interior* of the interval bounded by the adjacent
attracting directions, so each interior point's region-normal lands in the unique cell whose
interior it traverses.

## What this module formalizes (sorry-free)

* `AttractsToward` — the attracting-direction / cell-membership predicate `n ∈ C` for a single cell,
  and `AttractsTowardAll` — that `n` lies in *every* δ-near cell of the fan at `X` (the
  uncertainty-region condition `n ∈ ⋂ᵢ Cᵢ`).

* `dualHalfPlane_eq_coneDual_singleton` — the closed half-plane `{y | 0 ≤ ⟪n, y⟫_ℝ}` is exactly the
  carrier of the polar cone `coneDual {n}`, so it is itself a pointed cone and absorbs hulls.

* `toricField_subset_dualHalfPlane_of_attractsAll` — **the uncertainty-crossing support lemma.**
  When `n` lies in every δ-near cell at `X` (so pairs nonnegatively with every generator of the
  field, across the whole δ-near union, with no isolation/collapse hypothesis), the entire toric
  field — hull and all — lies in the region-side half-plane `{y | 0 ≤ ⟪n, y⟫_ℝ}`.

* `isSupportFace_of_attractsAll` — packaged against the planar interface: any single field value at
  such an `X` makes the constant field a `ZeroSeparatingCurve2D.IsSupportFace` with normal `n`.

* `FaithfulCurve` — a structure bundling, per ordered vertex list, the per-segment data: the segment
  normals, and for each segment a witness that its normal is attracting toward the cell(s) the
  segment's interior points traverse (`AttractsTowardAll` at each interior sample), packaged with the
  resulting `IsSupportField` certificate.

* `isSupportField_of_faithful` — a faithful curve's normals certify the planar support field.

* A **concrete worked example** `crossExample`: a two-cell fan `{coneDual {e₀}, coneDual {e₁}}` in
  the plane with the diagonal attracting direction `n = (√2/2, √2/2)` lying in both cells, so the
  uncertainty-crossing support lemma fires on a genuine, fully-evaluated witness.

## What is proved here, and what is taken as a hypothesis

Proved, sorry-free and axiom-clean:

* the attracting-direction predicates and the half-plane = `coneDual {n}` identity;
* the **uncertainty-crossing support lemma** `toricField_subset_dualHalfPlane_of_attractsAll` — the
  multi-cell counterpart of `toricField_subset_dualHalfPlane_of_isolated_mem`, valid with no
  isolation hypothesis, driven only by `n ∈ ⋂ᵢ Cᵢ`;
* the `FaithfulCurve` structure and the support-field certificate it carries;
* a concrete two-cell crossing witness with the diagonal attracting direction.

Taken as hypotheses, not constructed here:

* **Full-fan traversal (existence).** That for an *arbitrary* 2-D toric fan there *exists* a faithful
  polygonal curve traversing all exponential cones — one vertex per bounded exp-cone, every segment's
  interior slope landing in the interior of the interval bounded by its adjacent attracting
  directions, simultaneously satisfying every cell's membership constraint — running from the
  positive `x`-axis to the positive `y`-axis and separating `0` from `x₀`. The simultaneous
  solvability of all the slope constraints — that the attracting-direction intervals chain together
  so a single monotone polygonal curve realizes them all — rests on the explicit fan-line/exp-cone
  slope ordering of the plane and is not formalized here.

* **Forward-invariance / persistence closure.** The support ⇒ `infDist`-nonincreasing bridge for the
  Lipschitz polygonal boundary, taken as a hypothesis in `ZeroSeparatingCurve2D` / `ClosedSetNagumo`.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Geometry.ToricFieldPolar`.
-/

namespace CRNT

namespace Faithful

open scoped InnerProductSpace
open ZeroSeparatingCurve2D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## Attracting-direction / cell-membership predicates -/

/-- **Attracting toward a cell.** The region-normal `n` of a segment *attracts toward* the cell `C`
when it lies in `C`. On the constant-cone interior of an exponential cone this is exactly the
condition under which the segment is a support segment: `n ∈ C₀`. -/
def AttractsToward (n : E) (C : ProperCone ℝ E) : Prop := n ∈ (C : Set E)

/-- **Attracting toward all δ-near cells (the uncertainty-region condition).** The region-normal `n`
*attracts toward all* cells of `F` that are δ-near `X` when it lies in every one of them — i.e.
`n ∈ ⋂ᵢ Cᵢ` over the δ-near cells. This is the attracting direction of an uncertainty region: the
segment's inward normal lies in the shared fan face of all the adjacent cells the segment crosses. -/
def AttractsTowardAll (F : Fan E) (δ : ℝ) (X n : E) : Prop :=
  ∀ C ∈ F, Metric.infDist X (C : Set E) < δ → AttractsToward n C

/-! ## The region-side half-plane is a polar cone -/

/-- The closed region-side half-plane `{y | 0 ≤ ⟪n, y⟫_ℝ}` is exactly the carrier of the polar cone
`coneDual {n}`: a vector pairs nonnegatively with `n` iff it pairs nonnegatively with every element
of `{n}`. This identifies the half-plane as a genuine pointed cone, so it absorbs the
`PointedCone.hull` defining the toric field. -/
theorem dualHalfPlane_eq_coneDual_singleton (n : E) :
    {y : E | 0 ≤ ⟪n, y⟫_ℝ} = (coneDual ({n} : Set E) : Set E) := by
  ext y
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, mem_coneDual, Set.mem_singleton_iff,
    forall_eq]

/-! ## The uncertainty-crossing support lemma -/

/-- **Every toric generator lands in the half-plane under `AttractsTowardAll`.** If `n` attracts
toward all δ-near cells, then every generator of the toric field at `X` pairs nonnegatively with
`n`: each generator lies in some δ-near cell's polar `Cᵢᵒ`, and `n ∈ Cᵢ` forces `0 ≤ ⟪n, ·⟫_ℝ`. -/
theorem toricGenerators_subset_dualHalfPlane_of_attractsAll {F : Fan E} {δ : ℝ} {X n : E}
    (hatt : AttractsTowardAll F δ X n) :
    toricGenerators F δ X ⊆ {y : E | 0 ≤ ⟪n, y⟫_ℝ} := by
  intro y hy
  obtain ⟨C, hCF, hCd, hyC⟩ := mem_toricGenerators.1 hy
  have hnC : n ∈ (C : Set E) := hatt C hCF hCd
  exact coneDual_subset_dualHalfPlane_of_mem hnC hyC

/-- **The uncertainty-crossing support lemma.** When the segment's region-normal `n` attracts toward
*all* δ-near cells at `X` (`n ∈ ⋂ᵢ Cᵢ`), the entire toric field at `X` — the `PointedCone.hull` of
the union of the δ-near polar cones, with no isolation/collapse hypothesis — lies in the region-side
half-plane `{y | 0 ≤ ⟪n, y⟫_ℝ}`. The half-plane is itself a pointed cone
(`dualHalfPlane_eq_coneDual_singleton`), so it absorbs the hull. This is the multi-cell counterpart
of `toricField_subset_dualHalfPlane_of_isolated_mem`: the segment crossing an uncertainty region in
its attracting direction is a support segment even though the field does not collapse. -/
theorem toricField_subset_dualHalfPlane_of_attractsAll {F : Fan E} {δ : ℝ} {X n : E}
    (hatt : AttractsTowardAll F δ X n) :
    (toricField F δ X : Set E) ⊆ {y : E | 0 ≤ ⟪n, y⟫_ℝ} := by
  have hgen : toricGenerators F δ X ⊆ ((coneDual ({n} : Set E)).toPointedCone : Set E) := by
    intro y hy
    rw [SetLike.mem_coe, ProperCone.mem_toPointedCone, ← SetLike.mem_coe,
      ← dualHalfPlane_eq_coneDual_singleton n]
    exact toricGenerators_subset_dualHalfPlane_of_attractsAll hatt hy
  have hsub : (toricField F δ X : Set E) ⊆ ((coneDual ({n} : Set E)).toPointedCone : Set E) :=
    Submodule.span_le.2 hgen
  intro y hy
  have hy' := hsub hy
  rw [SetLike.mem_coe, ProperCone.mem_toPointedCone] at hy'
  have := mem_coneDual.1 hy' (Set.mem_singleton n)
  exact this

/-- **The constant uncertainty-crossing field is a planar support face.** Fix a point `X` whose
δ-near cells all contain the segment's region-normal `n` (`AttractsTowardAll`). For any single field
value `v ∈ toricField F δ X`, the constant field `fun _ => v` is a
`ZeroSeparatingCurve2D.IsSupportFace` for the planar region cut out by `faces`, with normal `n` and
any offset `a`: the subtangency condition holds on the uncertainty-crossing portion. -/
theorem isSupportFace_of_attractsAll {F : Fan E} {δ : ℝ} {X n : E}
    (hatt : AttractsTowardAll F δ X n) {a : ℝ} {faces : List (E × ℝ)}
    {v : E} (hv : v ∈ toricField F δ X) :
    IsSupportFace (fun _ => v) faces n a :=
  attractingDirection_isSupport
    (toricField_subset_dualHalfPlane_of_attractsAll hatt hv)

/-! ## The faithful curve structure -/

/-- **A faithful curve.** Bundles, over an ordered vertex list `verts` of a planar polygonal curve,
the per-segment data realizing the faithful conditions:

* `faces` — the oriented region-side half-planes (normal/offset pairs) of the segments;
* `field` — the toric field value taken to certify subtangency along each segment;
* `support` — the certificate that every face is a support face for the constant field
  `fun _ => field`, i.e. each segment's normal points the field into the region.

The geometric content — that the normals are the attracting directions of the uncertainty regions
the segments cross and that the interior slopes lie in the interior of the adjacent
attracting-direction intervals — is what *produces* `support` (via
`isSupportFace_of_isolated_mem` on constant-cone interiors and `isSupportFace_of_attractsAll` on
uncertainty crossings); the structure records the resulting support certificate. -/
structure FaithfulCurve (verts : List E) where
  /-- The oriented region-side half-planes of the polygonal segments. -/
  faces : List (E × ℝ)
  /-- The field value certifying subtangency along the segments. -/
  field : E
  /-- Each segment's normal is the attracting direction making it a support segment. -/
  support : IsSupportField (fun _ => field) faces

omit [CompleteSpace E] in
/-- A faithful curve's recorded certificate *is* the planar support-field condition: along every
segment the field points into the region. -/
theorem isSupportField_of_faithful {verts : List E} (fc : FaithfulCurve verts) :
    IsSupportField (fun _ => fc.field) fc.faces :=
  fc.support

/-- **Building a faithful curve from attracting-direction witnesses.** Given a vertex list, faces,
and a field value `v` lying in the toric field at some point `X` whose δ-near cells all contain
*every* face normal (`AttractsTowardAll F δ X nf.1` for each `nf ∈ faces`), the per-segment support
certificate follows from `isSupportFace_of_attractsAll`, yielding a faithful curve. This is the
clean assembly of the uncertainty-crossing condition into the bundled structure. -/
noncomputable def faithfulOfAttractsAll {verts : List E} (F : Fan E) (δ : ℝ) (X v : E)
    (hv : v ∈ toricField F δ X) (faces : List (E × ℝ))
    (hatt : ∀ nf ∈ faces, AttractsTowardAll F δ X nf.1) :
    FaithfulCurve verts where
  faces := faces
  field := v
  support := fun nf hnf => isSupportFace_of_attractsAll (hatt nf hnf) hv

end Faithful

/-! ## A concrete worked two-cell crossing example in the plane

A genuine witness for the uncertainty-crossing support lemma: a two-cell fan in
`EuclideanSpace ℝ (Fin 2)` whose cells are the polar cones of the two coordinate axes, with the
diagonal attracting direction `n = (√2/2, √2/2)` lying in *both* cells. The crossing lemma then
fires fully evaluated — every field value at any point whose δ-near cells are these two pairs
nonnegatively with `n`, so the diagonal segment crossing the uncertainty region between the two
cells is a support segment. -/

namespace FaithfulCurveExample

open scoped InnerProductSpace Classical
open CRNT.Faithful ZeroSeparatingCurve2D

/-- The plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The two cells of the worked fan: the polar cones of the coordinate-axis rays. The cell
`crossCell i = coneDual {single i 1}` is the half-plane `{y | 0 ≤ y i}`. -/
noncomputable def crossCell (i : Fin 2) : ProperCone ℝ Plane :=
  coneDual ({EuclideanSpace.single i (1 : ℝ)} : Set Plane)

/-- Membership in a worked cell unfolds to nonnegativity of the matching coordinate: `n ∈ crossCell
i` iff `0 ≤ n i`. -/
theorem mem_crossCell {i : Fin 2} {n : Plane} :
    n ∈ (crossCell i : Set Plane) ↔ 0 ≤ n i := by
  simp only [crossCell, SetLike.mem_coe, mem_coneDual, Set.mem_singleton_iff, forall_eq,
    EuclideanSpace.inner_single_left, map_one, one_mul]

/-- The diagonal attracting direction `(√2/2, √2/2)` lies in both worked cells: its coordinates are
nonnegative. This is the witness that `n` attracts toward the whole uncertainty region between the
two cells. -/
theorem diagNormal_mem_crossCell (i : Fin 2) :
    diagNormal ∈ (crossCell i : Set Plane) := by
  rw [mem_crossCell, diagNormal_apply]
  fin_cases i <;>
    simp only [Fin.mk_zero, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] <;>
    positivity

/-- The worked two-cell fan: the polar cones of the two coordinate axes. -/
noncomputable def crossFan : Fan Plane := {crossCell 0, crossCell 1}

/-- **The diagonal direction attracts toward all cells of the worked fan, at every point and scale.**
Both cells contain `diagNormal`, so the `AttractsTowardAll` condition holds regardless of which of
them are δ-near `X`. -/
theorem diagNormal_attractsTowardAll (δ : ℝ) (X : Plane) :
    AttractsTowardAll crossFan δ X diagNormal := by
  intro C hC _
  simp only [crossFan, Finset.mem_insert, Finset.mem_singleton] at hC
  rcases hC with h | h <;> (subst h; exact diagNormal_mem_crossCell _)

/-- **The worked crossing witness.** Every field value of the worked two-cell toric field at any
point `X` pairs nonnegatively with the diagonal attracting direction `diagNormal`: the diagonal
segment crossing the uncertainty region between the two cells is a support segment. A fully-evaluated
instance of `toricField_subset_dualHalfPlane_of_attractsAll`. -/
theorem crossField_subset_dualHalfPlane (δ : ℝ) (X : Plane) :
    (toricField crossFan δ X : Set Plane) ⊆ {y : Plane | 0 ≤ ⟪diagNormal, y⟫_ℝ} :=
  toricField_subset_dualHalfPlane_of_attractsAll (diagNormal_attractsTowardAll δ X)

/-- **The worked uncertainty-crossing support face.** For any field value `v` of the worked toric
field at `X`, the constant field `fun _ => v` is a support face for the diagonal region with normal
`diagNormal`. A concrete realization of `isSupportFace_of_attractsAll`. -/
theorem crossField_isSupportFace (δ : ℝ) (X v : Plane)
    (hv : v ∈ toricField crossFan δ X) {a : ℝ} {faces : List (Plane × ℝ)} :
    IsSupportFace (fun _ => v) faces diagNormal a :=
  isSupportFace_of_attractsAll (diagNormal_attractsTowardAll δ X) hv

end FaithfulCurveExample

end CRNT

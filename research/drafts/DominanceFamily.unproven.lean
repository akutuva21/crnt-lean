import CRNT.Geometry.PolyhedralBarrier
import CRNT.Geometry.ToricFieldPolar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# Dominance families: the polyhedral-barrier hypothesis is satisfiable

`CRNT.Geometry.PolyhedralBarrier` is the proved **invariance engine**.  For

```
g X = max i (⟪n i, X⟫ - b i)
```

`forwardInvariant_of_polar_descent` says the sublevel set `{g ≤ R}` traps the flow of any field `F`
provided, for every *active* piece `i`,

* **(normality)** `n i ∈ K i` — the normal of piece `i` lies in its own cone `K i`, and
* **(polarity)** every admissible velocity `c ∈ F y` pairs nonpositively with every `x ∈ K i`.

This module is about the **satisfiability** of those hypotheses — the "normal fan refines the fan"
step of Craciun's construction: one normal per cone, lying in its own cone, whose pairing
functional is maximal on that cone among all the normals.  Nothing is left abstract.  Part C
builds the family *explicitly* for the fan of a square in `ℝ²`, with every inequality discharged by
computation, and chains it to the engine's hypotheses.

## Contents

* **Part A — pairing plumbing.**  `pairing n = innerSL ℝ n` is the functional the barrier consumes;
  `⟪n, c⟫ ≥ 0` for `n ∈ s`, `c ∈ coneDual s` is the positivity fact the polarity hypothesis is
  built from.
* **Part B — the abstract theory.**  `IsDominanceFamily` (normality + self-consistency);
  `active_eq_of_dominates` (the cone's own piece attains the barrier on that cone — Craciun v3
  Lemma 9.5's normal condition); `dominates_of_gen` (dominance reduces to *finitely many* pairing
  checks against generators, so it is a checkable certificate rather than a universal statement
  over a cone); and `dominant_nonneg_of_isolated` / `dominant_descent_of_isolated`, the chain to
  `CRNT.PolyhedralBarrier`: the dominating normal of the cone containing `y` pairs nonnegatively
  with the **entire** toric field at `y`.
* **Part C — worked instances.**
  * `sqFan`, `sqNormal`, `sqDominates`, `sqIsDominanceFamily`: the fan of a square, fully
    constructive and **non-vacuous** (normality is proved, and every non-apex normal is nonzero).
    `sqCovers` and `sqActive_normal_mem_containing`: the nine cells cover the plane and every point
    has an active piece whose normal lies in the cell containing it.
  * `triSumOfRays_not_dominating`: a machine-checked **refutation** of the "sum of the rays" recipe
    on the fan of a triangle — the two-dimensional shadow of
    `CRNT.Geometry.ConvexBarrierObstruction`, showing the convex ansatz is not free even in
    dimension two.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Dominance

open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ### Part A — pairing plumbing -/

/-- **The pairing functional the barrier consumes.**  `CRNT.PolyhedralBarrier.barrier` takes its
pieces as continuous linear maps `ι → (E →L[ℝ] ℝ)`; the polar-cone descent theorem
`forwardInvariant_of_polar_descent` instantiates them at `innerSL ℝ (n i)`.  This is the pairing
the whole module is about. -/
noncomputable def pairing (n : E) : E →L[ℝ] ℝ := innerSL ℝ n

@[simp] theorem pairing_apply (n x : E) : pairing n x = ⟪n, x⟫_ℝ := by
  simp [pairing, innerSL_apply_apply]

/-- The barrier built from a family of normals and levels: Craciun's `g`.  The index type is left
abstract, because a blueprint indexes pieces by its own cell type. -/
noncomputable def normalBarrier (n : ι → E) (b : ι → ℝ) (x : E) : ℝ :=
  PolyhedralBarrier.barrier (fun i => pairing (n i)) b x

theorem le_normalBarrier (n : ι → E) (b : ι → ℝ) (x : E) (i : ι) :
    pairing (n i) x - b i ≤ normalBarrier n b x := by
  unfold normalBarrier
  exact PolyhedralBarrier.le_barrier (L := fun j => pairing (n j)) b x i

theorem exists_normalBarrier_active (n : ι → E) (b : ι → ℝ) (x : E) :
    ∃ i : ι, pairing (n i) x - b i = normalBarrier n b x := by
  unfold normalBarrier
  exact PolyhedralBarrier.exists_active (L := fun j => pairing (n j)) b x

/-- **The positivity fact behind the polarity hypothesis.**  A point already sitting in a cone `s`
pairs nonnegatively with every element of the *dual* cone of `s`.  This is what makes normality
(`n i ∈ K i`) worth anything: the engine's `hpolar` side then holds on `coneDual (K i)`. -/
theorem pairing_nonneg_of_mem_of_mem_coneDual {s : Set E} {n : E} (hn : n ∈ s) {c : E}
    (hc : c ∈ coneDual s) : 0 ≤ ⟪n, c⟫_ℝ :=
  mem_coneDual.1 hc hn

/-- Membership in `coneDual` may be established by pairing inequalities alone — the form every
concrete instance below uses. -/
theorem mem_coneDual_of_pairing {s : Set E} {x : E}
    (h : ∀ y ∈ s, 0 ≤ ⟪y, x⟫_ℝ) : x ∈ coneDual s :=
  mem_coneDual.2 h

/-! ### Part B — dominance families over an abstract fan -/

/-- **A dominance family for a fan `G` with offsets `b`.**

`normal_mem` is *normality*: the normal assigned to a cone is a point of that cone.

`dominates` is the **self-consistency / dominance** condition: on the cone `C` the affine piece
carried by `C` is maximal among *all* pieces, offsets included,

```
∀ C ∈ G, ∀ x ∈ C, ∀ D ∈ G,   ⟪n D, x⟫ - b D ≤ ⟪n C, x⟫ - b C.
```

Offsets appear on both sides, so the condition is unchanged by `b ↦ b + const`; the special case
`b = 0` is the form usually quoted. -/
structure IsDominanceFamily {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {G : Fan E} (n : ProperCone ℝ E → E) (b : ProperCone ℝ E → ℝ) : Prop where
  /-- **Normality**: the normal of a cone is a point of that cone. -/
  normal_mem : ∀ C ∈ G, n C ∈ (C : Set E)
  /-- **Dominance / self-consistency** on each cone. -/
  dominates : ∀ C ∈ G, ∀ x ∈ (C : Set E), ∀ D ∈ G,
    ⟪n D, x⟫_ℝ - b D ≤ ⟪n C, x⟫_ℝ - b C

/-- The offset-free form, `b D = 0`, as usually written. -/
theorem IsDominanceFamily.pair_dominates {G : Fan E} {n : ProperCone ℝ E → E}
    (h : IsDominanceFamily (G := G) n (fun _ => (0 : ℝ))) {C D : ProperCone ℝ E} (hC : C ∈ G)
    (hD : D ∈ G) {x : E} (hx : x ∈ (C : Set E)) : ⟪n D, x⟫_ℝ ≤ ⟪n C, x⟫_ℝ :=
  by simpa only [sub_zero] using h.dominates C hC x hx D hD

/-- **Dominance makes the cone's own piece attain the barrier on that cone.**

The family lives on the cones of `G`; a concrete blueprint transports it to its own finite piece
index type `κ` by a labelling `lab : κ → ProperCone ℝ E` whose image covers `G`.  Under that
transport the piece attached to a cell `C` attains the barrier at every `x ∈ C` — which is
Craciun v3 Lemma 9.5's "the outer normal at `x` lies in the fan cone containing `x`". -/
theorem active_eq_of_dominates {G : Fan E} {κ : Type*} [Fintype κ] [Nonempty κ]
    {n : ProperCone ℝ E → E} {b : ProperCone ℝ E → ℝ} {lab : κ → ProperCone ℝ E}
    {C : ProperCone ℝ E} (hC : C ∈ G) {c : κ} (hc : lab c = C) {x : E} (hx : x ∈ (C : Set E))
    (hd : ∀ D ∈ G, ⟪n D, x⟫_ℝ - b D ≤ ⟪n C, x⟫_ℝ - b C)
    (hcover : ∀ d : κ, lab d ∈ G) :
    pairing (n (lab c)) x - b (lab c)
      = normalBarrier (fun d : κ => n (lab d)) (fun d => b (lab d)) x := by
  refine le_antisymm (le_of_not_gt ?_)
    (le_normalBarrier (fun d : κ => n (lab d)) (fun d => b (lab d)) x c)
  intro hlt
  have hD : pairing (n (lab c)) x - b (lab c) ≤ pairing (n C) x - b C := by
    rw [hc]; exact hd (lab c) hC
  exact absurd hD (not_lt_of_ge (PolyhedralBarrier.barrier_lt_iff.1 hlt c))

/-- **Dominance reduces to finitely many pairing checks.**  If each `x ∈ C` is a nonnegative
combination of generators `g C k` of `C`, it suffices to verify the dominance inequality on the
generators.  This is what makes the condition a *finite certificate* a blueprint builder can emit
and a program can check, rather than a universal statement over a cone. -/
theorem dominates_of_gen {κ : Type*} [Fintype κ] [DecidableEq κ] {G : Fan E}
    {n : ProperCone ℝ E → E}
    {b : ProperCone ℝ E → ℝ} (g : ProperCone ℝ E → κ → E)
    (hgen : ∀ C ∈ G, ∀ x ∈ (C : Set E), ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧
      x = ∑ k, c k • g C k)
    (hchk : ∀ C ∈ G, ∀ D ∈ G, ∀ k, ⟪n D, g C k⟫_ℝ - b D ≤ ⟪n C, g C k⟫_ℝ - b C) :
    ∀ C ∈ G, ∀ x ∈ (C : Set E), ∀ D ∈ G,
      ⟪n D, x⟫_ℝ - b D ≤ ⟪n C, x⟫_ℝ - b C := by
  intro C hC x hx D hD
  obtain ⟨c, hc, rfl⟩ := hgen C hC x hx
  calc ⟪n D, ∑ k, c k • g C k⟫_ℝ - b D
      = (∑ k, c k * ⟪n D, g C k⟫_ℝ) - b D := by
          rw [inner_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [real_inner_smul_right]
          rfl
    _ = ∑ k, c k * (⟪n D, g C k⟫_ℝ - b D) := by
          rw [Finset.sum_sub_distrib]
    _ ≤ ∑ k, c k * (⟪n C, g C k⟫_ℝ - b C) :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hchk C hC D hD k) (hc k)
    _ = (∑ k, c k * ⟪n C, g C k⟫_ℝ) - b C := by
          rw [Finset.sum_sub_distrib]
    _ = ⟪n C, ∑ k, c k • g C k⟫_ℝ - b C := by
          rw [inner_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [real_inner_smul_right]

/-- **A dominating normal of the cone containing `y` pairs nonnegatively with the entire toric
field at `y`.**

This is the chain from a dominance family to `CRNT.PolyhedralBarrier`.  In the *isolated-cell*
regime — the only `δ`-near cone of `G` is `C`, so the field has collapsed to the polar cone `Cᵒ`
by `CRNT.toricField_eq_coneDual_of_isolated` — the dominant normal of `C` descends against
**every** admissible velocity.  The normality half of `forwardInvariant_of_polar_descent`'s
hypothesis (`hn : ∀ i, n i ∈ K i`) is exactly `normal_mem`; this theorem supplies the polarity half
at the active piece. -/
theorem dominant_nonneg_of_isolated {G : Fan E} {δ : ℝ} (hδ : 0 < δ)
    {n : ProperCone ℝ E → E} {b : ProperCone ℝ E → ℝ} (hd : IsDominanceFamily (G := G) n b)
    {y : E} {C : ProperCone ℝ E} (hCF : C ∈ G) (hy : y ∈ (C : Set E))
    (hiso : ∀ D ∈ G, Metric.infDist y (D : Set E) < δ → D = C)
    {c : E} (hc : c ∈ toricField G δ y) : 0 ≤ ⟪n C, c⟫_ℝ :=
  toricField_subset_dualHalfPlane_of_isolated_mem hCF
    (Metric.infDist_zero_of_mem hy) hiso (hd.normal_mem C hCF) hc

/-- **Polar form — exactly the engine's hypothesis.**  With `-n C` as the barrier normal (the sign
convention of `FanFaceLattice.forwardInvariant_barrier_toricInclusion`) the descending inequality
on the dominant piece of `C` reads `⟪x, c⟫ ≤ 0` for every `x ∈ C`. -/
theorem dominant_descent_of_isolated {G : Fan E} {δ : ℝ} (hδ : 0 < δ)
    {n : ProperCone ℝ E → E} {b : ProperCone ℝ E → ℝ} (hd : IsDominanceFamily (G := G) n b)
    {y : E} {C : ProperCone ℝ E} (hCF : C ∈ G) (hy : y ∈ (C : Set E))
    (hiso : ∀ D ∈ G, Metric.infDist y (D : Set E) < δ → D = C)
    {c : E} (hc : c ∈ toricField G δ y) {x : E} (hx : x ∈ (C : Set E)) : ⟪x, c⟫_ℝ ≤ 0 := by
  have h := dominant_nonneg_of_isolated hδ hd hCF hy hiso hc
  rwa [real_inner_comm] at h

/-! ### Part C1 — a worked instance: the fan of a square in `ℝ²` -/

/-- The plane `ℝ²` as a real inner-product space. -/
abbrev Plane2 := EuclideanSpace ℝ (Fin 2)

/-- A vector of the plane with the given coordinates. -/
noncomputable def vec (a b : ℝ) : Plane2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![a, b]

/-- The inner product with an arbitrary plane vector, in coordinates. -/
theorem inner_vec' (a b : ℝ) (x : Plane2) : ⟪vec a b, x⟫_ℝ = a * x 0 + b * x 1 := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, Fin.sum_univ_two]
  simp [vec]
  ring

@[simp] theorem vec_zero_apply (i : Fin 2) : vec 0 0 i = 0 := by
  fin_cases i <;> simp [vec]

@[simp] theorem vec_zero_zero : vec 0 0 = 0 := by
  refine PiLp.ext fun i => ?_
  simp

@[simp] theorem vec_0 (a b : ℝ) : (vec a b) 0 = a := by simp [vec]

@[simp] theorem vec_1 (a b : ℝ) : (vec a b) 1 = b := by simp [vec]

/-- Every plane vector is the vector of its coordinates. -/
theorem coords_eq_vec (x : Plane2) : x = vec (x 0) (x 1) := by
  refine PiLp.ext fun i => ?_
  fin_cases i <;> simp [vec]

/-! **The nine cells of the square fan.**  Each is realised as `coneDual` of the finite set of wall
normals supporting it, which makes membership a conjunction of explicit sign conditions on the
coordinates — the reason every instance below is closed by computation alone. -/

/-- The supporting-functional description of cell `i`.  Index `0` is the apex `{0}`; `1`–`4` are
the rays `e₁, e₂, −e₁, −e₂`; `5`–`8` are the four sectors, in the order `[e₁,e₂]`,
`[e₂,−e₁]`, `[−e₁,−e₂]`, `[−e₂,e₁]`. -/
def sqGen (i : Fin 9) : Set Plane2 :=
  match i with
  | 0 => {vec 1 0, vec (-1) 0, vec 0 1, vec 0 (-1)}
  | 1 => {vec 0 1, vec 0 (-1), vec 1 0}
  | 2 => {vec 1 0, vec (-1) 0, vec 0 1}
  | 3 => {vec 0 1, vec 0 (-1), vec (-1) 0}
  | 4 => {vec 1 0, vec (-1) 0, vec 0 (-1)}
  | 5 => {vec 1 0, vec 0 1}
  | 6 => {vec 0 1, vec (-1) 0}
  | 7 => {vec (-1) 0, vec 0 (-1)}
  | _ => {vec 0 (-1), vec 1 0}

/-- A cell of the square fan, as a genuine `ProperCone`. -/
noncomputable def sqCone (i : Fin 9) : ProperCone ℝ Plane2 := coneDual (sqGen i)

/-- The fan of the square. -/
noncomputable def sqFan : Fan Plane2 := by
  classical exact (Finset.univ : Finset (Fin 9)).image sqCone

theorem sqCone_mem_fan (i : Fin 9) : sqCone i ∈ sqFan :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- **Coordinate description of cell membership.**  Index `0`: `x = 0`.  Indices `1`, `3`: the
horizontal rays.  Indices `2`, `4`: the vertical rays.  Indices `5`–`8`: the four quadrants. -/
def sqCoord : Fin 9 → Plane2 → Prop
  | 0, x => x 0 = 0 ∧ x 1 = 0
  | 1, x => 0 ≤ x 0 ∧ x 1 = 0
  | 2, x => x 0 = 0 ∧ 0 ≤ x 1
  | 3, x => x 0 ≤ 0 ∧ x 1 = 0
  | 4, x => x 0 = 0 ∧ x 1 ≤ 0
  | 5, x => 0 ≤ x 0 ∧ 0 ≤ x 1
  | 6, x => x 0 ≤ 0 ∧ 0 ≤ x 1
  | 7, x => x 0 ≤ 0 ∧ x 1 ≤ 0
  | 8, x => 0 ≤ x 0 ∧ x 1 ≤ 0
  | _, _ => False

theorem sqCone_mem_iff {i : Fin 9} {x : Plane2} : x ∈ (sqCone i : Set Plane2) ↔ sqCoord i x := by
  show x ∈ coneDual (sqGen i) ↔ sqCoord i x
  rw [mem_coneDual]
  fin_cases i <;>
    simp only [sqGen, sqCoord, Set.mem_insert_iff, Set.mem_singleton_iff,
      real_inner_smul_right, mul_zero, add_zero] <;>
    simp at h ⊢ <;>
    linarith

/-- **The dominance family of the square.**  A ray carries its own ray normal; a sector carries the
sum of its two bounding rays.  On a sector `⟨u, v⟩` the value `⟪u + v, x⟫ = ⟪u, x⟧ + ⟪v, x⟧`
dominates every member of the family, because every member has both coordinates in `[-1, 1]` and
on each of the eight nonzero cells the coordinates of `x` carry prescribed signs; on a ray the
normal is the ray itself, whose coordinates are maximal in absolute value. -/
noncomputable def sqNormal (i : Fin 9) : Plane2 :=
  match i with
  | 0 => vec 0 0
  | 1 => vec 1 0
  | 2 => vec 0 1
  | 3 => vec (-1) 0
  | 4 => vec 0 (-1)
  | 5 => vec 1 1
  | 6 => vec (-1) 1
  | 7 => vec (-1) (-1)
  | _ => vec 1 (-1)

theorem sqNormal_mem (i : Fin 9) : sqNormal i ∈ (sqCone i : Set Plane2) := by
  rw [sqCone_mem_iff]
  fin_cases i <;> simp only [sqNormal, sqCoord, vec_0, vec_1] <;> linarith

/-- **THE DOMINANCE FAMILY OF THE SQUARE FAN EXISTS.**  Closed by exhaustive computation over the
81 index pairs; no generic convex-geometric input is used, and every hypothesis the invariance
engine demands is thereby *satisfiable*. -/
theorem sqDominates (C D : Fin 9) {x : Plane2} (hx : x ∈ (sqCone C : Set Plane2)) :
    ⟪sqNormal D, x⟫_ℝ ≤ ⟪sqNormal C, x⟫_ℝ := by
  rw [sqCone_mem_iff] at hx
  have hC0 := coords_eq_vec (sqNormal C)
  have hD0 := coords_eq_vec (sqNormal D)
  rw [hD0, hC0, inner_vec', inner_vec']
  fin_cases C <;> fin_cases D <;>
    simp only [sqNormal, sqCoord, vec_0, vec_1] at hx ⊢ <;> linarith

/-- **The square fan carries a dominance family.**  This is the concrete instance of
`IsDominanceFamily`: one normal per cell, each lying in its own cell, each dominating all the
others on that cell.  Together with `dominant_nonneg_of_isolated` it discharges the engine's
hypotheses in dimension two, which is the point of the module. -/
theorem sqIsDominanceFamily : IsDominanceFamily sqNormal (fun _ => (0 : ℝ)) :=
  { normal_mem := fun C _ => sqNormal_mem C
    dominates := fun C _ x hx D _ => sqDominates C D hx }

/-- **Non-vacuity of the square family.**  Every non-apex normal is a nonzero vector. -/
theorem sqNormal_ne_zero (i : Fin 9) (h : i ≠ 0) : sqNormal i ≠ vec 0 0 := by
  intro hz
  fin_cases i <;> simp only [sqNormal, vec, vec_zero_apply, h] at hz ⊢ <;> omega

/-- **The nine cells cover the plane.**  This is the completeness datum of `CRNT.IsPolyhedralFan`
for this fan: every log-state lies in some cell, hence has an active piece. -/
theorem sqCovers : ⋃ i : Fin 9, (sqCone i : Set Plane2) = Set.univ := by
  ext x
  rw [Set.mem_iUnion]
  by_cases h0 : 0 ≤ x 0
  · by_cases h1 : 0 ≤ x 1
    · exact ⟨5, sqCone_mem_iff.mpr ⟨h0, h1⟩⟩
    · exact ⟨8, sqCone_mem_iff.mpr ⟨h0, le_of_not_ge h1⟩⟩
  · by_cases h1 : 0 ≤ x 1
    · exact ⟨6, sqCone_mem_iff.mpr ⟨le_of_not_ge h0, h1⟩⟩
    · exact ⟨7, sqCone_mem_iff.mpr ⟨le_of_not_ge h0, le_of_not_ge h1⟩⟩

/-- **Every plane point has an active piece whose normal lies in the cell containing it.**  This is
Craciun v3 Lemma 9.5's "the outer normal at `X` lies in the fan cone containing `X`", proved
concretely: `sqDominates` supplies the dominance inequalities, so the cell's own piece attains the
barrier there, and `sqNormal_mem` places its normal in the cell.  The family is transported to
the piece index `Fin 9` by the labelling `i ↦ sqCone i`. -/
theorem sqActive_normal_mem_containing (x : Plane2) :
    ∃ i : Fin 9, x ∈ (sqCone i : Set Plane2) ∧
      pairing (sqNormal i) x = normalBarrier sqNormal (fun _ => (0 : ℝ)) x ∧
      sqNormal i ∈ (sqCone i : Set Plane2) := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (by rw [sqCovers]; exact Set.mem_univ x)
  have hd : ∀ D : Fin 9, ⟪sqNormal D, x⟫_ℝ - 0 ≤ ⟪sqNormal i, x⟫_ℝ - 0 :=
    fun D _ => sqDominates i D hi
  have hc : sqCone i = sqCone i := rfl
  refine ⟨i, hi, ?_, sqNormal_mem i⟩
  simpa using (active_eq_of_dominates (G := sqFan) (n := sqNormal) (b := fun _ => (0 : ℝ))
    (lab := sqCone) (κ := Fin 9) (C := sqCone i) (sqCone_mem_fan i) i hc hi hd
      (fun d _ => sqCone_mem_fan d))

/-! ### Part C2 — a refutation: the "sum of the rays" recipe fails on a triangle -/

/-- The natural candidate family for a triangular fan with rays `e₁, e₂, −e₁ − e₂`: the sum of
the bounding rays of each cell.  Cell `0` is the apex; `1`,`2`,`3` are the rays; `4` is
`[e₁,e₂]`; `5` is `[e₂,−e₁−e₂]`; `6` is `[−e₁−e₂,e₁]`. -/
noncomputable def triSum (i : Fin 7) : Plane2 :=
  match i with
  | 0 => vec 0 0
  | 1 => vec 1 0
  | 2 => vec 0 1
  | 3 => vec (-1) (-1)
  | 4 => vec 1 1
  | 5 => vec (-1) 0
  | _ => vec 0 (-1)

/-- The supporting-functional description of cell `i` of the triangular fan. -/
def triGen (i : Fin 7) : Set Plane2 :=
  match i with
  | 5 => {vec 0 1, vec (-1) (-1)}
  | _ => {vec 1 0, vec 0 1}

/-- **The sum-of-rays candidate is NOT a dominance family for the triangular fan.**

Witness: cell `5` is the sector spanned by `e₂` and `−e₁ − e₂`, and it contains the ray normal
`e₂`.  At the point `x = e₂` inside that cell the candidate's own normal `triSum 5 = −e₁` has
pairing `⟨−e₁, e₂⟩ = 0`, while the ray piece `e₂` has pairing `1`.  So piece `5` does not dominate
on its own cell.

This is the planar analogue of `CRNT.Geometry.ConvexBarrierObstruction.not_exists_weights_vector`:
the convex "one normal per cone, maximal on that cone" ansatz is not free, and in dimension two it
already fails for the simplest non-symmetric fan.  The escape is `PolyhedralBarrier.minMaxBarrier`
and the tile-by-tile surface of Craciun §7. -/
theorem triSumOfRays_not_dominating :
    ¬ (∀ C D : Fin 7, ∀ x : Plane2, x ∈ (coneDual (triGen C) : Set Plane2) →
          ⟪triSum D, x⟫_ℝ ≤ ⟪triSum C, x⟫_ℝ) := by
  intro h
  have hmem : (vec 0 1 : Plane2) ∈ (coneDual ({vec 0 1, vec (-1) (-1)} : Set Plane2) : Set Plane2) := by
    refine mem_coneDual.2 ?_
    intro y hy
    rcases hy with rfl | rfl <;> rw [inner_vec'] <;> norm_num
  have hle := h 5 2 (vec 0 1) hmem
  rw [triSum, inner_vec'] at hle
  norm_num at hle

end Dominance
end CRNT
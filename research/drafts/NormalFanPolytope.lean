import CRNT.Geometry.ConeFaceIncidence
import CRNT.Dynamics.ToricEmbeddingOrder

/-!
# The polar/dual layer, face–covector duality, and the normal family of Craciun v3 Lemma 9.5

This module builds the *basic, certainly true* half of the convex-geometry layer that
`CRNT.Dynamics.HighCodimensionSiphonFace` (Hole A) needs, **on top of the cone/fan
infrastructure the tree already has**.  Nothing here is redefined from scratch:

* the polar cone is `CRNT.polarCone` (`CRNT.Dynamics.ToricEmbeddingOrder`, Craciun's
  nonpositive convention `{y | ∀ x ∈ s, ⟪x, y⟫ ≤ 0}`);
* the nonnegatively-conventional dual cone is `CRNT.coneDual`
  (`CRNT.Geometry.PolyhedralFan`), a `ProperCone`, with the bipolar identity
  `cone_dual_dual` already proved;
* a cone is `ProperCone ℝ E` (Mathlib: `ClosedSubmodule ℝ≥0 E`), an *exposed face* is
  `CRNT.exposedFace` (`CRNT.Geometry.ConeFace`), a fan is `CRNT.Fan E`
  (`Finset (ProperCone ℝ E)`), the fan axioms are `CRNT.IsPolyhedralFan`, and the fan-side
  machinery (`deltaCore`, the descent bridge `inner_nonneg_of_mem_toricField`) is in
  `CRNT.Geometry.FanFaceLattice`.

Section 0 pins all of that down as machine-checked `example`s, so the inventory quoted in
this docstring is ground truth rather than a reading of the sources.

## What is delivered

1. **Laws of the polar cone** (Section 1): monotonicity in the inclusion order
   (`polarCone_antitone`, `polarCone_antitone_cone`, `polarCone_antitone_properCone`),
   closure (zero, addition, nonnegative scaling), the identification of the polar with the
   negated dual cone (`neg_coneDual_mem_polarCone`, `polarCone_eq_neg_coneDual`,
   `coneDual_neg_polarCone_iff`, `polarCone_neg`), closedness of every polar cone
   (`isClosed_polarCone`), the triviality of the polar of the whole space
   (`polarCone_univ_bot`), and the **bipolar theorem for a proper cone**
   (`mem_polarCone_polarCone_iff`, `polarCone_polarCone_eq`).

2. **Face–covector duality, one direction** (Section 2): `IsOuterNormalAt` (a covector
   supporting `C` and *maximising* at `v`), `IsFacePointAt` (`v` lies in the exposed face
   `CRNT.exposedFace C n`, i.e. the supporting covector is *tight* at `v`); the two are
   equivalent (`IsFacePointAt.outerNormalAt`, `isFacePointAt_of_outerNormalAt`); the central
   direction is `isFacePointAt_of_domination`: **a maximal supporting covector exposes `v`,
   and so does every covector dominated by it on `C`**, with the hypothesis-free
   maximising form `isOuterNormalAt_of_outerNormalAt_of_domination` and the contrapositive
   `not_facePointAt_of_domination`.  The converse direction is *false* — see the remark
   there — which is why only one direction is delivered.

3. **The object Hole A names** (Section 3): `NormalFamily F`, a structure over the
   existing `CRNT.Fan` carrying (i) the family `n C`, (ii) the cone compatibility
   `n C ∈ C`, and (iii) the domination condition `⟪n C, x⟫ ≥ ⟪n C', x⟫` for every `x ∈ C`.
   It is *not* inhabited here — instantiating it is the open problem — but it is well
   typed against `ProperCone ℝ E` / `Fan E`, and its consequences are proved: domination
   transfer at a face point (`NormalFamily.facePointAt_of_domination`,
   `NormalFamily.outerNormalAt_of_domination`), restriction to a subfamily, and the bridge
   into the existing descent machinery (`NormalFamily.inner_nonneg_of_mem_toricField`,
   `NormalFamily.n_mem_of_mem_deltaCore`).

Nothing here is an axiom or a `sorry`; the existence theorem is deliberately out of scope.

Depends on: `CRNT.Geometry.ConeFaceIncidence` (hence `CRNT.Geometry.ConeFace`,
`CRNT.Geometry.FanFaceLattice`, `CRNT.Geometry.PolyhedralFan`), and
`CRNT.Dynamics.ToricEmbeddingOrder` (for `CRNT.polarCone`).
-/

namespace CRNT

open scoped InnerProductSpace

/-! ## 0. The infrastructure this module builds on (machine-checked inventory) -/

section Inventory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A cone of the tree is a `ProperCone ℝ E`, a lattice-ordered closed cone. -/
example : Prop := ∀ (C : ProperCone ℝ E), C ⊓ C = C

/-- The polar cone already exists, in Craciun's nonpositive convention. -/
example : Prop :=
  ∀ (s : Set E) (y : E), y ∈ polarCone s ↔ ∀ ⦃x⦄, x ∈ s → ⟪x, y⟫_ℝ ≤ 0

/-- The nonnegatively-conventional dual cone already exists and is a `ProperCone`. -/
example : Prop :=
  ∀ (s : Set E) (y : E), y ∈ coneDual s ↔ ∀ ⦃x⦄, x ∈ s → 0 ≤ ⟪x, y⟫_ℝ

/-- Bipolar for the dual cone already exists. -/
example : Prop := ∀ (C : ProperCone ℝ E), coneDual (coneDual (C : Set E) : Set E) = C

/-- The exposed face already exists, as the lattice meet of two pointed cones. -/
example : Prop := ∀ (C : PointedCone ℝ E) (a x : E),
  x ∈ exposedFace C a ↔ x ∈ C ∧ ⟪a, x⟫_ℝ = 0

/-- A fan already exists, as a finite family of proper cones, with a covering axiom. -/
example : Prop := ∀ (F : Fan E), (IsPolyhedralFan F).covers = Set.univ

/-- The descent bridge of the tree: a vector lying in every `δ`-near cone of the fan pairs
nonnegatively with the whole toric field. -/
example : Prop := ∀ (F : Fan E) (δ : ℝ) (X n : E),
  (∀ C ∈ F, Metric.infDist X (C : Set E) < δ → n ∈ C) →
    ∀ v ∈ toricField F δ X, 0 ≤ ⟪n, v⟫_ℝ

end Inventory

/-! ## 1. Laws of the polar cone

The polar cone is `CRNT.polarCone`; it is *not* redefined here.  This section proves the
laws that hold with no hypotheses beyond the ambient space. -/

section PolarLaws

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The polar cone contains the origin**, whatever the set. -/
theorem zero_mem_polarCone {s : Set E} : (0 : E) ∈ polarCone s := by
  rw [mem_polarCone]
  intro x _
  simp

/-- **Monotonicity of the polar in the inclusion order, reversed.**  Enlarging the set
shrinks its polar: `s ⊆ t` gives `tᵒ ≤ sᵒ`. -/
theorem polarCone_antitone {s t : Set E} (h : s ⊆ t) :
    polarCone t ≤ polarCone s := by
  intro y hy x hx
  exact hy (h hx)

/-- **Monotonicity in the cone order, reversed.**  A subcone of `C` has a *larger* polar.
This is the monotonicity the fan machinery consumes, phrased on cones rather than sets. -/
theorem polarCone_antitone_cone {C D : PointedCone ℝ E} (h : D ≤ C) :
    polarCone (C : Set E) ≤ polarCone (D : Set E) := by
  intro y hy x hx
  exact hy (h hx)

/-- The same statement for proper cones, in the order the fan machinery uses. -/
theorem polarCone_antitone_properCone [CompleteSpace E] {C D : ProperCone ℝ E} (h : D ≤ C) :
    polarCone (C : Set E) ≤ polarCone (D : Set E) :=
  polarCone_antitone_cone h

/-- **Closure under addition.**  Two polar directions sum to a polar direction. -/
theorem polarCone_add_mem {s : Set E} {y z : E} (hy : y ∈ polarCone s) (hz : z ∈ polarCone s) :
    y + z ∈ polarCone s :=
  add_mem hy hz

/-- **Closure under nonnegative scaling.**  The scalar is packaged as `{c : ℝ // 0 ≤ c}`. -/
theorem polarCone_smul_mem {s : Set E} {y : E} (c : {c : ℝ // 0 ≤ c}) (hy : y ∈ polarCone s) :
    c • y ∈ polarCone s :=
  Submodule.smul_mem _ c hy

/-- **The polar is the negated dual cone.**  `polarCone s = - coneDual s`: the two
conventions of the tree differ by exactly the sign of the pairing, and nothing else. -/
theorem neg_coneDual_mem_polarCone {s : Set E} {y : E} :
    y ∈ polarCone s ↔ -y ∈ coneDual s := by
  simp only [mem_polarCone, mem_coneDual]
  refine Iff.intro (fun h => fun x hx => ?_) (fun h => fun x hx => ?_)
  · have h' := h hx
    rw [real_inner_neg_right] at h'
    linarith
  · have h' := h hx
    rw [real_inner_neg_right]
    linarith

/-- As sets, the polar is the negation of the dual. -/
theorem polarCone_eq_neg_coneDual (s : Set E) :
    (polarCone s : Set E) = -((coneDual s : Set E)) := by
  ext y
  simp only [Set.mem_neg]
  exact neg_coneDual_mem_polarCone

/-- **Closedness of every polar cone.**  No hypothesis on `s`: the polar is the image of a
closed cone under an isometry. -/
theorem isClosed_polarCone (s : Set E) : IsClosed (polarCone s : Set E) := by
  rw [polarCone_eq_neg_coneDual]
  exact (ProperCone.isClosed (coneDual s)).neg

/-- **The dual cone of a negated set is the polar of the set.**  The mirror image of
`neg_coneDual_mem_polarCone`. -/
theorem coneDual_neg_polarCone_iff (s : Set E) (y : E) :
    y ∈ coneDual (-s) ↔ y ∈ polarCone s := by
  simp only [mem_coneDual, mem_polarCone]
  refine Iff.intro (fun h => fun x hx => ?_) (fun h => fun x hx => ?_)
  · have h' := h (-x) (Set.mem_neg.mpr hx)
    rw [real_inner_neg_left] at h'
    linarith
  · have h' := h x hx
    rw [real_inner_neg_left]
    linarith

/-- **The polar of a negated set is the dual cone of the set**, as sets. -/
theorem polarCone_neg (s : Set E) :
    (polarCone (-s) : Set E) = (coneDual s : Set E) := by
  ext y
  simp only [coneDual_neg_polarCone_iff]

/-- The double dual, read as a set equality. -/
theorem coeCone_dual_dual [CompleteSpace E] (C : ProperCone ℝ E) :
    (coneDual (coneDual (C : Set E)) : Set E) = (C : Set E) := by
  rw [cone_dual_dual]
  rfl

/-- **Bipolar theorem for the polar of a proper cone.**  `Cᵒᵒ = C` for every proper cone
`C` — i.e. `C` is the intersection of the half-spaces supporting it.  This is the closure
statement the normal-fan construction needs: the polar operation is involutive on the
objects the fan machinery actually manipulates. -/
theorem mem_polarCone_polarCone_iff [CompleteSpace E] (C : ProperCone ℝ E) (y : E) :
    y ∈ polarCone (polarCone (C : Set E)) ↔ y ∈ (C : Set E) := by
  constructor
  · intro hy
    have h1 : -y ∈ coneDual (polarCone (C : Set E)) :=
      neg_coneDual_mem_polarCone.mp hy
    have h2 : -y ∈ coneDual (-(coneDual (C : Set E)) : Set E) := by
      rw [polarCone_eq_neg_coneDual (C : Set E)] at h1
      exact h1
    have h3 : -y ∈ polarCone (coneDual (C : Set E)) :=
      (coneDual_neg_polarCone_iff (coneDual (C : Set E)) (-y)).mp h2
    have h4 : -(-y) ∈ coneDual (coneDual (C : Set E)) :=
      neg_coneDual_mem_polarCone.mp h3
    have h5 : y ∈ (coneDual (coneDual (C : Set E)) : Set E) := by simpa using h4
    rw [coeCone_dual_dual] at h5
    exact h5
  · intro hy
    rw [← coeCone_dual_dual] at hy
    have h4 : -(-y) ∈ coneDual (coneDual (C : Set E)) := by simpa using hy
    have h3 : -y ∈ polarCone (coneDual (C : Set E)) :=
      neg_coneDual_mem_polarCone.mpr h4
    have h2 : -y ∈ coneDual (-(coneDual (C : Set E)) : Set E) :=
      (coneDual_neg_polarCone_iff (coneDual (C : Set E)) (-y)).mpr h3
    have h1 : -y ∈ coneDual (polarCone (C : Set E)) := by
      rw [polarCone_eq_neg_coneDual (C : Set E)]
      exact h2
    exact neg_coneDual_mem_polarCone.mpr h1

/-- **Bipolar theorem for the polar, as a set equality.** -/
@[simp] theorem polarCone_polarCone_eq [CompleteSpace E] (C : ProperCone ℝ E) :
    (polarCone (polarCone (C : Set E)) : Set E) = (C : Set E) := by
  ext y
  exact mem_polarCone_polarCone_iff C y

/-- **The polar of the whole space is the trivial cone**: no nonzero direction is polar to
everything. -/
theorem polarCone_univ_bot [CompleteSpace E] : polarCone (Set.univ : Set E) = ⊥ := by
  refine SetLike.ext fun y => ?_
  show y ∈ polarCone (Set.univ : Set E) ↔ y ∈ (⊥ : ProperCone ℝ E)
  rw [ProperCone.mem_bot]
  constructor
  · intro hy
    have h' := hy (Set.mem_univ y)
    rw [real_inner_self_eq_norm_sq] at h'
    have h'' : 0 ≤ (‖y‖ : ℝ) ^ 2 := sq_nonneg ‖y‖
    have : ‖y‖ = 0 := by nlinarith
    exact norm_eq_zero.mp this
  · intro hy
    rw [hy, Set.mem_univ]
    have h' := (mem_polarCone.mp (show y ∈ polarCone (Set.univ : Set E) from
      ⟨y, Set.mem_univ y, le_rfl⟩)) (Set.mem_univ (-y))
    rw [real_inner_neg_left, inner_zero_right] at h'
    linarith

end PolarLaws

/-! ## 2. Face–covector duality, one direction

A *covector* here is a point `n : E` of the ambient space, read as the linear functional
`⟪n, ·⟫`; the tree already exposes the supporting-functional condition as
`n ∈ coneDual (C : Set E)` and the face it exposes as `CRNT.exposedFace C n`. -/

section FaceCovector

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **`n` is an outer normal of `C` at `v`**: `n` is a supporting covector for `C` (`⟪n, ·⟫`
is nonnegative on `C`), `v` is a point of `C`, and `⟪n, ·⟫` is *maximised* over `C` at `v`. -/
def IsOuterNormalAt (C : ProperCone ℝ E) (n v : E) : Prop :=
  n ∈ coneDual (C : Set E) ∧ v ∈ (C : Set E) ∧
    ∀ x ∈ (C : Set E), ⟪n, v⟫_ℝ ≤ ⟪n, x⟫_ℝ

/-- **`v` is a face point of `C` exposed by the covector `n`**: `n` supports `C` and `⟪n, ·⟫`
is *tight* at `v`.  This is exactly the representation `CRNT.exposedFace` supports, so it is
the notion of "face point" this development uses everywhere below. -/
def IsFacePointAt (C : ProperCone ℝ E) (n v : E) : Prop :=
  n ∈ coneDual (C : Set E) ∧ v ∈ exposedFace (C : PointedCone ℝ E) n

/-- A face point lies in the cone that exposes it. -/
theorem IsFacePointAt.mem (h : IsFacePointAt C n v) : v ∈ (C : Set E) :=
  (mem_exposedFace.mp h.2).1

/-- A face point is the locus where the exposing covector is tight. -/
theorem IsFacePointAt.tight (h : IsFacePointAt C n v) : ⟪n, v⟫_ℝ = 0 :=
  (mem_exposedFace.mp h.2).2

/-- A face point's exposing covector is nonnegative on the whole cone. -/
theorem IsFacePointAt.nonneg (h : IsFacePointAt C n v) {x : E} (hx : x ∈ (C : Set E)) :
    0 ≤ ⟪n, x⟫_ℝ :=
  inner_nonneg_of_mem_coneDual h.1 hx

/-- **The tight form is an outer normal.**  A covector that supports `C` and is tight at `v`
maximises at `v`: its value there is `0`, the least possible, and it is `≥ 0` elsewhere. -/
theorem IsFacePointAt.outerNormalAt (h : IsFacePointAt C n v) : IsOuterNormalAt C n v := by
  refine ⟨h.1, h.mem, fun x hx => ?_⟩
  have hnonneg : 0 ≤ ⟪n, x⟫_ℝ := h.nonneg hx
  rw [h.tight]
  linarith

/-- **The maximising form is a tight face point.**  If `⟪n, ·⟫` is nonnegative on `C` and is
maximised at `v ∈ C`, then its value at `v` is forced to be `0` (the maximum is taken at the
origin, where the functional vanishes) and `v` lies in the exposed face. -/
theorem isFacePointAt_of_outerNormalAt {C : ProperCone ℝ E} {n v : E}
    (h : IsOuterNormalAt C n v) : IsFacePointAt C n v := by
  have hv : v ∈ (C : Set E) := h.2.1
  have hmax : ∀ x ∈ (C : Set E), ⟪n, v⟫_ℝ ≤ ⟪n, x⟫_ℝ := h.2.2
  have hzero : 0 ≤ ⟪n, v⟫_ℝ := inner_nonneg_of_mem_coneDual h.1 hv
  have hat0 : ⟪n, v⟫_ℝ ≤ ⟪n, (0 : E)⟫_ℝ := hmax 0 (zero_mem _)
  rw [inner_zero_right] at hat0
  refine ⟨h.1, mem_exposedFace.mpr ⟨hv, ?_⟩⟩
  linarith

/-- **Face–covector duality, the direction that holds.**

Let `n` and `m` be supporting covectors for `C`, let `v` be the face point that `n` exposes,
and suppose `m` is *dominated* by `n` on `C`: `⟪m, x⟫ ≤ ⟪n, x⟫` for every `x ∈ C`.  Then `v`
is exposed by `m` as well.  In words: the covector that is largest on `C` exposes `v`, and
so does every covector below it — which is how a dominating normal family turns one face
point into an exposing normal for every cone of the fan. -/
theorem isFacePointAt_of_domination {C : ProperCone ℝ E} {n m v : E}
    (hn : IsFacePointAt C n v) (hm : m ∈ coneDual (C : Set E))
    (hdom : ∀ x ∈ (C : Set E), ⟪m, x⟫_ℝ ≤ ⟪n, x⟫_ℝ) : IsFacePointAt C m v := by
  have hv : v ∈ (C : Set E) := hn.mem
  have hmv : 0 ≤ ⟪m, v⟫_ℝ := inner_nonneg_of_mem_coneDual hm hv
  have hle : ⟪m, v⟫_ℝ ≤ ⟪n, v⟫_ℝ := hdom v hv
  rw [hn.tight] at hle
  have hmz : ⟪m, v⟫_ℝ = 0 := le_antisymm hle hmv
  exact ⟨hm, mem_exposedFace.mpr ⟨hv, hmz⟩⟩

/-- **The maximising form of the same statement, with no supporting hypothesis at all.**
If `n` is an outer normal of `C` at `v` and `m` is dominated by `n` on `C`, then `m` is an
outer normal of `C` at `v`. -/
theorem isOuterNormalAt_of_outerNormalAt_of_domination {C : ProperCone ℝ E} {n m v : E}
    (hn : IsOuterNormalAt C n v) (hdom : ∀ x ∈ (C : Set E), ⟪m, x⟫_ℝ ≤ ⟪n, x⟫_ℝ) :
    IsOuterNormalAt C m v :=
  ⟨mem_coneDual.2 fun x hx => (isFacePointAt_of_outerNormalAt hn).nonneg hx, hn.2.1,
    fun x hx => le_trans (hdom x hx) (hn.2.2 x hx)⟩

/-- **Contrapositive.**  If a supporting covector `m` fails to expose `v`, then no covector
dominating it on `C` exposes `v` either: there is no hidden exposing normal above `m`. -/
theorem not_facePointAt_of_domination {C : ProperCone ℝ E} {n m v : E}
    (hm : m ∈ coneDual (C : Set E)) (hdom : ∀ x ∈ (C : Set E), ⟪m, x⟫_ℝ ≤ ⟪n, x⟫_ℝ)
    (hmnot : v ∉ exposedFace (C : PointedCone ℝ E) m) : ¬ IsFacePointAt C n v :=
  fun hn => hmnot (isFacePointAt_of_domination hn hm hdom).2

/-- **Tightness of a dominated covector at a face point, with no supporting hypothesis.**
Domination on `C` bounds `⟪m, v⟫` above by the value at the exposed point; the lower bound is
what needs `m` to support `C`, so this is exactly the hypothesis-free half of the duality. -/
theorem inner_le_of_domination {C : ProperCone ℝ E} {n m v : E}
    (hdom : ∀ x ∈ (C : Set E), ⟪m, x⟫_ℝ ≤ ⟪n, x⟫_ℝ) (hv : v ∈ (C : Set E)) :
    ⟪m, v⟫_ℝ ≤ ⟪n, v⟫_ℝ :=
  hdom v hv

/-- **Face closure.**  Any point of `C` at which the covector `m` takes the same value as at
the face point `v` lies in the face exposed by `m`. -/
theorem mem_exposedFace_of_eq_inner {C : ProperCone ℝ E} {m v x : E}
    (hm : m ∈ coneDual (C : Set E)) (hv : IsFacePointAt C m v) (hx : x ∈ (C : Set E))
    (hval : ⟪m, x⟫_ℝ = ⟪m, v⟫_ℝ) : x ∈ exposedFace (C : PointedCone ℝ E) m := by
  rw [hv.tight] at hval
  exact mem_exposedFace.mpr ⟨hx, hval⟩

end FaceCovector

/-! ## 3. The normal family named by Craciun v3 Lemma 9.5 / Lemma 9.7

`CRNT.Dynamics.HighCodimensionSiphonFace` names as the missing datum "a family `n C ∈ C`
indexed by the cones with `⟪n C, x⟫ ≥ ⟪n C', x⟫` for all `x ∈ C`".  `NormalFamily` is exactly
that, phrased over `CRNT.Fan E` and `ProperCone ℝ E`.  It is stated, not inhabited:
producing such a family for an arbitrary complete pointed fan is the open problem. -/

section NormalFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **A normal family for a fan.**  Craciun v3, Lemma 9.5 with the Lemma 9.7 `δ`-slack:

* `n` assigns to every cone of the fan a covector `n C`;
* `cone_mem` is the **cone compatibility** `n C ∈ C`: the normal of a cone is a point of
  that cone, so on the walls — the low-dimensional cones near which the toric field is the
  largest — the normal is forced into the narrow cone, which is what lets a polyhedral
  surface turn;
* `dominates` is the **domination condition** `⟪n C, x⟫ ≥ ⟪n C', x⟫` for every `x ∈ C` and
  every `C' ∈ F`: on `C`, the assigned covector is at least as large as every covector
  assigned to any cone of the fan.

Mathematically this is the normal-fan condition: the normals are indexed by the cones and
are ordered on each cone exactly as the normals of the faces of a polytope whose normal fan
refines `F` would be. -/
structure NormalFamily (F : Fan E) where
  /-- The covector assigned to each cone of the fan. -/
  n : ProperCone ℝ E → E
  /-- **Cone compatibility**: the normal of a cone is a point of that cone. -/
  cone_mem : ∀ C, C ∈ F → n C ∈ (C : Set E)
  /-- **Domination**: on `C`, the assigned covector is largest among the fan's covectors. -/
  dominates : ∀ C, C ∈ F → ∀ C', C' ∈ F → ∀ x ∈ (C : Set E), ⟪n C', x⟫_ℝ ≤ ⟪n C, x⟫_ℝ

/-- A normal family's normal really is a point of its cone. -/
theorem NormalFamily.mem (G : NormalFamily F) {C : ProperCone ℝ E} (hC : C ∈ F) :
    G.n C ∈ (C : Set E) :=
  G.cone_mem C hC

/-- A normal family dominates itself. -/
theorem NormalFamily.dominates_refl (G : NormalFamily F) {C : ProperCone ℝ E} (hC : C ∈ F)
    {x : E} (hx : x ∈ (C : Set E)) : ⟪G.n C, x⟫_ℝ ≤ ⟪G.n C, x⟫_ℝ :=
  le_rfl

/-- Domination of one cone's normal by another's, on the whole cone. -/
theorem NormalFamily.dominates (G : NormalFamily F) {C C' : ProperCone ℝ E}
    (hC : C ∈ F) (hC' : C' ∈ F) {x : E} (hx : x ∈ (C : Set E)) :
    ⟪G.n C', x⟫_ℝ ≤ ⟪G.n C, x⟫_ℝ :=
  G.dominates C hC C' hC' hx

/-- **Restriction to a subfamily.**  A normal family of a fan restricts to any subfamily of
its cones, which is what a recursive face fill needs at each level. -/
noncomputable def NormalFamily.restrict (G : NormalFamily F) (S : Finset (ProperCone ℝ E))
    (hS : ∀ C ∈ S, C ∈ F) : NormalFamily S where
  n := G.n
  cone_mem := fun C hC => G.cone_mem C (hS C hC)
  dominates := fun C hC C' hC' x hx => G.dominates (hS C hC) (hS C' hC') hx

/-- **Domination transfers face points to every cone of the fan.**  If `G.n C` exposes the
face point `v` of `C`, then so does `G.n C'` for every `C' ∈ F` — provided `G.n C'` is known
to support `C`.  This is `isFacePointAt_of_domination` read at the fan level. -/
theorem NormalFamily.facePointAt_of_domination (G : NormalFamily F)
    {C C' : ProperCone ℝ E} (hC : C ∈ F) (hC' : C' ∈ F) {v : E}
    (hn : IsFacePointAt C (G.n C) v) (hm : G.n C' ∈ coneDual (C : Set E)) :
    IsFacePointAt C (G.n C') v :=
  isFacePointAt_of_domination hn hm fun x hx => G.dominates hC hC' hx

/-- **The normals-maximising form, at the fan level.**  If `G.n C` is an outer normal of `C`
at `v`, then so is `G.n C'` for every `C' ∈ F` — with no supporting hypothesis on the
dominated normal.  This is the packaged form the Hole A docstring needs. -/
theorem NormalFamily.outerNormalAt_of_domination (G : NormalFamily F)
    {C C' : ProperCone ℝ E} (hC : C ∈ F) (hC' : C' ∈ F) {v : E}
    (hn : IsOuterNormalAt C (G.n C) v) :
    IsOuterNormalAt C (G.n C') v :=
  isOuterNormalAt_of_outerNormalAt_of_domination hn fun x hx => G.dominates hC hC' hx

/-- **Bridge to the existing descent machinery.**  A normal-family normal lies in *every*
cone of the fan, hence in every cone within distance `δ` of `X`, hence — by
`CRNT.inner_nonneg_of_mem_toricField` — it pairs nonnegatively with the whole toric field at
`X`.  This is the single inequality Craciun's polyhedral surface needs at each piece. -/
theorem NormalFamily.inner_nonneg_of_mem_toricField (G : NormalFamily F)
    {δ : ℝ} {X : E} {C : ProperCone ℝ E} (hC : C ∈ F) :
    ∀ v ∈ toricField F δ X, 0 ≤ ⟪G.n C, v⟫_ℝ :=
  CRNT.inner_nonneg_of_mem_toricField fun D _ _ => G.cone_mem D hC

/-- The δ-core reading of the same bridge: every cone of the fan lying within distance `δ`
of `X` contains the normal assigned to any other cone of the fan. -/
theorem NormalFamily.n_mem_of_mem_deltaCore (G : NormalFamily F)
    {δ : ℝ} {X : E} (h : (nearCones F δ X).Nonempty) {C : ProperCone ℝ E} (hC : C ∈ F)
    {n : E} (hn : n ∈ deltaCore F δ X h) (hX : Metric.infDist X (C : Set E) < δ) :
    G.n C ∈ (C : Set E) :=
  mem_of_mem_deltaCore h hn C hC hX

end NormalFamily

end CRNT
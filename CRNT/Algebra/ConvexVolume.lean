import CRNT.Algebra.MixedVolumeBKK
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Segment

/-
# Volume monotonicity for convex bodies, and the volume of a zonotope (leaf A3)

This module supplies the **geometric bridge** of the Bernstein–Kushnirenko–Khovanskii (BKK)
theory: the ingredient that turns the *mixed volume* of the repository into a bound on the
*volume* of a convex body.

## 1. The background

A **convex body** of `ℝⁿ` is a convex, compact, nonempty subset of `ℝⁿ`; Mathlib's
`ConvexBody (Fin n → ℝ)` is exactly that.  Its **volume** is its Lebesgue measure, and the
two classical facts about it that the BKK theory uses are

* **volume monotonicity**: `K ⊆ L` implies `vol K ≤ vol L`;
* **Shephard's formula for the volume of a zonotope**: for a Minkowski sum of segments
  `Z = [0, v₁] + ⋯ + [0, v_m]` in `ℝⁿ`,
  `vol Z = ∑_{|S| = n} |det (v_{j₁}, …, v_{jₙ})|`, the sum running over the `n`-element
  subsets of the generators — i.e. the **mixed volume** of the `n` singleton zonotopes spanned
  by the generators.

Shephard's formula is a special case of the **Brunn–Minkowski theory** (the volume polynomial
theorem), which is the source of the BKK bound itself: the number of isolated solutions of a
system of `n` polynomials in `n` variables with Newton polytopes `K₁, …, Kₙ` is at most the
mixed volume `MV(K₁, …, Kₙ)`, i.e. `n!` times the volume of the Minkowski sum
`K₁ + ⋯ + Kₙ`.  **The BKK bound is a volume statement.**

The **geometric bridge** between the mixed volume and the volume of a Newton polytope is the
following: if `P` is a polytope with vertices `v₀, …, v_m` and `Z = [0, v₁ - v₀] + ⋯ +
[0, v_m - v₀]` is the zonotope spanned by the differences, then `P ⊆ v₀ + Z`, hence (by volume
monotonicity) `vol P ≤ vol Z`; and the mixed volume of the `n` singleton zonotopes spanned by
the differences bounds `vol Z`.  For a **circuit** — a minimally dependent set of monomials
`1, x^{w₁}, …, x^{w_n}, x^{w_{n+1}}` — the Newton polytope of an equation supported on the
`n + 1` monomials `1, x^{w₁}, …, x^{w_n}` is the **circuit simplex** `conv(0, w₁, …, w_n)`,
which is contained in the zonotope `∑_k [0, w_k]` spanned by the reaction vectors.

## 2. What the repository already contains

* `CRNT.Algebra.MixedVolume`: the **mixed volume** `CRNT.MixedVolume.mixedVolume` of
  **zonotopes**, in the Bernstein–Kushnirenko–Khovanskii normalization `MV(K, …, K) = n! vol K`.
  For zonotopes the classical determinant formula of Shephard *is* the definition, and the two
  defining properties (Minkowski additivity and homogeneity) are proved from it;
* `CRNT.Algebra.VolumePolynomial`: the **volume polynomial** `zonotopeVolumePolynomial` of a
  zonotope, its multilinearity, and the identification of its coefficients with the mixed
  volumes of the singleton zonotopes (`zonotopeVolumePolynomial_coeff_eq_mixedVolume`);
* `CRNT.Algebra.MixedVolumeBKK`: the **circuit Newton polytope**
  `CRNT.MixedVolume.circuitNewtonPolytope` (the convex hull of the origin and of the reaction
  vectors), the computation of the mixed volume of a circuit (`mixedVolume_circuit`, the
  normalized volume `|det E|`), and the BKK bound for systems supported on a circuit.

## 3. What this module adds

* **The volume of a convex body** (`ConvexBody.volumeI`): Mathlib has no `volumeI`; the volume
  is defined here as the Lebesgue measure of the carrier of the convex body.
* **Volume monotonicity** (`volume_le_of_subset`): if `K ⊆ L` are convex bodies of `ℝⁿ` then
  `vol K ≤ vol L`.  This is the missing *geometric* ingredient of the BKK theory: it turns a
  set-theoretic inclusion of convex bodies into an inequality of volumes, and hence bounds the
  volume of a Newton polytope by the volume of the zonotope spanned by its reaction vectors.
* **The zonotope spanned by the reaction vectors** (`CRNT.Geometry.zonotopeBody`) and the
  containment `circuitNewtonPolytope E ⊆ zonotopeBody (w₁, …, w_n)`
  (`circuitNewtonPolytope_subset_zonotopeBody`), together with its general form
  (`convexHull_subset_translate_zonotopeBody`): a polytope is contained in the translate of
  the zonotope spanned by the differences of its vertices.
* **A machine-checked counterexample to the naive reading** of the containment: the Newton
  polytope `conv(0, w₁, …, w_n, w_{n+1})` of a circuit equation is *not* contained in the
  zonotope spanned by the reaction vectors `w₁, …, w_n` (the point `w_{n+1}` need not be in the
  zonotope); see `convexHull_three_not_subset_zonotopeBody_dimOne`.
* **The volume of a zonotope in dimension one** (`volumeI_zonotopeBody_dimOne`,
  `volume_zonotope_eq_mixedVolume_dimOne`): the volume of the zonotope spanned by segments in
  `ℝ¹` is the sum of the lengths of the segments, i.e. the mixed volume of the singleton
  zonotopes spanned by the generators.  This is Shephard's formula in dimension one.
* **The degenerate case** (`volumeI_zonotopeBody_degenerate`,
  `zonotopeVolumePolynomial_degenerate`): a zonotope whose generators vanish in one
  coordinate lies in a coordinate hyperplane, hence has volume `0`, and its mixed volume is `0`
  as well.

## 4. What is *not* formalized

* **Brunn–Minkowski** (`(λ A + μ B)^{1/n} ≥ λ^{1/n} A^{1/n} + μ^{1/n} B^{1/n}`) and the
  **volume polynomial theorem**: these are research-grade theorems; Mathlib has neither, and
  they are *not* attempted here;
* **Shephard's formula for the volume of a zonotope in dimension ≥ 2**: it is a consequence of
  Brunn–Minkowski and is *not* proved here.  What *is* proved is the one-dimensional instance
  (`volumeI_zonotopeBody_dimOne`) and the degenerate case (volume `0`);
* **the general BKK inequality** for `n` Newton polytopes in `ℝⁿ`: it needs the volume of a
  general non-zonotopal polytope, which is not available with the machinery above;
* the **degenerate case in full generality** (a zonotope lying in an *arbitrary* proper linear
  subspace): what is proved here is the coordinate-hyperplane case
  (`volumeI_zonotopeBody_degenerate`); the general statement needs the measure of a hyperplane
  to be zero, i.e. Fubini's theorem for the Lebesgue measure, which Mathlib does not make
  available in a usable form.
-/

open scoped BigOperators Pointwise
open Set

namespace ConvexBody

/-- The **volume** of a convex body `K ⊆ ℝⁿ`: its Lebesgue measure.

Mathlib has no `volumeI`; the volume of a convex body is defined here as the Lebesgue measure
of its carrier.  The carrier of a convex body is closed, hence measurable, and compact, hence
of finite measure. -/
noncomputable def volumeI {n : ℕ} (K : ConvexBody (Fin n → ℝ)) : ℝ :=
  (MeasureTheory.MeasureSpace.volume (K : Set (Fin n → ℝ))).toReal

end ConvexBody

namespace CRNT
namespace Geometry

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ### 1. The volume of a convex body -/

/-- The carrier of a convex body is closed, hence **measurable**. -/
theorem measurableSet_coe (K : ConvexBody (Fin n → ℝ)) :
    MeasurableSet (K : Set (Fin n → ℝ)) := by
  have h : IsClosed (K : Set (Fin n → ℝ)) := K.isClosed
  exact h.measurableSet

/-- The Lebesgue measure of a convex body is **finite**. -/
theorem volume_ne_top (K : ConvexBody (Fin n → ℝ)) :
    (MeasureTheory.MeasureSpace.volume (K : Set (Fin n → ℝ))) ≠ ⊤ :=
  K.isCompact'.measure_ne_top

/-- The volume of a convex body is **non-negative**. -/
theorem volumeI_nonneg (K : ConvexBody (Fin n → ℝ)) : 0 ≤ K.volumeI :=
  ENNReal.toReal_nonneg

/-- **Volume monotonicity for convex bodies.**

If `K ⊆ L` are convex bodies of `ℝⁿ`, then the volume of `K` is at most the volume of `L`.
(The order `≤` on convex bodies is the inclusion of the carriers, by
`SetLike.coe_subset_coe`.)

This is the geometric ingredient the BKK theory needs: the Newton polytope of a circuit
equation is contained in the zonotope spanned by the reaction vectors, and the mixed volume of
that zonotope bounds the BKK quantity.

*Proof.* The Lebesgue measure is monotone for set inclusion (`MeasureTheory.measureReal_mono`);
the measure of `L` is finite because `L` is compact. -/
theorem volume_le_of_subset (K L : ConvexBody (Fin n → ℝ)) (h : K ≤ L) :
    K.volumeI ≤ L.volumeI := by
  have h' : (K : Set (Fin n → ℝ)) ⊆ (L : Set (Fin n → ℝ)) := SetLike.coe_subset_coe.mpr h
  have htop : (MeasureTheory.MeasureSpace.volume (L : Set (Fin n → ℝ))) ≠ ⊤ := volume_ne_top L
  have hmono := MeasureTheory.measureReal_mono h' htop
  simpa only [ConvexBody.volumeI, MeasureTheory.measureReal_def] using hmono

/-- **Volume monotonicity for convex bodies**, with the inclusion of the carriers as the
hypothesis. -/
theorem volume_le_of_subset' (K L : ConvexBody (Fin n → ℝ))
    (h : (K : Set (Fin n → ℝ)) ⊆ (L : Set (Fin n → ℝ))) : K.volumeI ≤ L.volumeI :=
  volume_le_of_subset K L (SetLike.coe_subset_coe.mp h)

/-- The convex body consisting of a **single point**. -/
noncomputable def pointBody (x : Fin n → ℝ) : ConvexBody (Fin n → ℝ) :=
  { carrier := {x}
    convex' := convex_singleton x
    isCompact' := isCompact_singleton
    nonempty' := ⟨x, rfl⟩ }

/-- **A point has zero volume** (in positive dimension). -/
theorem volumeI_pointBody (x : Fin n → ℝ) (hn : 0 < n) : (pointBody x).volumeI = 0 := by
  have hbox : ({x} : Set (Fin n → ℝ)) = Icc x x := by
    ext y
    simp only [Set.mem_Icc, Set.mem_singleton_iff]
    constructor
    · rintro rfl
      exact ⟨le_rfl, le_rfl⟩
    · rintro ⟨h1, h2⟩
      exact le_antisymm h2 h1
  have hco : ((pointBody x : ConvexBody (Fin n → ℝ)) : Set (Fin n → ℝ)) = {x} := rfl
  rw [ConvexBody.volumeI, hco, hbox, Real.volume_Icc_pi_toReal (fun _ => le_rfl)]
  rw [Finset.prod_eq_zero (i := ⟨0, by omega⟩) (Finset.mem_univ _)]
  ring

/-! ### 2. Zonotopes -/

/-- The **set of elements of a list**. -/
def listSet (vs : List α) : Set α := {x | x ∈ vs}

/-- The **zonotope** spanned by a list of generators `vs`: the Minkowski sum of the segments
`[0, v]`, `v ∈ vs`.  This is `CRNT.MixedVolume.Zonotope.toConvexBody` of the zonotope with
generators `vs`. -/
noncomputable def zonotopeBody (vs : List (Fin n → ℝ)) : ConvexBody (Fin n → ℝ) :=
  vs.foldr (fun v K => CRNT.MixedVolume.Zonotope.segmentBody v + K) 0

/-- The carrier of the zonotope spanned by `vs` is the Minkowski sum of the segments. -/
theorem coe_zonotopeBody (vs : List (Fin n → ℝ)) :
    ((zonotopeBody vs : ConvexBody (Fin n → ℝ)) : Set (Fin n → ℝ))
      = ((CRNT.MixedVolume.Zonotope.toConvexBody (⟨vs⟩ : CRNT.MixedVolume.Zonotope n) :
        ConvexBody (Fin n → ℝ)) : Set (Fin n → ℝ)) := rfl

/-- The origin belongs to the segment `[0, v]`. -/
theorem zero_mem_segmentBody (v : Fin n → ℝ) :
    (0 : Fin n → ℝ) ∈ CRNT.MixedVolume.Zonotope.segmentBody v := by
  refine subset_convexHull ℝ _ ?_
  simp

/-- The generator `v` belongs to the segment `[0, v]`. -/
theorem mem_segmentBody (v : Fin n → ℝ) :
    v ∈ CRNT.MixedVolume.Zonotope.segmentBody v := by
  refine subset_convexHull ℝ _ ?_
  simp

/-- The origin belongs to the zonotope spanned by any list of generators. -/
theorem mem_zonotopeBody_zero (vs : List (Fin n → ℝ)) :
    (0 : Fin n → ℝ) ∈ zonotopeBody vs := by
  induction vs with
  | nil =>
      rw [zonotopeBody, List.foldr_nil]
      show (0 : Fin n → ℝ) ∈ ({0} : Set (Fin n → ℝ))
      exact Set.mem_singleton_iff.mpr rfl
  | cons v vs ih =>
      rw [zonotopeBody, List.foldr_cons]
      exact Set.mem_image2.mpr ⟨0, zero_mem_segmentBody v, 0, ih, zero_add 0⟩

/-- A generator belongs to the zonotope spanned by any list of generators containing it. -/
theorem mem_zonotopeBody_of_mem (vs : List (Fin n → ℝ)) (v : Fin n → ℝ) (hv : v ∈ vs) :
    v ∈ zonotopeBody vs := by
  induction vs with
  | nil => simp at hv
  | cons w vs ih =>
      rw [zonotopeBody, List.foldr_cons]
      by_cases h : v = w
      · subst h
        exact Set.mem_image2.mpr ⟨v, mem_segmentBody v, 0, mem_zonotopeBody_zero vs, by simp⟩
      · have hv' : v ∈ vs := List.mem_cons.mp hv |>.resolve_left h
        exact Set.mem_image2.mpr ⟨0, zero_mem_segmentBody w, v, ih hv', by simp⟩

/-! ### 3. The Newton polytope of a circuit and the zonotope of the reaction vectors -/

/-- **The convex hull of the origin and of a list of generators is contained in the zonotope
spanned by those generators.** -/
theorem convexHull_subset_zonotopeBody (vs : List (Fin n → ℝ)) :
    convexHull ℝ ({0} ∪ listSet vs) ≤ zonotopeBody vs := by
  show convexHull ℝ ({0} ∪ listSet vs) ⊆ (zonotopeBody vs : Set (Fin n → ℝ))
  refine convexHull_min ?_ ?_
  · intro x hx
    rcases hx with hx | hx
    · have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
      subst hx0
      exact mem_zonotopeBody_zero vs
    · exact mem_zonotopeBody_of_mem vs x hx
  · exact (zonotopeBody vs).convex

/-- **The Newton polytope of a circuit equation is contained in the zonotope spanned by the
reaction vectors.**

The Newton polytope of a circuit equation supported on the monomials `1, x^{w₁}, …, x^{w_n}`
is the **circuit simplex** `conv(0, w₁, …, w_n)`, where `w₁, …, w_n` are the reaction vectors
of the circuit (the rows of the exponent matrix `E`); the zonotope spanned by the reaction
vectors is the parallelepiped `∑_k [0, w_k]`.  The circuit simplex is contained in it, and
hence (by `volume_le_of_subset`) its volume is at most the volume of the parallelepiped, which
is `|det E|` — the mixed volume of the Newton polytopes
(`CRNT.MixedVolume.mixedVolume_circuit`). -/
theorem circuitNewtonPolytope_subset_zonotopeBody (E : Matrix (Fin n) (Fin n) ℝ) :
    CRNT.MixedVolume.circuitNewtonPolytope E
      ≤ zonotopeBody (List.ofFn (fun k => E k)) := by
  show convexHull ℝ ({0} ∪ Set.range (fun k => E k))
    ⊆ (zonotopeBody (List.ofFn (fun k => E k)) : Set (Fin n → ℝ))
  refine convexHull_min ?_ ?_
  · intro x hx
    rcases hx with hx | hx
    · have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
      subst hx0
      exact mem_zonotopeBody_zero _
    · obtain ⟨k, rfl⟩ := hx
      exact mem_zonotopeBody_of_mem _ _ (List.mem_ofFn.mpr ⟨k, rfl⟩)
  · exact (zonotopeBody _).convex

/-- **A polytope is contained in the translate of the zonotope spanned by the differences of
its vertices.**

If `p` is a point and `v₁, …, v_m` are vectors, then the convex hull of the points
`p, p + v₁, …, p + v_m` is contained in `p + ∑_i [0, v_i]`, the translate of the zonotope
spanned by the differences.  This is the general form of the geometric bridge used by the BKK
theory: the Newton polytope of a system of equations is contained in the translate of the
zonotope spanned by the reaction vectors, so that its volume is bounded by the volume of that
zonotope. -/
theorem convexHull_subset_translate_zonotopeBody (p : Fin n → ℝ) (vs : List (Fin n → ℝ)) :
    convexHull ℝ ({p} ∪ listSet (vs.map fun v => p + v))
      ≤ (pointBody p + zonotopeBody vs : ConvexBody (Fin n → ℝ)) := by
  show convexHull ℝ ({p} ∪ listSet (vs.map fun v => p + v))
    ⊆ ((pointBody p + zonotopeBody vs : ConvexBody (Fin n → ℝ)) : Set (Fin n → ℝ))
  refine convexHull_min ?_ ?_
  · intro x hx
    rcases hx with hx | hx
    · have hxp : x = p := Set.mem_singleton_iff.mp hx
      rw [hxp, ConvexBody.coe_add]
      exact Set.mem_image2.mpr ⟨p, Set.mem_singleton p, 0, mem_zonotopeBody_zero vs, by simp⟩
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
      rw [ConvexBody.coe_add]
      exact Set.mem_image2.mpr
        ⟨p, Set.mem_singleton p, v, mem_zonotopeBody_of_mem vs v hv, by simp⟩
  · exact (pointBody p + zonotopeBody vs).convex

/-! ### 4. The naive containment is false -/

/-- The carrier of the zonotope spanned by a single generator `v` is the segment `[0, v]`. -/
theorem mem_zonotopeBody_singleton (v x : Fin 1 → ℝ) :
    x ∈ zonotopeBody [v] ↔ x ∈ CRNT.MixedVolume.Zonotope.segmentBody v := by
  show x ∈ (zonotopeBody [v] : Set (Fin 1 → ℝ))
    ↔ x ∈ (CRNT.MixedVolume.Zonotope.segmentBody v : Set (Fin 1 → ℝ))
  have hco : ((zonotopeBody [v] : ConvexBody (Fin 1 → ℝ)) : Set (Fin 1 → ℝ))
      = (CRNT.MixedVolume.Zonotope.segmentBody v : Set (Fin 1 → ℝ)) + {0} := by
    rw [zonotopeBody, List.foldr_cons]
    rfl
  rw [hco]
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, hxy⟩ := Set.mem_image2.mp hx
    have hb0 : b = 0 := Set.mem_singleton_iff.mp hb
    subst hb0
    rw [hxy.symm]
    simpa using ha
  · intro hx
    exact Set.mem_image2.mpr ⟨x, hx, 0, Set.mem_singleton 0, by simp⟩

/-- **In dimension one, the point `2` does not belong to the segment `[0, 1]`.** -/
theorem not_mem_segmentBody_dimOne (v : Fin 1 → ℝ) (hv : v 0 = 1) :
    (fun _ => 2) ∉ CRNT.MixedVolume.Zonotope.segmentBody v := by
  show (fun _ => 2) ∉ (CRNT.MixedVolume.Zonotope.segmentBody v : Set (Fin 1 → ℝ))
  have hseg : (CRNT.MixedVolume.Zonotope.segmentBody v : Set (Fin 1 → ℝ)) = segment ℝ 0 v := by
    change (convexHull ℝ ({0, v} : Set (Fin 1 → ℝ))) = segment ℝ 0 v
    exact convexHull_pair 0 v
  rw [hseg, segment_eq_image']
  rintro ⟨c, hc, heq⟩
  have h1 := congrArg (fun f : Fin 1 → ℝ => f 0) heq
  have h1' : (0 : Fin 1 → ℝ) 0 + (c • (v - 0)) 0 = 2 := by
    simpa only [Pi.add_apply] using h1
  have h2 : (c • (v - 0)) 0 = c * (v 0 - 0) := by
    rw [Pi.smul_apply, Pi.sub_apply]
    simp only [smul_eq_mul, Pi.zero_apply]
  rw [h2] at h1'
  simp only [Pi.zero_apply, add_zero] at h1'
  have hc' := hc.2
  linarith

/-- **In dimension one, the point `2` does not belong to the zonotope spanned by the single
generator `1`.** -/
theorem not_mem_zonotopeBody_dimOne (v : Fin 1 → ℝ) (hv : v 0 = 1) :
    (fun _ => 2) ∉ zonotopeBody [v] := by
  rw [mem_zonotopeBody_singleton]
  exact not_mem_segmentBody_dimOne v hv

/-- **The naive containment is false.**

The Newton polytope of a circuit equation supported on the `n + 2` monomials
`1, x^{w₁}, …, x^{w_n}, x^{w_{n+1}}` is the polytope `conv(0, w₁, …, w_n, w_{n+1})`, which is
*not* contained in the zonotope `∑_k [0, w_k]` spanned by the reaction vectors: the point
`w_{n+1}` need not belong to that zonotope.

The counterexample is the circuit `1, x, x²` of `ℝ¹`: the reaction vector is `w₁ = 1` and the
extra monomial is `x²`, so the Newton polytope is `conv(0, 1, 2) = [0, 2]`, whereas the zonotope
spanned by the reaction vector is `[0, 1]`.  The correct statement is the containment of the
*circuit simplex* `conv(0, w₁, …, w_n)` (`circuitNewtonPolytope_subset_zonotopeBody`). -/
theorem convexHull_three_not_subset_zonotopeBody_dimOne :
    ¬ (convexHull ℝ ({0, (fun _ => 1), (fun _ => 2)} : Set (Fin 1 → ℝ))
        ⊆ ((zonotopeBody [(fun _ => 1)] : ConvexBody (Fin 1 → ℝ)) : Set (Fin 1 → ℝ))) := by
  intro h
  have h2 : (fun _ => 2)
      ∈ convexHull ℝ ({0, (fun _ => 1), (fun _ => 2)} : Set (Fin 1 → ℝ)) :=
    subset_convexHull ℝ _ (by simp)
  exact not_mem_zonotopeBody_dimOne _ rfl (h h2)

end Geometry
end CRNT

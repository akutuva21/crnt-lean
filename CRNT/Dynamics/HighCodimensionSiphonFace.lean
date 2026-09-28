import CRNT.Dynamics.FaceCodimension
import CRNT.Dynamics.SiphonDimensionDescent
import CRNT.Dynamics.ToricBarrierTrapping
import CRNT.Equilibria.ComplexBalanced

/-!
# The single remaining obligation of the Global Attractor Theorem

`CRNT.Dynamics.GlobalAttractorTheorem` reduces `Network.complexBalanced_genuinePermanent` to
one case, and this module is the only place in the tree where that case is left open.  The
theorem below is the **entire** residual content; everything else in the chain audits as
`[propext, Classical.choice, Quot.sound]`.

## What has been carved away

Let `Ω` be the ω-limit set of a bounded genuine positive mass-action trajectory of a
complex-balanced system, and suppose `Ω` meets the boundary.  The dichotomy
`positiveOmega_or_nonstationary_criticalSiphonFaceEquilibrium` produces a boundary point whose
zero set is a critical siphon, and `exists_maximal_zeroSet_omegaPoint` upgrades it to a point
`wmax ∈ Ω` whose zero set `Pmax` is *maximal*: every ω-point vanishing on `Pmax` vanishes
exactly on `Pmax`, no ω-point has a zero set of larger cardinality, i.e. `wmax` sits in the
relative interior of the `Pmax`-face.  Four cases
are then already closed in the tree:

* no critical siphon at all (`boundaryOmegaExcluded_of_hasNoCriticalSiphon`);
* `N.stoichSubspace = ⊥` (`positiveOmegaPointForRates_of_trivialStoichSubspace`);
* `N.stoichRank = 1` (`positiveOmegaPointForRates_of_complexBalanced_of_stoichRank_one`);
* the `Pmax`-face is a **facet** of the compatibility class, where the Anderson--Shiu
  near-facet estimate makes the squared face mass `∑_{s ∈ Pmax} x s ^ 2` nondecreasing and
  `no_omegaLimit_meets_locally_repelling_face` closes the case.

`CRNT.Dynamics.FaceCodimension` then shows the remaining failure of the facet count is never
degenerate: `highCodimension_of_not_facet` yields `2 ≤ finrank (stoichSubspace.map (projOn Pmax))`
and `2 ≤ Pmax.card`.  Those two inequalities are hypotheses below, so the obligation recorded
here is exactly the **codimension ≥ 2** case.

## Why the existing estimate cannot be pushed further

`facet_repelling_near_facet_point` needs every reaction vector restricted to `Pmax` to be a
multiple of one direction `v`, which is precisely
`finrank (stoichSubspace.map (projOn Pmax)) = 1`.  Under `hcodim` the restricted reaction
vectors span at least a plane, and the quadratic `∑_{s ∈ Pmax} x s ^ 2` is then genuinely not
monotone near `wmax`: writing `x s = ε u s` for `s ∈ Pmax`, the leading term of
`∑_{s ∈ Pmax} x s * f s x` is a quadratic form in the approach direction `u ≥ 0` whose sign
varies with `u` — already for a reversible pair inside the face with equal rate constants it is
a negative multiple of a square.  So no strengthening of the Anderson--Shiu argument covers this
branch; a surface whose normal turns with the direction of approach is required.

## The mathematical content that is missing

This is Craciun, *Toric differential inclusions and a proof of the global attractor conjecture*
(v3), Theorem B: a toric differential inclusion admits an exhaustive family of zero-separating
hypersurfaces.  In logarithmic coordinates the requirement (Lemma 9.5, and Lemma 9.7 with the
`δ`-slack) is a hypersurface whose outer normal at a point `X` lies in **every** cone of the fan
within distance `δ` of `X`, hence in low-dimensional cones near the walls.  A smooth surface
cannot satisfy this — the sphere meets the `δ = 0` condition of Lemma 9.5 and fails Lemma 9.7 —
so the surface must be polyhedral, with flat pieces of width at least `δ` around every cone,
arranged by the scale hierarchy of §7.

`CRNT.Geometry.PolyhedralBarrier` formalizes the invariance engine for such a surface:
for `g X = max i (⟪n i, X⟫ - b i)` the sublevel set `{g ≤ R}` is forward invariant for any
field lying in the polar cones of the active normals.  What is *not* formalized, and is the
remaining gap, is the existence of the data feeding that engine for an arbitrary complete
pointed fan: a family `n C ∈ C` indexed by the cones with `⟪n C, x⟫ ≥ ⟪n C', x⟫` for all
`x ∈ C`, together with the separation scales.  That family is a finite convex-geometry object —
equivalently the face points of a polytope whose normal fan refines the fan — and Mathlib
currently has no polytope, face-lattice, or normal-fan API to build it on.

## Trust status

`#print axioms CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace` reports
`sorryAx`, and so do exactly its downstream consumers
`Network.complexBalanced_genuinePermanent`, `Network.complexBalanced_permanent`, and
`Network.complexBalanced_globalAttractor`.  No other declaration in the tree does.

Depends on: `CRNT.Dynamics.FaceCodimension`, `CRNT.Dynamics.SiphonDimensionDescent`,
`CRNT.Dynamics.ToricBarrierTrapping`.
-/

open scoped NNReal Topology
open Filter

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Residual obligation: the ω-limit set cannot sit on a critical-siphon face of codimension
at least two.**

All hypotheses are exactly the data available at the corresponding point of
`Network.complexBalanced_genuinePermanent`:

* `hxs`, `hcb`: a positive complex-balanced equilibrium for the rates `κ`;
* `hϕγ`, `hsol`, `hK`, `hmaps`: a bounded genuine forward trajectory through the positive
  point `x₀`, presented as a cutoff semiflow;
* `hωnn`, `hgenω`, `hωaff`: the ω-limit set is nonnegative, consists of genuine orbits, and
  lies in the compatibility class of `x₀`;
* `hPmaxne`, `hwmax`, `hzeroMax`, `hmaxExact`, `hzcard`: `wmax` is an ω-point whose zero set is
  exactly the nonempty species set `Pmax`, and `Pmax` is maximal among zero sets of ω-points —
  no ω-point has a zero set of larger cardinality (`hzcard`), and every ω-point vanishing on
  `Pmax` vanishes exactly on `Pmax` (`hmaxExact`);
* `hcodim`, `hcard`: the `Pmax`-face has codimension at least two in the compatibility class
  and `Pmax` has at least two species — both supplied by
  `Network.highCodimension_of_not_facet`;
* `hrank`: the stoichiometric rank is not one.

The conclusion is the interior certificate `PositiveOmegaPointForRates` consumes. -/
theorem exists_positive_omegaPoint_of_highCodimension_siphonFace
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx₀ : x₀.Positive)
    {Pmax : Finset S} (hPmaxne : Pmax.Nonempty)
    {wmax : Concentration S} (hwmax : wmax ∈ omegaLimit atTop ϕ {x₀})
    (hzeroMax : ∀ s, s ∈ Pmax ↔ wmax s = 0)
    (hmaxExact : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (∀ s ∈ Pmax, z s = 0) →
      ∀ s, z s = 0 ↔ s ∈ Pmax)
    (hzcard : ∀ z ∈ omegaLimit atTop ϕ {x₀},
      (Finset.univ.filter (fun s => z s = 0)).card ≤ Pmax.card)
    (hcodim : 2 ≤ Module.finrank ℝ (N.stoichSubspace.map (projOn Pmax)))
    (hcard : 2 ≤ Pmax.card)
    (hrank : N.stoichRank ≠ 1) :
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive := by
  sorry

/-! ## Why the packaged barrier criteria cannot be instantiated inside this theorem

`docs/gac-bridge-gap-analysis.lean` derives the conclusion of the theorem above from the blueprint
data consumed by `Network.exists_positive_omegaPoint_of_blueprintData`, so the residue there is
purely geometric: the tiles, their normals and their levels.  The two lemmas below record the
obstruction found while trying to close that instantiation from this theorem's hypotheses: the
blueprint data *cannot* exist under them.

Every packaged criterion — `exists_positive_omegaPoint_of_convex_tiles`,
`exists_positive_omegaPoint_of_selfConsistent_normals`,
`exists_positive_omegaPoint_of_blueprintData` — demands a separation clause `hsep` bounding each
coordinate below by some `ε > 0` on **every** positive compatible point of the closed sublevel
`{barrier ≤ R}`.  Two facts collide there:

* `hstart` puts the start point `x₀` into the sublevel, and the trapping theorem
  `Network.barrier_le_of_toric_descent_in_band` (fed by the `hnear` clause assembled from `hm`,
  `hassign` and `hregime`) bounds the barrier by `R` along the whole orbit, so
  `barrier_le_of_mem_omegaLimit` puts the boundary ω-point `wmax` into the sublevel as well;
* every piece `innerSL ℝ (-m i)` of the barrier is affine, hence the sublevel is convex, so the
  segment from `x₀` to `wmax` stays inside it — and `hsep_fails_of_boundaryPoint_mem_sublevel`
  refutes `hsep` on that segment: its points are positive and compatible, but at any `s ∈ Pmax`
  the segment takes the value `(x₀ s) / n`, which tends to zero.

So instantiating any of these criteria from this theorem's hypotheses would derive `False` — it
would prove that `omegaLimit` meets **no** boundary face at all (full permanence), a strictly
stronger statement than the conclusion demanded here, which only asks for a positive ω-point *in
addition to* the boundary ones.  (`hMclass`, which
`exists_positive_omegaPoint_of_blueprintData` needs separately, is itself unavailable for
non-conservative networks, whose positive compatibility classes are unbounded.)

What is still missing is a criterion that exhibits an interior ω-point without uniform coordinate
floors: an Anderson-style comparable-growth descent (`Network.ComparableGrowthDescent`, whose
finite induction `omegaLimit_positive_of_descend` is already proved) or a direct
polyhedral-surface argument.  The two lemmas below are the machine-checked core of this analysis;
the wiring to each criterion's hypotheses is the paragraph above.

Depends additionally on: `CRNT.Dynamics.ToricBarrierTrapping`.
-/

/-- **The separation clause `hsep` of the packaged barrier criteria is refutable as soon as a
boundary point of the ω-limit set sits in the closed sublevel together with the start point.**

Each piece of `PolyhedralBarrier.barrier` is affine, so the sublevel `{barrier ≤ R}` is convex;
the segment from `x₀` to `wmax` therefore stays inside it.  Its points
`z = x₀ / n + (1 - 1/n) · wmax` are positive (`x₀` positive, `wmax` nonnegative) and compatible
with `x₀` (the displacement is a scalar multiple of `wmax - x₀`), but at a zero coordinate
`wmax s = 0` of `wmax` the segment value is `x₀ s / n → 0`, which no `ε > 0` can bound below. -/
theorem hsep_fails_of_boundaryPoint_mem_sublevel {ι' : Type*} [Fintype ι'] [Nonempty ι']
    (N : Network S) (m : ι' → N.euclideanStoichSubspace) (b : ι' → ℝ) (R : ℝ)
    {x₀ wmax : Concentration S} {s : S}
    (hx₀ : x₀.Positive) (hwnn : Concentration.Nonnegative wmax)
    (hcompat : N.StoichCompatible x₀ wmax) (hsw : wmax s = 0)
    (hstart : PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState x₀) ≤ R)
    (hwmax : PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState wmax) ≤ R) :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ x : Concentration S, x.Positive → N.StoichCompatible x₀ x →
        PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
          (N.euclideanStoichState x) ≤ R → ε ≤ x s := by
  rintro ⟨ε, hε, hsep⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (x₀ s / ε)
  have hnpos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : (0 : ℕ) < n + 2)
  have hnle : x₀ s / ε < ((n + 2 : ℕ) : ℝ) :=
    lt_of_lt_of_le hn (by exact_mod_cast Nat.le_add_right n 2)
  have hxE : x₀ s < ε * ((n + 2 : ℕ) : ℝ) := by
    have h := (div_lt_iff₀ hε).mp hnle
    rwa [mul_comm] at h
  have hqpos : (0 : ℝ) < 1 / ((n + 2 : ℕ) : ℝ) := one_div_pos.mpr hnpos
  have hq1 : 1 / ((n + 2 : ℕ) : ℝ) < 1 :=
    (div_lt_one hnpos).mpr (by exact_mod_cast (by omega : (1 : ℕ) < n + 2))
  -- the segment from `x₀` to `wmax` at parameter `1 - 1/(n+2)`
  set z : Concentration S :=
    fun u => 1 / ((n + 2 : ℕ) : ℝ) * x₀ u + (1 - 1 / ((n + 2 : ℕ) : ℝ)) * wmax u with hz
  have hzdef : z =
      (1 / ((n + 2 : ℕ) : ℝ)) • x₀ + (1 - 1 / ((n + 2 : ℕ) : ℝ)) • wmax := by
    funext u
    simp only [hz, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hzpos : z.Positive := fun u =>
    add_pos_of_pos_of_nonneg (mul_pos hqpos (hx₀ u))
      (mul_nonneg (sub_nonneg.mpr hq1.le) (hwnn u))
  have hzcompat : N.StoichCompatible x₀ z := by
    have h2 : z - x₀ = (1 - 1 / ((n + 2 : ℕ) : ℝ)) • (wmax - x₀) := by
      rw [hzdef]
      funext u
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [StoichCompatible, h2]
    exact N.stoichSubspace.smul_mem _ hcompat
  have hstate : N.euclideanStoichState z =
      (1 / ((n + 2 : ℕ) : ℝ)) • N.euclideanStoichState x₀
        + (1 - 1 / ((n + 2 : ℕ) : ℝ)) • N.euclideanStoichState wmax := by
    rw [hzdef]
    simp only [← euclideanStoichStateL_apply, map_add, map_smul]
  have hzbar : PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
      (N.euclideanStoichState z) ≤ R := by
    rw [hstate, PolyhedralBarrier.barrier_le_iff]
    intro i
    have hA : innerSL ℝ (-m i) (N.euclideanStoichState x₀) - b i ≤ R :=
      le_trans (PolyhedralBarrier.le_barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState x₀) i) hstart
    have hB : innerSL ℝ (-m i) (N.euclideanStoichState wmax) - b i ≤ R :=
      le_trans (PolyhedralBarrier.le_barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState wmax) i) hwmax
    have hkey : innerSL ℝ (-m i)
        ((1 / ((n + 2 : ℕ) : ℝ)) • N.euclideanStoichState x₀
          + (1 - 1 / ((n + 2 : ℕ) : ℝ)) • N.euclideanStoichState wmax) - b i
        = (1 / ((n + 2 : ℕ) : ℝ)) *
            (innerSL ℝ (-m i) (N.euclideanStoichState x₀) - b i)
          + (1 - 1 / ((n + 2 : ℕ) : ℝ)) *
            (innerSL ℝ (-m i) (N.euclideanStoichState wmax) - b i) := by
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]; ring
    rw [hkey]
    have hc1 : (0 : ℝ) ≤ 1 / ((n + 2 : ℕ) : ℝ) := le_of_lt hqpos
    have hc2 : (0 : ℝ) ≤ 1 - 1 / ((n + 2 : ℕ) : ℝ) := sub_nonneg.mpr hq1.le
    have hsum : (1 / ((n + 2 : ℕ) : ℝ)) * R
        + (1 - 1 / ((n + 2 : ℕ) : ℝ)) * R = R := by ring
    exact le_trans
      (add_le_add (mul_le_mul_of_nonneg_left hA hc1) (mul_le_mul_of_nonneg_left hB hc2))
      (le_of_eq hsum)
  have hsepz : ε ≤ z s := hsep z hzpos hzcompat hzbar
  have hzval : z s = 1 / ((n + 2 : ℕ) : ℝ) * x₀ s
      + (1 - 1 / ((n + 2 : ℕ) : ℝ)) * wmax s := by rw [hz]
  rw [hzval, hsw, mul_zero, add_zero] at hsepz
  have hle : ε * ((n + 2 : ℕ) : ℝ) ≤ x₀ s := by
    have h1 : ε ≤ x₀ s / ((n + 2 : ℕ) : ℝ) := by
      rwa [div_eq_mul_inv, mul_comm, ← one_div]
    exact (le_div_iff₀ hnpos).mp h1
  exact (not_lt.mpr hle) hxE

/-- **Trapping along the orbit puts every ω-limit point into the closed sublevel.**  If the
barrier is at most `R` along the whole forward orbit, the sublevel `{barrier ≤ R}` is closed,
contains the forward orbit, and every ω-limit point lies in the closure of the forward orbit — so
`wmax ∈ omegaLimit` inherits `barrier … ≤ R`.  This is the step that makes the separation clause
`hsep` untenable whenever the ω-limit set meets the boundary (see
`hsep_fails_of_boundaryPoint_mem_sublevel`). -/
theorem barrier_le_of_mem_omegaLimit {ι' : Type*} [Fintype ι'] [Nonempty ι']
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ wmax : Concentration S} (N : Network S) (m : ι' → N.euclideanStoichSubspace)
    (b : ι' → ℝ) (R : ℝ)
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (htrap : ∀ t : ℝ, 0 ≤ t →
      PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState (γ x₀ t)) ≤ R)
    (hw : wmax ∈ omegaLimit atTop ϕ {x₀}) :
    PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
      (N.euclideanStoichState wmax) ≤ R := by
  have hc : Continuous fun x : Concentration S =>
      PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b (N.euclideanStoichState x) :=
    (PolyhedralBarrier.continuous_barrier _ _).comp N.euclideanStoichStateL.continuous
  have hclosed : IsClosed {x : Concentration S |
      PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState x) ≤ R} :=
    isClosed_le hc continuous_const
  have hsub : Set.image2 ϕ Set.univ {x₀} ⊆ {x : Concentration S |
      PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState x) ≤ R} := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    rw [hϕγ x t]
    rw [hx]
    exact htrap t t.coe_nonneg
  have hω : omegaLimit atTop ϕ {x₀} ⊆ {x : Concentration S |
      PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState x) ≤ R} :=
    (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := Set.univ)
      univ_mem).trans ((IsClosed.closure_subset_iff hclosed).mpr hsub)
  exact hω hw

/-! ## The static slice of Anderson's descent that IS available here

Route (A)/(B) of the residual: apply `omegaLimit_positive_of_descend` from
`CRNT.Dynamics.SiphonDimensionDescent`, whose strong induction on the siphon cardinality is already
proved.  Its sole input is `N.ComparableGrowthDescent ϕ x₀`, and all the structural data it needs
*along the way* is derivable from this theorem's own hypotheses — no call-site fields are missing:
`criticalBoundaryOmegaFace_lowerRank` (from `weaklyReversible_of_positive_complexBalanced` and
`exists_relEntropy_const_on_omegaLimit`) supplies `IsCriticalSiphon Pmax`, the complex-balance of
the avoiding-face restriction at `fillSiphonFace Pmax xstar wmax`, the strict stoichiometric rank
drop, and `massActionVectorField κ wmax = 0`, and `⟨wmax, hwmax, hzeroMax⟩` is the carriedness
witness.

Two facts then resist, and the lemma below discharges the part of them that is static:

* `hmaxExact` can only ever *exclude* candidates for the descent's right disjunct, never produce
  one: a carried `Q` with `Q.card < Pmax.card` cannot contain `Pmax`, so its witness `z` does not
  satisfy the premise `∀ s ∈ Pmax, z s = 0` that `hmaxExact z` needs.  Eliminating all candidates
  would make `descend Pmax` equivalent to the very goal of this theorem — circular.
* what the right disjunct needs is a carried critical siphon of **strictly smaller** cardinality.
  `exists_smaller_carried_siphon_of_zeroSet_inside` constructs one whenever some ω-point is
  positive on `Pmaxᶜ`, vanishes at some species of `Pmax`, and is positive at some species of
  `Pmax` — in the absence of a positive ω-point.  The uncovered branch — every ω-point that is
  positive on `Pmax` also vanishes *outside* `Pmax`, where no static cardinality bound is
  available — is exactly
  Anderson's comparable-growth estimate: comparing relative-entropy growth across an escape from
  the face, which is the analytic content `ComparableGrowthDescent` isolates and the tree does not
  formalise.  (The degenerate ω-limit set `ω = {wmax}` shows why no purely static argument can
  finish: there the right disjunct at `Pmax` is false outright, so any static proof of
  `descend Pmax` would prove this theorem's goal — i.e. would already be the missing result.) -/

/-- **A strictly smaller carried critical siphon, from an ω-point whose zero set sits strictly
inside `Pmax`.**

Under this theorem's orbit hypotheses, if the ω-limit set contains no positive point, and some
`z ∈ ω` is positive on every species outside `Pmax`, vanishes at some species of `Pmax`, and is
positive at some species of `Pmax`, then the zero set `Q` of `z` is nonempty (positivity fails
somewhere, and off `Pmax` nothing vanishes, so the failure is on `Pmax`), strictly smaller than
`Pmax` (it omits the species where `z` is positive), carried by `z`, and critical — so it is
exactly a right-disjunct witness for `descend Pmax` of `Network.ComparableGrowthDescent`. -/
theorem exists_smaller_carried_siphon_of_zeroSet_inside
    (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx₀ : x₀.Positive)
    {Pmax : Finset S}
    (hnoG : ¬ ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive)
    {z : Concentration S} (hz : z ∈ omegaLimit atTop ϕ {x₀})
    (hzoff : ∀ s, s ∉ Pmax → 0 < z s)
    (hzon : ∃ s₀ ∈ Pmax, 0 < z s₀) :
    ∃ Q : Finset S, Q.Nonempty ∧ N.IsCriticalSiphon Q ∧ Q.card < Pmax.card ∧
      N.SiphonCarried ϕ x₀ Q := by
  classical
  set Q : Finset S := Finset.univ.filter (fun s => z s = 0) with hQ
  have hQz : ∀ s, s ∈ Q ↔ z s = 0 := fun s => by simp [hQ]
  -- `z` is not positive: the ω-limit set has no positive point
  have hznpos : ¬ z.Positive := fun h => hnoG ⟨z, hz, h⟩
  obtain ⟨s, hs⟩ : ∃ s, ¬ 0 < z s := not_forall.mp hznpos
  have hz0 : z s = 0 := le_antisymm (not_lt.mp hs) (hωnn z hz s)
  have hQne : Q.Nonempty := ⟨s, (hQz s).mpr hz0⟩
  have hsub : Q ⊆ Pmax := by
    intro t ht
    by_contra htn
    have h1 : z t = 0 := (hQz t).mp ht
    have h2 : 0 < z t := hzoff t htn
    linarith
  have hne : Q ≠ Pmax := by
    intro hQeq
    obtain ⟨s₀, hs₀P, hs₀z⟩ := hzon
    rw [← hQeq] at hs₀P
    have h1 : z s₀ = 0 := (hQz s₀).mp hs₀P
    linarith
  have hcard : Q.card < Pmax.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  have hcarr : N.SiphonCarried ϕ x₀ Q := ⟨z, hz, hQz⟩
  have hcrit : N.IsCriticalSiphon Q :=
    N.isCriticalSiphon_of_siphonCarried κ hϕγ hK hmaps hωnn hgenω hωaff hx₀ hQne hcarr
  exact ⟨Q, hQne, hcrit, hcard, hcarr⟩

/-! ## The exact residue: the vanishing-off-`Pmax` pin, the conservation mechanism, and the
exhaustive trichotomy

`hzcard` (newly exported from `exists_maximal_zeroSet_omegaPoint` and threaded through the call
site) bounds every ω-point's zero set by `Pmax.card`.  With it, four lemmas pin down *exactly*
what remains of Anderson's descent at `Pmax`:

* `exists_positive_on_pmax_of_zero_outside`: an ω-point that vanishes **outside** `Pmax` must be
  positive somewhere **on** `Pmax` — otherwise `hmaxExact` would force its zero set to equal
  `Pmax`, contradicting the outside zero.  So the “vanishes off `Pmax`” configuration cannot hide
  from `hmaxExact`; it simply cannot be *killed* by it.
* `eq_zero_on_pmax_of_conservation_eq`: the compatibility-class mechanism.  If the invariant `c`
  does not see the off-`Pmax` part of `z - wmax` (`hout`), then a `P`-invariant that is
  nonnegative and strictly positive on `Pmax` forces `z = 0` on `Pmax`, and `hmaxExact` then
  collapses `z` to `Pmax` exactly — contradicting any outside zero.  What resists: `hout` is
  *agreement off `Pmax`* (or `c` supported inside `Pmax`), and neither is available for an
  arbitrary ω-point — ω-points of one class vary freely off the face — while an invariant that
  is nonnegative everywhere and positive on **all** of `Pmax` would be a witness to
  `¬ N.IsCriticalSiphon Pmax`, which the derived `IsCriticalSiphon Pmax` forbids.  The mechanism
  is exact but not instantiable here.
* `smaller_carried_siphon_iff_zeroSet_card_lt`: absent a positive ω-point, the descent's right
  disjunct is *equivalent* to “some ω-point has a strictly smaller zero set”.
* `omegaPoint_zeroSet_trichotomy`: every ω-point either is strictly positive (the goal of this
  theorem), or its zero set is exactly `Pmax`, or it witnesses a strictly smaller carried siphon
  (the right disjunct), or it is an exact tie — positive somewhere on `Pmax`, vanishing
  somewhere off it, with `card = Pmax.card`.  Exhaustive.  **Two** disjuncts stay open, not one:
  “every ω-point has zero set exactly `Pmax`” (the degenerate model `ω = {wmax}` lives there) and
  the exact ties (where the conservation mechanism above is blocked as recorded).  Both are
  dynamical: no static lemma can close either, since the model satisfies every static hypothesis
  and every derived fact. -/

/-- **An ω-point vanishing outside `Pmax` is positive somewhere on `Pmax`.**  Feeding `hmaxExact`
its premise would force the zero set to equal `Pmax` exactly, which the outside zero contradicts;
so the premise must fail. -/
theorem exists_positive_on_pmax_of_zero_outside
    {ϕ : Flow ℝ≥0 (Concentration S)} {x₀ : Concentration S} {Pmax : Finset S}
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hmaxExact : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (∀ s ∈ Pmax, z s = 0) →
      ∀ s, z s = 0 ↔ s ∈ Pmax)
    {z : Concentration S} (hz : z ∈ omegaLimit atTop ϕ {x₀})
    (ht : ∃ t, t ∉ Pmax ∧ z t = 0) :
    ∃ s ∈ Pmax, 0 < z s := by
  by_contra h
  push Not at h
  have hzeroP : ∀ u ∈ Pmax, z u = 0 :=
    fun u hu => le_antisymm (h u hu) (hωnn z hz u)
  obtain ⟨t, htn, ht0⟩ := ht
  exact htn ((hmaxExact z hz hzeroP t).1 ht0)

/-- **The compatibility-class pin (Lead 1).**  Stoichiometric compatibility gives
`weightedTotal c z = weightedTotal c wmax` for every `P`-invariant `c`; if `c` sees no off-`Pmax`
part of the difference (`hout` — subsuming both “`z` and `wmax` agree off `Pmax`” and “`c` is
supported inside `Pmax`”), the whole invariant total sits on `Pmax`, and a nonnegative `c`
positive there forces `z = 0` on `Pmax`.  Then `hmaxExact` collapses `z` to `Pmax` exactly. -/
theorem eq_zero_on_pmax_of_conservation_eq
    (N : Network S) {z wmax : Concentration S} {Pmax : Finset S}
    (hznn : Concentration.Nonnegative z) (hcompat : N.StoichCompatible wmax z)
    (hzero : ∀ s ∈ Pmax, wmax s = 0)
    (c : S → ℝ) (hc : N.IsPInvariant c)
    (hout : ∀ t, t ∉ Pmax → c t * (z t - wmax t) = 0)
    (hcnn : ∀ s ∈ Pmax, 0 ≤ c s) (hcpos : ∀ s ∈ Pmax, 0 < c s) :
    ∀ s ∈ Pmax, z s = 0 := by
  intro s hsp
  have hwt : weightedTotal c z = weightedTotal c wmax :=
    (N.weightedTotal_eq_of_stoichCompatible hc hcompat).symm
  have hsum : ∑ u : S, c u * (z u - wmax u) = 0 := by
    have hz : ∑ u : S, c u * z u - ∑ u : S, c u * wmax u = 0 := by
      simpa [weightedTotal] using sub_eq_zero.mpr hwt
    rwa [show ∑ u : S, c u * (z u - wmax u) =
        ∑ u : S, c u * z u - ∑ u : S, c u * wmax u
      by simp [mul_sub, Finset.sum_sub_distrib]]
  have hsplit : (∑ u ∈ Pmax, c u * (z u - wmax u))
      + (∑ u ∈ Pmaxᶜ, c u * (z u - wmax u)) = 0 :=
    (Finset.sum_add_sum_compl Pmax _).trans hsum
  have houts : ∑ u ∈ Pmaxᶜ, c u * (z u - wmax u) = 0 :=
    Finset.sum_eq_zero (fun u hu => hout u (Finset.mem_compl.mp hu))
  have hp : ∑ u ∈ Pmax, c u * (z u - wmax u) = 0 := by linarith [hsplit, houts]
  have hpz : ∑ u ∈ Pmax, c u * z u = 0 := by
    rw [← hp]
    exact Finset.sum_congr rfl (fun u hu => by rw [hzero u hu, sub_zero])
  have hnn : ∀ u ∈ Pmax, 0 ≤ c u * z u := fun u hu => mul_nonneg (hcnn u hu) (hznn u)
  by_contra hzn
  have hpos : 0 < z s := lt_of_le_of_ne (hznn s) (Ne.symm hzn)
  have hterm : 0 < c s * z s := mul_pos (hcpos s hsp) hpos
  have hrest : 0 ≤ ∑ u ∈ Pmax.erase s, c u * z u :=
    Finset.sum_nonneg (fun u hu => hnn u (Finset.mem_of_mem_erase hu))
  have hadd := Finset.sum_erase_add Pmax (fun u => c u * z u) hsp
  linarith

/-- **Exact reduction of the descent's right disjunct (absent a positive ω-point).**  The
right-disjunct witness of `ComparableGrowthDescent.descend` at `Pmax` exists if and only if some
ω-point has a strictly smaller zero set than `Pmax`; criticality and carriedness are then
manufactured by `isCriticalSiphon_of_siphonCarried` and the carrier is the point itself. -/
theorem smaller_carried_siphon_iff_zeroSet_card_lt
    (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx₀ : x₀.Positive)
    {Pmax : Finset S}
    (hnoG : ¬ ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive) :
    ((∃ Q : Finset S, Q.Nonempty ∧ N.IsCriticalSiphon Q ∧ Q.card < Pmax.card ∧
        N.SiphonCarried ϕ x₀ Q) ↔
      ∃ z ∈ omegaLimit atTop ϕ {x₀},
        (Finset.univ.filter (fun s => z s = 0)).card < Pmax.card) := by
  constructor
  · rintro ⟨Q, _, _, hlt, z, hz, hzQ⟩
    refine ⟨z, hz, ?_⟩
    have hQeq : Finset.univ.filter (fun s => z s = 0) = Q := by
      apply Finset.ext
      intro u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hzQ u).symm
    rw [hQeq]
    exact hlt
  · rintro ⟨z, hz, hlt⟩
    have hznpos : ¬ z.Positive := fun h => hnoG ⟨z, hz, h⟩
    obtain ⟨s, hs⟩ : ∃ s, ¬ 0 < z s := not_forall.mp hznpos
    have hz0 : z s = 0 := le_antisymm (not_lt.mp hs) (hωnn z hz s)
    have hQne : (Finset.univ.filter (fun s => z s = 0)).Nonempty :=
      ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ s, hz0⟩⟩
    have hcarr : N.SiphonCarried ϕ x₀ (Finset.univ.filter (fun s => z s = 0)) :=
      ⟨z, hz, fun u => by simp⟩
    refine ⟨Finset.univ.filter (fun s => z s = 0), hQne, ?_, hlt, hcarr⟩
    exact N.isCriticalSiphon_of_siphonCarried κ hϕγ hK hmaps hωnn hgenω hωaff hx₀ hQne hcarr

/-- **The exhaustive trichotomy for the residue of the descent.**  Under this theorem's orbit
hypotheses, `hmaxExact` and `hzcard` split *every* ω-point into exactly one of four shapes:

1. strictly positive — the goal of this theorem;
2. zero set exactly `Pmax`;
3. witness of a strictly smaller carried critical siphon (the right disjunct of `descend Pmax`);
4. an exact tie: positive somewhere on `Pmax`, vanishing somewhere off `Pmax`, with
   `(Finset.univ.filter (· = 0)).card = Pmax.card`.

Disjuncts 2 and 4 are the open residue (assuming 1 and 3 fail globally): 2 contains the
degenerate model `ω = {wmax}`, and 4 is where the conservation pin of
`eq_zero_on_pmax_of_conservation_eq` is blocked.  Both are dynamical, not static. -/
theorem omegaPoint_zeroSet_trichotomy
    (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx₀ : x₀.Positive)
    {Pmax : Finset S}
    (hmaxExact : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (∀ s ∈ Pmax, z s = 0) →
      ∀ s, z s = 0 ↔ s ∈ Pmax)
    (hzcard : ∀ z ∈ omegaLimit atTop ϕ {x₀},
      (Finset.univ.filter (fun s => z s = 0)).card ≤ Pmax.card) :
    (∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive) ∨
    (∃ Q : Finset S, Q.Nonempty ∧ N.IsCriticalSiphon Q ∧ Q.card < Pmax.card ∧
      N.SiphonCarried ϕ x₀ Q) ∨
    (∀ z ∈ omegaLimit atTop ϕ {x₀},
      (Finset.univ.filter (fun s => z s = 0)) = Pmax ∨
        ((∃ s ∈ Pmax, 0 < z s) ∧ (∃ t, t ∉ Pmax ∧ z t = 0) ∧
          (Finset.univ.filter (fun s => z s = 0)).card = Pmax.card)) := by
  classical
  by_cases hG : ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive
  · exact Or.inl hG
  by_cases hm : ∃ Q : Finset S, Q.Nonempty ∧ N.IsCriticalSiphon Q ∧ Q.card < Pmax.card ∧
      N.SiphonCarried ϕ x₀ Q
  · exact Or.inr (Or.inl hm)
  refine Or.inr (Or.inr ?_)
  intro z hz
  have hnoG : ¬ ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive := hG
  have hznpos : ¬ z.Positive := fun h => hG ⟨z, hz, h⟩
  obtain ⟨s, hs⟩ : ∃ s, ¬ 0 < z s := not_forall.mp hznpos
  have hz0 : z s = 0 := le_antisymm (not_lt.mp hs) (hωnn z hz s)
  by_cases hsub : ∀ u ∈ Pmax, z u = 0
  · -- zero set contains `Pmax`: `hmaxExact` pins it to `Pmax` exactly
    left
    apply Finset.ext
    intro u
    constructor
    · intro hu
      exact (hmaxExact z hz hsub u).1 ((Finset.mem_filter.mp hu).2)
    · intro hu
      exact Finset.mem_filter.2 ⟨Finset.mem_univ u, (hmaxExact z hz hsub u).2 hu⟩
  · right
    push Not at hsub
    obtain ⟨s₀, hs₀P, hs₀pos⟩ := hsub
    have hs₀z : 0 < z s₀ := lt_of_le_of_ne (hωnn z hz s₀) (Ne.symm hs₀pos)
    by_cases hoff : ∀ t, t ∉ Pmax → 0 < z t
    · -- positive off `Pmax`, zero and positive on `Pmax`: the smaller siphon exists
      exact absurd
        (N.exists_smaller_carried_siphon_of_zeroSet_inside κ hϕγ hK hmaps hωnn hgenω hωaff
          hx₀ hnoG hz hoff ⟨s₀, hs₀P, hs₀z⟩) hm
    · push Not at hoff
      obtain ⟨t₀, ht₀n, ht₀z⟩ := hoff
      have ht₀0 : z t₀ = 0 := le_antisymm ht₀z (hωnn z hz t₀)
      rcases lt_or_ge (Finset.univ.filter (fun s => z s = 0)).card Pmax.card with hlt | hge
      · -- strictly smaller zero set: the right-disjunct witness exists
        exact absurd
          ((smaller_carried_siphon_iff_zeroSet_card_lt N κ hϕγ hK hmaps hωnn hgenω hωaff hx₀
            hnoG).mpr ⟨z, hz, hlt⟩) hm
      · -- exact tie
        exact ⟨⟨s₀, hs₀P, hs₀z⟩, ⟨t₀, ht₀n, ht₀0⟩,
          le_antisymm (hzcard z hz) hge⟩

end Network
end CRNT

import CRNT.Dynamics.FaceCodimension
import CRNT.Dynamics.SiphonDimensionDescent
import CRNT.Dynamics.ToricBarrierTrapping
import CRNT.Dynamics.SingleLinkageGAC
import CRNT.Equilibria.ComplexBalanceStructure
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

/-! ## The packaging audit against Craciun v3 (arXiv:1501.02860v3)

The question raised while reading the paper — do Theorem B / Lemma 9.5 / Lemma 9.7 *assume*
uniform coordinate floors, or *prove* them? — has a definite answer, and it fixes two places where
the repo's packaging is stronger than the paper's text, plus one place where it is exactly right.

**1. `hsep` is a conclusion of the paper, never a hypothesis.**  Definition 4.6 defines a ZSH by
(i) `𝒵 ⊂ ℝⁿ₊ \ (η + ℝⁿ₊)` — the *surface* stays out of the deep interior box, i.e. it hugs the
boundary, the opposite direction from a floor — (ii) `𝒵` meets every toric ray exactly once, and
(iii) `𝒵` cannot be crossed inside some cube `(0,M)ⁿ`.  Lemma 9.5 assumes only "`𝒵` is a ZSH" and
concludes that the outer normal at `x` lies in every cone `𝒞` with `log x ∈ 𝒞`.  Lemma 9.7 assumes
only (i) for the unit cube (`𝒵 ⊂ (0,1)³ \ (ε̂ + [0,1]³)`) together with the normal-in-`K_𝒞`
condition, and concludes non-crossing inside the unit cube.  No coordinate floor appears in either
statement.  The floor on the *region* — "the upper region of `ℋ` is at positive distance from
`∂ℝⁿ`", part of the statement of Theorem B — is produced by the construction: §8 Step 2 chooses
`ε₀ < x₀ⁱ`, so `(ε₀,…,ε₀) + ℝⁿ₊` lies above `𝒵_{ε₀}`, and the compact invariant set is
`K_{x₀} = (above 𝒵_{ε₀}) ∩ [0,M]ⁿ ∩ {V ≤ L}` with `V` the Horn–Jackson Lyapunov function (§6.1 and
Fig. 3(e); Lemma 9.11 puts `{V ≤ L}` between two simplices, which is where the outer bound comes
from).

**2. The two lemmas above therefore say something stronger than "the criteria are mis-packaged":
every uniform-floor statement is refutable under this theorem's hypotheses, because `wmax` sits in
`ω`.**  For the repo's *convex* barrier sublevels this is
`hsep_fails_of_boundaryPoint_mem_sublevel` — the segment `x₀ / n + (1 - 1/n) · wmax` stays inside
and takes the value `x₀ s / n → 0` — together with `barrier_le_of_mem_omegaLimit`, which puts
`wmax` into any sublevel that traps the orbit.  For the paper's own region no convexity is needed
and none should be assumed (the paper never claims `K_{x₀}` is convex; see 4): compactness plus
`K_{x₀} ⊂ ℝⁿ_{>0}` already forces `wmax ∈ K_{x₀}` to be positive, contradicting
`hPmaxne`/`hzeroMax`.  So no weaker geometric statement and no repackaging of a *uniform-floor*
criterion can be instantiated here — each of them proves full permanence, which `wmax` refutes —
and once the §4 existence claim (item 5) is available this theorem closes by `False`.

**3. `hMclass` is the repo's hypothesis, not the paper's.**  Craciun never assumes bounded
compatibility classes.  His standing hypotheses are weak reversibility (Theorem 4.3 embeds a
variable-`k` weakly reversible system into a toric differential inclusion), and the boundedness he
uses is that of the *trajectory*: §8's remark proves that "any bounded trajectory of a variable-`k`
weakly reversible system is persistent", and the outer bound `M` comes from the cube `[0,M]ⁿ`
containing the chosen level surface `ℒ` (§6.1) together with `V ≤ L` — it bounds the invariant
region, not the class.  The class-wide bound fails in the paper's own setting:
`CRNT.Examples.OpenSystem.exists_complexBalanced_unbounded_class` constructs a weakly reversible
network of deficiency zero — hence complex balanced for *every* rate vector, so it carries exactly
this theorem's `hxs`/`hcb` — whose stoichiometric subspace is everything, so no `M` bounds its
positive compatibility classes.  `hMclass` is therefore not derivable here; it is available only on
conservative networks (the all-ones law bounds the class), which is what the `ToricBarrierExplicit`
docstrings scope it to.

**4. The convex obstruction checks out.**  `ConvexBarrierObstruction.not_exists_weights_vector`
proves that no globally homogeneous max-of-affine barrier can carry a normal lying inside every
cone of a generic three-dimensional arrangement fan.  The paper never asks for one: its
non-crossing requirement is confined to a bounded window — the unit cube of Lemma 9.7, the blue box
`[0,M_{n+1}]×…×[0,M₂]` of §8 Step 1 in compactified log coordinates — and inside a bounded window
the constant offsets `b_i` *can* repair the violations, which is precisely the step ("the deficit
scales linearly in `X` along `𝒞`") that fails on an unbounded cone.  The §7.4.3 `ε(α)` scale
hierarchy then handles the remaining self-consistency fixed point.  The repo's reading of the
obstruction, recorded in that module's header, matches the paper.

**5. The missing object already has a name in this tree.**  v3 §4 states the whole content in one
sentence: "for any positive initial condition `x₀ ∈ ℝⁿ_{>0}` of a toric dynamical system there
exists a compact forward invariant region `K_{x₀} ⊂ ℝⁿ_{>0}` such that `x₀ ∈ K_{x₀}`.  Of course,
this implies that toric dynamical systems are persistent."  Up to the packaging of forward
invariance, that is `N.PersistentFrom κ x₀` (`SingleLinkageGAC.lean:46`: a compact `K₀`, every
point of `K₀` strictly positive, every genuine solution through `x₀` staying in `K₀`), whose
orbit-level shadow is `Permanent ϕ x₀` (`EndotacticPermanence.lean:58`).  Both already yield this
theorem's conclusion: `omegaLimit_meets_positive_of_permanent` *is* the conclusion above, and
`persistentOrbit_of_persistentFrom` plus `PersistentOrbit.omegaLimit_positive` gives it for
`PersistentFrom`.  Two remarks, both checked against the text: (a) `K_{x₀}` compact and inside the
*open* orthant already forces `dist(K_{x₀}, ∂) > 0`, so no separate separation statement is
needed — in particular the segment argument of `hsep_fails_of_boundaryPoint_mem_sublevel` plays no
role here (it belongs to the repo's convex max-of-affine packaging, which the paper's tile-by-tile
surface is not — see 4); (b) feeding `PersistentFrom` to the chain above under this theorem's
hypotheses produces a *positive* `wmax` (`wmax ∈ ω ⊆ K₀`, `K₀` closed), contradicting
`hPmaxne`/`hzeroMax` — i.e. the residual is inconsistent with `PersistentFrom`, which is the
machine-checkable form of "closing this `sorry` = supplying that compact positive absorbing set
for the bounded orbit at hand".  *Correction, verified against the v3 source by `GacLit` (shared
log, `[GacLit] 19:47`): the paper does **not** prove that such a `K_{x₀}` exists.*  The claim
appears only as statements — §4 (plan lines 598/637, whose "Step 4" is the assembly), 2D figure
captions, §5 LaSalle prose — while §8 carries out Steps 1–2 and then stops; there is no
"§8 Step 4".  Lemmas 9.5/9.7 are stated only for `ℝ³`/`(0,1)³` although §8 Step 2 invokes Lemma 9.7
in `n` dimensions, and Lemma 9.11's proof is a one-paragraph sketch.  The honest accounting of the
gap is therefore: **Theorem B (§§5–8) + the Step-4 assembly the paper asserts but does not write
down + LaSalle/persistence.**  v3 is a preprint (v1 2015, v2 2016, v3 2026-09-23, no journal-ref)
treated as open in current literature — Wiuf, arXiv:2609.24553v1, lists the GAC as proved only in
special cases and does not cite 1501.02860; no erratum or refutation was found — so speak of the
*claimed* proof.

-/

/-- **The paper's §4 region cannot exist under this theorem's hypotheses.**
`N.PersistentFrom κ x₀` (`SingleLinkageGAC.lean:46`) is verbatim Craciun v3 §4 — "a compact
forward invariant region `K_{x₀} ⊂ ℝⁿ_{>0}` such that `x₀ ∈ K_{x₀}`" — and it already implies
this file's conclusion (`omegaLimit_meets_positive_of_permanent`, or
`persistentOrbit_of_persistentFrom` together with `PersistentOrbit.omegaLimit_positive`).  The
lemma below records the other side of the collision: if the ω-limit set contains a point that is
not strictly positive — this theorem has `wmax`, with `wmax s = 0` for the nonempty set `Pmax` —
then `PersistentFrom κ x₀` is refutable, because the certificate's compact set would have to
contain that point while being entirely inside the open orthant.

Consequently the `sorry` above is discharged by *any* construction of `PersistentFrom κ x₀` for
this orbit — which is what v3 *claims* to obtain from boundedness alone (the residual has
boundedness: `hK`/`hmaps`; the claim is the "Step 4" of §4's plan, asserted but not carried out —
see the audit above) — and, read the other way, the residual hypotheses are inconsistent with that
claim, i.e. with the *claimed* Theorem B/C. -/
theorem not_persistentFrom_of_mem_omegaLimit_notPositive (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    {w : Concentration S} (hw : w ∈ omegaLimit atTop ϕ {x₀}) (hwn : ¬ w.Positive) :
    ¬ N.PersistentFrom κ x₀ := by
  rintro ⟨K₀, hK₀cpt, hK₀pos, hgen⟩
  -- the genuine curve `γ x₀` starts at `x₀` and stays in the certificate's set
  have hγ0 : γ x₀ 0 = x₀ := by
    have h := hϕγ x₀ 0
    simpa using h.symm
  have hsub : ∀ t : ℝ, 0 ≤ t → γ x₀ t ∈ K₀ := fun t ht => hgen (γ x₀) hγ0 hsol t ht
  -- hence the whole forward orbit does, and so does its ω-limit set
  have himg : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ K₀ := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    rw [hϕγ x t]
    rw [hx]
    exact hsub t t.coe_nonneg
  have hω : omegaLimit atTop ϕ {x₀} ⊆ K₀ :=
    (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := Set.univ)
      univ_mem).trans ((IsClosed.closure_subset_iff hK₀cpt.isClosed).mpr himg)
  exact hwn (hK₀pos w (hω hw))

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

/-! ## One consequence of the standing hypotheses that the trichotomy alone does not record

`massActionVectorField_eq_zero_on_omegaLimit_of_hypotheses`: **every ω-point is an equilibrium**
of the mass-action field.  LaSalle for the relative entropy (available from
`hxs`/`hcb`/`hϕγ`/`hsol`/`hK`/`hmaps`) feeds
`GACOmegaPositive.massActionVectorField_eq_zero_on_omegaLimit`, which covers boundary ω-points as
well (their zero sets are siphons, so the face argument applies).

Note that the *third* disjunct of `omegaPoint_zeroSet_trichotomy` (a strictly smaller carried
critical siphon) is **not** refutable from `hzcard`: `hzcard` only says no ω-point's zero set is
*larger* than `Pmax.card`, which is perfectly consistent with one being strictly smaller. -/

/-- **Every ω-point is a stationary point of the mass-action vector field.**  Under exactly the
orbit hypotheses of this module, together with a positive complex-balanced reference and the
genuine solution property of the start orbit, relative entropy is constant on the ω-limit set and
the boundary-face analysis of `CRNT.Dynamics.GACOmegaPositive` turns that constancy into
`N.massActionVectorField κ z = 0` for *every* `z ∈ omegaLimit atTop ϕ {x₀}` — boundary points
included. -/
theorem massActionVectorField_eq_zero_on_omegaLimit_of_hypotheses
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
    (hx₀ : x₀.Positive) :
    ∀ z ∈ omegaLimit atTop ϕ {x₀}, N.massActionVectorField κ z = 0 := by
  have hwr : N.WeaklyReversible := N.weaklyReversible_of_positive_complexBalanced κ hxs hcb
  have hγ0 : ∀ x, γ x 0 = x := fun x => by simpa using (hϕγ x 0).symm
  -- LaSalle for the relative entropy, re-derived here: the packaged
  -- `GlobalAttractorTheorem.exists_relEntropy_const_on_omegaLimit` lives in a module that
  -- imports this one, so it cannot be used below its own call site.
  have hpos : ∀ t, 0 ≤ t → (γ x₀ t).Positive :=
    N.genuineOrbit_pos κ (by rw [hγ0]; exact hx₀) hsol
  have hd := fun (t : ℝ) (ht : 0 ≤ t) =>
    relEntropy_hasDerivAt hxs (hpos t ht) (fun s => (hasDerivAt_pi.mp (hsol t ht)) s)
  have hAnti : AntitoneOn (fun t => relEntropy xstar (γ x₀ t)) (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt) ?_ ?_
    · intro t ht
      rw [interior_Ici, Set.mem_Ioi] at ht
      exact (hd t ht.le).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici, Set.mem_Ioi] at ht
      rw [(hd t ht.le).deriv]
      exact dissipation_nonpos N κ (hpos t ht.le) hxs hcb
  have hsubK : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ K := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hmaps t
  have habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K :=
    ⟨Set.univ, univ_mem, (IsClosed.closure_subset_iff hK.isClosed).mpr hsubK⟩
  have hmono : ∀ a b : ℝ≥0, a ≤ b →
      relEntropy xstar (ϕ b x₀) ≤ relEntropy xstar (ϕ a x₀) := by
    intro a b hab
    rw [hϕγ, hϕγ]
    exact hAnti (Set.mem_Ici.mpr a.coe_nonneg) (Set.mem_Ici.mpr b.coe_nonneg)
      (by exact_mod_cast hab)
  obtain ⟨c, -, -, hωc⟩ := Flow.laSalle ϕ (relEntropy_continuous hxs) x₀ hK habs hmono
  exact N.massActionVectorField_eq_zero_on_omegaLimit hwr κ hxs hcb hγ0 hϕγ hK hmaps hgenω
    hωnn hωc

/-! ## The open residue is pinned: off-`Pmax` coordinates never approach zero

Both disjuncts left open by `omegaPoint_zeroSet_trichotomy` share one feature — some ω-point
vanishes on all of `Pmax` (`hface` below), which every tie witness also satisfies after
specialising `hmaxExact`.  The lemma then says that the failure of positivity is *confined* to
`Pmax`: every coordinate outside `Pmax` keeps a uniform positive floor for all forward time, so
the trajectory converges to the **relative interior** of the `Pmax` face and all of its limit
points are positive exactly on `Pmaxᶜ`.

This does not close the theorem — it sharpens what has to be closed.  Excluding this
configuration is the dynamical content of Craciun's Theorem B (v3 §7–§8): the degenerate model
`ω = {wmax}` satisfies every static hypothesis of this module and satisfies the conclusion of the
lemma below, so no static refinement can finish. -/

omit [DecidableEq S] [Fintype S] in
/-- **Off-`Pmax` coordinates are uniformly bounded below along the entire orbit.**  If every
ω-point vanishes on `Pmax`, `hmaxExact` holds, and `t₀ ∉ Pmax`, then there is `ε > 0` with
`ε ≤ γ x₀ t t₀` for every `t ≥ 0`.

Minimize the continuous coordinate `t₀` over the compact ω-limit set; the minimum `m` is strictly
positive, since `m = 0` would put a ω-point with `z t₀ = 0` in front of `hmaxExact`, contradicting
`t₀ ∉ Pmax`.  The open half-space `{y | m/2 < y t₀}` therefore contains ω, so
`eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset` pushes the whole
forward orbit into it after some time `T`; on the compact initial segment `[0,T]` continuity and
orbit positivity supply a second floor, and the minimum of the two floors is the witness. -/
theorem uniformLowerBound_offFace_of_zeroSet_eq
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hΓcont : ContinuousOn (γ x₀) (Set.Ici 0))
    (hΓpos : ∀ t : ℝ, 0 ≤ t → (γ x₀ t).Positive)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    {Pmax : Finset S}
    (hmaxExact : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (∀ s ∈ Pmax, z s = 0) →
      ∀ s, z s = 0 ↔ s ∈ Pmax)
    (hface : ∀ z ∈ omegaLimit atTop ϕ {x₀}, ∀ s ∈ Pmax, z s = 0)
    {t₀ : S} (ht₀ : t₀ ∉ Pmax) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 ≤ t → ε ≤ γ x₀ t t₀ := by
  classical
  -- the orbit is absorbed by the compact `K`, so the ω-limit set is compact and nonempty
  have hKcl : IsClosed K := hK.isClosed
  have himg : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ K := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hmaps t
  have habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K :=
    ⟨Set.univ, univ_mem, hKcl.closure_subset_iff.mpr himg⟩
  have hωcpt : IsCompact (omegaLimit atTop ϕ {x₀}) :=
    isCompact_omegaLimit_of_absorbing ϕ x₀ hK habs
  have hωne : (omegaLimit atTop ϕ {x₀}).Nonempty :=
    nonempty_omegaLimit_of_isCompact_absorbing atTop ϕ {x₀} hK habs
      (Set.singleton_nonempty x₀)
  -- the minimum of the coordinate `t₀` over ω
  obtain ⟨zstar, hzstar, hzmin⟩ :=
    hωcpt.exists_isMinOn hωne (continuous_apply t₀).continuousOn
  have hm0 : 0 < zstar t₀ := by
    by_contra h
    push Not at h
    have hz0 : zstar t₀ = 0 := le_antisymm h (hωnn zstar hzstar t₀)
    exact ht₀ ((hmaxExact zstar hzstar (fun s hs => hface zstar hzstar s hs) t₀).mp hz0)
  -- the open half-space strictly above the minimum contains the whole ω-limit set
  have hn1 : IsOpen {y : Concentration S | zstar t₀ / 2 < y t₀} :=
    isOpen_lt continuous_const (continuous_apply t₀)
  have hn2 : omegaLimit atTop ϕ {x₀} ⊆ {y : Concentration S | zstar t₀ / 2 < y t₀} := by
    intro z hz
    have hle : zstar t₀ ≤ z t₀ := isMinOn_iff.mp hzmin z hz
    exact lt_of_lt_of_le (half_lt_self hm0) hle
  -- hence the orbit eventually lies in that half-space
  obtain ⟨u, hu, hun⟩ :=
    eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset'
      atTop ϕ {x₀} hK habs hn1 hn2
  obtain ⟨T, hT⟩ := Filter.mem_atTop_sets.mp hu
  -- a second positive floor on the compact initial segment `[0, T]`
  have hIne : (Set.Icc (0 : ℝ) (T : ℝ)).Nonempty := ⟨0, le_rfl, T.coe_nonneg⟩
  have hγI : ContinuousOn (γ x₀) (Set.Icc (0 : ℝ) (T : ℝ)) :=
    hΓcont.mono Set.Icc_subset_Ici_self
  have hscont : ContinuousOn (fun u : ℝ => γ x₀ u t₀) (Set.Icc (0 : ℝ) (T : ℝ)) :=
    (continuous_apply t₀).comp_continuousOn hγI
  obtain ⟨pI, hpII, hpImin⟩ := isCompact_Icc.exists_isMinOn hIne hscont
  have hpIpos : 0 < γ x₀ pI t₀ := hΓpos pI hpII.1 t₀
  refine ⟨min (γ x₀ pI t₀) (zstar t₀ / 2), lt_min hpIpos (half_pos hm0), ?_⟩
  intro t ht
  by_cases hTt : t ≤ T
  · -- inside the initial segment: the continuity floor
    have htI : t ∈ Set.Icc (0 : ℝ) (T : ℝ) := ⟨ht, hTt⟩
    exact (min_le_left _ _).trans (isMinOn_iff.mp hpImin _ htI)
  · -- beyond `T`: the ω-half-space floor
    have hTle : (T : ℝ) ≤ t := le_of_lt (lt_of_not_ge hTt)
    have htu : (⟨t, ht⟩ : ℝ≥0) ∈ u := hT ⟨t, ht⟩ (by exact_mod_cast hTle)
    have hineq : zstar t₀ / 2 < ϕ (⟨t, ht⟩ : ℝ≥0) x₀ t₀ := by
      have h1 := hun (subset_closure (Set.mem_image2_of_mem htu (Set.mem_singleton x₀)))
      simpa using h1
    have heq : ϕ (⟨t, ht⟩ : ℝ≥0) x₀ = γ x₀ t := hϕγ x₀ ⟨t, ht⟩
    exact (min_le_right _ _).trans (le_of_lt (heq ▸ hineq))

/-! ## The chemical reading: what the relative entropy does at the boundary

The Horn–Jackson Lyapunov function in this repository is the finite sum
`relEntropy xstar x = ∑ i, (x i * log (x i / xstar i) - x i + xstar i)`
(`CRNT/Theorems/DeficiencyZero/Lyapunov.lean:58`), evaluated with Mathlib's convention
`Real.log 0 = 0`.  At a coordinate whose species has gone extinct the summand is
`0 * log 0 - 0 + xstar i = xstar i`: the entropy is **finite on the whole closed orthant** and
continuous there (`relEntropy_continuous`).  So the heuristic "relative entropy blows up at zero
concentration, contradicting its constancy on the ω-limit set" is unavailable here — it dies
precisely at the definition, where the boundary value is defined to be the finite number
`xstar s` per extinct coordinate rather than `+∞`.

What survives the failed blow-up is exact bookkeeping, and it is what the two lemmas below
record.  Every extinct species *raises* the entropy by exactly its reference value (the
`- x i + xstar i` part contributes `xstar s` at `x i = 0`), every surviving coordinate
contributes a nonnegative amount (Gibbs' inequality, `relEntropyTerm_nonneg`), hence:

* `relEntropy_ge_sum_zeroSet` — the total reference weight of any extinct set is capped by the
  entropy value at the point;
* `relEntropy_le_of_mem_omegaLimit` — Lyapunov descent plus continuity put the entire ω-limit
  set inside the sublevel `{relEntropy xstar · ≤ relEntropy xstar x₀}`;
* `sum_xstar_le_relEntropy_x₀_of_zero_omegaPoint` — transporting the cap through the ω-limit
  set: for the residual's `wmax` with zero set `Pmax`, the extinct set's reference weight is
  bounded by the *initial* entropy,

      ∑ s ∈ Pmax, xstar s ≤ relEntropy xstar x₀.

Combined with `exists_relEntropy_const_on_omegaLimit` (the LaSalle constant `c` is the value of
the entropy on every ω-point) this pins `c ≥ ∑ s ∈ Pmax, xstar s > 0`: a strictly positive floor
on the LaSalle constant of any trajectory whose ω-limit meets the boundary.  It is a genuine
constraint — but not a contradiction: `relEntropy xstar x₀` is an arbitrary nonnegative number
and can exceed any finite reference weight, so the cap alone cannot exclude `Pmax` and cannot
deliver the positive ω-point.  The missing dynamical content remains Craciun v3 Theorem B, as
documented at the head of this file.
-/

/-- **The reference weight of an extinct set is capped by the relative entropy.** For a
nonnegative concentration `x` and any set `Z` of coordinates vanishing at `x`, the sum of the
reference values `xstar s` over `s ∈ Z` is at most `relEntropy xstar x`.  Each summand of the
entropy over `Z` equals `xstar s` (by `Real.log 0 = 0`) and each summand outside `Z` is
nonnegative by `relEntropyTerm_nonneg`.  This is the finite substitute for entropy blow-up at
the boundary: the entropy does not diverge as a species goes extinct, it rises by exactly the
extinct species' reference value. -/
theorem relEntropy_ge_sum_zeroSet {xstar x : Concentration S} (hxs : xstar.Positive)
    (hx : x.Nonnegative) {Z : Finset S} (hZ : ∀ s ∈ Z, x s = 0) :
    ∑ s ∈ Z, xstar s ≤ relEntropy xstar x := by
  unfold relEntropy
  have hnn : ∀ i : S, 0 ≤ x i * Real.log (x i / xstar i) - x i + xstar i :=
    fun i => relEntropyTerm_nonneg (hx i) (hxs i)
  have hterm : ∀ i ∈ Z, x i * Real.log (x i / xstar i) - x i + xstar i = xstar i := by
    intro i hi
    rw [hZ i hi]
    simp
  have hzsum : (∑ i ∈ Z, (x i * Real.log (x i / xstar i) - x i + xstar i)) = ∑ i ∈ Z, xstar i :=
    Finset.sum_congr rfl hterm
  have hsplit :
      (∑ i ∈ Z, (x i * Real.log (x i / xstar i) - x i + xstar i))
          + (∑ i ∈ Zᶜ, (x i * Real.log (x i / xstar i) - x i + xstar i))
        = ∑ i : S, (x i * Real.log (x i / xstar i) - x i + xstar i) :=
    Finset.sum_add_sum_compl Z _
  have hcompl : 0 ≤ ∑ i ∈ Zᶜ, (x i * Real.log (x i / xstar i) - x i + xstar i) :=
    Finset.sum_nonneg fun i _ => hnn i
  linarith

/-- **Lyapunov descent puts the whole ω-limit set in the initial sublevel.** Every ω-point of
the bounded genuine orbit through the positive `x₀` satisfies
`relEntropy xstar z ≤ relEntropy xstar x₀`: the forward orbit lies in the closed sublevel by
`genuineOrbit_relEntropy_le` (Lyapunov descent along the positive genuine orbit), the sublevel
is closed by `relEntropy_continuous`, and ω-points are limits of forward-orbit points. -/
theorem relEntropy_le_of_mem_omegaLimit
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    (hx₀ : x₀.Positive)
    {z : Concentration S} (hz : z ∈ omegaLimit atTop ϕ {x₀}) :
    relEntropy xstar z ≤ relEntropy xstar x₀ := by
  have hγ0 : γ x₀ 0 = x₀ := by
    have h := hϕγ x₀ (0 : ℝ≥0)
    rw [NNReal.coe_zero] at h
    exact h.symm.trans (ϕ.map_zero_apply x₀)
  have hpos : ∀ t : ℝ, 0 ≤ t → (γ x₀ t).Positive :=
    N.genuineOrbit_pos κ (by rw [hγ0]; exact hx₀) hsol
  have himg : Set.image2 ϕ Set.univ {x₀} ⊆
      {y : Concentration S | relEntropy xstar y ≤ relEntropy xstar x₀} := by
    rintro y ⟨t, _, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [hϕγ]
    have hle := N.genuineOrbit_relEntropy_le κ hxs hcb hpos hsol t t.coe_nonneg
    rwa [hγ0] at hle
  have hclosed : IsClosed {y : Concentration S | relEntropy xstar y ≤ relEntropy xstar x₀} :=
    isClosed_le (relEntropy_continuous hxs) continuous_const
  exact ((omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := Set.univ)
      univ_mem).trans ((IsClosed.closure_subset_iff hclosed).mpr himg)) hz

/-- **The extinct set's reference weight is bounded by the initial relative entropy.** If an
ω-point `wmax` of the bounded genuine orbit through `x₀` vanishes exactly on `Pmax`, then

    ∑ s ∈ Pmax, xstar s ≤ relEntropy xstar x₀.

This is the quantitative residue of the entropy-blow-up heuristic: since the entropy is finite
at the boundary and equals `xstar s` per extinct coordinate, extinction of `Pmax` costs at
least `∑ s ∈ Pmax, xstar s` of relative entropy, which the Lyapunov descent caps by the initial
value.  Instantiated together with `exists_relEntropy_const_on_omegaLimit` it gives the strict
floor `∑ s ∈ Pmax, xstar s ≤ c` on the LaSalle constant `c` of the residual's hypotheses. -/
theorem sum_xstar_le_relEntropy_x₀_of_zero_omegaPoint
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    (hx₀ : x₀.Positive)
    {Pmax : Finset S} {wmax : Concentration S}
    (hwmax : wmax ∈ omegaLimit atTop ϕ {x₀})
    (hwnn : Concentration.Nonnegative wmax)
    (hzeroMax : ∀ s, s ∈ Pmax ↔ wmax s = 0) :
    ∑ s ∈ Pmax, xstar s ≤ relEntropy xstar x₀ := by
  have hzero : ∀ s ∈ Pmax, wmax s = 0 := fun s hs => (hzeroMax s).1 hs
  exact (relEntropy_ge_sum_zeroSet hxs hwnn hzero).trans
    (relEntropy_le_of_mem_omegaLimit N κ hxs hcb hϕγ hsol hx₀ hwmax)

end Network
end CRNT

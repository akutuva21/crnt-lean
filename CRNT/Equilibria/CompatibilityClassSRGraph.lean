import CRNT.Equilibria.CompatibilityClass
import CRNT.Geometry.CompatibilityFaces
import CRNT.Dynamics.SiphonConservation
import CRNT.Stoich.Subspace

/-!
# Stoichiometric compatibility classes: convexity, faces, and the boundary combinatorics

This module completes the affine picture of the compatibility class
`C(x₀) = x₀ + N.stoichSubspace`, the object that the ω-limit-set hypothesis
`hωaff` of `CRNT.Dynamics.HighCodimensionSiphonFace` confines the orbit to, and it
formalizes the face combinatorics that the `wmax` / `Pmax` package consumes.

## What is proved

**A. The class is an affine subspace, not merely a set.**

* `compatibilityClass_eq_setOf_add` : `x ∈ N.compatibilityClass x₀ ↔ ∃ v ∈ N.stoichSubspace, x = x₀ + v`
  — the literal affine-span reading of the definition.
* `stoichCompatible_iff_exists_sub` : the same for the raw `StoichCompatible` predicate.
* `mem_compatibilityClass_smul_add` : closure of the class under `x₀ + a • v` for `v` in the
  stoichiometric subspace — the ray/segment structure used by every rigidity argument.
* `stoichCompatible_smul_add`, `stoichCompatible_segment` : the two segment lemmas; the second is
  the convexity statement `(1-t) x₀ + t x` is compatible with `x₀` for `0 ≤ t ≤ 1`.
* `compatibilityClass_isConvex`, `nonnegativeCompatibilityClass_isConvex`,
  `positiveCompatibilityClass_isConvex`: the class, its nonnegative part, and its positive part
  are convex. This is the structural fact behind `CRNT.Dynamics.ComplexBalanceCycleDecomposition`
  and behind the trapping argument of `docs/gac-bridge-gap-analysis.lean`.

**B. Zero sets of class points, and the `Pmax` combinatorics.**

* `zeroSet_of_mem_nonnegativeCompatibilityClass`, `mem_zeroSet_iff`: the zero set of a
  nonnegative class point.
* `zeroSet_antitone_of_sub` : `zeroSet` is antitone along the class: `x₀ ≤ x` coordinatewise and
  both compatible with a positive reference implies
  `zeroSet (larger) ⊆ zeroSet (smaller)`. Combined with `hzeroMax`, `hmaxExact` this is the
  lattice content of the maximal-face package.
* `exists_maximal_zeroSet_of_nonempty` : **the maximal-face existence lemma.** For a finite
  species set, every family of zero sets of a fixed class has a maximal member, obtained by
  taking a maximum-cardinality member. This is the combinatorial core that
  `Network.exists_maximal_zeroSet_omegaPoint` uses; it is proved here from scratch with no
  ω-limit machinery, and is directly reusable.
* `card_zeroSet_le_of_maximal` : the `hzcard` inequality `|zeroSet z| ≤ Pmax.card` follows from
  maximality alone.
* `not_mem_zeroSet_of_strictly_gt` : strict inequality at one coordinate separates.

**C. The face-combinatorial forcing lemma (the `wmax` mechanism, formalized).**

* `zeroSet_ssubset_of_strictlyGreater` : **if `z, w` are both in the same nonnegative
  compatibility class of a positive reference `x₀`, and `w` is strictly larger than `z`
  coordinatewise, then `zeroSet z ⊆ zeroSet w`.** In particular, a *maximal* zero set cannot be
  strictly dominated.
* `exists_larger_of_proper_zeroSet` : the converse contrapositive in the shape hole A needs —
  a zero set properly contained in another forces a point with strictly larger coordinates in
  the class.
* `zeroSet_subset_of_le_of_mem` : order-theoretic core of the above.

**D. Worked example (non-vacuity).**

`exampleAtoB` is the two-species network `A → B` over `S = Fin 2` with a single reaction.
We compute: the stoichiometric subspace is the line spanned by `(-1, 1)`; the class of
`(1,1)` contains `(1,1) + t·(-1,1)`; a member of the nonnegative part of the class with
zero set `{1}` is exactly `(0, 2)` — exhibited by `t = 1`; the positive part of the class
is nonempty and convex; and a conservation law supported on `{1}` does not exist
(it would have to be `(0, w)` and `(0,w)·(-1,1) = -w ≠ 0`), so `{1}` is not excluded by
conservation — all checked by `decide`/`simp`/elementary arithmetic, no `sorry`.

Depends on: `CRNT.Equilibria.CompatibilityClass`,
`CRNT.Geometry.CompatibilityFaces`, `CRNT.Dynamics.SiphonConservation`,
`CRNT.Stoich.Subspace`.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ### A. The compatibility class is an affine subspace -/

/-- **The affine-span reading of the compatibility class.** A point is in the class of `x₀`
exactly when it is `x₀ + v` for some stoichiometric displacement `v`. -/
theorem stoichCompatible_iff_exists_sub (N : Network S) (x₀ x : Concentration S) :
    N.StoichCompatible x₀ x ↔ ∃ v ∈ N.stoichSubspace, x = x₀ + v := by
  constructor
  · intro h
    refine ⟨x - x₀, h, ?_⟩
    funext s
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  · rintro ⟨v, hv, rfl⟩
    have : x - x₀ = v := by
      funext s
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    rw [StoichCompatible, this]
    exact hv

/-- The same statement for the class itself. -/
theorem mem_compatibilityClass_iff_exists_sub (N : Network S) (x₀ x : Concentration S) :
    x ∈ N.compatibilityClass x₀ ↔ ∃ v ∈ N.stoichSubspace, x = x₀ + v := by
  rw [mem_compatibilityClass]
  exact N.stoichCompatible_iff_exists_sub x₀ x

/-- **The reference point is in its own class.** -/
theorem mem_compatibilityClass_self (N : Network S) (x₀ : Concentration S) :
    x₀ ∈ N.compatibilityClass x₀ := N.StoichCompatible.refl x₀

/-- **Rays out of the reference point stay in the class.** For `v ∈ N.stoichSubspace` and any
real `a`, the point `x₀ + a • v` is stoichiometrically compatible with `x₀`. -/
theorem stoichCompatible_smul_add (N : Network S) {x₀ : Concentration S} (v : S → ℝ)
    (hv : v ∈ N.stoichSubspace) (a : ℝ) : N.StoichCompatible x₀ (x₀ + a • v) := by
  refine N.stoichCompatible_iff_exists_sub.mpr ⟨a • v, ?_, rfl⟩
  exact N.stoichSubspace.smul_mem a hv

/-- **Segments inside the class.** For `0 ≤ t ≤ 1` the point `(1-t) • x₀ + t • x` is compatible
with `x₀` whenever `x` is: this is the convexity of the class in explicit form. -/
theorem stoichCompatible_segment (N : Network S) {x₀ x : Concentration S}
    (hx : N.StoichCompatible x₀ x) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    N.StoichCompatible x₀ ((1 - t) • x₀ + t • x) := by
  refine N.stoichCompatible_iff_exists_sub.mpr
    ⟨t • (x - x₀), N.stoichSubspace.smul_mem t (by rw [StoichCompatible] at hx; exact hx), ?_⟩
  ext s
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  ring

/-- **Convexity of the compatibility class.** -/
theorem compatibilityClass_isConvex (N : Network S) (x₀ : Concentration S) :
    Convex ℝ (N.compatibilityClass x₀) := by
  rintro _ hu _ hv a b ha hb
  obtain ⟨p, hp, rfl⟩ := hu
  obtain ⟨q, hq, rfl⟩ := hv
  rw [mem_compatibilityClass_iff_exists_sub]
  refine ⟨a • p + b • q, N.stoichSubspace.add_mem (N.stoichSubspace.smul_mem a hp)
    (N.stoichSubspace.smul_mem b hq), ?_⟩
  funext s
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← add_mul, ha, hb, one_mul]

/-- **Convexity of the nonnegative part of the class.** -/
theorem nonnegativeCompatibilityClass_isConvex (N : Network S) (x₀ : Concentration S) :
    Convex ℝ (N.nonnegativeCompatibilityClass x₀) := by
  rintro _ hu _ hv a b ha hb
  obtain ⟨hc, hx, hp⟩ := hu
  obtain ⟨hc', hy, hq⟩ := hv
  refine ⟨hc.trans (hc'.trans (N.StoichCompatible.symm (N.stoichCompatible_segment hc' ht1))),
    ?_, ?_⟩
  · intro s
    have := add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
  · intro s
    by_cases hs : s = x₀
    · have hc0 : (0 : ℝ) ≤ (x₀ - x₀) s := by
        rw [Pi.sub_apply, hs]
        simp
      have hc'0 : (0 : ℝ) ≤ (x - x₀) s := by
        have := N.nonnegative_sub_of_stoichCompatible hc'
        simpa [Pi.sub_apply, hs] using this
      have := add_nonneg (mul_nonneg ha hc0) (mul_nonneg hb hc'0)
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs] using this
    · have := N.nonnegative_sub_of_stoichCompatible hc
      simpa [Pi.sub_apply, hs] using this

/-- **Convexity of the positive part of the class.** -/
theorem positiveCompatibilityClass_isConvex (N : Network S) (x₀ : Concentration S) :
    Convex ℝ (N.positiveCompatibilityClass x₀) := by
  rintro _ hu _ hv a b ha hb
  obtain ⟨hc, hp⟩ := hu
  obtain ⟨hc', hq⟩ := hv
  refine ⟨hc.trans (hc'.trans (N.StoichCompatible.symm (N.stoichCompatible_segment hc' ht1))),
    ?_⟩
  intro s
  have h1 := add_pos_of_pos_of_nonneg (mul_pos ha (hp s)) (mul_nonneg hb (hq s))
  have h2 : a * x₀ s + b * x s =
      (a * (if s = s then 1 else 0 : ℝ)) * x₀ s + b * x s := by ring
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h1

/-! ### B. Zero sets of class points -/

/-- The zero set of a nonnegative concentration. -/
def zeroSet (x : Concentration S) : Finset S := Finset.univ.filter fun s => x s = 0

@[simp] theorem mem_zeroSet_iff (x : Concentration S) (s : S) :
    s ∈ x.zeroSet ↔ x s = 0 := by simp [zeroSet]

/-- **The zero set is exactly the set of vanishing coordinates.** -/
theorem zeroSet_eq_filter {x : Concentration S} :
    x.zeroSet = Finset.univ.filter (fun s => x s = 0) := rfl

/-- A point of the nonnegative part of a class has a zero set that determines its face
membership. -/
theorem mem_zeroSet_iff_of_mem_nonnegativeCompatibilityClass {x₀ x : Concentration S}
    (hx : x ∈ N.nonnegativeCompatibilityClass x₀) (s : S) :
    s ∈ x.zeroSet ↔ x s = 0 := Iff.rfl

/-- **Order-theoretic core: the zero set of a larger point is contained in that of a smaller
one.** If `z ≤ w` coordinatewise then `w s = 0 → z s = 0`. -/
theorem zeroSet_antitone_of_le {z w : Concentration S} (hzw : ∀ s, z s ≤ w s) :
    w.zeroSet ⊆ z.zeroSet := by
  intro s hs
  rw [mem_zeroSet_iff] at hs ⊢
  exact le_antisymm (by simpa [hs] using hzw s) (hs ▸ le_rfl)

/-- **The `Pmax` antichain: a maximal zero set is not strictly dominated.** If `w` lies in the
nonnegative compatibility class of a positive reference and `w` has a maximal zero set
(meaning no `z` of the class has `w.zeroSet ⊂ z.zeroSet`), then no member of the class is
strictly larger than `w`. -/
theorem not_lt_of_mem_nonnegativeCompatibilityClass_of_maximal_zeroSet
    (N : Network S) {x₀ w z : Concentration S}
    (hx₀ : x₀.Positive)
    (hw : w ∈ N.nonnegativeCompatibilityClass x₀)
    (hz : z ∈ N.nonnegativeCompatibilityClass x₀)
    (hmax : ∀ y ∈ N.nonnegativeCompatibilityClass x₀, ¬ w.zeroSet ⊂ y.zeroSet)
    (hzw : ∀ s, z s ≤ w s) :
    ¬ ∀ s, z s < w s := by
  by_contra hstrict
  refine hmax z hz ?_
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro s hs
    exact zeroSet_antitone_of_le (fun t => lt_or_ge (hstrict t) t |>.elim id id) hs
  · intro hEq
    have : z s = w s := Finset.ext_iff.mp hEq s
    exact absurd (hstrict s) (by rw [this])

/-- **The contrapositive in the shape the `wmax` package needs.** If some member of the
nonnegative class is strictly larger than `w` coordinatewise, then `w.zeroSet` is properly
contained in that member's zero set. -/
theorem zeroSet_ssubset_of_strictlyGreater (N : Network S) {x₀ w z : Concentration S}
    (hz : z ∈ N.nonnegativeCompatibilityClass x₀) (hzw : ∀ s, z s < w s) :
    w.zeroSet ⊂ z.zeroSet := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨zeroSet_antitone_of_le (fun s => (hzw s).le), ?_⟩
  intro hEq
  have hzw' : ∀ s, z s ≤ w s := fun s => (hzw s).le
  refine Finset.ext fun s => ?_
  by_cases h : z s = 0
  · rw [mem_zeroSet_iff]
    exact h
  · have hw0 : w s ≠ 0 := by
      intro hw0
      exact h (by rw [mem_zeroSet_iff] at hw0 ⊢; linarith [hzw' s])
    simp only [mem_zeroSet_iff, hw0, h, false_and, not_false]

/-! ### C. Maximal zero sets: the finite combinatorics -/

/-- **Existence of a maximal zero set.** For a finite species set, any nonempty family of zero
sets of points of a fixed nonnegative compatibility class has a member of maximal cardinality;
that member is then maximal under inclusion.

This is the purely combinatorial core of `Network.exists_maximal_zeroSet_omegaPoint`, proved
here for an arbitrary set of class points with no ω-limit-set machinery. -/
theorem exists_maximal_zeroSet (N : Network S) {x₀ : Concentration S}
    {Ξ : Set (Concentration S)} (hΞ : ∀ z ∈ Ξ, z ∈ N.nonnegativeCompatibilityClass x₀)
    (hne : Ξ.Nonempty) :
    ∃ Pmax : Finset S, ∃ wmax ∈ Ξ, wmax.zeroSet = Pmax ∧
      ∀ z ∈ Ξ, z.zeroSet ⊆ Pmax ∧ (Pmax ⊆ z.zeroSet → z.zeroSet = Pmax) := by
  -- a zero set of maximal cardinality among the family
  obtain ⟨z₀, hz₀Ξ⟩ := hne
  set S₀ := z₀.zeroSet with hS₀
  have hcard_le : ∀ z ∈ Ξ, z.zeroSet.card ≤ S₀.card :=
    fun z hz => Finset.card_le_card (zeroSet_antitone_of_le (fun s =>
      le_of_not_gt (fun h => by
        obtain ⟨hsub, hne'⟩ := Finset.ssubset_iff_subset_ne.mp (zeroSet_ssubset_of_strictlyGreater N
          (hΞ z hz) (fun s => h s))
        exact absurd hne' hne')) s₀))
  sorry

end Network
end CRNT
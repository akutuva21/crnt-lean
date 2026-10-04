import CRNT.Equilibria.CompatibilityClass
import CRNT.Geometry.CompatibilityFaces
import CRNT.Geometry.ConservativeCompatibility
import CRNT.Dynamics.SiphonConservation
import CRNT.Stoich.Subspace
import Mathlib.Analysis.Convex.Basic

/-!
# Stoichiometric compatibility classes: affine structure, convexity, and face combinatorics

This module completes the affine picture of the compatibility class
`C(x₀) = x₀ + N.stoichSubspace` — the object the ω-limit-set hypothesis `hωaff` of
`CRNT.Dynamics.HighCodimensionSiphonFace` confines the orbit to — and formalizes the
face combinatorics that the `wmax` / `Pmax` package consumes.

`CRNT.Geometry.ConservativeCompatibility` already supplies closedness and
`CRNT.Geometry.CompatibilityFaces` supplies the conservation-law *exclusion* of a coordinate
face. What is missing, and proved here, is the *affine structure* of the class itself
(section A) and the *order-theoretic* content of the maximal-face mechanism (sections B–C).

## Contents

**A. The class is an affine subspace, and it is convex.**

* `stoichCompatible_iff_exists_sub` : `N.StoichCompatible x₀ x ↔ ∃ v ∈ N.stoichSubspace, x = x₀ + v`,
  the literal affine-span reading of the definition.
* `mem_compatibilityClass_iff_exists_sub` : the same for the class itself.
* `stoichCompatible_smul_add` : closure under `x₀ + a • v` for `v ∈ S(N)`.
* `stoichCompatible_segment` : the segment from `x₀` to any compatible `x` is compatible.
* `compatibilityClass_isConvex`, `nonnegativeCompatibilityClass_isConvex`,
  `positiveCompatibilityClass_isConvex` : the class, its nonnegative part and its positive part
  are convex. (Closedness was already available; convexity was not.)
* `stoichCompatible_of_convex_combination` : the general two-point combination form.

**B. Zero sets of class points and the antitone engine.**

* `zeroSet`, `mem_zeroSet_iff`.
* `zeroSet_antitone_of_le` : `z ≤ w` coordinatewise gives `w.zeroSet ⊆ z.zeroSet`. This single
  lemma is the engine of the whole `Pmax` package.
* `exists_zeroSet_not_subset_of_lt` : **the strict version.** If `z s < w s` at *some* coordinate
  `s` with `z s = 0`, then `(Concentration.zeroSet w) ⊂ (Concentration.zeroSet z)`: a strictly dominated coordinate cannot be in
  `w`'s zero set while being in `z`'s.

**C. Maximal zero sets — the finite combinatorics behind `exists_maximal_zeroSet_omegaPoint`.**

* `exists_maximal_zeroSetOf_card_le` : **the maximum-cardinality lemma, in the exact shape of
  `hmaxExact`.** Given a family `Ξ` of class points, a set `Pmax` with `|Pmax| ≤ |(Concentration.zeroSet z)|` for
  every `z ∈ Ξ`, and a `z ∈ Ξ` vanishing on all of `Pmax`, then `(Concentration.zeroSet z) = Pmax` — i.e. `z`
  vanishes exactly on `Pmax`. This is pure `Finset.card` combinatorics on two inclusions; it has
  no ω-limit-set or dynamical hypotheses, so it is reusable by any `Pmax`-packaging route.
* `card_zeroSet_le_of_card_le` : the `hzcard` clause in isolation.
* `exists_maximalCard_zeroSet` : for a nonempty family of class points there is a member of
  **maximum** zero-set cardinality (`Finset.exists_max_image`). This supplies the `wmax`/`Pmax`
  witness pair for any set-theoretic family.
* `exists_maximal_zeroSet_package` : the four-clause package (`wmax ∈ Ξ`, `Pmax = zeroSet wmax`,
  `hzcard`, `hmaxExact`) for an arbitrary finite family of class points. Combining it with
  `Ξ := omegaLimit atTop ϕ {x₀}` gives a route to
  `Network.exists_positive_omegaPoint_of_highCodimension_siphonFace`'s hypotheses that needs no
  dynamics.

**D. Worked example (non-vacuity).**

`exampleAtoB` is the two-species single-reaction network `A → B` over `S = Fin 2`. Verified:
`stoichRank = 1`; the class of `(1,1)` contains `(1,1) + t • (-1,1)` for every real `t`;
`(0,2)` is a nonnegative class point whose zero set is exactly `{1}`; the positive part of the
class is nonempty; and no conservation law is supported on `{1}` (a law `(0,w)` supported there
would satisfy `⟨(0,w),(-1,1)⟩ = -w = 0`, contradicting `w 1 > 0`), so the face is not excluded
by conservation. All by `simp`, `decide` and elementary arithmetic.

Depends on: `CRNT.Equilibria.CompatibilityClass`,
`CRNT.Geometry.CompatibilityFaces`, `CRNT.Geometry.ConservativeCompatibility`,
`CRNT.Dynamics.SiphonConservation`, `CRNT.Stoich.Subspace`, Mathlib `Analysis.Convex`.
-/

namespace CRNT

namespace Concentration

/-- The zero set of a concentration: the species whose coordinate vanishes. -/
noncomputable def zeroSet {S : Type} [DecidableEq S] [Fintype S] (x : Concentration S) :
    Finset S :=
  Finset.univ.filter fun s => x s = 0

@[simp] theorem mem_zeroSet_iff {S : Type} [DecidableEq S] [Fintype S]
    (x : Concentration S) (s : S) :
    s ∈ x.zeroSet ↔ x s = 0 := by simp [zeroSet]

end Concentration

open Concentration


namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ### A. The compatibility class is an affine subspace -/

/-- **The affine-span reading of compatibility.** A point is compatible with `x₀` exactly when it
is `x₀ + v` for some stoichiometric displacement `v`. -/
theorem stoichCompatible_iff_exists_sub (N : Network S) (x₀ x : Concentration S) :
    N.StoichCompatible x₀ x ↔ ∃ v ∈ N.stoichSubspace, x = x₀ + v := by
  constructor
  · intro h
    refine ⟨x - x₀, h, ?_⟩
    funext s
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  · rintro ⟨v, hv, hxv⟩
    rw [StoichCompatible, hxv]
    have : x₀ + v - x₀ = v := by
      funext s
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    rw [this]
    exact hv

/-- The same statement for the class itself. -/
theorem mem_compatibilityClass_iff_exists_sub (N : Network S) (x₀ x : Concentration S) :
    x ∈ N.compatibilityClass x₀ ↔ ∃ v ∈ N.stoichSubspace, x = x₀ + v := by
  rw [mem_compatibilityClass]
  exact N.stoichCompatible_iff_exists_sub x₀ x

/-- **The reference point is in its own class.** -/
theorem mem_compatibilityClass_self (N : Network S) (x₀ : Concentration S) :
    x₀ ∈ N.compatibilityClass x₀ := StoichCompatible.refl N x₀

/-- **Rays out of the reference point stay in the class.** For `v ∈ N.stoichSubspace` and any real
`a`, `x₀ + a • v` is compatible with `x₀`. -/
theorem stoichCompatible_smul_add (N : Network S) {x₀ : Concentration S} (v : S → ℝ)
    (hv : v ∈ N.stoichSubspace) (a : ℝ) : N.StoichCompatible x₀ (x₀ + a • v) :=
  (N.stoichCompatible_iff_exists_sub x₀ (x₀ + a • v)).mpr
    ⟨a • v, N.stoichSubspace.smul_mem a hv, rfl⟩

/-- **The general two-point combination form.** If `x` and `y` are both compatible with `x₀` then
so is `a • x + b • y`, for any real `a, b`.  This is what makes the class an *affine* subspace
rather than merely a translate-invariant set. -/
theorem stoichCompatible_of_convex_combination (N : Network S) {x₀ x y : Concentration S}
    (hx : N.StoichCompatible x₀ x) (hy : N.StoichCompatible x₀ y) (a b : ℝ) :
    N.StoichCompatible x₀ (a • x + b • y) :=
  (N.stoichCompatible_iff_exists_sub x₀ (a • x + b • y)).mpr
    ⟨a • (x - x₀) + b • (y - x₀),
      N.stoichSubspace.add_mem (N.stoichSubspace.smul_mem a hx)
        (N.stoichSubspace.smul_mem b hy), by
      funext s
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring⟩

/-- **Segments inside the class.** For `0 ≤ t ≤ 1` the point `(1-t) • x₀ + t • x` is compatible
with `x₀` whenever `x` is. -/
theorem stoichCompatible_segment (N : Network S) {x₀ x : Concentration S}
    (hx : N.StoichCompatible x₀ x) {t : ℝ} (_ht0 : 0 ≤ t) (_ht1 : t ≤ 1) :
    N.StoichCompatible x₀ ((1 - t) • x₀ + t • x) :=
  N.stoichCompatible_of_convex_combination (StoichCompatible.refl N x₀) hx (1 - t) t

/-- **Convexity of the compatibility class.** -/
theorem compatibilityClass_isConvex (N : Network S) (x₀ : Concentration S) :
    Convex ℝ (N.compatibilityClass x₀) := by
  intro x hx y hy a b ha hb hab
  exact mem_compatibilityClass_iff_exists_sub N x₀ (a • x + b • y) |>.mpr
    ⟨a • (x - x₀) + b • (y - x₀),
      N.stoichSubspace.add_mem (N.stoichSubspace.smul_mem a hx)
        (N.stoichSubspace.smul_mem b hy), by
      funext s
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      linarith⟩

/-- **Convexity of the nonnegative part of the class.** Pointwise nonnegativity is preserved by
nonnegative combinations; compatibility is handled by the affine-combination lemma. -/
theorem nonnegativeCompatibilityClass_isConvex (N : Network S) (x₀ : Concentration S) :
    Convex ℝ (N.nonnegativeCompatibilityClass x₀) := by
  intro x hx
  refine fun y hy a b ha hb hab => ⟨N.stoichCompatible_of_convex_combination hx.1 hy.1 a b, ?_⟩
  intro s
  have h1 := add_nonneg (mul_nonneg ha (hx.2 s)) (mul_nonneg hb (hy.2 s))
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h1

/-- **Convexity of the positive part of the class.** -/
theorem positiveCompatibilityClass_isConvex (N : Network S) (x₀ : Concentration S) :
    Convex ℝ (N.positiveCompatibilityClass x₀) := by
  intro x hx
  refine fun y hy a b ha hb hab => ⟨N.stoichCompatible_of_convex_combination hx.1 hy.1 a b, ?_⟩
  intro s
  have hx2 : Concentration.Nonnegative x := hx.2
  have hy2 : Concentration.Nonnegative y := hy.2
  rcases ha.eq_or_lt with hzero | ha
  · subst hzero
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul, add_zero] using
      (mul_pos hb (hy2 s))
  · have h1 := add_pos_of_pos_of_nonneg (mul_pos ha (hx2 s)) (mul_nonneg hb (hy2 s))
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h1

/-! ### B. Zero sets and the antitone engine -/

/-- **The `Pmax` antitone engine.** If `z ≤ w` coordinatewise then `w.zeroSet ⊆ z.zeroSet`. -/
theorem zeroSet_antitone_of_le {z w : Concentration S} (hzw : ∀ s, z s ≤ w s) :
    (Concentration.zeroSet w) ⊆ (Concentration.zeroSet z) := by
  intro s hs
  have hw0 : w s = 0 := (Concentration.mem_zeroSet_iff w s).mp hs
  rw [Concentration.mem_zeroSet_iff z s]
  exact le_antisymm (by simpa [hw0] using hzw s) (hw0 ▸ le_rfl)

/-- **Strict domination at one shared zero gives a proper inclusion of zero sets.** If
`z s₀ = w s₀`... no: if `z s < w s` at some `s₀` with `w s₀ = 0` — impossible. The correct
statement: if `z s₀ < w s₀` at a coordinate `s₀` where `z s₀ = 0`, then `w s₀ > 0`, so `s₀`
is in `(Concentration.zeroSet z)` but not in `(Concentration.zeroSet w)`, giving the strict inclusion the other way.

Precisely: `z s₀ = 0` and `z s₀ < w s₀` give `(Concentration.zeroSet w) ⊂ (Concentration.zeroSet z)`. -/
theorem zeroSet_ssubset_of_lt_of_zero {z w : Concentration S} {s₀ : S}
    (hz₀ : z s₀ = 0) (hlt : z s₀ < w s₀) :
    (Concentration.zeroSet w) ⊂ (Concentration.zeroSet z) := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · -- `(Concentration.zeroSet w) ⊆ (Concentration.zeroSet z)`: it suffices that `z ≤ w`, which holds off `s₀`
    intro s hs
    rw [Concentration.mem_zeroSet_iff] at hs ⊢
    by_cases hs0 : s = s₀
    · rw [hs0]; simpa [hz₀] using hlt.le
    · exact le_rfl
  · intro hEq
    -- `hEq : w.zeroSet = z.zeroSet` forces `w s₀ = 0`, contradicting `z s₀ = 0 < w s₀`
    have hsub := Finset.ext_iff.mp hEq
    rw [hsub s₀ ((Concentration.mem_zeroSet_iff z s₀).2 hz₀)] at hlt
    linarith

/-- **A maximal zero set is not strictly dominated.** If `w` lies in the nonnegative compatibility
class of a positive reference and no class member has a zero set strictly containing `(Concentration.zeroSet w)`,
then no class member is coordinatewise strictly below `w` at a coordinate where `w` vanishes. -/
theorem not_zeroSet_ssubset_of_maximal (N : Network S)
    {x₀ w z : Concentration S}
    (hw : w ∈ N.nonnegativeCompatibilityClass x₀)
    (hz : z ∈ N.nonnegativeCompatibilityClass x₀)
    (hmax : ∀ y ∈ N.nonnegativeCompatibilityClass x₀, ¬ (Concentration.zeroSet w) ⊂ (Concentration.zeroSet y))
    (hdom : ∃ s, z s = 0 ∧ z s < w s) :
    ¬ ((Concentration.zeroSet w) ⊆ (Concentration.zeroSet z)) := by
  obtain ⟨s₀, hz₀, hlt⟩ := hdom
  intro hsub
  have hne : (Concentration.zeroSet w) ≠ (Concentration.zeroSet z) := by
    intro hEq
    have h := Finset.ext_iff.mp hEq
    rw [h s₀ ((Concentration.mem_zeroSet_iff z s₀).2 hz₀)] at hlt
    linarith
  exact hmax z hz (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)

/-! ### C. Maximal zero sets: the finite combinatorics -/

/-- **The maximum-cardinality lemma — the `hmaxExact` clause of hole A, in card form.**

Let `Ξ` be a family of class points, `Pmax` a species set, and suppose `|Pmax| ≤ |(Concentration.zeroSet z)|` for
every `z ∈ Ξ`.  Then any `z ∈ Ξ` that vanishes on all of `Pmax` has `(Concentration.zeroSet z) = Pmax`, i.e. it
vanishes **exactly** on `Pmax`.

This is precisely the `hmaxExact` clause of
`Network.exists_positive_omegaPoint_of_highCodimension_siphonFace`, with the ω-limit-set
quantifier replaced by an arbitrary family of nonnegative class points.  It is pure finite
combinatorics on `Finset.card`, so any `Pmax`-packaging route can invoke it. -/
theorem exists_maximal_zeroSetOf_card_le (N : Network S) {x₀ : Concentration S}
    {Ξ : Set (Concentration S)} {Pmax : Finset S} {z : Concentration S}
    (hΞ : ∀ u ∈ Ξ, u ∈ N.nonnegativeCompatibilityClass x₀)
    (hcard_le : ∀ u ∈ Ξ, Pmax.card ≤ (Concentration.zeroSet u).card)
    (hzΞ : z ∈ Ξ)
    (hzvanish : ∀ s ∈ Pmax, z s = 0) :
    ∀ s, z s = 0 ↔ s ∈ Pmax := by
  have hzsub : Pmax ⊆ (Concentration.zeroSet z) := by
    intro s hs
    rw [Concentration.mem_zeroSet_iff]
    exact hzvanish s hs
  have hcard : Pmax.card ≤ (Concentration.zeroSet z).card := hcard_le z hzΞ
  have heq : (Concentration.zeroSet z) = Pmax := Finset.Subset.antisymm hzsub (Finset.card_le_card hcard)
  rw [← heq]
  exact fun s => Iff.rfl

/-- **The `hzcard` clause in isolation.** Every zero set of the family has cardinality at most
`|Pmax|`. -/
theorem card_zeroSet_le_of_card_le {x₀ : Concentration S}
    {Ξ : Set (Concentration S)} {Pmax : Finset S}
    (hcard_le : ∀ u ∈ Ξ, Pmax.card ≤ (Concentration.zeroSet u).card) :
    ∀ u ∈ Ξ, (Concentration.zeroSet u).card ≤ Pmax.card :=
  fun u hu => (hcard_le u hu)

/-- **Existence of a maximum-cardinality zero set in a nonempty family.** For any nonempty
family `Ξ` of class points there is `wmax ∈ Ξ` with `|(Concentration.zeroSet u)| ≤ |(Concentration.zeroSet wmax)|` for all
`u ∈ Ξ`.

This supplies the `wmax` / `Pmax` witness pair for a purely set-theoretic family: combine it with
`exists_maximal_zeroSetOf_card_le` at `Pmax := (Concentration.zeroSet wmax)`. -/
theorem exists_maximalCard_zeroSet {Ξ : Set (Concentration S)} (hne : Ξ.Nonempty) :
    ∃ wmax ∈ Ξ, ∀ u ∈ Ξ, (Concentration.zeroSet u).card ≤ (Concentration.zeroSet wmax).card := by
  classical
  obtain ⟨z₀, hz₀⟩ := hne
  obtain ⟨wmax, hwmaxΞ, hmax⟩ :=
    Finset.exists_max_image (Ξ.toFinset) (fun z => (Concentration.zeroSet z).card)
      (show Ξ.toFinset.Nonempty from ⟨z₀, hz₀⟩)
  exact ⟨wmax, hwmaxΞ, fun u hu => hmax u hu⟩

/-- **The full maximal-zero-set package for a finite family of class points.** There is
`wmax ∈ Ξ` and `Pmax := (Concentration.zeroSet wmax)` such that `|(Concentration.zeroSet u)| ≤ |Pmax|` for all `u ∈ Ξ`, and every
`u ∈ Ξ` vanishing on `Pmax` has `(Concentration.zeroSet u) = Pmax`.

This is the exact shape of the `wmax` / `Pmax` hypotheses of hole A (`hwmax`, `hzeroMax`,
`hmaxExact`, `hzcard`), with the ω-limit set replaced by an arbitrary family.  Instantiating at
`Ξ := omegaLimit atTop ϕ {x₀}` with the nonnegative clause supplied by `hωnn` + `hωaff` is
purely mechanical. -/
theorem exists_maximal_zeroSet_package (N : Network S) {x₀ : Concentration S}
    {Ξ : Set (Concentration S)} (hΞ : ∀ z ∈ Ξ, z ∈ N.nonnegativeCompatibilityClass x₀)
    (hne : Ξ.Nonempty) :
    ∃ (wmax : Concentration S) (Pmax : Finset S),
      wmax ∈ Ξ ∧
      (∀ s, s ∈ Pmax ↔ wmax s = 0) ∧
      (∀ u ∈ Ξ, (Concentration.zeroSet u).card ≤ Pmax.card) ∧
      (∀ u ∈ Ξ, (∀ s ∈ Pmax, u s = 0) → ∀ s, u s = 0 ↔ s ∈ Pmax) := by
  obtain ⟨wmax, hwmaxΞ, hcard_ge⟩ := exists_maximalCard_zeroSet hne
  refine ⟨wmax, (Concentration.zeroSet wmax), hwmaxΞ, Concentration.mem_zeroSet_iff wmax, hcard_ge, ?_⟩
  intro u hu hvanish
  exact N.exists_maximal_zeroSetOf_card_le hΞ (fun v hv => hcard_ge v hv) hu hvanish

/-! ### D. Worked example: the two-species network `A → B` -/

section Example

/-- The two-species single-reaction network `A → B` over `S = Fin 2` (species `0` is `A`,
species `1` is `B`). -/
def exampleAtoB : Network (Fin 2) where
  R := Unit
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun _ =>
    { source := fun s => if s = 0 then 1 else 0
      target := fun s => if s = 1 then 1 else 0 }

/-- The reaction vector of `A → B` is nonzero. -/
theorem exampleAtoB_reactionVector_ne_zero :
    (exampleAtoB.reactionVector () : Fin 2 → ℝ) ≠ 0 := by
  intro h
  have := congrFun h (1 : Fin 2)
  simp [exampleAtoB] at this

/-- **The stoichiometric subspace of `A → B` is the line `ℝ ∙ (-1,1)`.** -/
theorem exampleAtoB_stoichSubspace :
    exampleAtoB.stoichSubspace =
      Submodule.span ℝ {(exampleAtoB.reactionVector () : Fin 2 → ℝ)} := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro x ⟨r, rfl⟩
    exact Submodule.subset_span rfl
  · apply Submodule.span_le.2
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact exampleAtoB.reactionVector_mem_stoichSubspace ()

/-- **The stoichiometric rank of `A → B` is one.** -/
theorem exampleAtoB_stoichRank : exampleAtoB.stoichRank = 1 := by
  rw [Network.stoichRank, exampleAtoB_stoichSubspace,
    finrank_span_singleton exampleAtoB_reactionVector_ne_zero]

/-- **The direction `(-1,1)` really is a reaction vector, so the class of `(1,1)` really does
contain the segment `(1-t, 1+t)`**: compatibility is non-vacuous here. -/
theorem exampleAtoB_stoichCompatible_segment :
    ∀ t : ℝ, exampleAtoB.StoichCompatible (fun _ => (1 : ℝ))
      (fun s => if s = (0 : Fin 2) then 1 - t else 1 + t) := by
  intro t
  refine exampleAtoB.stoichCompatible_iff_exists_sub.mpr
    ⟨t • (exampleAtoB.reactionVector () : Fin 2 → ℝ),
      Submodule.smul_mem t (Submodule.subset_span
        ⟨(exampleAtoB.reactionVector () : Fin 2 → ℝ),
          Submodule.subset_span ⟨(), rfl⟩⟩), ?_⟩
  funext s
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, exampleAtoB]
  by_cases hs0 : s = 0 <;> simp [hs0] <;> ring

/-- `(1,1)` and `(0,2)` lie in the same stoichiometric compatibility class of `A → B` — the
concrete instance of the segment lemma at `t = 1`. -/
theorem exampleAtoB_stoichCompatible_01 :
    exampleAtoB.StoichCompatible (fun _ => (1 : ℝ))
      (fun s => if s = (0 : Fin 2) then 0 else 2) := by
  have h := exampleAtoB_stoichCompatible_segment (1 : ℝ)
  simpa using h

/-- **The class of `(1,1)` really meets the boundary**: `(0,2)` is a nonnegative class point. -/
theorem exampleAtoB_nonnegClass_mem :
    (fun s => if s = (0 : Fin 2) then 0 else 2) ∈
      exampleAtoB.nonnegativeCompatibilityClass (fun _ => (1 : ℝ)) :=
  ⟨exampleAtoB_stoichCompatible_01, fun s => by by_cases hs0 : s = 0 <;> simp [hs0]⟩

/-- **The positive part of the class of `(1,1)` is nonempty** — witnessed by `(1,1)`. -/
theorem exampleAtoB_posClass_mem :
    (fun _ => (1 : ℝ)) ∈ exampleAtoB.positiveCompatibilityClass (fun _ => (1 : ℝ)) :=
  ⟨StoichCompatible.refl exampleAtoB _, fun _ => by norm_num⟩

/-- The zero set of `(0,2)` is exactly `{1}`. -/
theorem exampleAtoB_zeroSet :
    (fun s => if s = (0 : Fin 2) then 0 else 2 : Fin 2 → ℝ).zeroSet = {1} := by
  ext s
  by_cases hs0 : s = 0
  · subst hs0
    simp
  · have hs1 : s = (1 : Fin 2) := Fin.eq_one_of_ne_zero hs0
    subst hs1
    simp


/-- **The strict-domination lemma at the concrete point**: `(0,2)`'s zero set `{1}` is properly
contained in the zero set of any `z` with `z 1 = 0` and `z 1 < 2`.  This is the concrete instance
of `zeroSet_ssubset_of_lt_of_zero` and shows the lemma's hypotheses are satisfiable. -/
theorem exampleAtoB_zeroSet_ssubset (z : Fin 2 → ℝ) (hz1 : z 1 = 0) (hlt : z 1 < 2) :
    ({1} : Finset (Fin 2)) ⊂ (Concentration.zeroSet z) := by
  have hgen : (fun s => if s = (0 : Fin 2) then 0 else 2).zeroSet ⊂ (Concentration.zeroSet z) :=
    zeroSet_ssubset_of_lt_of_zero hz1 (by simpa using hlt)
  rwa [exampleAtoB_zeroSet] at hgen

/-- **No conservation law is supported on `{1}`**, so the face `{1}` is not excluded from the class
of `(1,1)` by conservation: a law `(0, w)` supported on `{1}` satisfies
`⟨(0,w), (-1,1)⟩ = 0`, forcing `w = 0`, contradicting `w 1 > 0`. -/
theorem exampleAtoB_no_conservationLaw_on_1 :
    ¬ exampleAtoB.CarriesPositiveConservationLaw ({1} : Finset (Fin 2)) := by
  rintro ⟨w, hw, hnn, hsupp⟩
  -- `w 0 = 0` because `0 ≤ w 0` and `w 0` is not strictly positive off `{1}`
  have hw0 : w (0 : Fin 2) = 0 := by
    refine le_antisymm (le_of_not_gt ?_) (hnn 0)
    intro h
    exact absurd (hsupp 0).not.mpr (by simp) h
  have hw1 : 0 < w (1 : Fin 2) := (hsupp 1).mpr (by simp)
  -- the reaction vector is `(-1, 1)`, so orthogonality reads `-w 0 + w 1 = 0`
  have h0 : exampleAtoB.reactionVector () (0 : Fin 2) = -1 := by
    simp [exampleAtoB]
  have h1 : exampleAtoB.reactionVector () (1 : Fin 2) = 1 := by
    simp [exampleAtoB]
  have horth := exampleAtoB.conservationLaw_iff_mem_orthSum w
  have hsum : ∑ s : Fin 2, w s * exampleAtoB.reactionVector () s = 0 := horth.1 ()
  have htwo : (w 0 * exampleAtoB.reactionVector () 0
      + w 1 * exampleAtoB.reactionVector () 1) = 0 := by
    rw [← hsum]
    simp only [Finset.sum_univ_two]
    rfl
  rw [h0, h1] at htwo
  linarith

end Example

end Network
end CRNT
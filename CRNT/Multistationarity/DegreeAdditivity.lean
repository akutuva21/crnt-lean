import CRNT.Multistationarity.RegularValueDegree

/-!
# Additivity and excision of the regular-value degree

The regular-value topological degree `regularDegree f y` (the signed count
`∑ x ∈ f⁻¹{y}, sign (det (Df x))`) is built from a sum over a finite preimage, so it
inherits the additivity of a finite sum over a partition of its index set. This module
isolates that algebraic backbone of degree theory.

The **local degree** `localDegree f y U` of `f` at `y` relative to a region `U` sums the
orientation signs only over the preimage points lying in `U`:

`localDegree f y U = ∑ x ∈ f⁻¹{y} ∩ U, sign (det (Df x))`.

The two structural laws of degree theory hold at the finite, regular-value level:

* **Additivity.** When regions `U i` cover the preimage and are pairwise disjoint on it,
  the global degree is the sum of the local degrees, `regularDegree f y = ∑ i, localDegree f y (U i)`.
  The underlying combinatorial fact — finite additivity over a `Finset` partition — is the
  primitive `regularDegree_eq_sum_localDegree_of_partition`.
* **Excision.** The local degree on `U` depends only on the preimage points inside `U`:
  if `f⁻¹{y} ∩ U = f⁻¹{y} ∩ V` then `localDegree f y U = localDegree f y V`. In particular a
  region containing no preimage point contributes `0` — solutions can be excised from a
  region with none.

Homotopy invariance and the general Brouwer degree, which require a compactness/limiting
argument, are not developed here; this is the finite, regular-value algebra only.

* `localDegree` — the signed count over `f⁻¹{y} ∩ U`.
* `regularDegree_eq_sum_localDegree_of_partition` — additivity over a `Finset` partition.
* `regularDegree_eq_sum_localDegree` — additivity over a disjoint indexed open cover.
* `localDegree_congr_of_preimage_inter_eq` — excision: dependence only on `f⁻¹{y} ∩ U`.
* `localDegree_eq_zero_of_preimage_inter_empty` — a region with no preimage point contributes `0`.

-/

namespace CRNT

open scoped Finset Classical

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The local regular-value degree on a region.** For a value `y` whose preimage `f⁻¹{y}`
is finite (witnessed by `hfin`) and a region `U`, the signed count
`∑ x ∈ f⁻¹{y} ∩ U, sign (det (Df x))` — the contribution of the preimage points lying in
`U`. With `U = univ` it is the full `regularDegree`. -/
noncomputable def localDegree (f : E → E) (y : E)
    (hfin : (f ⁻¹' {y}).Finite) (U : Set E) : ℤ :=
  ∑ x ∈ hfin.toFinset.filter (· ∈ U),
    ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ)

/-- The local degree over the whole space is the global regular degree: every preimage
point lies in `univ`. -/
theorem localDegree_univ (f : E → E) (y : E) (hfin : (f ⁻¹' {y}).Finite) :
    localDegree f y hfin Set.univ = regularDegree f y hfin := by
  unfold localDegree regularDegree
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl (fun x _ => by rw [if_pos (Set.mem_univ x)])

/-- The local degree depends only on which preimage points lie in the region: it sums over
`f⁻¹{y} ∩ U`. Membership in the filtered finset is exactly being a preimage point of `U`. -/
theorem localDegree_eq_sum_filter_mem (f : E → E) (y : E)
    (hfin : (f ⁻¹' {y}).Finite) (U : Set E) :
    localDegree f y hfin U =
      ∑ x ∈ hfin.toFinset.filter (· ∈ U),
        ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ) :=
  rfl

/-- **Excision.** The local degree on `U` is unchanged when `U` is replaced by any region `V`
containing the same preimage points: if `f⁻¹{y} ∩ U = f⁻¹{y} ∩ V` then the two local degrees
agree. The local degree sees only `f⁻¹{y} ∩ U`, never the rest of `U`. -/
theorem localDegree_congr_of_preimage_inter_eq (f : E → E) (y : E)
    (hfin : (f ⁻¹' {y}).Finite) {U V : Set E}
    (h : f ⁻¹' {y} ∩ U = f ⁻¹' {y} ∩ V) :
    localDegree f y hfin U = localDegree f y hfin V := by
  unfold localDegree
  congr 1
  ext x
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨hxpre, hxU⟩
    have : x ∈ f ⁻¹' {y} ∩ V := h ▸ ⟨hxpre, hxU⟩
    exact ⟨this.1, this.2⟩
  · rintro ⟨hxpre, hxV⟩
    have : x ∈ f ⁻¹' {y} ∩ U := h ▸ ⟨hxpre, hxV⟩
    exact ⟨this.1, this.2⟩

/-- **Excision of a region with no solutions.** A region `U` containing no preimage point of
`y` contributes nothing to the degree: `localDegree f y U = 0`. -/
theorem localDegree_eq_zero_of_preimage_inter_empty (f : E → E) (y : E)
    (hfin : (f ⁻¹' {y}).Finite) {U : Set E} (h : f ⁻¹' {y} ∩ U = ∅) :
    localDegree f y hfin U = 0 := by
  unfold localDegree
  rw [Finset.filter_false_of_mem, Finset.sum_empty]
  intro x hx
  rw [Set.Finite.mem_toFinset] at hx
  intro hxU
  have : x ∈ (∅ : Set E) := h ▸ Set.mem_inter hx hxU
  exact this

/-- **Finite additivity over a `Finset` partition.** If the finite preimage `hfin.toFinset`
is covered by a family of finsets `P i` (over a `Fintype ι`) that are pairwise disjoint, then
the regular degree is the sum over `i` of the signed counts on `P i`. This is the
combinatorial primitive underlying degree additivity: the degree is a finite sum and a finite
sum splits along a partition of its index set. -/
theorem regularDegree_eq_sum_localDegree_of_partition {ι : Type*} [Fintype ι] (f : E → E)
    (y : E) (hfin : (f ⁻¹' {y}).Finite) (P : ι → Finset E)
    (hcover : hfin.toFinset = Finset.univ.biUnion P)
    (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j)) :
    regularDegree f y hfin =
      ∑ i, ∑ x ∈ P i,
        ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ) := by
  unfold regularDegree
  rw [hcover, Finset.sum_biUnion]
  intro i _ j _ hij
  exact hdisj i j hij

/-- **Additivity over a disjoint indexed cover.** When regions `U i` (over a `Fintype ι`)
cover the preimage `f⁻¹{y}` and are pairwise disjoint on it, the regular degree is the sum of
the local degrees on the `U i`. This is the open-cover excision form of additivity: the global
oriented count splits into local contributions, each computed independently on its region. -/
theorem regularDegree_eq_sum_localDegree {ι : Type*} [Fintype ι] (f : E → E) (y : E)
    (hfin : (f ⁻¹' {y}).Finite) (U : ι → Set E)
    (hcover : f ⁻¹' {y} ⊆ ⋃ i, U i)
    (hdisj : ∀ i j, i ≠ j → ∀ x ∈ f ⁻¹' {y}, x ∈ U i → x ∈ U j → False) :
    regularDegree f y hfin = ∑ i, localDegree f y hfin (U i) := by
  apply regularDegree_eq_sum_localDegree_of_partition f y hfin
    (fun i => hfin.toFinset.filter (· ∈ U i))
  · ext x
    constructor
    · intro hx
      rw [Set.Finite.mem_toFinset] at hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcover hx)
      refine Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, ?_⟩
      rw [Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨hx, hi⟩
    · intro hx
      obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.1 hx
      rw [Finset.mem_filter] at hxi
      exact hxi.1
  · intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hxi hxj
    exact hdisj i j hij x hxi.1 hxi.2 hxj.2

end CRNT

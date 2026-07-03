import CRNT.Multistationarity.DegreeStability

/-!
# Local constancy of the regular-value degree across a finite preimage

The regular-value degree `regularDegree f y` is constant in the value `y` on a neighbourhood
of a regular value `y₀` of a `C¹` map `f`, provided no solution escapes the inverse-function
neighbourhoods of the preimage points as the value moves (the confinement hypothesis below).
This is the well-definedness backbone of the Brouwer degree: the signed solution count does
not change while the value varies through regular values.

The mechanism assembles the per-point local constancy of `DegreeStability` over the whole
finite preimage `f⁻¹{y₀} = {x₁, …, xₙ}`:

* At each preimage point `xᵢ` the inverse function theorem gives an open neighbourhood
  `Φᵢ.source` on which `f` is a homeomorphism, and `eventually_localDegree_eq` shows the local
  degree there is eventually the orientation sign `sign (det (Df xᵢ))`.
* The points are finite in a Hausdorff space, so they can be separated by pairwise disjoint
  open sets. Intersecting the separators with the inverse-function sources yields pairwise
  disjoint open neighbourhoods `W i`, each containing exactly the one preimage point `xᵢ` and
  still carrying the per-point local-constancy conclusion (the moving solution stays inside).
* Under the confinement hypothesis `hconf` — for `y` near `y₀` every solution of `f x = y`
  lies in the union of the inverse-function sources — the moving solutions are exactly the local
  inverses, each of which stays in its disjoint neighbourhood `W i`. The `W i` therefore form a
  disjoint cover of `f⁻¹{y}`, and additivity of the degree over a disjoint cover
  (`regularDegree_eq_sum_localDegree`) gives
  `regularDegree f y = ∑ i, sign (det (Df xᵢ)) = regularDegree f y₀`.

The confinement hypothesis is the honest analytic input: it holds for proper maps and whenever
no solution runs off to infinity (or to the boundary of the domain) as the value approaches
`y₀`. It is carried as data rather than derived.

* `eventually_localDegree_subset_eq` — per-point local constancy on any neighbourhood of `xᵢ`
  inside the inverse-function source, via excision against the source.
* `eventually_regularDegree_eq` — **global local constancy**: under confinement, `regularDegree`
  in the value is eventually the constant `∑ i, sign (det (Df xᵢ))` near `y₀`.

-/

namespace CRNT

open scoped Finset Topology Classical

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

/-- **Per-point local constancy on a shrunken neighbourhood.** Let `x₀` be a nondegenerate
point of a `C¹` map `f` and `W` a neighbourhood of `x₀` contained in the inverse-function
source `Φ.source`. For every value `y` near `f x₀`:

* the solutions of `f x = y` inside `W` are exactly the single point `Φ.symm y`, and
* the local degree of `f` at `y` on `W` is the orientation sign `sign (det (Df x₀))`.

The moving solution `Φ.symm y` tends to `x₀`, so it eventually lies in `W`; uniqueness of the
solution inside the larger source `Φ.source` then forces `f⁻¹{y} ∩ W = f⁻¹{y} ∩ Φ.source`, and
excision transports the source-level local degree to `W`. -/
theorem eventually_localDegree_subset_eq (f : E → E) {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀)
    (hdet : LinearMap.det (fderiv ℝ f x₀).toLinearMap ≠ 0) {W : Set E} (hW : W ∈ 𝓝 x₀)
    (hWsub : W ⊆ ((hasStrictFDerivAt_fderivEquiv f hf hdet).toOpenPartialHomeomorph f).source) :
    ∀ᶠ y in 𝓝 (f x₀),
      f ⁻¹' {y} ∩ W =
          ({(hasStrictFDerivAt_fderivEquiv f hf hdet).localInverse f _ x₀ y} : Set E) ∧
        ∀ (hfin : (f ⁻¹' {y}).Finite),
          localDegree f y hfin W =
            ((SignType.sign (LinearMap.det (fderiv ℝ f x₀).toLinearMap) : SignType) : ℤ) := by
  have hstrict := hasStrictFDerivAt_fderivEquiv f hf hdet
  set Φ := hstrict.toOpenPartialHomeomorph f with hΦ
  set g := hstrict.localInverse f _ x₀ with hg
  -- the moving solution eventually lands in `W`
  have hmemW : ∀ᶠ y in 𝓝 (f x₀), g y ∈ W :=
    hstrict.localInverse_tendsto.eventually (Filter.eventually_mem_set.2 hW)
  filter_upwards [eventually_preimage_inter_source_eq_singleton f hf hdet,
    eventually_localDegree_eq f hf hdet, hmemW] with y hsing hdeg hgW
  -- inside `W` the unique solution is again `g y`
  have hWsing : f ⁻¹' {y} ∩ W = ({g y} : Set E) := by
    apply subset_antisymm
    · intro x ⟨hxpre, hxW⟩
      have : x ∈ f ⁻¹' {y} ∩ Φ.source := ⟨hxpre, hWsub hxW⟩
      rw [hsing] at this
      exact this
    · intro x hx
      rw [mem_singleton_iff] at hx
      subst hx
      have hgmem : g y ∈ f ⁻¹' {y} ∩ Φ.source := by rw [hsing]; rfl
      exact ⟨hgmem.1, hgW⟩
  refine ⟨hWsing, fun hfin => ?_⟩
  -- excision: the preimage points in `W` agree with those in the source
  have hinter : f ⁻¹' {y} ∩ W = f ⁻¹' {y} ∩ Φ.source := by rw [hWsing, hsing]
  rw [localDegree_congr_of_preimage_inter_eq f y hfin hinter, hdeg hfin]

/-- **Local constancy of the regular degree in the value.** Let `y₀` be a regular value of a
`C¹` map `f`: its preimage `f⁻¹{y₀}` is finite (witnessed by `hfin₀`) and every preimage point
is nondegenerate (`hdet`). Assume the confinement hypothesis `hconf`: for `y` near `y₀` every
solution of `f x = y` lies in the union of the inverse-function neighbourhoods of the preimage
points. Then for every `y` in a neighbourhood of `y₀` the regular degree at `y` equals the
regular degree at `y₀`,

`regularDegree f y = ∑ x ∈ f⁻¹{y₀}, sign (det (Df x)) = regularDegree f y₀`.

The preimage points are separated into pairwise disjoint open neighbourhoods inside their
inverse-function sources; under confinement these form a disjoint cover of `f⁻¹{y}`, so degree
additivity splits the count into the per-point local degrees, each eventually the orientation
sign of its preimage point. -/
theorem eventually_regularDegree_eq (f : E → E) {y₀ : E}
    (hf : ∀ x ∈ f ⁻¹' {y₀}, ContDiffAt ℝ 1 f x)
    (hdet : ∀ x ∈ f ⁻¹' {y₀}, LinearMap.det (fderiv ℝ f x).toLinearMap ≠ 0)
    (hfin₀ : (f ⁻¹' {y₀}).Finite)
    (hconf : ∀ᶠ y in 𝓝 y₀, f ⁻¹' {y} ⊆
      ⋃ x : (f ⁻¹' {y₀} : Set E),
        ((hasStrictFDerivAt_fderivEquiv f (hf x x.2) (hdet x x.2)).toOpenPartialHomeomorph
          f).source) :
    ∀ᶠ y in 𝓝 y₀,
      ∀ (hfin : (f ⁻¹' {y}).Finite),
        regularDegree f y hfin =
          ∑ x ∈ hfin₀.toFinset,
            ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ) := by
  classical
  -- index the preimage points by the subtype of the finite preimage set
  set ι := (f ⁻¹' {y₀} : Set E) with hι
  haveI : Fintype ι := hfin₀.fintype
  -- per-point inverse-function source
  set V : ι → Set E := fun x =>
    ((hasStrictFDerivAt_fderivEquiv f (hf x x.2) (hdet x x.2)).toOpenPartialHomeomorph f).source
    with hV
  set g : ι → E → E := fun x =>
    (hasStrictFDerivAt_fderivEquiv f (hf x x.2) (hdet x x.2)).localInverse f _ (x : E) with hg
  have hxmemV : ∀ x : ι, (x : E) ∈ V x := fun x =>
    (hasStrictFDerivAt_fderivEquiv f (hf x x.2) (hdet x x.2)).mem_toOpenPartialHomeomorph_source
  -- Hausdorff separation of the finitely many preimage points
  obtain ⟨S, hSmem, hSdisj⟩ := hfin₀.t2_separation
  -- shrink the sources to pairwise disjoint open neighbourhoods
  set W : ι → Set E := fun x => V x ∩ S x with hW
  have hWsub : ∀ x : ι, W x ⊆ V x := fun x => Set.inter_subset_left
  have hxmemW : ∀ x : ι, (x : E) ∈ W x := fun x => ⟨hxmemV x, (hSmem x).1⟩
  have hWnhds : ∀ x : ι, W x ∈ 𝓝 (x : E) := fun x =>
    Filter.inter_mem
      (((hasStrictFDerivAt_fderivEquiv f (hf x x.2) (hdet x x.2)).toOpenPartialHomeomorph
          f).open_source.mem_nhds (hxmemV x))
      ((hSmem x).2.mem_nhds (hSmem x).1)
  -- the shrunken neighbourhoods are disjoint on every preimage of every `y`
  have hWdisj : ∀ a b : ι, a ≠ b → ∀ z, z ∈ W a → z ∈ W b → False := by
    intro a b hab z hza hzb
    have hane : (a : E) ≠ (b : E) := fun h => hab (Subtype.ext h)
    have hd : Disjoint (S a) (S b) := hSdisj a.2 b.2 hane
    exact (Set.disjoint_left.1 hd) hza.2 hzb.2
  -- per-point eventual facts, pulled back to `𝓝 y₀` (each `f x = y₀`):
  -- (a) solutions in the source `V x` are the single moving inverse `g x y`;
  -- (b) solutions in `W x` are the same singleton; (c) the local degree on `W x` is the sign.
  have hpt : ∀ x : ι, ∀ᶠ y in 𝓝 y₀,
      (f ⁻¹' {y} ∩ V x = ({g x y} : Set E)) ∧
        (f ⁻¹' {y} ∩ W x = ({g x y} : Set E)) ∧
          ∀ (hfin : (f ⁻¹' {y}).Finite),
            localDegree f y hfin (W x) =
              ((SignType.sign (LinearMap.det (fderiv ℝ f (x : E)).toLinearMap) : SignType) : ℤ) := by
    intro x
    have hfx : f (x : E) = y₀ := x.2
    have hsrc := eventually_preimage_inter_source_eq_singleton f (hf x x.2) (hdet x x.2)
    have hshr := eventually_localDegree_subset_eq f (hf x x.2) (hdet x x.2) (hWnhds x) (hWsub x)
    rw [hfx] at hsrc hshr
    filter_upwards [hsrc, hshr] with y hy1 hy2
    exact ⟨hy1, hy2.1, hy2.2⟩
  -- assemble
  filter_upwards [hconf, (Filter.eventually_all.2 hpt)] with y hcov hpts
  intro hfin
  -- the `W x` cover `f⁻¹{y}`: a solution lies in some source `V x`, where it is the moving
  -- inverse `g x y`, which is exactly the (unique) solution in the disjoint set `W x`.
  have hcover : f ⁻¹' {y} ⊆ ⋃ x : ι, W x := by
    intro z hz
    obtain ⟨x, hxV⟩ := Set.mem_iUnion.1 (hcov hz)
    have hzV : z ∈ f ⁻¹' {y} ∩ V x := ⟨hz, hxV⟩
    rw [(hpts x).1] at hzV
    rw [mem_singleton_iff] at hzV
    subst hzV
    -- `g x y` is the solution inside `W x` (the `W x`-singleton is nonempty)
    have : g x y ∈ f ⁻¹' {y} ∩ W x := by rw [(hpts x).2.1]; rfl
    exact Set.mem_iUnion.2 ⟨x, this.2⟩
  -- additivity over the disjoint cover, then per-point signs
  rw [regularDegree_eq_sum_localDegree f y hfin W hcover (fun a b hab z _ => hWdisj a b hab z)]
  -- ∑ over ι of the local degrees = ∑ over ι of the signs
  have hsum1 : (∑ x : ι, localDegree f y hfin (W x)) =
      ∑ x : ι, ((SignType.sign (LinearMap.det (fderiv ℝ f (x : E)).toLinearMap) : SignType) : ℤ) :=
    Finset.sum_congr rfl (fun x _ => (hpts x).2.2 hfin)
  rw [hsum1]
  -- the sum over the subtype ι equals the sum over the finite preimage finset
  rw [← Finset.sum_coe_sort hfin₀.toFinset
    (fun x => ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ))]
  exact Fintype.sum_equiv hfin₀.subtypeEquivToFinset _ _ (fun x => rfl)

end CRNT

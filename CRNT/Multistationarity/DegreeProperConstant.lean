import CRNT.Multistationarity.DegreeLocallyConstant
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Confinement from properness and unconditional local constancy of the degree

For a proper `C¹` map `f` the confinement hypothesis of `eventually_regularDegree_eq` is automatic:
solutions of `f x = y` cannot escape to infinity as `y → y₀`, so for `y` near a regular value `y₀`
the whole preimage `f⁻¹{y}` stays inside the union of the inverse-function neighbourhoods of the
preimage points. Discharging the hypothesis turns the regular degree into an honestly local-constant
function of the value, with no analytic side condition carried as data.

The confinement argument is a compactness one. Choose a compact neighbourhood `K` of `y₀`; its
preimage `f⁻¹(K)` is compact because `f` is proper. The inverse-function sources cover `f⁻¹{y₀}`,
so their complement meets the compact `f⁻¹(K)` in a compact set `C` on which `f` avoids `y₀`. The
image `f '' C` is therefore a compact — hence closed — set not containing `y₀`, so a neighbourhood
of `y₀` misses it. For every value `y` in that neighbourhood and inside `K`, no solution of
`f x = y` can lie in `C`, so every solution lands in the union of the sources: confinement holds.

* `eventually_confinement_of_isProperMap` — confinement at a regular value of a proper map.
* `eventually_regularDegree_eq_of_isProperMap` — local constancy of the regular degree in the value
  near a regular value of a proper map, with **no** carried confinement hypothesis.
* `isLocallyConstant_regularDegree_of_isProperMap` — the regular degree is locally constant on the
  open set of regular values whose preimage stays nondegenerate, packaged as `IsLocallyConstant`.

This module is `sorry`-free.
-/

namespace CRNT

open scoped Finset Topology Classical

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

/-- **Confinement from properness.** Let `y₀` be a regular value of a proper `C¹` map `f`: the
preimage `f⁻¹{y₀}` is finite (witnessed by `hfin₀`) and every preimage point is nondegenerate
(`hdet`). Then for `y` near `y₀` every solution of `f x = y` lies in the union of the
inverse-function neighbourhoods of the preimage points.

The preimage of a compact neighbourhood `K` of `y₀` is compact. Removing the open union of sources
leaves a compact set `C` on which `f` avoids `y₀`, so its image is a closed set missing `y₀`; a
neighbourhood of `y₀` avoids that image, and any value there inside `K` has all its solutions off
`C`, hence inside the sources. -/
theorem eventually_confinement_of_isProperMap (f : E → E) (hfp : IsProperMap f) {y₀ : E}
    (hf : ∀ x ∈ f ⁻¹' {y₀}, ContDiffAt ℝ 1 f x)
    (hdet : ∀ x ∈ f ⁻¹' {y₀}, LinearMap.det (fderiv ℝ f x).toLinearMap ≠ 0)
    (_hfin₀ : (f ⁻¹' {y₀}).Finite) :
    ∀ᶠ y in 𝓝 y₀, f ⁻¹' {y} ⊆
      ⋃ x : (f ⁻¹' {y₀} : Set E),
        ((hasStrictFDerivAt_fderivEquiv f (hf x x.2) (hdet x x.2)).toOpenPartialHomeomorph
          f).source := by
  classical
  -- the open union of inverse-function sources
  set U : Set E := ⋃ x : (f ⁻¹' {y₀} : Set E),
    ((hasStrictFDerivAt_fderivEquiv f (hf x x.2) (hdet x x.2)).toOpenPartialHomeomorph f).source
    with hU
  have hUopen : IsOpen U :=
    isOpen_iUnion fun x =>
      ((hasStrictFDerivAt_fderivEquiv f (hf x x.2) (hdet x x.2)).toOpenPartialHomeomorph
        f).open_source
  -- every preimage point lies in its own source, so the sources cover `f⁻¹{y₀}`
  have hcover₀ : f ⁻¹' {y₀} ⊆ U := by
    intro z hz
    refine Set.mem_iUnion.2 ⟨⟨z, hz⟩, ?_⟩
    exact (hasStrictFDerivAt_fderivEquiv f (hf z hz) (hdet z hz)).mem_toOpenPartialHomeomorph_source
  -- a compact neighbourhood of `y₀`, with compact preimage by properness
  obtain ⟨K, hKcompact, hKmem⟩ := exists_compact_mem_nhds y₀
  have hpreK : IsCompact (f ⁻¹' K) := hfp.isCompact_preimage hKcompact
  -- the compact leftover `C = f⁻¹(K) \ U`
  set C : Set E := f ⁻¹' K \ U with hC
  have hCcompact : IsCompact C := hpreK.diff hUopen
  -- `f` avoids `y₀` on `C`: any `z ∈ C` with `f z = y₀` would lie in `U`
  have hCavoid : y₀ ∉ f '' C := by
    rintro ⟨z, hzC, hzeq⟩
    exact hzC.2 (hcover₀ hzeq)
  -- `f '' C` is compact, hence closed, and misses `y₀`
  have hImgClosed : IsClosed (f '' C) := (hCcompact.image hfp.continuous).isClosed
  have hAvoidNhds : (f '' C)ᶜ ∈ 𝓝 y₀ := hImgClosed.compl_mem_nhds hCavoid
  -- for `y` near `y₀`, `y ∈ K` and `y ∉ f '' C`; then all solutions land in `U`
  filter_upwards [hKmem, hAvoidNhds] with y hyK hyImg
  intro z hz
  have hzfy : f z = y := hz
  have hzK : z ∈ f ⁻¹' K := by rw [Set.mem_preimage, hzfy]; exact hyK
  have hznotC : z ∉ C := by
    intro hzC
    exact hyImg ⟨z, hzC, hzfy⟩
  -- `z ∈ f⁻¹(K)` but `z ∉ C = f⁻¹(K) \ U`, so `z ∈ U`
  by_contra hzU
  exact hznotC ⟨hzK, hzU⟩

/-- **Local constancy of the regular degree at a regular value of a proper map.** With confinement
discharged from properness, near a regular value `y₀` of a proper `C¹` map the regular degree at
nearby values is the constant `∑ x ∈ f⁻¹{y₀}, sign (det (Df x))`. No analytic side condition is
carried. -/
theorem eventually_regularDegree_eq_of_isProperMap (f : E → E) (hfp : IsProperMap f) {y₀ : E}
    (hf : ∀ x ∈ f ⁻¹' {y₀}, ContDiffAt ℝ 1 f x)
    (hdet : ∀ x ∈ f ⁻¹' {y₀}, LinearMap.det (fderiv ℝ f x).toLinearMap ≠ 0)
    (hfin₀ : (f ⁻¹' {y₀}).Finite) :
    ∀ᶠ y in 𝓝 y₀,
      ∀ (hfin : (f ⁻¹' {y}).Finite),
        regularDegree f y hfin =
          ∑ x ∈ hfin₀.toFinset,
            ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ) :=
  eventually_regularDegree_eq f hf hdet hfin₀
    (eventually_confinement_of_isProperMap f hfp hf hdet hfin₀)

/-- The set of regular values of `f` with finite preimage all of whose points are nondegenerate.
On this set the regular degree is well-defined and, for a proper map, locally constant. -/
def IsRegularValue (f : E → E) (y : E) : Prop :=
  (f ⁻¹' {y}).Finite ∧
    (∀ x ∈ f ⁻¹' {y}, ContDiffAt ℝ 1 f x) ∧
      ∀ x ∈ f ⁻¹' {y}, LinearMap.det (fderiv ℝ f x).toLinearMap ≠ 0

/-- **The regular degree is locally constant on regular values of a proper map.** Packaged as a
function on the subtype of regular values, the regular degree agrees with its value at `y₀`
throughout a neighbourhood of any regular value `y₀`: it is `IsLocallyConstant`.

Local constancy is read off `eventually_regularDegree_eq_of_isProperMap`: near `y₀` both `y` and
`y₀` have regular degree equal to the common constant `∑ x ∈ f⁻¹{y₀}, sign (det (Df x))`. -/
theorem isLocallyConstant_regularDegree_of_isProperMap (f : E → E) (hfp : IsProperMap f) :
    IsLocallyConstant
      (fun y : {y : E // IsRegularValue f y} =>
        regularDegree f (y : E) y.2.1) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  rintro ⟨y₀, hy₀fin, hy₀cd, hy₀det⟩
  -- the constant value at `y₀`
  set c : ℤ := ∑ x ∈ hy₀fin.toFinset,
    ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ) with hc
  have hev := eventually_regularDegree_eq_of_isProperMap f hfp hy₀cd hy₀det hy₀fin
  -- `regularDegree f y₀ = c`
  have hy₀val : regularDegree f y₀ hy₀fin = c := hev.self_of_nhds hy₀fin
  -- pull the eventual equality back along the continuous subtype projection
  have htend : Tendsto (fun y : {y : E // IsRegularValue f y} => (y : E))
      (𝓝 (⟨y₀, hy₀fin, hy₀cd, hy₀det⟩ : {y : E // IsRegularValue f y})) (𝓝 y₀) :=
    continuous_subtype_val.continuousAt
  filter_upwards [htend.eventually hev] with y hy
  show regularDegree f (y : E) y.2.1 = regularDegree f y₀ hy₀fin
  rw [hy y.2.1, hy₀val]

end CRNT

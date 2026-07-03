import CRNT.Multistationarity.DegreeProperConstant

/-!
# Homotopy invariance of the regular-value degree

A `C¹` homotopy `H : ℝ × E → E` deforms its initial slice `H(0, ·)` into its final slice
`H(1, ·)` through the family of slice maps `H(s, ·)`. When a fixed value `y` is a regular value
of every slice along the deformation — finite preimage, all preimage points nondegenerate — the
regular-value degree at `y` is the same for every slice:

`regularDegree (H(0, ·)) y = regularDegree (H(1, ·)) y`.

This is the defining property of the topological degree: it is invariant under deformation of the
map. It is the gateway from the finite, regular-value primitive to the full Brouwer degree and to
the steady-state existence arguments that run a one-parameter family of maps and read off a
preserved nonzero degree.

The proof is parameter local-constancy plus connectedness. The map `s ↦ regularDegree (H(s, ·)) y`
is locally constant in the parameter `s`: at a regular slice `s₀` the preimage points of `H(s₀, ·)`
are finitely many nondegenerate solutions, each confined to its own inverse-function
neighbourhood; as `s` varies the slice preimage stays a disjoint cover by those same
neighbourhoods, with each local degree pinned to the orientation sign of its slice point, so the
signed count does not change. A locally constant function on the connected interval `[0, 1]` takes
the same value at `0` and at `1` (`IsLocallyConstant.apply_eq_of_isPreconnected`).

The parameter degree-stability engine `regularDegree_param_eq_of_disjointCover` is the parameter
analogue of `eventually_regularDegree_eq`: it consumes, at the moving parameter `s`, a disjoint
cover of the slice preimage whose per-piece local degrees are the orientation signs of the slice
`s₀` points, and returns the constant signed count. The eventual facts it consumes — the disjoint
cover and the per-piece sign — are the honest analytic input, derived for each slice from the
inverse function theorem exactly as on the value side, and carried here as data on the parameter.

* `regularDegree_param_eq_of_disjointCover` — parameter degree-stability from a disjoint cover with
  per-piece orientation signs.
* `regularDegree_homotopy_invariant_of_eventually` — invariance from parameter local-constancy
  packaged as an eventual disjoint-cover-with-signs hypothesis on a neighbourhood of each slice.
* `regularDegree_homotopy_invariant` — the headline: equal regular-value degree at the endpoint
  slices `H(0, ·)` and `H(1, ·)`.

-/

namespace CRNT

open scoped Finset Topology Classical

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- **Parameter degree-stability from a disjoint cover.** Fix a value `y` and a reference
parameter `s₀` whose slice `g s₀ = H(s₀, ·)` has finite preimage `hfin₀` of `y`. Suppose that for
the slice map `g s` at the moving parameter `s` there is a family of open neighbourhoods `W`,
indexed by the points of the reference slice's preimage, that cover the slice preimage
`(g s)⁻¹{y}` disjointly, and on each `W x` the local degree of `g s` at `y` equals the orientation
sign of the reference slice point `x`. Then the regular degree of the slice `g s` at `y` is the
constant signed count `∑ x, sign (det (D(g s₀) x))`.

This is degree additivity over the disjoint cover, then the per-piece signs, assembled over the
fixed reference preimage index — the parameter analogue of `eventually_regularDegree_eq`. -/
theorem regularDegree_param_eq_of_disjointCover (g : ℝ → E → E) (y : E) {s₀ : ℝ}
    (hfin₀ : ((g s₀) ⁻¹' {y}).Finite) {s : ℝ} (hfin : ((g s) ⁻¹' {y}).Finite)
    (W : ((g s₀) ⁻¹' {y} : Set E) → Set E)
    (hcover : (g s) ⁻¹' {y} ⊆ ⋃ x, W x)
    (hdisj : ∀ a b, a ≠ b → ∀ z, z ∈ W a → z ∈ W b → False)
    (hsign : ∀ x : ((g s₀) ⁻¹' {y} : Set E),
      localDegree (g s) y hfin (W x) =
        ((SignType.sign (LinearMap.det (fderiv ℝ (g s₀) (x : E)).toLinearMap) : SignType) : ℤ)) :
    regularDegree (g s) y hfin =
      ∑ x ∈ hfin₀.toFinset,
        ((SignType.sign (LinearMap.det (fderiv ℝ (g s₀) x).toLinearMap) : SignType) : ℤ) := by
  classical
  haveI : Fintype ((g s₀) ⁻¹' {y} : Set E) := hfin₀.fintype
  rw [regularDegree_eq_sum_localDegree (g s) y hfin W hcover
    (fun a b hab z _ => hdisj a b hab z)]
  have hsum : (∑ x : ((g s₀) ⁻¹' {y} : Set E), localDegree (g s) y hfin (W x)) =
      ∑ x : ((g s₀) ⁻¹' {y} : Set E),
        ((SignType.sign (LinearMap.det (fderiv ℝ (g s₀) (x : E)).toLinearMap) : SignType) : ℤ) :=
    Finset.sum_congr rfl (fun x _ => hsign x)
  rw [hsum,
    ← Finset.sum_coe_sort hfin₀.toFinset
      (fun x => ((SignType.sign (LinearMap.det (fderiv ℝ (g s₀) x).toLinearMap) : SignType) : ℤ))]
  exact Fintype.sum_equiv hfin₀.subtypeEquivToFinset _ _ (fun x => rfl)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- **Homotopy invariance from parameter local-constancy.** Write `g s = H(s, ·)` for the slice
maps. Assume that every slice along `[0, 1]` has a finite preimage of `y` (`hfin`), and that the
parameter map `s ↦ regularDegree (g s) y` is locally constant: near each `s₀ ∈ [0, 1]`, for `s`
in a neighbourhood the slice preimage admits a disjoint open cover whose per-piece local degrees
are the orientation signs of the reference slice points (`hloc`). Then the regular degree is the
same at the two endpoint slices `g 0` and `g 1`.

The eventual disjoint-cover-with-signs hypothesis forces `s ↦ regularDegree (g s) y` to be locally
constant (each nearby `s` and `s₀` reduce to the same constant signed count via
`regularDegree_param_eq_of_disjointCover`). Local constancy on the connected interval `[0, 1]`
gives equality of the endpoint values. -/
theorem regularDegree_homotopy_invariant_of_eventually (g : ℝ → E → E) (y : E)
    (hfin : ∀ s ∈ Set.Icc (0 : ℝ) 1, ((g s) ⁻¹' {y}).Finite)
    (hloc : ∀ s₀ ∈ Set.Icc (0 : ℝ) 1, ∀ (_hfin₀ : ((g s₀) ⁻¹' {y}).Finite),
      ∀ᶠ s in 𝓝 s₀, ∃ (hfins : ((g s) ⁻¹' {y}).Finite)
        (W : ((g s₀) ⁻¹' {y} : Set E) → Set E),
        ((g s) ⁻¹' {y} ⊆ ⋃ x, W x) ∧
        (∀ a b, a ≠ b → ∀ z, z ∈ W a → z ∈ W b → False) ∧
        ∀ x : ((g s₀) ⁻¹' {y} : Set E),
          localDegree (g s) y hfins (W x) =
            ((SignType.sign (LinearMap.det (fderiv ℝ (g s₀) (x : E)).toLinearMap) : SignType) : ℤ))
    (h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    regularDegree (g 0) y (hfin 0 h0) = regularDegree (g 1) y (hfin 1 h1) := by
  classical
  -- the parameter degree as a function on `[0, 1]`, with the preimage witness chosen by membership
  set F : Set.Icc (0 : ℝ) 1 → ℤ := fun s => regularDegree (g (s : ℝ)) y (hfin (s : ℝ) s.2) with hF
  -- `F` is locally constant: near each `s₀`, both `s` and `s₀` evaluate to the reference constant
  have hLC : IsLocallyConstant F := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro s₀
    -- the reference constant at `s₀`
    set hfin₀ := hfin (s₀ : ℝ) s₀.2 with hhfin₀
    set c : ℤ := ∑ x ∈ hfin₀.toFinset,
      ((SignType.sign (LinearMap.det (fderiv ℝ (g (s₀ : ℝ)) x).toLinearMap) : SignType) : ℤ) with hc
    -- `F s₀ = c` by applying the engine with the trivial cover `W` from the eventual fact at `s₀`
    have hev := hloc (s₀ : ℝ) s₀.2 hfin₀
    -- pull the eventual fact back along the subtype inclusion
    have htend : Tendsto (fun s : Set.Icc (0 : ℝ) 1 => (s : ℝ)) (𝓝 s₀) (𝓝 (s₀ : ℝ)) :=
      continuous_subtype_val.continuousAt
    -- value of `F` at `s₀` via the self-membership of the eventual filter
    have hself := hev.self_of_nhds
    obtain ⟨hfins₀', W₀, hcov₀, hdisj₀, hsign₀⟩ := hself
    have hFs₀ : F s₀ = c := by
      show regularDegree (g (s₀ : ℝ)) y (hfin (s₀ : ℝ) s₀.2) = c
      rw [regularDegree_param_eq_of_disjointCover (g := g) (y := y) (s₀ := (s₀ : ℝ))
        hfin₀ (hfin (s₀ : ℝ) s₀.2) W₀ hcov₀ hdisj₀ hsign₀]
    -- for `s` near `s₀`, `F s = c` likewise
    filter_upwards [htend.eventually hev] with s hs
    obtain ⟨hfins', W, hcov, hdisj, hsign⟩ := hs
    rw [hFs₀]
    show regularDegree (g (s : ℝ)) y (hfin (s : ℝ) s.2) = c
    rw [regularDegree_param_eq_of_disjointCover (g := g) (y := y) (s₀ := (s₀ : ℝ))
      hfin₀ (hfin (s : ℝ) s.2) W hcov hdisj hsign]
  -- the interval `[0, 1]` is connected, so `F` is constant on it
  haveI : PreconnectedSpace (Set.Icc (0 : ℝ) 1) :=
    Subtype.preconnectedSpace (isPreconnected_Icc (a := (0 : ℝ)) (b := 1))
  have hconst := hLC.apply_eq_of_preconnectedSpace (⟨0, h0⟩ : Set.Icc (0 : ℝ) 1) ⟨1, h1⟩
  simpa [hF] using hconst

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- **Homotopy invariance of the regular-value degree.** Let `H : ℝ × E → E` be a homotopy with
slice maps `H(s, ·)`, and let `y` be a value that is a regular value of every slice along
`[0, 1]`: each slice preimage of `y` is finite (`hfin`). Assume parameter local-constancy of the
slice degree near every parameter `s₀ ∈ [0, 1]`: for `s` in a neighbourhood the slice preimage
of `y` admits a disjoint open cover whose per-piece local degrees are the orientation signs of the
reference slice points (`hloc`). Then the regular-value degree at `y` is the same at the initial
and final slices:

`regularDegree (H(0, ·)) y = regularDegree (H(1, ·)) y`.

The slice degree is locally constant in the parameter and constant on the connected interval. The
parameter local-constancy data `hloc` is the analytic input; for a `C¹` homotopy whose slices are
proper it is supplied by the inverse function theorem and the confinement-from-properness argument
of `eventually_confinement_of_isProperMap`, applied per slice with the parameter as the moving
datum. -/
theorem regularDegree_homotopy_invariant (H : ℝ × E → E) (y : E)
    (hfin : ∀ s ∈ Set.Icc (0 : ℝ) 1, ((fun x => H (s, x)) ⁻¹' {y}).Finite)
    (hloc : ∀ s₀ ∈ Set.Icc (0 : ℝ) 1, ∀ (_hfin₀ : ((fun x => H (s₀, x)) ⁻¹' {y}).Finite),
      ∀ᶠ s in 𝓝 s₀, ∃ (hfins : ((fun x => H (s, x)) ⁻¹' {y}).Finite)
        (W : ((fun x => H (s₀, x)) ⁻¹' {y} : Set E) → Set E),
        ((fun x => H (s, x)) ⁻¹' {y} ⊆ ⋃ x, W x) ∧
        (∀ a b, a ≠ b → ∀ z, z ∈ W a → z ∈ W b → False) ∧
        ∀ x : ((fun x => H (s₀, x)) ⁻¹' {y} : Set E),
          localDegree (fun x => H (s, x)) y hfins (W x) =
            ((SignType.sign
              (LinearMap.det (fderiv ℝ (fun x => H (s₀, x)) (x : E)).toLinearMap) : SignType) : ℤ)) :
    regularDegree (fun x => H (0, x)) y (hfin 0 (by constructor <;> norm_num)) =
      regularDegree (fun x => H (1, x)) y (hfin 1 (by constructor <;> norm_num)) :=
  regularDegree_homotopy_invariant_of_eventually (fun s x => H (s, x)) y hfin hloc
    (by constructor <;> norm_num) (by constructor <;> norm_num)

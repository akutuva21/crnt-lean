import CRNT.Dynamics.DifferentialInclusion
import CRNT.Dynamics.Nagumo
import Mathlib.Analysis.Calculus.TangentCone.Basic
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Viability and subtangentiality for differential inclusions

The Bouligand/contingent tangent cone `tangentConeAt ℝ s x` (Mathlib) collects the directions
along which a curve may enter `s` from `x`: a velocity `y` lies in the cone exactly when there
are scalars `c n → ∞` and displacements `d n → 0` with `x + d n ∈ s` and `c n • d n → y`. The
Nagumo viability theorem characterizes forward invariance of a closed set `s` for a
differential inclusion by *subtangentiality*: every admissible velocity points into the cone.

This module builds the tangent-cone framework and the tractable half of Nagumo.

* `Subtangent F s` is the subtangentiality predicate: at each point of `s`, every velocity of
  the field lies in the tangent cone of `s`. `Subtangent.mono_field` records that a smaller
  field inherits subtangentiality, and `subtangent_univ` that the whole space is subtangent.

* `mem_tangentConeAt_of_solution` is the easy direction *invariance ⇒ subtangency along a
  solution*, proved here from `HasDerivAt`. If `γ 0 = x`, `γ` has velocity `v` at `0`, and `γ`
  stays in `s` for all forward time, then `v ∈ tangentConeAt ℝ s x`: the forward slopes
  `t⁻¹ • (γ t − x)` witness cone membership along `𝓝[>] 0`. `subtangent_of_forwardInvariant`
  packages this into `Subtangent` for fields all of whose pointed solutions exist and stay in
  the invariant region.

* `mem_tangentConeAt_of_le` computes inward directions for the closed coordinate halfspace
  `Set.Ici a ⊆ ℝ`: every `v ≥ 0` lies in `tangentConeAt ℝ (Set.Ici a) a` (reached along the
  segment into the halfspace). `scalar_subtangent_iff_inward` then phrases the
  scalar-halfspace Nagumo equivalence through the cone: for the closed halfspace `Ici 0`, the
  inward field condition `0 ≤ F` on the boundary is exactly subtangentiality there, and via
  `nagumo_halfspace_scalar` it certifies forward invariance.

The *general* converse — subtangentiality ⇒ forward invariance for an arbitrary closed `s` and
set-valued `F` — requires viability/solution-existence theory (Filippov selection, Peano
existence on a moving constraint) that is **absent** from Mathlib, and is not attempted here.
It is the residue gating Craciun's Theorem B in dimension ≥ 2.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.DifferentialInclusion`,
`CRNT.Dynamics.Nagumo`, `Mathlib.Analysis.Calculus.TangentCone.Basic`,
`Mathlib.Analysis.Calculus.TangentCone.Real`, `Mathlib.Analysis.Calculus.Deriv.Slope`.
-/

namespace CRNT

namespace DifferentialInclusion

open Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Subtangentiality.** A field `F` is subtangent to a set `s` when, at every point of `s`,
every admissible velocity lies in the Bouligand tangent cone of `s` at that point. This is the
hypothesis of the Nagumo viability theorem. -/
def Subtangent (F : Field E) (s : Set E) : Prop :=
  ∀ x ∈ s, F x ⊆ tangentConeAt ℝ s x

/-- The whole space is subtangent to any field: every velocity is a tangent direction of
`Set.univ`. -/
theorem subtangent_univ (F : Field E) : Subtangent F (Set.univ : Set E) := by
  intro x _ v _
  rw [tangentConeAt_univ]
  exact Set.mem_univ v

/-- A smaller field inherits subtangentiality: if `F x ⊆ G x` pointwise and `G` is subtangent
to `s`, then so is `F`. -/
theorem Subtangent.mono_field {F G : Field E} {s : Set E}
    (h : Subtangent G s) (hsub : ∀ x, F x ⊆ G x) : Subtangent F s :=
  fun x hx _v hv => h x hx (hsub x hv)

/-- A subtangentiality predicate is monotone in the velocity field on a fixed set, contravariant
in the cone's set via `tangentConeAt_mono`: if `s ⊆ t` and `F` is subtangent to `s`, the same
velocities are tangent to `t`. -/
theorem Subtangent.mono_set {F : Field E} {s t : Set E}
    (h : Subtangent F s) (hst : s ⊆ t) (hF : ∀ x ∈ t, x ∉ s → F x ⊆ tangentConeAt ℝ t x) :
    Subtangent F t := by
  intro x hx v hv
  by_cases hxs : x ∈ s
  · exact tangentConeAt_mono hst (h x hxs hv)
  · exact hF x hx hxs hv

/-- **Easy direction of Nagumo (invariance ⇒ subtangency along a solution).** If a curve `γ`
passes through `x` at time `0` with velocity `v`, and stays in `s` for all forward time, then
`v` lies in the Bouligand tangent cone of `s` at `x`.

The forward difference quotients `t⁻¹ • (γ t − x)` along `𝓝[>] 0` are exactly the witnesses of
cone membership: they live in `(s − x)` scaled, tend to `v` by `HasDerivAt`, and their
displacements tend to `0`. -/
theorem mem_tangentConeAt_of_solution {γ : ℝ → E} {x v : E} {s : Set E}
    (hx : γ 0 = x) (hd : HasDerivAt γ v 0) (hs : ∀ t, 0 ≤ t → γ t ∈ s) :
    v ∈ tangentConeAt ℝ s x := by
  refine mem_tangentConeAt_of_seq (𝓝[>] (0 : ℝ)) (fun t => t⁻¹) (fun t => γ (0 + t) - γ 0)
    ?_ ?_ ?_
  · -- displacements tend to 0
    have hca : ContinuousAt (fun t : ℝ => γ (0 + t)) 0 :=
      (show ContinuousAt γ (0 + 0) by simpa using hd.continuousAt).comp
        (f := fun t : ℝ => (0 : ℝ) + t)
        (by fun_prop : ContinuousAt (fun t : ℝ => (0 : ℝ) + t) 0)
    have hzero : Tendsto (fun t : ℝ => γ (0 + t)) (𝓝[>] (0 : ℝ)) (𝓝 (γ (0 + 0))) :=
      hca.continuousWithinAt
    have : Tendsto (fun t : ℝ => γ (0 + t) - γ 0) (𝓝[>] 0) (𝓝 (γ (0 + 0) - γ 0)) :=
      hzero.sub tendsto_const_nhds
    simpa using this
  · -- `x + d t = γ t ∈ s` eventually along `𝓝[>] 0`
    have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), (0 : ℝ) < t := self_mem_nhdsWithin
    filter_upwards [hmem] with t ht
    have : x + (γ (0 + t) - γ 0) = γ t := by rw [hx]; simp
    rw [this]
    exact hs t ht.le
  · -- forward slopes tend to `v`
    have := hd.tendsto_slope_zero_right
    simpa using this

/-- **Subtangency of a forward-invariant region.** If every pointed solution of `F` exists —
for each `x ∈ s` and each velocity `v ∈ F x` there is a solution through `x` with velocity `v`
at time `0` that stays in `s` for forward time — then `F` is subtangent to `s`.

The existence hypothesis is the content that Mathlib cannot supply in general; supplied, the
tangent-cone membership is the easy-direction lemma above. -/
theorem subtangent_of_forwardInvariant {F : Field E} {s : Set E}
    (hexists : ∀ x ∈ s, ∀ v ∈ F x, ∃ γ : ℝ → E,
      γ 0 = x ∧ HasDerivAt γ v 0 ∧ ∀ t, 0 ≤ t → γ t ∈ s) :
    Subtangent F s := by
  intro x hx v hv
  obtain ⟨γ, hγ0, hγd, hγs⟩ := hexists x hx v hv
  exact mem_tangentConeAt_of_solution hγ0 hγd hγs

end DifferentialInclusion

/-! ### Concrete case: the closed scalar halfspace `Set.Ici a`

Here `E = ℝ` and `s = Set.Ici a`. Every nonnegative velocity is an inward tangent direction at
the boundary point `a`. For the *positive* tangent cone `posTangentConeAt` (scalars in `ℝ≥0`),
the converse also holds — a tangent direction at the boundary is necessarily nonnegative — so
inward-ness and positive-subtangentiality coincide. The scalar Nagumo lemma
`nagumo_halfspace_scalar` then certifies forward invariance of the closed halfspace. -/

open Filter Set
open scoped Topology

/-- Every nonnegative velocity is an inward tangent direction of the closed halfspace `Ici a`
at the boundary point `a`: the segment from `a` to `a + v` lies in `Ici a`, so `v` is reached.
The witness lands in the *positive* tangent cone (scalars in `ℝ≥0`). -/
theorem mem_posTangentConeAt_Ici_of_le {a v : ℝ} (hv : 0 ≤ v) :
    v ∈ posTangentConeAt (Set.Ici a) a := by
  rcases eq_or_lt_of_le hv with hv0 | hv0
  · rw [← hv0]
    exact zero_mem_tangentConeAt (subset_closure (Set.mem_Ici.mpr le_rfl))
  · have hseg : openSegment ℝ a (a + v) ⊆ Set.Ici a := by
      rw [openSegment_eq_image]
      rintro y ⟨θ, hθ, rfl⟩
      simp only [Set.mem_Ici, smul_eq_mul]
      nlinarith [hθ.1, hθ.2, hv0]
    have := sub_mem_posTangentConeAt_of_openSegment_subset hseg
    simpa using this

/-- Every nonnegative velocity is an inward tangent direction of the closed halfspace `Ici a`
at the boundary point `a`, in the (two-sided) real tangent cone. -/
theorem mem_tangentConeAt_Ici_of_le {a v : ℝ} (hv : 0 ≤ v) :
    v ∈ tangentConeAt ℝ (Set.Ici a) a :=
  tangentConeAt_mono_field (mem_posTangentConeAt_Ici_of_le hv)

/-- A positive tangent direction of the closed halfspace `Ici a` at its boundary point `a` is
nonnegative: the scaled displacements that witness it are products of a nonnegative scalar and a
nonnegative displacement, so their limit is nonnegative. -/
theorem nonneg_of_mem_posTangentConeAt_Ici {a v : ℝ}
    (hv : v ∈ posTangentConeAt (Set.Ici a) a) : 0 ≤ v := by
  obtain ⟨α, l, hl, c, d, _hd, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hv
  haveI := hl
  refine ge_of_tendsto hcd ?_
  filter_upwards [hds] with n hn
  have hdn : 0 ≤ d n := by simpa [Set.mem_Ici] using hn
  have : (0 : ℝ) ≤ (c n : ℝ) * d n := mul_nonneg (c n).coe_nonneg hdn
  simpa [NNReal.smul_def] using this

/-- **The positive tangent cone of a closed scalar halfspace at its boundary is the set of
nonnegative directions.** This is the frontier case of the Nagumo viability criterion: a
velocity is positively subtangent to `Ici a` at the boundary iff it points inward. -/
theorem posTangentConeAt_Ici_self (a : ℝ) :
    posTangentConeAt (Set.Ici a) a = Set.Ici (0 : ℝ) :=
  Set.Subset.antisymm (fun _ hv => nonneg_of_mem_posTangentConeAt_Ici hv)
    (fun _ hv => mem_posTangentConeAt_Ici_of_le hv)

namespace DifferentialInclusion

open scoped BigOperators

/-- **Positive subtangentiality.** The Nagumo subtangentiality predicate phrased with the
positive tangent cone `posTangentConeAt` (scalars in `ℝ≥0`). This is the cone for which the
viability equivalence holds at the boundary of a closed convex set. -/
def PosSubtangent (F : Field ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, F x ⊆ posTangentConeAt s x

/-- **Inward-on-boundary is positive subtangentiality for the closed halfspace.** For
`Set.Ici (0 : ℝ)`, given that the field is positively subtangent on the open interior, the
boundary inward condition `0 ≤ F 0` is equivalent to positive subtangentiality of the field. -/
theorem inwardOnBoundary_iff_posSubtangent (F : Field ℝ)
    (hbody : ∀ x, 0 < x → F x ⊆ posTangentConeAt (Set.Ici (0 : ℝ)) x) :
    (∀ v ∈ F 0, (0 : ℝ) ≤ v) ↔ PosSubtangent F (Set.Ici (0 : ℝ)) := by
  constructor
  · intro hin x hx v hv
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hx) with hx0 | hx0
    · subst hx0
      rw [posTangentConeAt_Ici_self]
      exact Set.mem_Ici.mpr (hin v hv)
    · exact hbody x hx0 hv
  · intro hsub v hv
    have := hsub 0 (Set.mem_Ici.mpr le_rfl) hv
    rw [posTangentConeAt_Ici_self] at this
    exact this

/-- **Subtangency along solutions implies inward-on-boundary.** If a field `F` on `ℝ` is the
velocity field of solutions that stay in `Set.Ici 0` for forward time, then at the boundary
every admissible velocity is nonnegative — the easy direction specialized to the halfspace,
read through `posTangentConeAt_Ici_self`. -/
theorem inwardOnBoundary_of_solutions {F : Field ℝ}
    (hexists : ∀ v ∈ F 0, ∃ γ : ℝ → ℝ,
      γ 0 = 0 ∧ HasDerivAt γ v 0 ∧ ∀ t, 0 ≤ t → γ t ∈ Set.Ici (0 : ℝ)) :
    ∀ v ∈ F 0, (0 : ℝ) ≤ v := by
  intro v hv
  obtain ⟨γ, hγ0, hγd, hγs⟩ := hexists v hv
  -- the forward slopes have positive scalars `t⁻¹`, so `v` lies in the positive cone
  have hpos : v ∈ posTangentConeAt (Set.Ici (0 : ℝ)) 0 := by
    refine mem_tangentConeAt_of_seq (𝓝[>] (0 : ℝ)) (fun t => Real.toNNReal t⁻¹)
      (fun t => γ (0 + t) - γ 0) ?_ ?_ ?_
    · have hca : ContinuousAt (fun t : ℝ => γ (0 + t)) 0 :=
        (show ContinuousAt γ (0 + 0) by simpa using hγd.continuousAt).comp
          (f := fun t : ℝ => (0 : ℝ) + t)
          (by fun_prop : ContinuousAt (fun t : ℝ => (0 : ℝ) + t) 0)
      have hzero : Tendsto (fun t : ℝ => γ (0 + t)) (𝓝[>] (0 : ℝ)) (𝓝 (γ (0 + 0))) :=
        hca.continuousWithinAt
      have : Tendsto (fun t : ℝ => γ (0 + t) - γ 0) (𝓝[>] 0) (𝓝 (γ (0 + 0) - γ 0)) :=
        hzero.sub tendsto_const_nhds
      simpa using this
    · have hmemf : ∀ᶠ t in 𝓝[>] (0 : ℝ), (0 : ℝ) < t := self_mem_nhdsWithin
      filter_upwards [hmemf] with t ht
      have : (0 : ℝ) + (γ (0 + t) - γ 0) = γ t := by rw [hγ0]; simp
      rw [this]
      exact hγs t ht.le
    · have hslope := hγd.tendsto_slope_zero_right
      have hmemf : ∀ᶠ t in 𝓝[>] (0 : ℝ), (0 : ℝ) < t := self_mem_nhdsWithin
      refine hslope.congr' ?_
      filter_upwards [hmemf] with t ht
      have : (Real.toNNReal t⁻¹ : ℝ) = t⁻¹ := Real.coe_toNNReal _ (inv_nonneg.mpr ht.le)
      simp [NNReal.smul_def, this]
  rw [posTangentConeAt_Ici_self] at hpos
  exact hpos

end DifferentialInclusion

/-- **Closed forward-invariance of the scalar halfspace from inward-on-boundary, via the
tangent-cone framework.** A differentiable curve `γ` into `ℝ` with the inward field condition
on the boundary — `0 ≤ deriv γ t` whenever `γ t = 0` — together with a dissipativity bound
where `γ` is negative and a nonnegative start, stays in `Set.Ici 0` for all forward time.

This reuses the repo's scalar Nagumo lemma `nagumo_halfspace_scalar`; the inward-on-boundary
hypothesis is exactly positive subtangentiality at the boundary (`posTangentConeAt_Ici_self`),
so this is the viability ⇐ direction for the case the repo handles, phrased through the cone. -/
theorem forwardInvariant_Ici_of_nagumo {γ : ℝ → ℝ} {L : ℝ}
    (hd : ∀ t, HasDerivAt γ (deriv γ t) t)
    (hin : ∀ t, γ t < 0 → -L * γ t ≤ deriv γ t) (h0 : γ 0 ∈ Set.Ici (0 : ℝ)) :
    ∀ t, 0 ≤ t → γ t ∈ Set.Ici (0 : ℝ) :=
  fun t ht => Set.mem_Ici.mpr (nagumo_halfspace_scalar hd hin (Set.mem_Ici.mp h0) t ht)

end CRNT

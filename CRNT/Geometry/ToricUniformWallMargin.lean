import CRNT.Geometry.SmoothBarrierGluing
import CRNT.Geometry.FanWallsCrossed
import CRNT.Geometry.ToricStrictSupport
import CRNT.Dynamics.DissipationBound

namespace CRNT
open scoped InnerProductSpace
open SmoothBarrierGluing
variable {S : Type} [DecidableEq S] [Fintype S]

theorem Network.exists_uniform_toric_wall_margin_on_compact (N : Network S) (κ : N.RateConstants)
    {K : Set (EuclideanSpace ℝ S)} (hK : IsCompact K) (hne : K.Nonempty)
    {n : S → ℝ}
    (hpos : ∀ p ∈ K, Concentration.Positive (toEuclid.symm p))
    (hinward : ∀ r : N.R, 0 ≤ ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ)
    {r₀ : N.R} (hstrict : 0 < ⟪toEuclid n, toEuclid (N.reactionVector r₀)⟫_ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ K, ε ≤ ⟪toEuclid n, N.toricMassActionField κ p⟫_ℝ := by
  let f : EuclideanSpace ℝ S → ℝ := fun p => ⟪toEuclid n, N.toricMassActionField κ p⟫_ℝ
  have hfield : Continuous (N.toricMassActionField κ) := by
    unfold Network.toricMassActionField
    exact (LinearMap.continuous_of_finiteDimensional (toEuclid (ι := S)).toLinearMap).comp
      ((Network.continuous_massActionVectorField N κ).comp
        (LinearMap.continuous_of_finiteDimensional (toEuclid (ι := S)).symm.toLinearMap))
  have hf : Continuous f := continuous_const.inner hfield
  apply exists_uniform_pos_margin_on_compact hK hne hf.continuousOn
  intro p hp
  exact N.inner_toricMassActionField_pos_of_enabledInward κ (hpos p hp).nonnegative hinward
    (N.massActionRate_pos κ r₀ (hpos p hp)) hstrict


/-- Weak reversibility and activity discharge the strict-reaction witness, leaving only the
fan-supplied non-strict wall orientation and positivity of the compact section. -/
theorem Network.WeaklyReversible.exists_uniform_toric_activeWall_margin_on_compact
    {N : Network S} (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {K : Set (EuclideanSpace ℝ S)} (hK : IsCompact K) (hne : K.Nonempty)
    {n : S → ℝ} (hactive : N.ActiveWall n)
    (hpos : ∀ p ∈ K, Concentration.Positive (toEuclid.symm p))
    (hinward : ∀ r : N.R, 0 ≤ ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ K, ε ≤ ⟪toEuclid n, N.toricMassActionField κ p⟫_ℝ := by
  obtain ⟨r₀, hr₀⟩ := hwr.exists_strictlyInward_of_activeWall hactive
  exact N.exists_uniform_toric_wall_margin_on_compact κ hK hne hpos hinward hr₀

end CRNT

namespace CRNT
open scoped InnerProductSpace
variable {S : Type} [DecidableEq S] [Fintype S]

/-- A finite nonempty family of active toric walls admits one common positive inward margin on a
compact positive section.  This is the simultaneous quantitative estimate needed before smooth
finite wall gluing. -/
theorem Network.WeaklyReversible.exists_uniform_toric_activeWallList_margin_on_compact
    {N : Network S} (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {K : Set (EuclideanSpace ℝ S)} (hK : IsCompact K) (hne : K.Nonempty)
    (n : S → ℝ) (ns : List (S → ℝ))
    (hactive : N.ActiveWall n)
    (hactives : ∀ m ∈ ns, N.ActiveWall m)
    (hpos : ∀ p ∈ K, Concentration.Positive (toEuclid.symm p))
    (hinward : ∀ m ∈ n :: ns, ∀ r : N.R,
      0 ≤ ⟪toEuclid m, toEuclid (N.reactionVector r)⟫_ℝ) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ p ∈ K, ε ≤ ⟪toEuclid n, N.toricMassActionField κ p⟫_ℝ) ∧
      (∀ m ∈ ns, ∀ p ∈ K, ε ≤ ⟪toEuclid m, N.toricMassActionField κ p⟫_ℝ) := by
  induction ns generalizing n with
  | nil =>
      obtain ⟨ε, hε, hmargin⟩ :=
        hwr.exists_uniform_toric_activeWall_margin_on_compact κ hK hne hactive hpos
          (by intro r; exact hinward n (by simp) r)
      exact ⟨ε, hε, hmargin, by simp⟩
  | cons m ms ih =>
      have hmactive : N.ActiveWall m := hactives m (by simp)
      have hmsactive : ∀ q ∈ ms, N.ActiveWall q := by
        intro q hq
        exact hactives q (by simp [hq])
      have htailin : ∀ q ∈ m :: ms, ∀ r : N.R,
          0 ≤ ⟪toEuclid q, toEuclid (N.reactionVector r)⟫_ℝ := by
        intro q hq r
        exact hinward q (by simp_all) r
      obtain ⟨εt, hεt, hmt, hmst⟩ := ih m hmactive hmsactive htailin
      obtain ⟨εn, hεn, hn⟩ :=
        hwr.exists_uniform_toric_activeWall_margin_on_compact κ hK hne hactive hpos
          (by intro r; exact hinward n (by simp) r)
      refine ⟨min εn εt, lt_min hεn hεt, ?_, ?_⟩
      · intro p hp
        exact le_trans (min_le_left _ _) (hn p hp)
      · intro q hq p hp
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact le_trans (min_le_right _ _) (hmt p hp)
        · exact le_trans (min_le_right _ _) (hmst q hq p hp)


/-- **Finite active-wall toric field glues with one strict derivative margin.**  The common compact
wall margin supplied by weak reversibility feeds directly into `smoothWallList_descends_strictly`:
for arbitrary affine offsets, the log-sum-exp barrier built from a finite nonempty active-wall list
has derivative at most `-ε` along the genuine toric mass-action field at every point of the compact
positive section. -/
theorem Network.WeaklyReversible.exists_uniform_smooth_toric_wallList_descent_on_compact
    {N : Network S} (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {K : Set (EuclideanSpace ℝ S)} (hK : IsCompact K) (hne : K.Nonempty)
    (n : S → ℝ) (a : ℝ) (ns : List ((S → ℝ) × ℝ))
    (hactive : N.ActiveWall n)
    (hactives : ∀ ma ∈ ns, N.ActiveWall ma.1)
    (hpos : ∀ p ∈ K, Concentration.Positive (toEuclid.symm p))
    (hinward : ∀ m ∈ n :: ns.map Prod.fst, ∀ r : N.R,
      0 ≤ ⟪toEuclid m, toEuclid (N.reactionVector r)⟫_ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ K,
      ∃ D : EuclideanSpace ℝ S →L[ℝ] ℝ,
        HasFDerivAt
          (SmoothBarrierGluing.smoothWallList (innerSL ℝ (toEuclid n), a)
            (ns.map (fun ma => (innerSL ℝ (toEuclid ma.1), ma.2)))) D p ∧
        D (N.toricMassActionField κ p) ≤ -ε := by
  have hacts : ∀ m ∈ ns.map Prod.fst, N.ActiveWall m := by
    intro m hm
    rw [List.mem_map] at hm
    obtain ⟨ma, hma, rfl⟩ := hm
    exact hactives ma hma
  obtain ⟨ε, hε, hn, hns⟩ :=
    hwr.exists_uniform_toric_activeWallList_margin_on_compact κ hK hne n
      (ns.map Prod.fst) hactive hacts hpos hinward
  refine ⟨ε, hε, ?_⟩
  intro p hp
  apply SmoothBarrierGluing.smoothWallList_descends_strictly
  · simpa only [innerSL_apply_apply] using hn p hp
  · intro Mb hMb
    rw [List.mem_map] at hMb
    obtain ⟨ma, hma, rfl⟩ := hMb
    simpa only [innerSL_apply_apply] using hns ma.1 (by
      rw [List.mem_map]
      exact ⟨ma, hma, rfl⟩) p hp


/-- **Compact-band toric zero-separating surface.** A finite nonempty active-wall family whose
log-sum-exp band is contained in a compact positive section yields a genuine zero-separating surface
for the toric mass-action field.  This packages weak-reversibility strictness, simultaneous compact
margin extraction, smooth finite gluing, and metric separation into the exact surface interface. -/
theorem Network.WeaklyReversible.zeroSeparatingSurfaceExists_toric_activeWallList_of_compact_band
    {N : Network S} (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {K : Set (EuclideanSpace ℝ S)} (hK : IsCompact K) (hne : K.Nonempty)
    (n : S → ℝ) (a : ℝ) (ns : List ((S → ℝ) × ℝ))
    (hactive : N.ActiveWall n) (hactives : ∀ ma ∈ ns, N.ActiveWall ma.1)
    (hpos : ∀ p ∈ K, Concentration.Positive (toEuclid.symm p))
    (hinward : ∀ m ∈ n :: ns.map Prod.fst, ∀ r : N.R,
      0 ≤ ⟪toEuclid m, toEuclid (N.reactionVector r)⟫_ℝ)
    {x₀ : EuclideanSpace ℝ S} {c δ r : ℝ} (hδ : 0 < δ)
    (hband : ∀ y, c - δ ≤ SmoothBarrierGluing.smoothWallList (innerSL ℝ (toEuclid n), a)
          (ns.map (fun ma => (innerSL ℝ (toEuclid ma.1), ma.2))) y →
        SmoothBarrierGluing.smoothWallList (innerSL ℝ (toEuclid n), a)
          (ns.map (fun ma => (innerSL ℝ (toEuclid ma.1), ma.2))) y ≤ c + δ → y ∈ K)
    (hstart : SmoothBarrierGluing.smoothWallList (innerSL ℝ (toEuclid n), a)
      (ns.map (fun ma => (innerSL ℝ (toEuclid ma.1), ma.2))) x₀ ≤ c)
    (hL : ‖innerSL ℝ (toEuclid n)‖ ≤ 1) (hr : 0 < r) (hac : c + r ≤ a) :
    DifferentialInclusion.ZeroSeparatingSurfaceExists (N.toricMassActionField κ) x₀  := by
  have hacts : ∀ m ∈ ns.map Prod.fst, N.ActiveWall m := by
    intro m hm
    rw [List.mem_map] at hm
    obtain ⟨ma, hma, rfl⟩ := hm
    exact hactives ma hma
  obtain ⟨ε, hε, hn, hns⟩ :=
    hwr.exists_uniform_toric_activeWallList_margin_on_compact κ hK hne n
      (ns.map Prod.fst) hactive hacts hpos hinward
  apply SmoothBarrierGluing.zeroSeparatingSurfaceExists_smoothWallList_of_band
      (La := (innerSL ℝ (toEuclid n), a))
      (walls := ns.map (fun ma => (innerSL ℝ (toEuclid ma.1), ma.2))) hδ
  · intro y hlo hhi
    have hy := hband y hlo hhi
    exact le_trans hε.le (by simpa only [innerSL_apply_apply] using hn y hy)
  · intro Mb hMb y hlo hhi
    rw [List.mem_map] at hMb
    obtain ⟨ma, hma, rfl⟩ := hMb
    have hy := hband y hlo hhi
    exact le_trans hε.le (by simpa only [innerSL_apply_apply] using hns ma.1 (by
      rw [List.mem_map]; exact ⟨ma, hma, rfl⟩) y hy)
  · exact hstart
  · exact hL
  · exact hr
  · exact hac

end CRNT

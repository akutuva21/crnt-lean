import CRNT.Geometry.SmoothBarrierGluing
import CRNT.Geometry.FanWallsCrossed
import CRNT.Geometry.ToricStrictSupport
import CRNT.Dynamics.DissipationBound
import CRNT.Dynamics.ComplexBalanceStoichFanInclusion
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

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


/-- **Uniform source-order margin on one compact chamber patch.** If a fixed stoichiometric
direction lies in the interior of the selected negative source-order cone at every point of a
compact positive patch, and the patch avoids complex-balanced equilibria, strict chamber attraction
has a uniform positive margin there. This is the local quantitative input for finite tile gluing;
the remaining blueprint argument must arrange that each tile's band stays inside its chamber patch.
-/
theorem Network.exists_uniform_sourceOrderInterior_margin_on_compact
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {K : Set (EuclideanSpace ℝ S)} (hK : IsCompact K) (hne : K.Nonempty)
    (hpos : ∀ p ∈ K, Concentration.Positive (toEuclid.symm p))
    (hnotcb : ∀ p ∈ K, ¬ N.IsComplexBalanced κ (toEuclid.symm p))
    {z : N.euclideanStoichSubspace}
    (hz : ∀ p ∈ K,
      z ∈ interior (((N.relativeSourceOrderNegativeCone
        (N.relativeLogStoichProjection
          (fun s => Real.log (toEuclid.symm p s) - Real.log (xstar s)))).comap
            N.euclideanStoichSubspace.subtypeL :
              ProperCone ℝ N.euclideanStoichSubspace) : Set N.euclideanStoichSubspace)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ K,
      ε ≤ ⟪z.1, toEuclid (N.massActionVectorField κ (toEuclid.symm p))⟫_ℝ := by
  let f : EuclideanSpace ℝ S → ℝ := fun p =>
    ⟪z.1, toEuclid (N.massActionVectorField κ (toEuclid.symm p))⟫_ℝ
  have hfield : Continuous (fun p : EuclideanSpace ℝ S =>
      toEuclid (N.massActionVectorField κ (toEuclid.symm p))) := by
    exact (LinearMap.continuous_of_finiteDimensional (toEuclid (ι := S)).toLinearMap).comp
      ((Network.continuous_massActionVectorField N κ).comp
        (LinearMap.continuous_of_finiteDimensional (toEuclid (ι := S)).symm.toLinearMap))
  have hf : Continuous f := continuous_const.inner hfield
  apply SmoothBarrierGluing.exists_uniform_pos_margin_on_compact hK hne hf.continuousOn
  intro p hp
  have hstrict := N.massActionVectorField_inner_pos_of_mem_interior_sourceOrderNegativeCone
    κ (hpos p hp) hxs hcb (hnotcb p hp) (hz p hp)
  change 0 < f p at hstrict
  exact hstrict

/-- **Finite source-order wall cover of a compact positive patch.** If every point of a compact
positive non-equilibrium patch has an interior direction in its selected source-order chamber,
continuity gives a neighborhood with a positive margin for that direction. Compactness extracts
finitely many such directions and one common margin, with at least one selected wall supporting at
each point. This is the finite local wall data needed before the blueprint's separate tile and
offset gluing step. -/
theorem Network.exists_finite_sourceOrderWallCover_on_compact
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {K : Set (EuclideanSpace ℝ S)} (hK : IsCompact K) (hne : K.Nonempty)
    (hpos : ∀ p ∈ K, Concentration.Positive (toEuclid.symm p))
    (hnotcb : ∀ p ∈ K, ¬ N.IsComplexBalanced κ (toEuclid.symm p))
    (hdir : ∀ p ∈ K, ∃ z : N.euclideanStoichSubspace,
      z ∈ interior (((N.relativeSourceOrderNegativeCone
        (N.relativeLogStoichProjection
          (fun s => Real.log (toEuclid.symm p s) - Real.log (xstar s)))).comap
            N.euclideanStoichSubspace.subtypeL :
              ProperCone ℝ N.euclideanStoichSubspace) : Set N.euclideanStoichSubspace)) :
    ∃ z : K → N.euclideanStoichSubspace,
      (∀ p, z p ∈ interior (((N.relativeSourceOrderNegativeCone
        (N.relativeLogStoichProjection
          (fun s => Real.log (toEuclid.symm p.1 s) - Real.log (xstar s)))).comap
            N.euclideanStoichSubspace.subtypeL :
              ProperCone ℝ N.euclideanStoichSubspace) : Set N.euclideanStoichSubspace)) ∧
      ∃ t : Finset K, ∃ ε : ℝ, 0 < ε ∧
        ∀ y ∈ K, ∃ p ∈ t,
          ε ≤ ⟪(z p).1, toEuclid (N.massActionVectorField κ (toEuclid.symm y))⟫_ℝ := by
  classical
  let z : K → N.euclideanStoichSubspace := fun p => Classical.choose (hdir p.1 p.2)
  have hz (p : K) : z p ∈ interior (((N.relativeSourceOrderNegativeCone
      (N.relativeLogStoichProjection
        (fun s => Real.log (toEuclid.symm p.1 s) - Real.log (xstar s)))).comap
          N.euclideanStoichSubspace.subtypeL :
            ProperCone ℝ N.euclideanStoichSubspace) : Set N.euclideanStoichSubspace) :=
    Classical.choose_spec (hdir p.1 p.2)
  let wallField (w : N.euclideanStoichSubspace) (y : EuclideanSpace ℝ S) : ℝ :=
    ⟪w.1, toEuclid (N.massActionVectorField κ (toEuclid.symm y))⟫_ℝ
  have hfield : Continuous (fun y : EuclideanSpace ℝ S =>
      toEuclid (N.massActionVectorField κ (toEuclid.symm y))) := by
    exact (LinearMap.continuous_of_finiteDimensional (toEuclid (ι := S)).toLinearMap).comp
      ((Network.continuous_massActionVectorField N κ).comp
        (LinearMap.continuous_of_finiteDimensional (toEuclid (ι := S)).symm.toLinearMap))
  have hwallContinuous (w : N.euclideanStoichSubspace) : Continuous (wallField w) := by
    dsimp [wallField]
    exact continuous_const.inner hfield
  have hwallPositive (p : K) : 0 < wallField (z p) p.1 := by
    have hstrict := N.massActionVectorField_inner_pos_of_mem_interior_sourceOrderNegativeCone
      κ (hpos p.1 p.2) hxs hcb (hnotcb p.1 p.2) (hz p)
    change 0 < wallField (z p) p.1 at hstrict
    exact hstrict
  let margin (p : K) : ℝ := wallField (z p) p.1 / 2
  let U : EuclideanSpace ℝ S → Set (EuclideanSpace ℝ S) := fun x =>
    if hx : x ∈ K then
      {y | margin ⟨x, hx⟩ < wallField (z ⟨x, hx⟩) y}
    else Set.univ
  have hopen : ∀ x ∈ K, IsOpen (U x) := by
    intro x hx
    have heq : U x = {y | margin ⟨x, hx⟩ < wallField (z ⟨x, hx⟩) y} := by
      simp [U, hx]
    rw [heq]
    exact isOpen_lt continuous_const (hwallContinuous (z ⟨x, hx⟩))
  have hmem : ∀ x ∈ K, x ∈ U x := by
    intro x hx
    have hposx := hwallPositive ⟨x, hx⟩
    simp only [U, dif_pos hx, Set.mem_setOf_eq]
    dsimp [margin]
    linarith
  obtain ⟨t, htcover⟩ :=
    SmoothBarrierGluing.exists_finite_chart_centers hK U hopen hmem
  have htne : t.Nonempty := by
    by_contra h
    have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    obtain ⟨x, hx⟩ := hne
    have hxcover := htcover hx
    simp [ht0] at hxcover
  obtain ⟨p₀, hp₀, hmin⟩ := Finset.exists_mem_eq_inf' htne margin
  let ε : ℝ := t.inf' htne margin
  have hε : 0 < ε := by
    dsimp [ε]
    rw [hmin]
    dsimp [margin]
    exact half_pos (hwallPositive p₀)
  have hεle (p : K) (hp : p ∈ t) : ε ≤ margin p := by
    dsimp [ε]
    exact Finset.inf'_le _ hp
  refine ⟨z, hz, t, ε, hε, ?_⟩
  intro y hy
  have hycover := htcover hy
  rcases Set.mem_iUnion.mp hycover with ⟨p, hpcover⟩
  rcases Set.mem_iUnion.mp hpcover with ⟨hp, hyU⟩
  refine ⟨p, hp, ?_⟩
  have hyMargin : margin p < wallField (z p) y := by
    change y ∈ U p.1 at hyU
    simpa [U, p.2] using hyU
  exact le_of_lt (lt_of_le_of_lt (hεle p hp) hyMargin)

/-- The negative relative-log gradient belongs to the selected closed source-order cone and has
strictly positive pairing with the mass-action field away from complex balance. The projection
does not change the pairing because the field lies in the stoichiometric subspace. -/
theorem Network.massActionVectorField_inner_negRelativeLogStoichProjection_pos
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hnotcb : ¬ N.IsComplexBalanced κ x) :
    0 < ⟪-toEuclid (N.relativeLogStoichProjection
      (fun s => Real.log (x s) - Real.log (xstar s))),
      toEuclid (N.massActionVectorField κ x)⟫_ℝ := by
  let u : S → ℝ := fun s => Real.log (x s) - Real.log (xstar s)
  let X : EuclideanSpace ℝ S := toEuclid u
  let F : EuclideanSpace ℝ S := toEuclid (N.massActionVectorField κ x)
  have hfieldStoich : N.massActionVectorField κ x ∈ N.stoichSubspace := by
    rw [N.massActionVectorField_eq_sum κ x]
    exact Submodule.sum_mem _ fun r _ =>
      Submodule.smul_mem _ _ (N.reactionVector_mem_stoichSubspace r)
  have hF : F ∈ N.euclideanStoichSubspace := by
    change toEuclid (N.massActionVectorField κ x) ∈ N.euclideanStoichSubspace
    rw [Network.euclideanStoichSubspace, Submodule.mem_map]
    exact ⟨N.massActionVectorField κ x, hfieldStoich, rfl⟩
  let P : EuclideanSpace ℝ S := N.euclideanStoichSubspace.starProjection X
  have horth : ⟪X - P, F⟫_ℝ = 0 :=
    N.euclideanStoichSubspace.starProjection_inner_eq_zero X F hF
  have hproj : toEuclid (N.relativeLogStoichProjection u) = P := by
    simp [P, relativeLogStoichProjection, X]
  have hpair : ⟪X, F⟫_ℝ = ⟪P, F⟫_ℝ := by
    calc
      ⟪X, F⟫_ℝ = ⟪(X - P) + P, F⟫_ℝ := by congr 1; abel
      _ = ⟪X - P, F⟫_ℝ + ⟪P, F⟫_ℝ := inner_add_left _ _ _
      _ = ⟪P, F⟫_ℝ := by rw [horth, zero_add]
  have hdiss : (∑ s, u s * N.massActionVectorField κ x s) < 0 := by
    have hle := N.dissipation_nonpos κ hx hxs hcb
    by_contra hnot
    have hge : 0 ≤ ∑ s, u s * N.massActionVectorField κ x s := not_lt.mp hnot
    have heq : (∑ s, u s * N.massActionVectorField κ x s) = 0 := le_antisymm hle hge
    exact hnotcb (N.complexBalanced_of_dissipation_eq_zero κ hx hxs hcb (by simpa [u] using heq))
  have hpairFull : ⟪X, F⟫_ℝ = ∑ s, u s * N.massActionVectorField κ x s := by
    simp [X, F, u, inner_toEuclid]
  have hpairProj :
      ⟪toEuclid (N.relativeLogStoichProjection u), F⟫_ℝ =
        ∑ s, u s * N.massActionVectorField κ x s := by
    rw [hproj]
    exact hpair.symm.trans hpairFull
  have hresult : 0 < -⟪toEuclid (N.relativeLogStoichProjection u), F⟫_ℝ := by
    rw [hpairProj]
    exact neg_pos.mpr hdiss
  simpa [u, F] using hresult

/-- **Finite tie-safe source-order wall cover.** On a compact positive patch avoiding
complex-balanced equilibria, the negative projected relative-log gradient supplies a positive
wall direction at every point, including source-order ties where the selected closed chamber has
empty interior. Continuity and compactness produce finitely many such directions with a common
positive margin. Compactness also gives a uniform radius: every ball of that radius around a point
of `K` lies in one selected wall's strict-positive chart. This is the local-to-tile step; a single
separating surface still requires the separate blueprint gluing. -/
theorem Network.exists_finite_negativeLogWallCover_on_compact
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {K : Set (EuclideanSpace ℝ S)} (hK : IsCompact K) (hne : K.Nonempty)
    (hpos : ∀ p ∈ K, Concentration.Positive (toEuclid.symm p))
    (hnotcb : ∀ p ∈ K, ¬ N.IsComplexBalanced κ (toEuclid.symm p)) :
    ∃ z : K → N.euclideanStoichSubspace,
      (∀ p, (z p).1 ∈ N.relativeSourceOrderNegativeCone
        (N.relativeLogStoichProjection
          (fun s => Real.log (toEuclid.symm p.1 s) - Real.log (xstar s)))) ∧
      ∃ t : Finset K, ∃ ε : ℝ, 0 < ε ∧
        ((∀ y ∈ K, ∃ p ∈ t,
            ε ≤ ⟪(z p).1, toEuclid (N.massActionVectorField κ (toEuclid.symm y))⟫_ℝ) ∧
          ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ K, ∃ p ∈ t, ∀ q ∈ Metric.ball y δ,
            ε < ⟪(z p).1, toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ) := by
  classical
  let u (p : K) : S → ℝ := fun s =>
    Real.log (toEuclid.symm p.1 s) - Real.log (xstar s)
  let z (p : K) : N.euclideanStoichSubspace :=
    ⟨-toEuclid (N.relativeLogStoichProjection (u p)), by
      rw [Network.euclideanStoichSubspace, Submodule.mem_map]
      refine ⟨-N.relativeLogStoichProjection (u p),
        N.stoichSubspace.neg_mem (N.relativeLogStoichProjection_mem (u p)), ?_⟩
      simp⟩
  have hz (p : K) : (z p).1 ∈ N.relativeSourceOrderNegativeCone
      (N.relativeLogStoichProjection (u p)) := by
    change -toEuclid (N.relativeLogStoichProjection (u p)) ∈ _
    exact N.negativeRelativeLogStoichProjection_mem_relativeSourceOrderNegativeCone (u p)
  let wallField (w : N.euclideanStoichSubspace) (y : EuclideanSpace ℝ S) : ℝ :=
    ⟪w.1, toEuclid (N.massActionVectorField κ (toEuclid.symm y))⟫_ℝ
  have hfield : Continuous (fun y : EuclideanSpace ℝ S =>
      toEuclid (N.massActionVectorField κ (toEuclid.symm y))) := by
    exact (LinearMap.continuous_of_finiteDimensional (toEuclid (ι := S)).toLinearMap).comp
      ((Network.continuous_massActionVectorField N κ).comp
        (LinearMap.continuous_of_finiteDimensional (toEuclid (ι := S)).symm.toLinearMap))
  have hwallContinuous (w : N.euclideanStoichSubspace) : Continuous (wallField w) := by
    dsimp [wallField]
    exact continuous_const.inner hfield
  have hwallPositive (p : K) : 0 < wallField (z p) p.1 := by
    have h := N.massActionVectorField_inner_negRelativeLogStoichProjection_pos κ
      (hpos p.1 p.2) hxs hcb (hnotcb p.1 p.2)
    change 0 < ⟪-toEuclid (N.relativeLogStoichProjection (u p)),
      toEuclid (N.massActionVectorField κ (toEuclid.symm p.1))⟫_ℝ at h
    simpa [wallField, z, u] using h
  let margin (p : K) : ℝ := wallField (z p) p.1 / 2
  let U : EuclideanSpace ℝ S → Set (EuclideanSpace ℝ S) := fun x =>
    if hx : x ∈ K then
      {y | margin ⟨x, hx⟩ < wallField (z ⟨x, hx⟩) y}
    else Set.univ
  have hopen : ∀ x ∈ K, IsOpen (U x) := by
    intro x hx
    have heq : U x = {y | margin ⟨x, hx⟩ < wallField (z ⟨x, hx⟩) y} := by
      simp [U, hx]
    rw [heq]
    exact isOpen_lt continuous_const (hwallContinuous (z ⟨x, hx⟩))
  have hmem : ∀ x ∈ K, x ∈ U x := by
    intro x hx
    have hposx := hwallPositive ⟨x, hx⟩
    simp only [U, dif_pos hx, Set.mem_setOf_eq]
    dsimp [margin]
    linarith
  obtain ⟨t, htcover⟩ :=
    SmoothBarrierGluing.exists_finite_chart_centers hK U hopen hmem
  have htne : t.Nonempty := by
    by_contra h
    have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    obtain ⟨x, hx⟩ := hne
    have hxcover := htcover hx
    simp [ht0] at hxcover
  obtain ⟨p₀, hp₀, hmin⟩ := Finset.exists_mem_eq_inf' htne margin
  let ε : ℝ := t.inf' htne margin
  have hε : 0 < ε := by
    dsimp [ε]
    rw [hmin]
    dsimp [margin]
    exact half_pos (hwallPositive p₀)
  have hεle (p : K) (hp : p ∈ t) : ε ≤ margin p := by
    dsimp [ε]
    exact Finset.inf'_le _ hp
  refine ⟨z, hz, t, ε, hε, ?_, ?_⟩
  · intro y hy
    have hycover := htcover hy
    rcases Set.mem_iUnion.mp hycover with ⟨p, hpcover⟩
    rcases Set.mem_iUnion.mp hpcover with ⟨hp, hyU⟩
    refine ⟨p, hp, ?_⟩
    have hyMargin : margin p < wallField (z p) y := by
      change y ∈ U p.1 at hyU
      simpa [U, p.2] using hyU
    exact le_of_lt (lt_of_le_of_lt (hεle p hp) hyMargin)
  · let I := {p : K // p ∈ t}
    have hopenI : ∀ p : I, IsOpen (U p.1.1) := fun p => hopen p.1.1 p.1.2
    have hcoverI : K ⊆ ⋃ p : I, U p.1.1 := by
      intro y hy
      have hycover := htcover hy
      rcases Set.mem_iUnion.mp hycover with ⟨p, hpcover⟩
      rcases Set.mem_iUnion.mp hpcover with ⟨hp, hyU⟩
      exact Set.mem_iUnion.2 ⟨⟨p, hp⟩, hyU⟩
    obtain ⟨δ, hδ, hballs⟩ := lebesgue_number_lemma_of_metric hK hopenI hcoverI
    refine ⟨δ, hδ, ?_⟩
    intro y hy
    obtain ⟨p, hball⟩ := hballs y hy
    refine ⟨p.1, p.2, ?_⟩
    intro q hq
    have hqU : q ∈ U p.1.1 := hball hq
    have hqMargin : margin p.1 < wallField (z p.1) q := by
      change q ∈ U p.1.1 at hqU
      simpa [U, p.1.2] using hqU
    exact lt_of_le_of_lt (hεle p.1 p.2) hqMargin

/-- **A small tile inherits one inward wall.** If every point of a compact patch has a radius-`δ`
neighborhood on which some selected wall pairs with the field above `ε`, then every nonempty tile
inside the patch with diameter below `δ` lies in one such wall chart. This is the local support
fact consumed by the faithful tile construction. -/
theorem Network.exists_negativeLogWall_margin_on_small_patch
    (N : Network S) (κ : N.RateConstants)
    {K : Set (EuclideanSpace ℝ S)}
    (z : K → N.euclideanStoichSubspace) (t : Finset K) {ε δ : ℝ}
    (hcover : ∀ y ∈ K, ∃ p ∈ t, ∀ q ∈ Metric.ball y δ,
      ε < ⟪(z p).1, toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ)
    {T : Set (EuclideanSpace ℝ S)} (hne : T.Nonempty) (hTK : T ⊆ K)
    (hdiam : ∀ x ∈ T, ∀ y ∈ T, dist x y < δ) :
    ∃ p ∈ t, ∀ q ∈ T,
      ε < ⟪(z p).1, toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨p, hp, hchart⟩ := hcover x (hTK hx)
  refine ⟨p, hp, ?_⟩
  intro q hq
  have hqball : q ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, dist_comm]
    exact hdiam x hx q hq
  exact hchart q hqball

/-- A compact patch can be covered by finitely many small balls, each carrying one fixed
inward wall on the entire ball. The radius is chosen so each patch has diameter below the local
chart radius. -/
theorem Network.exists_finite_negativeLogWall_patch_cover
    (N : Network S) (κ : N.RateConstants)
    {K : Set (EuclideanSpace ℝ S)} (hK : IsCompact K)
    (z : K → N.euclideanStoichSubspace) (t : Finset K) {ε δ : ℝ}
    (hδ : 0 < δ)
    (hcover : ∀ y ∈ K, ∃ p ∈ t, ∀ q ∈ Metric.ball y δ,
      ε < ⟪(z p).1, toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ) :
    ∃ C : Finset K,
      K ⊆ ⋃ c ∈ C, Metric.ball c.1 (δ / 3) ∧
      (∀ c ∈ C, ∃ p ∈ t, ∀ q ∈ Metric.ball c.1 (δ / 3),
        ε < ⟪(z p).1, toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ) ∧
      (∀ c ∈ C, ∀ x ∈ Metric.ball c.1 (δ / 3), ∀ y ∈ Metric.ball c.1 (δ / 3),
        dist x y < δ) := by
  let U : EuclideanSpace ℝ S → Set (EuclideanSpace ℝ S) :=
    fun x => Metric.ball x (δ / 3)
  have hopen : ∀ x ∈ K, IsOpen (U x) := by
    intro x hx
    exact Metric.isOpen_ball
  have hmem : ∀ x ∈ K, x ∈ U x := by
    intro x hx
    exact Metric.mem_ball_self (div_pos hδ (by norm_num))
  obtain ⟨C, hCcover⟩ := SmoothBarrierGluing.exists_finite_chart_centers hK U hopen hmem
  refine ⟨C, ?_, ?_, ?_⟩
  · simpa [U] using hCcover
  · intro c hc
    obtain ⟨p, hp, hchart⟩ := hcover c.1 c.2
    refine ⟨p, hp, ?_⟩
    intro q hq
    apply hchart q
    rw [Metric.mem_ball] at hq ⊢
    exact lt_of_lt_of_le hq (by nlinarith [hδ])
  · intro c hc x hx y hy
    rw [Metric.mem_ball] at hx hy
    calc
      dist x y ≤ dist x c.1 + dist c.1 y := dist_triangle x c.1 y
      _ < δ / 3 + δ / 3 := add_lt_add hx (by simpa [dist_comm] using hy)
      _ < δ := by linarith


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

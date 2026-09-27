import CRNT.Geometry.SmoothBarrierGluing
import CRNT.Geometry.FanWallsCrossed
import CRNT.Geometry.FanRefinement
import CRNT.Geometry.ToricStrictSupport
import CRNT.Dynamics.DissipationBound
import CRNT.Dynamics.ComplexBalanceStoichFanInclusion
import CRNT.Geometry.ZeroSeparatingInduction
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Thickening

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


/-- A strictly positive pairing with the mass-action field at a positive concentration is
witnessed by a reaction whose displacement has positive pairing with the same normal. Weak
reversibility then makes that reaction's normal an active wall. This turns the local inward-wall
data selected on Craciun blueprint tiles into the active-wall certificates consumed by the
zero-separating surface construction. -/
theorem Network.WeaklyReversible.activeWall_of_positive_toricField_pairing
    {N : Network S} (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive) (n : S → ℝ)
    (hpair : 0 < ⟪toEuclid n,
      N.toricMassActionField κ (toEuclid x)⟫_ℝ) :
    N.ActiveWall n := by
  rw [N.inner_toricMassActionField_eq_sum κ n (toEuclid x)] at hpair
  have hsum : 0 < ∑ r : N.R,
      N.massActionRate κ r x *
      ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ := by
    simpa using hpair
  have hterm : ∃ r : N.R, 0 < N.massActionRate κ r x *
      ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ := by
    by_contra hnone
    have hnonpos : ∀ r ∈ (Finset.univ : Finset N.R),
        N.massActionRate κ r x *
          ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ ≤ 0 := by
      intro r _
      exact le_of_not_gt (fun hr => hnone ⟨r, hr⟩)
    have hsum_nonpos : ∑ r : N.R, N.massActionRate κ r x *
        ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ ≤ 0 :=
      Finset.sum_nonpos hnonpos
    linarith
  obtain ⟨r, hr⟩ := hterm
  have hrate : 0 < N.massActionRate κ r x := N.massActionRate_pos κ r hx
  have hdisplacement : 0 <
      ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ := by
    rcases mul_pos_iff.mp hr with ⟨_, hdisp⟩ | ⟨hrateNeg, _⟩
    · exact hdisp
    · exact (not_lt_of_ge hrate.le hrateNeg).elim
  have hpotential := N.reaction_strictlyInward_iff_potential_lt n r |>.mp hdisplacement
  exact ⟨(N.reaction r).source, (N.reaction r).target,
    N.reaches_of_reaction r, hwr r, ne_of_lt hpotential⟩


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

/-- Heine-Cantor transfers any positive state-space chart radius to a coordinate radius on a
compact face patch. This is the compactness step used to choose the projected-base and fiber scales
before selecting one wall on each refined tile. -/
theorem exists_uniform_chart_radius_on_compact_facePatch
    {n : ℕ} {facePatch : Set (Fin (n + 1) → ℝ)}
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S) (hψ : Continuous ψ)
    (hfaceCompact : IsCompact facePatch) {δwall : ℝ} (hδwall : 0 < δwall) :
    ∃ δcoord : ℝ, 0 < δcoord ∧
      ∀ x ∈ facePatch, ∀ y ∈ facePatch, dist x y < δcoord →
        dist (ψ x) (ψ y) < δwall := by
  obtain ⟨δcoord, hδcoord, hmap⟩ :=
    (Metric.uniformContinuousOn_iff.mp
      (hfaceCompact.uniformContinuousOn_of_continuous hψ.continuousOn)) δwall hδwall
  exact ⟨δcoord, hδcoord, hmap⟩

/-- A sufficiently fine restricted one-bit fiber patch inherits one fixed inward wall from the
compact wall-chart cover. The geometric strip estimate controls distance in fiber coordinates;
`hmapDiam` transfers that bound through the chosen state-space chart, after which the existing
small-patch lemma selects a single wall valid on the entire patch. -/
theorem Network.exists_negativeLogWall_on_oneBitFiberPatch
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {baseTile : ι → Set (Fin n → ℝ)} {lower upper : (Fin n → ℝ) → ℝ}
    {epsilon : ℝ}
    (cover : CRNT.ZeroSeparatingInduction.CompactOneBitFiberPatchCover
      facePatch base baseTile lower upper epsilon)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S)
    {K : Set (EuclideanSpace ℝ S)} (z : K → N.euclideanStoichSubspace)
    (t : Finset K) {ε δwall δcoord η tolerance : ℝ}
    (hchart : ∀ y ∈ K, ∃ p ∈ t, ∀ q ∈ Metric.ball y δwall,
      ε < ⟪(z p).1, toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ)
    (p : Σ i : ι, Fin (cover.tiling.subdivisionCount + 1))
    (hne : (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
      (baseTile p.1) lower upper p.2).Nonempty)
    (himage : ψ '' (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
      (baseTile p.1) lower upper p.2) ⊆ K)
    (hmapDiam : ∀ x ∈ facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2,
      ∀ y ∈ facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2,
      dist x y < δcoord → dist (ψ x) (ψ y) < δwall)
    (hprojectedSmall : ∀ a ∈ baseTile p.1, ∀ b ∈ baseTile p.1,
      dist a b < η)
    (hendpointVariation : ∀ a ∈ baseTile p.1, ∀ b ∈ baseTile p.1,
      dist a b < η →
        dist (CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpoint lower upper p.2.succ a)
          (CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpoint lower upper p.2.succ b) < tolerance)
    (hηsmall : η < δcoord)
    (hbudget : epsilon + tolerance < δcoord) (hδcoord : 0 < δcoord) :
    ∃ wall ∈ t, ∀ q ∈
      ψ '' (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2),
      ε < ⟪(z wall).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ := by
  let patch := facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
    (baseTile p.1) lower upper p.2
  have hdiam : ∀ x ∈ ψ '' patch, ∀ y ∈ ψ '' patch, dist x y < δwall := by
    intro x hx y hy
    rcases hx with ⟨x₀, hx₀, rfl⟩
    rcases hy with ⟨y₀, hy₀, rfl⟩
    apply hmapDiam x₀ hx₀ y₀ hy₀
    have hxTile : x₀ ∈ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2 := hx₀.2
    have hyTile : y₀ ∈ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2 := hy₀.2
    have hxbase : CRNT.ZeroSeparatingInduction.forgetLastCoordinate n x₀ ∈ baseTile p.1 := by
      change (let y := CRNT.ZeroSeparatingInduction.forgetLastCoordinate n x₀
        y ∈ baseTile p.1 ∧ _) at hxTile
      exact hxTile.1
    have hybase : CRNT.ZeroSeparatingInduction.forgetLastCoordinate n y₀ ∈ baseTile p.1 := by
      change (let y := CRNT.ZeroSeparatingInduction.forgetLastCoordinate n y₀
        y ∈ baseTile p.1 ∧ _) at hyTile
      exact hyTile.1
    exact CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile_pair_dist_lt
      (baseTile p.1) lower upper epsilon tolerance δcoord η p.2 x₀ y₀ hxTile hyTile
      (hprojectedSmall _ hxbase _ hybase)
      hendpointVariation
      (by
        intro y hy
        exact cover.tiling.fiber_width_le p.2 y (cover.baseTile_subset p.1 hy))
      hηsmall hbudget hδcoord
  have hpatchNonempty : (ψ '' patch).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨ψ x, ⟨x, hx, rfl⟩⟩
  exact N.exists_negativeLogWall_margin_on_small_patch κ z t hchart
    hpatchNonempty himage hdiam

/-- A compact one-bit refinement admits a wall label on every nonempty restricted tile whenever
the projected tiles are small enough for the endpoint graphs to vary within the local wall-chart
budget. This packages the local selections as one assignment on the refined tile indices, ready
for the later face-incidence and inward-orientation construction. -/
theorem Network.exists_oneBitFiberPatchWallSelection
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {baseTile : ι → Set (Fin n → ℝ)} {lower upper : (Fin n → ℝ) → ℝ}
    {epsilon : ℝ}
    (cover : CRNT.ZeroSeparatingInduction.CompactOneBitFiberPatchCover
      facePatch base baseTile lower upper epsilon)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S)
    {K : Set (EuclideanSpace ℝ S)} (z : K → N.euclideanStoichSubspace)
    (t : Finset K) {ε δwall δcoord η tolerance : ℝ}
    (hchart : ∀ y ∈ K, ∃ p ∈ t, ∀ q ∈ Metric.ball y δwall,
      ε < ⟪(z p).1, toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ)
    (himage : ∀ p : Σ i : ι, Fin (cover.tiling.subdivisionCount + 1),
      ψ '' (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2) ⊆ K)
    (hmapDiam : ∀ p : Σ i : ι, Fin (cover.tiling.subdivisionCount + 1),
      ∀ x ∈ facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2,
      ∀ y ∈ facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2,
      dist x y < δcoord → dist (ψ x) (ψ y) < δwall)
    (hprojectedSmall : ∀ p : Σ i : ι, Fin (cover.tiling.subdivisionCount + 1),
      ∀ a ∈ baseTile p.1, ∀ b ∈ baseTile p.1, dist a b < η)
    (hendpointVariation : ∀ p : Σ i : ι, Fin (cover.tiling.subdivisionCount + 1),
      ∀ a ∈ baseTile p.1, ∀ b ∈ baseTile p.1, dist a b < η →
        dist (CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpoint
          lower upper p.2.succ a)
          (CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpoint
            lower upper p.2.succ b) < tolerance)
    (hηsmall : η < δcoord) (hbudget : epsilon + tolerance < δcoord)
    (hδcoord : 0 < δcoord) :
    ∃ selected : (Σ i : ι, Fin (cover.tiling.subdivisionCount + 1)) → Option K,
      (∀ p, ¬ (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2).Nonempty → selected p = none) ∧
      (∀ p, (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2).Nonempty → ∃ wall, selected p = some wall) ∧
      (∀ p wall, selected p = some wall → wall ∈ t ∧ ∀ q ∈
        ψ '' (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2),
        ε < ⟪(z wall).1,
          toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ) := by
  classical
  have hlocal : ∀ (p : Σ i : ι, Fin (cover.tiling.subdivisionCount + 1)),
      (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2).Nonempty →
      ∃ wall ∈ t, ∀ q ∈
        ψ '' (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2),
        ε < ⟪(z wall).1,
          toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ := by
    intro p hne
    exact N.exists_negativeLogWall_on_oneBitFiberPatch κ cover ψ z t hchart p
      hne (himage p) (hmapDiam p) (hprojectedSmall p) (hendpointVariation p)
      hηsmall hbudget hδcoord
  let selected : (Σ i : ι, Fin (cover.tiling.subdivisionCount + 1)) → Option K :=
    fun p => if hne : (facePatch ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2).Nonempty then
      some (Classical.choose (hlocal p hne)) else none
  refine ⟨selected, ?_, ?_, ?_⟩
  · intro p hne
    simp [selected, hne]
  · intro p hne
    refine ⟨Classical.choose (hlocal p hne), ?_⟩
    simp [selected, hne]
  · intro p wall hselected
    dsimp [selected] at hselected
    split at hselected
    · rename_i hne
      have hwall : Classical.choose (hlocal p hne) = wall := by
        simpa using hselected
      rw [← hwall]
      exact Classical.choose_spec (hlocal p hne)
    · simp at hselected

/-- On the compact positive projective radial patch, extract the finite inward wall charts and a
uniform coordinate scale before choosing any blueprint subdivision. This separates the compact
chart data from the tile family, so later fan refinements can select their walls on their own
subdivision without attempting to reindex an unrelated atlas. -/
theorem Network.exists_compactProjectiveRadialWallChart
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (diagramTile : ι → Set (Fin (n + 1) → ℝ)) (upper : Fin (n + 1) → ℝ)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S) (hψ : Continuous ψ)
    (hdiagramNonnegative : ∀ k x, x ∈ diagramTile k → ∀ i, 0 ≤ x i)
    (hdiagramNonzero : ∀ k x, x ∈ diagramTile k → x ≠ 0)
    (hdiagramAnchor : ∀ k x, x ∈ diagramTile k → x 0 = 1)
    (hdiagramCompact : ∀ k, IsCompact (diagramTile k))
    (hupper : ∀ i, 0 < upper i)
    (hdiagramCoversNormalizedDomain : ∀ x,
      x ∈ ZeroSeparatingInduction.craciunProjectiveDomain → x 0 = 1 →
        x ∈ ⋃ k, diagramTile k)
    (hfaceNonempty : (⋃ k, ZeroSeparatingInduction.radialBoxDiagramTile
      (diagramTile k) upper (hdiagramNonnegative k) (hdiagramNonzero k) hupper ∩
        ZeroSeparatingInduction.craciunProjectiveDomain).Nonempty)
    (hpositive : ∀ x, x ∈ ⋃ k, ZeroSeparatingInduction.radialBoxDiagramTile
      (diagramTile k) upper (hdiagramNonnegative k) (hdiagramNonzero k) hupper ∩
        ZeroSeparatingInduction.craciunProjectiveDomain →
      Concentration.Positive (toEuclid.symm (ψ x)))
    (hnotcb : ∀ x, x ∈ ⋃ k, ZeroSeparatingInduction.radialBoxDiagramTile
      (diagramTile k) upper (hdiagramNonnegative k) (hdiagramNonzero k) hupper ∩
        ZeroSeparatingInduction.craciunProjectiveDomain →
      ¬ N.IsComplexBalanced κ (toEuclid.symm (ψ x))) :
    let facePatch : Set (Fin (n + 1) → ℝ) :=
      ⋃ k, ZeroSeparatingInduction.radialBoxDiagramTile (diagramTile k) upper
        (hdiagramNonnegative k) (hdiagramNonzero k) hupper ∩
          ZeroSeparatingInduction.craciunProjectiveDomain
    let K : Set (EuclideanSpace ℝ S) := ψ '' facePatch
    ∃ δcoord δwall : ℝ, 0 < δcoord ∧ 0 < δwall ∧
      ∃ z : K → N.euclideanStoichSubspace, ∃ t : Finset K, ∃ ε : ℝ,
        0 < ε ∧
        (∀ y ∈ K, ∃ wall ∈ t, ∀ q ∈ Metric.ball y δwall,
          ε < ⟪(z wall).1,
            toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ) ∧
        (∀ x y, x ∈ facePatch → y ∈ facePatch → dist x y < δcoord →
          dist (ψ x) (ψ y) < δwall) := by
  classical
  let facePatch : Set (Fin (n + 1) → ℝ) :=
    ⋃ k, ZeroSeparatingInduction.radialBoxDiagramTile (diagramTile k) upper
      (hdiagramNonnegative k) (hdiagramNonzero k) hupper ∩
        ZeroSeparatingInduction.craciunProjectiveDomain
  let K : Set (EuclideanSpace ℝ S) := ψ '' facePatch
  have hfaceCompact : IsCompact facePatch := by
    dsimp [facePatch]
    exact (ZeroSeparatingInduction.isCompact_and_covers_projectiveRadialTiles
      diagramTile upper hdiagramNonnegative hdiagramAnchor hdiagramCompact hupper
      hdiagramCoversNormalizedDomain).1
  have hKcompact : IsCompact K := hfaceCompact.image hψ
  have hKne : K.Nonempty := by
    obtain ⟨x, hx⟩ := hfaceNonempty
    exact ⟨ψ x, ⟨x, hx, rfl⟩⟩
  have hKpos : ∀ p ∈ K, Concentration.Positive (toEuclid.symm p) := by
    rintro p ⟨x, hx, rfl⟩
    exact hpositive x hx
  have hKnotcb : ∀ p ∈ K, ¬ N.IsComplexBalanced κ (toEuclid.symm p) := by
    rintro p ⟨x, hx, rfl⟩
    exact hnotcb x hx
  obtain ⟨z, _, t, ε, hε, _, δwall, hδwall, hchart⟩ :=
    N.exists_finite_negativeLogWallCover_on_compact κ hxs hcb hKcompact hKne hKpos hKnotcb
  obtain ⟨δcoord, hδcoord, hmap⟩ :=
    exists_uniform_chart_radius_on_compact_facePatch ψ hψ hfaceCompact hδwall
  dsimp only
  exact ⟨δcoord, δwall, hδcoord, hδwall, z, t, ε, hε, hchart,
    by
      intro x y hx hy hdist
      exact hmap x hx y hy hdist⟩

/-- Craciun v3, §7.4.3 Case 1.2 and §8 Step 1: on a compact positive projective face patch,
choose the fiber and projected-base tile scales from Heine-Cantor, then select one inward wall on
every nonempty refined patch. This composes the projective small-tile construction with the local
wall selector, rather than leaving the scale and map-diameter obligations as caller hypotheses. -/
theorem Network.exists_compactProjectiveRadialWallSelection
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (diagramTile : ι → Set (Fin (n + 1) → ℝ)) (upper : Fin (n + 1) → ℝ)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S) (hψ : Continuous ψ)
    (hdiagramNonnegative : ∀ k x, x ∈ diagramTile k → ∀ i, 0 ≤ x i)
    (hdiagramNonzero : ∀ k x, x ∈ diagramTile k → x ≠ 0)
    (hdiagramAnchor : ∀ k x, x ∈ diagramTile k → x 0 = 1)
    (hdiagramCompact : ∀ k, IsCompact (diagramTile k))
    (hupper : ∀ i, 0 < upper i)
    (hdiagramCoversNormalizedDomain : ∀ x,
      x ∈ ZeroSeparatingInduction.craciunProjectiveDomain → x 0 = 1 →
        x ∈ ⋃ k, diagramTile k)
    (hprojectedInteriorsDisjoint : ∀ i j, i ≠ j →
      interior (ZeroSeparatingInduction.forgetLastCoordinate n ''
        (ZeroSeparatingInduction.radialBoxDiagramTile (diagramTile i) upper
          (hdiagramNonnegative i) (hdiagramNonzero i) hupper ∩
            ZeroSeparatingInduction.craciunProjectiveDomain)) ∩
      interior (ZeroSeparatingInduction.forgetLastCoordinate n ''
        (ZeroSeparatingInduction.radialBoxDiagramTile (diagramTile j) upper
          (hdiagramNonnegative j) (hdiagramNonzero j) hupper ∩
            ZeroSeparatingInduction.craciunProjectiveDomain)) = ∅)
    (hfaceNonempty : (⋃ k, ZeroSeparatingInduction.radialBoxDiagramTile
      (diagramTile k) upper (hdiagramNonnegative k) (hdiagramNonzero k) hupper ∩
        ZeroSeparatingInduction.craciunProjectiveDomain).Nonempty)
    (hpositive : ∀ x, x ∈ ⋃ k, ZeroSeparatingInduction.radialBoxDiagramTile
      (diagramTile k) upper (hdiagramNonnegative k) (hdiagramNonzero k) hupper ∩
        ZeroSeparatingInduction.craciunProjectiveDomain →
      Concentration.Positive (toEuclid.symm (ψ x)))
    (hnotcb : ∀ x, x ∈ ⋃ k, ZeroSeparatingInduction.radialBoxDiagramTile
      (diagramTile k) upper (hdiagramNonnegative k) (hdiagramNonzero k) hupper ∩
        ZeroSeparatingInduction.craciunProjectiveDomain →
      ¬ N.IsComplexBalanced κ (toEuclid.symm (ψ x))) :
    let facePatch : Set (Fin (n + 1) → ℝ) :=
      ⋃ k, ZeroSeparatingInduction.radialBoxDiagramTile (diagramTile k) upper
        (hdiagramNonnegative k) (hdiagramNonzero k) hupper ∩
          ZeroSeparatingInduction.craciunProjectiveDomain
    let K : Set (EuclideanSpace ℝ S) := ψ '' facePatch
    ∃ δcoord : ℝ, 0 < δcoord ∧
    ∃ m : ℕ, ∃ baseTile : ι × Fin m → Set (Fin n → ℝ),
      ∃ cover : ZeroSeparatingInduction.CompactOneBitFiberPatchCover facePatch
        (ZeroSeparatingInduction.forgetLastCoordinate n '' facePatch) baseTile (fun _ => 0)
          (fun _ => upper (Fin.last n)) (δcoord / 4),
      ∃ z : K → N.euclideanStoichSubspace, ∃ t : Finset K, ∃ ε : ℝ,
      ∃ selected : (Σ i : ι × Fin m,
          Fin (cover.tiling.subdivisionCount + 1)) → Option K,
        0 < ε ∧
        (∀ p, ¬ (facePatch ∩ ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) (fun _ => 0) (fun _ => upper (Fin.last n)) p.2).Nonempty →
            selected p = none) ∧
        (∀ p, (facePatch ∩ ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) (fun _ => 0) (fun _ => upper (Fin.last n)) p.2).Nonempty →
            ∃ wall, selected p = some wall) ∧
        (∀ p wall, selected p = some wall → wall ∈ t ∧ ∀ q ∈
          ψ '' (facePatch ∩ ZeroSeparatingInduction.projectionFiberSubdivisionTile
            (baseTile p.1) (fun _ => 0) (fun _ => upper (Fin.last n)) p.2),
          ε < ⟪(z wall).1,
            toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ) ∧
      (ZeroSeparatingInduction.forgetLastCoordinate n '' facePatch = ⋃ p, baseTile p) ∧
      (∀ p, IsCompact (baseTile p)) ∧
      (∀ p q, p ≠ q → interior (baseTile p) ∩ interior (baseTile q) = ∅) := by
  classical
  let facePatch : Set (Fin (n + 1) → ℝ) :=
    ⋃ k, ZeroSeparatingInduction.radialBoxDiagramTile (diagramTile k) upper
      (hdiagramNonnegative k) (hdiagramNonzero k) hupper ∩
        ZeroSeparatingInduction.craciunProjectiveDomain
  let K : Set (EuclideanSpace ℝ S) := ψ '' facePatch
  have hfaceCompact : IsCompact facePatch := by
    dsimp [facePatch]
    exact (ZeroSeparatingInduction.isCompact_and_covers_projectiveRadialTiles
      diagramTile upper hdiagramNonnegative hdiagramAnchor hdiagramCompact hupper
      hdiagramCoversNormalizedDomain).1
  have hKcompact : IsCompact K := hfaceCompact.image hψ
  have hKne : K.Nonempty := by
    obtain ⟨x, hx⟩ := hfaceNonempty
    exact ⟨ψ x, ⟨x, hx, rfl⟩⟩
  have hKpos : ∀ p ∈ K, Concentration.Positive (toEuclid.symm p) := by
    rintro p ⟨x, hx, rfl⟩
    exact hpositive x hx
  have hKnotcb : ∀ p ∈ K, ¬ N.IsComplexBalanced κ (toEuclid.symm p) := by
    rintro p ⟨x, hx, rfl⟩
    exact hnotcb x hx
  obtain ⟨z, _, t, ε, hε, _, δwall, hδwall, hchart⟩ :=
    N.exists_finite_negativeLogWallCover_on_compact κ hxs hcb hKcompact hKne hKpos hKnotcb
  obtain ⟨δcoord, hδcoord, hmap⟩ :=
    exists_uniform_chart_radius_on_compact_facePatch ψ hψ hfaceCompact hδwall
  let εtile : ℝ := δcoord / 4
  have hεtile : 0 < εtile := by dsimp [εtile]; positivity
  have heta : 0 < δcoord / 4 := by positivity
  obtain ⟨m, baseTile, coverData⟩ :=
    ZeroSeparatingInduction.compactProjectiveRadialFamily_smallPatchCover_refiningDiagramTiles
      diagramTile upper εtile (δcoord / 4) hdiagramNonnegative hdiagramNonzero
      hdiagramAnchor hdiagramCompact hupper hεtile heta hdiagramCoversNormalizedDomain
      hprojectedInteriorsDisjoint
  let cover := coverData.1
  have hsmall := coverData.2.1
  have hbaseCover := coverData.2.2.1
  have hbaseTileCompact := coverData.2.2.2.1
  have hbaseTileDisjoint := coverData.2.2.2.2
  have himage : ∀ p : Σ i : ι × Fin m, Fin (cover.tiling.subdivisionCount + 1),
      ψ '' (facePatch ∩ ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) (fun _ => 0) (fun _ => upper (Fin.last n)) p.2) ⊆ K := by
    intro p q hq
    rcases hq with ⟨x, hx, rfl⟩
    exact ⟨x, hx.1, rfl⟩
  have hmapDiam : ∀ p : Σ i : ι × Fin m, Fin (cover.tiling.subdivisionCount + 1),
      ∀ x ∈ facePatch ∩ ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) (fun _ => 0) (fun _ => upper (Fin.last n)) p.2,
      ∀ y ∈ facePatch ∩ ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) (fun _ => 0) (fun _ => upper (Fin.last n)) p.2,
      dist x y < δcoord → dist (ψ x) (ψ y) < δwall := by
    intro p x hx y hy hdist
    exact hmap x hx.1 y hy.1 hdist
  have hprojectedSmall : ∀ p : Σ i : ι × Fin m, Fin (cover.tiling.subdivisionCount + 1),
      ∀ a ∈ baseTile p.1, ∀ b ∈ baseTile p.1, dist a b < δcoord / 4 := by
    intro p a ha b hb
    exact hsmall p.1 a ha b hb
  have hendpointVariation : ∀ p : Σ i : ι × Fin m, Fin (cover.tiling.subdivisionCount + 1),
      ∀ a ∈ baseTile p.1, ∀ b ∈ baseTile p.1, dist a b < δcoord / 4 →
        dist (ZeroSeparatingInduction.projectionFiberSubdivisionEndpoint
          (fun _ => 0) (fun _ => upper (Fin.last n)) p.2.succ a)
          (ZeroSeparatingInduction.projectionFiberSubdivisionEndpoint
            (fun _ => 0) (fun _ => upper (Fin.last n)) p.2.succ b) < δcoord / 4 := by
    intro p a ha b hb hab
    have heq : ZeroSeparatingInduction.projectionFiberSubdivisionEndpoint
        (fun _ => 0) (fun _ => upper (Fin.last n)) p.2.succ a =
        ZeroSeparatingInduction.projectionFiberSubdivisionEndpoint
          (fun _ => 0) (fun _ => upper (Fin.last n)) p.2.succ b := by
      simp [ZeroSeparatingInduction.projectionFiberSubdivisionEndpoint,
        ZeroSeparatingInduction.tileScaleInterpolation]
    rw [heq]
    simpa using heta
  have hbudget : εtile + δcoord / 4 < δcoord := by
    dsimp [εtile]
    linarith
  obtain ⟨selected, hnone, hsome, hselected⟩ :=
    N.exists_oneBitFiberPatchWallSelection κ cover ψ z t hchart himage hmapDiam
      hprojectedSmall hendpointVariation (by linarith) hbudget hδcoord
  dsimp only
  exact ⟨δcoord, hδcoord, m, baseTile, cover, z, t, ε, selected, hε,
    hnone, hsome, hselected, hbaseCover, hbaseTileCompact, hbaseTileDisjoint⟩

/-- A selected inward wall on a compact one-bit tile produces a differentiable local barrier.
Compactness lets its affine offset dominate the finite tail of other walls, and the existing
dominant-head estimate then makes the smooth wall list nonincreasing along the toric mass-action
field throughout that tile. This is the local analytic output consumed by the later cross-tile
gluing step. -/
theorem Network.exists_selected_oneBitFiberPatch_smoothBarrier
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {baseTile : ι → Set (Fin n → ℝ)} {lower upper : (Fin n → ℝ) → ℝ}
    {epsilon : ℝ}
    (cover : CRNT.ZeroSeparatingInduction.CompactOneBitFiberPatchCover
      facePatch base baseTile lower upper epsilon)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S) (hψ : Continuous ψ)
    {K : Set (EuclideanSpace ℝ S)} (z : K → N.euclideanStoichSubspace)
    (t : Finset K) {ε : ℝ} (hε : 0 < ε)
    (selected : (Σ i : ι, Fin (cover.tiling.subdivisionCount + 1)) → Option K)
    (hselected : ∀ p wall, selected p = some wall → wall ∈ t ∧ ∀ q ∈
      ψ '' (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2),
      ε < ⟪(z wall).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ)
    (p : Σ i : ι, Fin (cover.tiling.subdivisionCount + 1)) (wall : K)
    (hwall : selected p = some wall)
    (tailHead : (EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ)
    (tail : List ((EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ))
    : ∃ gap a : ℝ, ∀ q ∈
      ψ '' (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2),
      ∃ D : EuclideanSpace ℝ S →L[ℝ] ℝ,
        HasFDerivAt
          (SmoothBarrierGluing.smoothWallList
            (innerSL ℝ (z wall).1, a) (tailHead :: tail)) D q ∧
        D (toEuclid (N.massActionVectorField κ (toEuclid.symm q))) ≤ 0 := by
  let patch := facePatch ∩
    CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
      (baseTile p.1) lower upper p.2
  have hcompact : IsCompact (ψ '' patch) :=
    (cover.facePatch_tile_compact p).image hψ
  have hwall := hselected p wall hwall
  have hhead : ∀ q ∈ ψ '' patch,
      ε ≤ innerSL ℝ (z wall).1
        (toEuclid (N.massActionVectorField κ (toEuclid.symm q))) := by
    intro q hq
    simpa only [innerSL_apply_apply] using le_of_lt (hwall.2 q hq)
  have hfield : Continuous
      (fun q : EuclideanSpace ℝ S =>
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))) := by
    exact (LinearMap.continuous_of_finiteDimensional
      (toEuclid (ι := S)).toLinearMap).comp
        ((Network.continuous_massActionVectorField N κ).comp
          (LinearMap.continuous_of_finiteDimensional
            (toEuclid (ι := S)).symm.toLinearMap))
  exact SmoothBarrierGluing.exists_compact_wallBarrier_offset_with_smoothWallList_nonpos_of_continuousField
    hfield (ψ '' patch) hcompact (innerSL ℝ (z wall).1) tailHead tail hε hhead

/-- The compact-patch barriers selected on two intersecting refined tiles can be smoothly glued
on their entire overlap. The offsets and finite wall tail are the actual ones supplied by the
tilewise dominant-head construction; membership in the overlap lets each tile's derivative bound
be applied at the same point. This is the analytic pairwise-gluing step for the finite blueprint.
-/
theorem Network.exists_overlapping_oneBitFiberPatch_localSmoothMax
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {baseTile : ι → Set (Fin n → ℝ)} {lower upper : (Fin n → ℝ) → ℝ}
    {epsilon : ℝ}
    (cover : CRNT.ZeroSeparatingInduction.CompactOneBitFiberPatchCover
      facePatch base baseTile lower upper epsilon)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S) (hψ : Continuous ψ)
    {K : Set (EuclideanSpace ℝ S)} (z : K → N.euclideanStoichSubspace)
    (t : Finset K) {ε : ℝ} (hε : 0 < ε)
    (selected : (Σ i : ι, Fin (cover.tiling.subdivisionCount + 1)) → Option K)
    (hselected : ∀ p wall, selected p = some wall → wall ∈ t ∧ ∀ q ∈
      ψ '' (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2),
      ε < ⟪(z wall).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ)
    (p r : Σ i : ι, Fin (cover.tiling.subdivisionCount + 1))
    (wallP wallR : K)
    (hwP : selected p = some wallP) (hwR : selected r = some wallR)
    (tailHead : (EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ)
    (tail : List ((EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ)) :
    ∃ gapP aP gapR aR : ℝ,
      ∀ q ∈ ψ ''
        ((facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
            (baseTile p.1) lower upper p.2) ∩
          (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
            (baseTile r.1) lower upper r.2)),
        ∃ D : EuclideanSpace ℝ S →L[ℝ] ℝ,
          HasFDerivAt
            (SmoothBarrierGluing.smoothMaxF
              (SmoothBarrierGluing.smoothWallList
                (innerSL ℝ (z wallP).1, aP) (tailHead :: tail))
              (SmoothBarrierGluing.smoothWallList
                (innerSL ℝ (z wallR).1, aR) (tailHead :: tail))) D q ∧
          D (toEuclid (N.massActionVectorField κ (toEuclid.symm q))) ≤ 0 := by
  obtain ⟨gapP, aP, hbarrierP⟩ := N.exists_selected_oneBitFiberPatch_smoothBarrier
    κ cover ψ hψ z t hε selected hselected p wallP hwP tailHead tail
  obtain ⟨gapR, aR, hbarrierR⟩ := N.exists_selected_oneBitFiberPatch_smoothBarrier
    κ cover ψ hψ z t hε selected hselected r wallR hwR tailHead tail
  refine ⟨gapP, aP, gapR, aR, ?_⟩
  intro q hq
  rcases hq with ⟨x, ⟨hxP, hxR⟩, rfl⟩
  have hqP : ψ x ∈ ψ '' (facePatch ∩
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2) := ⟨x, hxP, rfl⟩
  have hqR : ψ x ∈ ψ '' (facePatch ∩
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile r.1) lower upper r.2) := ⟨x, hxR, rfl⟩
  obtain ⟨DP, hDP, hDPnonpos⟩ := hbarrierP (ψ x) hqP
  obtain ⟨DR, hDR, hDRnonpos⟩ := hbarrierR (ψ x) hqR
  exact SmoothBarrierGluing.smoothMaxF_descends_along
    (X := fun q : EuclideanSpace ℝ S =>
      toEuclid (N.massActionVectorField κ (toEuclid.symm q)))
    hDP hDR hDPnonpos hDRnonpos

/-- Every nonempty patch of a compact one-bit blueprint can be assigned its own compactly
dominant smooth wall barrier at once. The pointwise construction uses finite-dimensional
classical choice over the tile index; the empty patches are irrelevant to descent. This is the
simultaneous tile-barrier atlas needed before applying Craciun's face-by-face gluing order. -/
theorem Network.exists_simultaneous_oneBitFiberPatch_barriers
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {baseTile : ι → Set (Fin n → ℝ)} {lower upper : (Fin n → ℝ) → ℝ}
    {epsilon : ℝ}
    (cover : CRNT.ZeroSeparatingInduction.CompactOneBitFiberPatchCover
      facePatch base baseTile lower upper epsilon)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S) (hψ : Continuous ψ)
    {K : Set (EuclideanSpace ℝ S)} (z : K → N.euclideanStoichSubspace)
    (t : Finset K) {ε : ℝ} (hε : 0 < ε)
    (selected : (Σ i : ι, Fin (cover.tiling.subdivisionCount + 1)) → Option K)
    (hselected : ∀ p wall, selected p = some wall → wall ∈ t ∧ ∀ q ∈
      ψ '' (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2),
      ε < ⟪(z wall).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ)
    (hlabels : ∀ p, (facePatch ∩
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2).Nonempty → ∃ wall, selected p = some wall)
    (tailHead : (EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ)
    (tail : List ((EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ)) :
    ∃ offset : (Σ i : ι, Fin (cover.tiling.subdivisionCount + 1)) → ℝ,
      ∀ p q, q ∈ ψ '' (facePatch ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2) →
        ∃ D : EuclideanSpace ℝ S →L[ℝ] ℝ,
          HasFDerivAt
            (SmoothBarrierGluing.smoothWallList
              ((selected p).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1), offset p)
              (tailHead :: tail)) D q ∧
          D (toEuclid (N.massActionVectorField κ (toEuclid.symm q))) ≤ 0 := by
  classical
  let head (p : Σ i : ι, Fin (cover.tiling.subdivisionCount + 1)) :=
    (selected p).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1)
  have hlocal : ∀ p, ∃ a : ℝ,
      ∀ q ∈ ψ '' (facePatch ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2),
        ∃ D : EuclideanSpace ℝ S →L[ℝ] ℝ,
          HasFDerivAt (SmoothBarrierGluing.smoothWallList (head p, a)
            (tailHead :: tail)) D q ∧
          D (toEuclid (N.massActionVectorField κ (toEuclid.symm q))) ≤ 0 := by
    intro p
    by_cases hne : (facePatch ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2).Nonempty
    · obtain ⟨wall, hwall⟩ := hlabels p hne
      obtain ⟨gap, a, hbarrier⟩ := N.exists_selected_oneBitFiberPatch_smoothBarrier
        κ cover ψ hψ z t hε selected hselected p wall hwall tailHead tail
      refine ⟨a, ?_⟩
      intro q hq
      have hq' : q ∈ ψ '' (facePatch ∩
          CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
            (baseTile p.1) lower upper p.2) := hq
      simpa [head, hwall] using hbarrier q hq'
    · refine ⟨0, ?_⟩
      intro q hq
      rcases hq with ⟨x, hx, rfl⟩
      exact False.elim (hne ⟨x, hx⟩)
  let offset : (Σ i : ι, Fin (cover.tiling.subdivisionCount + 1)) → ℝ :=
    fun p => Classical.choose (hlocal p)
  refine ⟨offset, ?_⟩
  intro p q hq
  have hbarrier := Classical.choose_spec (hlocal p)
  simpa [offset, head] using hbarrier q hq

/-- The compact projective wall construction continues through the smooth-barrier stage: every
refined tile receives its selected inward normal and an offset, and its smooth wall list has
nonpositive derivative along the mass-action field throughout that tile. This is the local dynamic
atlas required before Craciun's lexicographic face filling. -/
theorem Network.exists_compactProjectiveRadialBarrierAtlas
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (diagramTile : ι → Set (Fin (n + 1) → ℝ)) (upper : Fin (n + 1) → ℝ)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S) (hψ : Continuous ψ)
    (hdiagramNonnegative : ∀ k x, x ∈ diagramTile k → ∀ i, 0 ≤ x i)
    (hdiagramNonzero : ∀ k x, x ∈ diagramTile k → x ≠ 0)
    (hdiagramAnchor : ∀ k x, x ∈ diagramTile k → x 0 = 1)
    (hdiagramCompact : ∀ k, IsCompact (diagramTile k))
    (hupper : ∀ i, 0 < upper i)
    (hdiagramCoversNormalizedDomain : ∀ x,
      x ∈ ZeroSeparatingInduction.craciunProjectiveDomain → x 0 = 1 →
        x ∈ ⋃ k, diagramTile k)
    (hprojectedInteriorsDisjoint : ∀ i j, i ≠ j →
      interior (ZeroSeparatingInduction.forgetLastCoordinate n ''
        (ZeroSeparatingInduction.radialBoxDiagramTile (diagramTile i) upper
          (hdiagramNonnegative i) (hdiagramNonzero i) hupper ∩
            ZeroSeparatingInduction.craciunProjectiveDomain)) ∩
      interior (ZeroSeparatingInduction.forgetLastCoordinate n ''
        (ZeroSeparatingInduction.radialBoxDiagramTile (diagramTile j) upper
          (hdiagramNonnegative j) (hdiagramNonzero j) hupper ∩
            ZeroSeparatingInduction.craciunProjectiveDomain)) = ∅)
    (hfaceNonempty : (⋃ k, ZeroSeparatingInduction.radialBoxDiagramTile
      (diagramTile k) upper (hdiagramNonnegative k) (hdiagramNonzero k) hupper ∩
        ZeroSeparatingInduction.craciunProjectiveDomain).Nonempty)
    (hpositive : ∀ x, x ∈ ⋃ k, ZeroSeparatingInduction.radialBoxDiagramTile
      (diagramTile k) upper (hdiagramNonnegative k) (hdiagramNonzero k) hupper ∩
        ZeroSeparatingInduction.craciunProjectiveDomain →
      Concentration.Positive (toEuclid.symm (ψ x)))
    (hnotcb : ∀ x, x ∈ ⋃ k, ZeroSeparatingInduction.radialBoxDiagramTile
      (diagramTile k) upper (hdiagramNonnegative k) (hdiagramNonzero k) hupper ∩
        ZeroSeparatingInduction.craciunProjectiveDomain →
      ¬ N.IsComplexBalanced κ (toEuclid.symm (ψ x)))
    (tailHead : (EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ)
    (tail : List ((EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ)) :
    let facePatch : Set (Fin (n + 1) → ℝ) :=
      ⋃ k, ZeroSeparatingInduction.radialBoxDiagramTile (diagramTile k) upper
        (hdiagramNonnegative k) (hdiagramNonzero k) hupper ∩
          ZeroSeparatingInduction.craciunProjectiveDomain
    let K : Set (EuclideanSpace ℝ S) := ψ '' facePatch
    ∃ δcoord : ℝ, 0 < δcoord ∧
    ∃ m : ℕ, ∃ baseTile : ι × Fin m → Set (Fin n → ℝ),
    ∃ cover : ZeroSeparatingInduction.CompactOneBitFiberPatchCover facePatch
      (ZeroSeparatingInduction.forgetLastCoordinate n '' facePatch) baseTile (fun _ => 0)
        (fun _ => upper (Fin.last n)) (δcoord / 4),
    ∃ z : K → N.euclideanStoichSubspace, ∃ t : Finset K, ∃ ε : ℝ,
    ∃ selected : (Σ i : ι × Fin m,
        Fin (cover.tiling.subdivisionCount + 1)) → Option K,
    ∃ offset : (Σ i : ι × Fin m,
        Fin (cover.tiling.subdivisionCount + 1)) → ℝ,
      0 < ε ∧
      (∀ p, ¬ (facePatch ∩ ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) (fun _ => 0) (fun _ => upper (Fin.last n)) p.2).Nonempty →
          selected p = none) ∧
      (∀ p, (facePatch ∩ ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) (fun _ => 0) (fun _ => upper (Fin.last n)) p.2).Nonempty →
          ∃ wall, selected p = some wall) ∧
      (∀ p wall, selected p = some wall → wall ∈ t ∧ ∀ q ∈
        ψ '' (facePatch ∩ ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) (fun _ => 0) (fun _ => upper (Fin.last n)) p.2),
        ε < ⟪(z wall).1,
          toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ) ∧
      (∀ p q, q ∈ ψ '' (facePatch ∩
          ZeroSeparatingInduction.projectionFiberSubdivisionTile
            (baseTile p.1) (fun _ => 0) (fun _ => upper (Fin.last n)) p.2) →
        ∃ D : EuclideanSpace ℝ S →L[ℝ] ℝ,
          HasFDerivAt
            (SmoothBarrierGluing.smoothWallList
              ((selected p).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1), offset p)
              (tailHead :: tail)) D q ∧
          D (toEuclid (N.massActionVectorField κ (toEuclid.symm q))) ≤ 0) := by
  dsimp only
  obtain ⟨δcoord, hδcoord, m, baseTile, cover, z, t, ε, selected,
      hε, hnone, hsome, hselected, _, _, _⟩ :=
    N.exists_compactProjectiveRadialWallSelection κ hxs hcb diagramTile upper ψ hψ
      hdiagramNonnegative hdiagramNonzero hdiagramAnchor hdiagramCompact hupper
      hdiagramCoversNormalizedDomain hprojectedInteriorsDisjoint hfaceNonempty hpositive hnotcb
  obtain ⟨offset, hatlas⟩ := N.exists_simultaneous_oneBitFiberPatch_barriers κ
    cover ψ hψ z t hε selected hselected hsome tailHead tail
  exact ⟨δcoord, hδcoord, m, baseTile, cover, z, t, ε, selected, offset,
    hε, hnone, hsome, hselected, hatlas⟩

/-- Craciun v3, §8 Steps 1–2: build a compact wall-barrier atlas on the fan-labeled radial
blueprint itself. The projected small-patch cover is crossed with the fan arrangement before the
fiber tiling is created, and wall selection plus barrier construction then use that same cover.
This keeps the fan-face seam order and every restricted tile's chart label definitionally aligned. -/
theorem Network.exists_compactProjectiveFanRadialBarrierAtlas
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (diagramTile : ι → Set (Fin (n + 1) → ℝ)) (upper : Fin (n + 1) → ℝ)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S) (hψ : Continuous ψ)
    (hdiagramNonnegative : ∀ k x, x ∈ diagramTile k → ∀ i, 0 ≤ x i)
    (hdiagramNonzero : ∀ k x, x ∈ diagramTile k → x ≠ 0)
    (hdiagramAnchor : ∀ k x, x ∈ diagramTile k → x 0 = 1)
    (hdiagramCompact : ∀ k, IsCompact (diagramTile k))
    (hupper : ∀ i, 0 < upper i)
    (hdiagramCoversNormalizedDomain : ∀ x,
      x ∈ ZeroSeparatingInduction.craciunProjectiveDomain → x 0 = 1 →
        x ∈ ⋃ k, diagramTile k)
    (hfaceNonempty : (⋃ k, ZeroSeparatingInduction.radialBoxDiagramTile
      (diagramTile k) upper (hdiagramNonnegative k) (hdiagramNonzero k) hupper ∩
        ZeroSeparatingInduction.craciunProjectiveDomain).Nonempty)
    (hpositive : ∀ x, x ∈ ⋃ k, ZeroSeparatingInduction.radialBoxDiagramTile
      (diagramTile k) upper (hdiagramNonnegative k) (hdiagramNonzero k) hupper ∩
        ZeroSeparatingInduction.craciunProjectiveDomain →
      Concentration.Positive (toEuclid.symm (ψ x)))
    (hnotcb : ∀ x, x ∈ ⋃ k, ZeroSeparatingInduction.radialBoxDiagramTile
      (diagramTile k) upper (hdiagramNonnegative k) (hdiagramNonzero k) hupper ∩
        ZeroSeparatingInduction.craciunProjectiveDomain →
      ¬ N.IsComplexBalanced κ (toEuclid.symm (ψ x)))
    (F : Fan (EuclideanSpace ℝ (Fin n))) (hF : IsPolyhedralFan F)
    (hFdual : FanRefinement.HasDualFGCells F)
    [Fintype {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)}]
    (tailHead : (EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ)
    (tail : List ((EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ)) :
    let facePatch : Set (Fin (n + 1) → ℝ) :=
      ⋃ k, ZeroSeparatingInduction.radialBoxDiagramTile (diagramTile k) upper
        (hdiagramNonnegative k) (hdiagramNonzero k) hupper ∩
          ZeroSeparatingInduction.craciunProjectiveDomain
    let base : Set (Fin n → ℝ) := ZeroSeparatingInduction.forgetLastCoordinate n '' facePatch
    let K : Set (EuclideanSpace ℝ S) := ψ '' facePatch
    ∃ δcoord : ℝ, 0 < δcoord ∧ ∃ δwall : ℝ, 0 < δwall ∧
      ∃ small : ZeroSeparatingInduction.CompactSmallBaseTiling base (δcoord / 4),
      ∃ cover : ZeroSeparatingInduction.CompactOneBitFiberPatchCover facePatch base
        (fun p : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
          C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)} ×
            Fin small.count =>
          FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual p.1 ∩
            small.tile p.2)
        (fun _ => 0) (fun _ => upper (Fin.last n)) (δcoord / 4),
      ∃ z : K → N.euclideanStoichSubspace, ∃ t : Finset K, ∃ ε : ℝ,
      ∃ selected : (Σ p : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
        C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)} ×
          Fin small.count, Fin (cover.tiling.subdivisionCount + 1)) → Option K,
      ∃ offset : (Σ p : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
        C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)} ×
          Fin small.count, Fin (cover.tiling.subdivisionCount + 1)) → ℝ,
        0 < ε ∧
        (∀ y ∈ K, ∃ wall ∈ t, ∀ q ∈ Metric.ball y δwall,
          ε < ⟪(z wall).1,
            toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ) ∧
        (∀ p, ¬ (facePatch ∩ ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual p.1.1 ∩
            small.tile p.1.2) (fun _ => 0) (fun _ => upper (Fin.last n)) p.2).Nonempty →
              selected p = none) ∧
        (∀ p, (facePatch ∩ ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual p.1.1 ∩
            small.tile p.1.2) (fun _ => 0) (fun _ => upper (Fin.last n)) p.2).Nonempty →
              ∃ wall, selected p = some wall) ∧
        (∀ p wall, selected p = some wall → wall ∈ t ∧ ∀ q ∈
          ψ '' (facePatch ∩ ZeroSeparatingInduction.projectionFiberSubdivisionTile
            (FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual p.1.1 ∩
              small.tile p.1.2) (fun _ => 0) (fun _ => upper (Fin.last n)) p.2),
          ε < ⟪(z wall).1,
            toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ) ∧
        (∀ p q, q ∈ ψ '' (facePatch ∩
            ZeroSeparatingInduction.projectionFiberSubdivisionTile
              (FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual p.1.1 ∩
                small.tile p.1.2) (fun _ => 0) (fun _ => upper (Fin.last n)) p.2) →
          ∃ D : EuclideanSpace ℝ S →L[ℝ] ℝ,
            HasFDerivAt
              (SmoothBarrierGluing.smoothWallList
                ((selected p).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1), offset p)
                (tailHead :: tail)) D q ∧
            D (toEuclid (N.massActionVectorField κ (toEuclid.symm q))) ≤ 0) := by
  classical
  let facePatch : Set (Fin (n + 1) → ℝ) :=
    ⋃ k, ZeroSeparatingInduction.radialBoxDiagramTile (diagramTile k) upper
      (hdiagramNonnegative k) (hdiagramNonzero k) hupper ∩
        ZeroSeparatingInduction.craciunProjectiveDomain
  let base : Set (Fin n → ℝ) := ZeroSeparatingInduction.forgetLastCoordinate n '' facePatch
  let K : Set (EuclideanSpace ℝ S) := ψ '' facePatch
  have hfaceCompact : IsCompact facePatch := by
    dsimp [facePatch]
    exact (ZeroSeparatingInduction.isCompact_and_covers_projectiveRadialTiles
      diagramTile upper hdiagramNonnegative hdiagramAnchor hdiagramCompact hupper
      hdiagramCoversNormalizedDomain).1
  have hbaseCompact : IsCompact base :=
    hfaceCompact.image (ZeroSeparatingInduction.forgetLastCoordinate n).continuous_of_finiteDimensional
  have hbaseNonempty : base.Nonempty := by
    obtain ⟨x, hx⟩ := hfaceNonempty
    exact ⟨ZeroSeparatingInduction.forgetLastCoordinate n x, ⟨x, hx, rfl⟩⟩
  obtain ⟨δcoord, δwall, hδcoord, hδwall, z, t, ε, hε, hchart, hmap⟩ :=
    N.exists_compactProjectiveRadialWallChart κ hxs hcb diagramTile upper ψ hψ
      hdiagramNonnegative hdiagramNonzero hdiagramAnchor hdiagramCompact hupper
      hdiagramCoversNormalizedDomain hfaceNonempty hpositive hnotcb
  have hquarter : 0 < δcoord / 4 := by positivity
  let small := ZeroSeparatingInduction.exists_compact_small_interior_disjoint_cover
    base hbaseCompact hquarter
  have hupperPositive : 0 < upper (Fin.last n) := hupper (Fin.last n)
  have horder : ∀ y ∈ base, (fun _ : Fin n → ℝ => 0) y ≤ upper (Fin.last n) := by
    intro y hy
    exact le_of_lt hupperPositive
  have hfaceBand : facePatch ⊆ ZeroSeparatingInduction.projectionFiberBand base
      (fun _ => some (0 : ℝ)) (fun _ => some (upper (Fin.last n))) := by
    intro x hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    have hbox := ZeroSeparatingInduction.radialBoxDiagramTile_subset_box (diagramTile k) upper
      (hdiagramNonnegative k) (hdiagramNonzero k) hupper hk.1
    apply (ZeroSeparatingInduction.mem_projectionFiberBand_bounded_iff base
      (fun _ => 0) (fun _ => upper (Fin.last n)) x).2
    refine ⟨⟨x, hx, rfl⟩, ?_, ?_⟩
    · exact (hbox (Fin.last n)).1
    · exact (hbox (Fin.last n)).2
  let cover := FanRefinement.exists_small_fan_labeledOneBitFiberPatchCover
    facePatch hfaceCompact base small.tile small.covers small.tile_compact
      small.interiors_disjoint (fun _ => 0) (fun _ => upper (Fin.last n))
      (δcoord / 4) continuous_const continuous_const horder hquarter hfaceBand F hF hFdual
  have himage : ∀ p : Σ q : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)} ×
        Fin small.count, Fin (cover.tiling.subdivisionCount + 1),
      ψ '' (facePatch ∩ ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual p.1.1 ∩
          small.tile p.1.2) (fun _ => 0) (fun _ => upper (Fin.last n)) p.2) ⊆ K := by
    intro p q hq
    rcases hq with ⟨x, hx, rfl⟩
    exact ⟨x, hx.1, rfl⟩
  have hmapDiam : ∀ p : Σ q : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)} ×
        Fin small.count, Fin (cover.tiling.subdivisionCount + 1),
      ∀ x ∈ facePatch ∩ ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual p.1.1 ∩
            small.tile p.1.2) (fun _ => 0) (fun _ => upper (Fin.last n)) p.2,
      ∀ y ∈ facePatch ∩ ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual p.1.1 ∩
            small.tile p.1.2) (fun _ => 0) (fun _ => upper (Fin.last n)) p.2,
      dist x y < δcoord → dist (ψ x) (ψ y) < δwall := by
    intro p x hx y hy hdist
    exact hmap x y hx.1 hy.1 hdist
  have hprojectedSmall : ∀ p : Σ q : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)} ×
        Fin small.count, Fin (cover.tiling.subdivisionCount + 1),
      ∀ a ∈ FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual p.1.1 ∩
          small.tile p.1.2,
      ∀ b ∈ FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual p.1.1 ∩
          small.tile p.1.2, dist a b < δcoord / 4 := by
    intro p a ha b hb
    exact small.tile_diameter_lt p.1.2 a ha.2 b hb.2
  have hendpointVariation : ∀ p : Σ q : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)} ×
        Fin small.count, Fin (cover.tiling.subdivisionCount + 1),
      ∀ a ∈ FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual p.1.1 ∩
          small.tile p.1.2,
      ∀ b ∈ FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual p.1.1 ∩
          small.tile p.1.2,
      dist a b < δcoord / 4 →
        dist (ZeroSeparatingInduction.projectionFiberSubdivisionEndpoint
          (fun _ => 0) (fun _ => upper (Fin.last n)) p.2.succ a)
          (ZeroSeparatingInduction.projectionFiberSubdivisionEndpoint
            (fun _ => 0) (fun _ => upper (Fin.last n)) p.2.succ b) < δcoord / 4 := by
    intro p a ha b hb hab
    have heq : ZeroSeparatingInduction.projectionFiberSubdivisionEndpoint
        (fun _ => 0) (fun _ => upper (Fin.last n)) p.2.succ a =
        ZeroSeparatingInduction.projectionFiberSubdivisionEndpoint
          (fun _ => 0) (fun _ => upper (Fin.last n)) p.2.succ b := by
      simp [ZeroSeparatingInduction.projectionFiberSubdivisionEndpoint,
        ZeroSeparatingInduction.tileScaleInterpolation]
    rw [heq]
    simpa using hquarter
  have hbudget : δcoord / 4 + δcoord / 4 < δcoord := by linarith
  obtain ⟨selected, hnone, hsome, hselected⟩ :=
    N.exists_oneBitFiberPatchWallSelection κ cover ψ z t hchart himage hmapDiam
      hprojectedSmall hendpointVariation (by linarith) hbudget hδcoord
  obtain ⟨offset, hatlas⟩ := N.exists_simultaneous_oneBitFiberPatch_barriers κ
    cover ψ hψ z t hε selected hselected hsome tailHead tail
  dsimp only
  exact ⟨δcoord, hδcoord, δwall, hδwall, small, cover, z, t, ε, selected, offset,
    hε, hchart, hnone, hsome, hselected, hatlas⟩

/-- The §8 Step 1 restriction of a one-bit blueprint to a closed projective domain preserves the
selected inward-wall atlas. Each clipped tile is compact, its old wall label remains inward on the
smaller patch, and the simultaneous offset choice therefore supplies tile-local barriers on the
restricted family used for the subsequent lexicographic fill. -/
theorem Network.exists_simultaneous_restrictedOneBitFiberPatch_barriers
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {baseTile : ι → Set (Fin n → ℝ)} {lower upper : (Fin n → ℝ) → ℝ}
    {epsilon : ℝ}
    (cover : CRNT.ZeroSeparatingInduction.CompactOneBitFiberPatchCover
      facePatch base baseTile lower upper epsilon)
    (domain : Set (Fin (n + 1) → ℝ)) (hdomain : IsClosed domain)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S) (hψ : Continuous ψ)
    {K : Set (EuclideanSpace ℝ S)} (z : K → N.euclideanStoichSubspace)
    (t : Finset K) {ε : ℝ} (hε : 0 < ε)
    (selected : (Σ i : ι, Fin (cover.tiling.subdivisionCount + 1)) → Option K)
    (hselected : ∀ p wall, selected p = some wall → wall ∈ t ∧ ∀ q ∈
      ψ '' (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2),
      ε < ⟪(z wall).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ)
    (hlabels : ∀ p, (facePatch ∩
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2).Nonempty → ∃ wall, selected p = some wall)
    (tailHead : (EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ)
    (tail : List ((EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ)) :
    ∃ offset : (Σ i : ι, Fin (cover.tiling.subdivisionCount + 1)) → ℝ,
      ∀ p q, q ∈ ψ '' ((facePatch ∩ domain) ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2) →
        ∃ D : EuclideanSpace ℝ S →L[ℝ] ℝ,
          HasFDerivAt
            (SmoothBarrierGluing.smoothWallList
              ((selected p).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1), offset p)
              (tailHead :: tail)) D q ∧
          D (toEuclid (N.massActionVectorField κ (toEuclid.symm q))) ≤ 0 := by
  let restricted := cover.restrict_to_closedDomain domain hdomain
  have hselectedRestricted : ∀ p wall, selected p = some wall → wall ∈ t ∧ ∀ q ∈
      ψ '' ((facePatch ∩ domain) ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2),
      ε < ⟪(z wall).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ := by
    intro p wall hp
    have hs := hselected p wall hp
    refine ⟨hs.1, ?_⟩
    intro q hq
    rcases hq with ⟨x, hx, rfl⟩
    exact hs.2 _ ⟨x, ⟨hx.1.1, hx.2⟩, rfl⟩
  have hlabelsRestricted : ∀ p,
      ((facePatch ∩ domain) ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2).Nonempty →
        ∃ wall, selected p = some wall := by
    intro p hne
    apply hlabels p
    exact hne.mono (by
      intro x hx
      exact ⟨hx.1.1, hx.2⟩)
  have hbarriers := N.exists_simultaneous_oneBitFiberPatch_barriers
    κ restricted ψ hψ z t hε selected hselectedRestricted hlabelsRestricted tailHead tail
  rcases hbarriers with ⟨offset, hoffset⟩
  refine ⟨offset, ?_⟩
  intro p q hq
  exact hoffset p q hq

/-- Craciun v3, §8 Step 1: clip the projective radial blueprint to a closed domain and retain a
simultaneous inward smooth-barrier atlas on every clipped tile. Parent diagram labels, the shared
fiber subdivision, and the wall assignment all survive restriction. -/
theorem Network.exists_compactProjectiveRadialRestrictedBarrierAtlas
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (diagramTile : ι → Set (Fin (n + 1) → ℝ)) (upper : Fin (n + 1) → ℝ)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S) (hψ : Continuous ψ)
    (hdiagramNonnegative : ∀ k x, x ∈ diagramTile k → ∀ i, 0 ≤ x i)
    (hdiagramNonzero : ∀ k x, x ∈ diagramTile k → x ≠ 0)
    (hdiagramAnchor : ∀ k x, x ∈ diagramTile k → x 0 = 1)
    (hdiagramCompact : ∀ k, IsCompact (diagramTile k))
    (hupper : ∀ i, 0 < upper i)
    (hdiagramCoversNormalizedDomain : ∀ x,
      x ∈ ZeroSeparatingInduction.craciunProjectiveDomain → x 0 = 1 →
        x ∈ ⋃ k, diagramTile k)
    (hprojectedInteriorsDisjoint : ∀ i j, i ≠ j →
      interior (ZeroSeparatingInduction.forgetLastCoordinate n ''
        (ZeroSeparatingInduction.radialBoxDiagramTile (diagramTile i) upper
          (hdiagramNonnegative i) (hdiagramNonzero i) hupper ∩
            ZeroSeparatingInduction.craciunProjectiveDomain)) ∩
      interior (ZeroSeparatingInduction.forgetLastCoordinate n ''
        (ZeroSeparatingInduction.radialBoxDiagramTile (diagramTile j) upper
          (hdiagramNonnegative j) (hdiagramNonzero j) hupper ∩
            ZeroSeparatingInduction.craciunProjectiveDomain)) = ∅)
    (hfaceNonempty : (⋃ k, ZeroSeparatingInduction.radialBoxDiagramTile
      (diagramTile k) upper (hdiagramNonnegative k) (hdiagramNonzero k) hupper ∩
        ZeroSeparatingInduction.craciunProjectiveDomain).Nonempty)
    (hpositive : ∀ x, x ∈ ⋃ k, ZeroSeparatingInduction.radialBoxDiagramTile
      (diagramTile k) upper (hdiagramNonnegative k) (hdiagramNonzero k) hupper ∩
        ZeroSeparatingInduction.craciunProjectiveDomain →
      Concentration.Positive (toEuclid.symm (ψ x)))
    (hnotcb : ∀ x, x ∈ ⋃ k, ZeroSeparatingInduction.radialBoxDiagramTile
      (diagramTile k) upper (hdiagramNonnegative k) (hdiagramNonzero k) hupper ∩
        ZeroSeparatingInduction.craciunProjectiveDomain →
      ¬ N.IsComplexBalanced κ (toEuclid.symm (ψ x)))
    (domain : Set (Fin (n + 1) → ℝ)) (hdomain : IsClosed domain)
    (tailHead : (EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ)
    (tail : List ((EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ)) :
    let facePatch : Set (Fin (n + 1) → ℝ) :=
      ⋃ k, ZeroSeparatingInduction.radialBoxDiagramTile (diagramTile k) upper
        (hdiagramNonnegative k) (hdiagramNonzero k) hupper ∩
          ZeroSeparatingInduction.craciunProjectiveDomain
    let K : Set (EuclideanSpace ℝ S) := ψ '' facePatch
    ∃ δcoord : ℝ, 0 < δcoord ∧
    ∃ m : ℕ, ∃ baseTile : ι × Fin m → Set (Fin n → ℝ),
    ∃ cover : ZeroSeparatingInduction.CompactOneBitFiberPatchCover facePatch
      (ZeroSeparatingInduction.forgetLastCoordinate n '' facePatch) baseTile (fun _ => 0)
        (fun _ => upper (Fin.last n)) (δcoord / 4),
    ∃ z : K → N.euclideanStoichSubspace, ∃ t : Finset K, ∃ ε : ℝ,
    ∃ selected : (Σ i : ι × Fin m,
        Fin (cover.tiling.subdivisionCount + 1)) → Option K,
    ∃ offset : (Σ i : ι × Fin m,
        Fin (cover.tiling.subdivisionCount + 1)) → ℝ,
      0 < ε ∧
      (∀ p wall, selected p = some wall → wall ∈ t ∧ ∀ q ∈
        ψ '' (facePatch ∩ ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) (fun _ => 0) (fun _ => upper (Fin.last n)) p.2),
        ε < ⟪(z wall).1,
          toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ) ∧
      (∀ p, (facePatch ∩ ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) (fun _ => 0) (fun _ => upper (Fin.last n)) p.2).Nonempty →
          ∃ wall, selected p = some wall) ∧
      (∀ p q, q ∈ ψ '' ((facePatch ∩ domain) ∩
          ZeroSeparatingInduction.projectionFiberSubdivisionTile
            (baseTile p.1) (fun _ => 0) (fun _ => upper (Fin.last n)) p.2) →
        ∃ D : EuclideanSpace ℝ S →L[ℝ] ℝ,
          HasFDerivAt
            (SmoothBarrierGluing.smoothWallList
              ((selected p).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1), offset p)
              (tailHead :: tail)) D q ∧
          D (toEuclid (N.massActionVectorField κ (toEuclid.symm q))) ≤ 0) := by
  dsimp only
  obtain ⟨δcoord, hδcoord, m, baseTile, cover, z, t, ε, selected,
      hε, _, hlabels, hselected, _, _, _⟩ :=
    N.exists_compactProjectiveRadialWallSelection κ hxs hcb diagramTile upper ψ hψ
      hdiagramNonnegative hdiagramNonzero hdiagramAnchor hdiagramCompact hupper
      hdiagramCoversNormalizedDomain hprojectedInteriorsDisjoint hfaceNonempty hpositive hnotcb
  obtain ⟨offset, hatlas⟩ := N.exists_simultaneous_restrictedOneBitFiberPatch_barriers
    κ cover domain hdomain ψ hψ z t hε selected hselected hlabels tailHead tail
  exact ⟨δcoord, hδcoord, m, baseTile, cover, z, t, ε, selected, offset,
    hε, hselected, hlabels, hatlas⟩

/-- The simultaneously chosen barriers from a one-bit tile atlas have a differentiable,
nonincreasing smooth maximum on every pairwise patch overlap. The per-tile offsets are fixed
globally by `exists_simultaneous_oneBitFiberPatch_barriers`, so this overlap result is compatible
with the finite face-by-face gluing construction. -/
theorem Network.oneBitFiberPatchAtlas_pairwise_glue
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {baseTile : ι → Set (Fin n → ℝ)} {lower upper : (Fin n → ℝ) → ℝ}
    {epsilon : ℝ}
    (cover : CRNT.ZeroSeparatingInduction.CompactOneBitFiberPatchCover
      facePatch base baseTile lower upper epsilon)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S)
    {K : Set (EuclideanSpace ℝ S)} (z : K → N.euclideanStoichSubspace)
    (selected : (Σ i : ι, Fin (cover.tiling.subdivisionCount + 1)) → Option K)
    (tailHead : (EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ)
    (tail : List ((EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ))
    (offset : (Σ i : ι, Fin (cover.tiling.subdivisionCount + 1)) → ℝ)
    (p r : Σ i : ι, Fin (cover.tiling.subdivisionCount + 1))
    {q : EuclideanSpace ℝ S}
    (hq : q ∈ ψ ''
      ((facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2) ∩
        (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile r.1) lower upper r.2)))
    (hatlas : ∀ p q, q ∈ ψ '' (facePatch ∩
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2) →
      ∃ D : EuclideanSpace ℝ S →L[ℝ] ℝ,
        HasFDerivAt
          (SmoothBarrierGluing.smoothWallList
            ((selected p).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1), offset p)
            (tailHead :: tail)) D q ∧
        D (toEuclid (N.massActionVectorField κ (toEuclid.symm q))) ≤ 0) :
    ∃ D : EuclideanSpace ℝ S →L[ℝ] ℝ,
      HasFDerivAt
        (SmoothBarrierGluing.smoothMaxF
          (SmoothBarrierGluing.smoothWallList
            ((selected p).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1), offset p)
            (tailHead :: tail))
          (SmoothBarrierGluing.smoothWallList
            ((selected r).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1), offset r)
            (tailHead :: tail))) D q ∧
      D (toEuclid (N.massActionVectorField κ (toEuclid.symm q))) ≤ 0 := by
  rcases hq with ⟨x, ⟨hxP, hxR⟩, rfl⟩
  have hqP : ψ x ∈ ψ '' (facePatch ∩
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2) := ⟨x, hxP, rfl⟩
  have hqR : ψ x ∈ ψ '' (facePatch ∩
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile r.1) lower upper r.2) := ⟨x, hxR, rfl⟩
  obtain ⟨DP, hDP, hDPnonpos⟩ := hatlas p (ψ x) hqP
  obtain ⟨DR, hDR, hDRnonpos⟩ := hatlas r (ψ x) hqR
  exact SmoothBarrierGluing.smoothMaxF_descends_along
    (X := fun q : EuclideanSpace ℝ S =>
      toEuclid (N.massActionVectorField κ (toEuclid.symm q)))
    hDP hDR hDPnonpos hDRnonpos

/-- Craciun v3, §8 Step 1 and §7.4.3: after clipping the blueprint to a closed domain, one
simultaneous choice of tile barriers gives a smooth-max differential inequality on every overlap
of the restricted tiles. This is the finite overlap-compatibility package needed by the next
face-filling stage. -/
theorem Network.exists_restrictedOneBitFiberPatchAtlas_pairwise_glue
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {baseTile : ι → Set (Fin n → ℝ)} {lower upper : (Fin n → ℝ) → ℝ}
    {epsilon : ℝ}
    (cover : CRNT.ZeroSeparatingInduction.CompactOneBitFiberPatchCover
      facePatch base baseTile lower upper epsilon)
    (domain : Set (Fin (n + 1) → ℝ)) (hdomain : IsClosed domain)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S) (hψ : Continuous ψ)
    {K : Set (EuclideanSpace ℝ S)} (z : K → N.euclideanStoichSubspace)
    (t : Finset K) {ε : ℝ} (hε : 0 < ε)
    (selected : (Σ i : ι, Fin (cover.tiling.subdivisionCount + 1)) → Option K)
    (hselected : ∀ p wall, selected p = some wall → wall ∈ t ∧ ∀ q ∈
      ψ '' (facePatch ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2),
      ε < ⟪(z wall).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ)
    (hlabels : ∀ p, (facePatch ∩
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2).Nonempty →
      ∃ wall, selected p = some wall)
    (tailHead : (EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ)
    (tail : List ((EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ)) :
    ∃ offset : (Σ i : ι,
        Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1)) → ℝ,
      ∀ p r : Σ i : ι,
          Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1),
        ∀ q ∈ ψ ''
          (((facePatch ∩ domain) ∩
            CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
              (baseTile p.1) lower upper p.2) ∩
            ((facePatch ∩ domain) ∩
              CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
                (baseTile r.1) lower upper r.2)),
          ∃ D : EuclideanSpace ℝ S →L[ℝ] ℝ,
            HasFDerivAt
              (SmoothBarrierGluing.smoothMaxF
                (SmoothBarrierGluing.smoothWallList
                  ((selected p).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1), offset p)
                  (tailHead :: tail))
                (SmoothBarrierGluing.smoothWallList
                  ((selected r).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1), offset r)
                  (tailHead :: tail))) D q ∧
            D (toEuclid (N.massActionVectorField κ (toEuclid.symm q))) ≤ 0 := by
  let restricted := cover.restrict_to_closedDomain domain hdomain
  have hselectedRestricted : ∀ p wall, selected p = some wall → wall ∈ t ∧ ∀ q ∈
      ψ '' ((facePatch ∩ domain) ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2),
      ε < ⟪(z wall).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ := by
    intro p wall hp
    have hs := hselected p wall hp
    refine ⟨hs.1, ?_⟩
    intro q hq
    rcases hq with ⟨x, hx, rfl⟩
    exact hs.2 _ ⟨x, ⟨hx.1.1, hx.2⟩, rfl⟩
  have hlabelsRestricted : ∀ p,
      ((facePatch ∩ domain) ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2).Nonempty →
        ∃ wall, selected p = some wall := by
    intro p hne
    apply hlabels p
    exact hne.mono (by
      intro x hx
      exact ⟨hx.1.1, hx.2⟩)
  obtain ⟨offset, hatlas⟩ := N.exists_simultaneous_restrictedOneBitFiberPatch_barriers
    κ cover domain hdomain ψ hψ z t hε selected hselected hlabels tailHead tail
  refine ⟨offset, ?_⟩
  intro p r q hq
  exact N.oneBitFiberPatchAtlas_pairwise_glue κ restricted ψ z selected
    tailHead tail offset p r hq hatlas

/-- On a finite common intersection of clipped tiles, the nested smooth maximum of every tile's
barrier still has a nonincreasing derivative along the mass-action field. This is the finite-face
compatibility form needed when a lexicographic fill encounters a face incident to more than two
tiles. -/
theorem Network.restrictedOneBitFiberPatch_finite_overlap_glue
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {baseTile : ι → Set (Fin n → ℝ)} {lower upper : (Fin n → ℝ) → ℝ}
    {epsilon : ℝ}
    (cover : CRNT.ZeroSeparatingInduction.CompactOneBitFiberPatchCover
      facePatch base baseTile lower upper epsilon)
    (domain : Set (Fin (n + 1) → ℝ)) (hdomain : IsClosed domain)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S)
    {K : Set (EuclideanSpace ℝ S)} (z : K → N.euclideanStoichSubspace)
    (selected : (Σ i : ι,
      Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1)) → Option K)
    (offset : (Σ i : ι,
      Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1)) → ℝ)
    (tailHead : (EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ)
    (tail : List ((EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ))
    (p : Σ i : ι,
      Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1))
    (ps : List (Σ i : ι,
      Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1)))
    {q : EuclideanSpace ℝ S}
    (hp : q ∈ ψ '' ((facePatch ∩ domain) ∩
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2))
    (hps : ∀ r ∈ ps, q ∈ ψ '' ((facePatch ∩ domain) ∩
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile r.1) lower upper r.2))
    (hatlas : ∀ r q, q ∈ ψ '' ((facePatch ∩ domain) ∩
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile r.1) lower upper r.2) →
      ∃ D : EuclideanSpace ℝ S →L[ℝ] ℝ,
        HasFDerivAt
          (SmoothBarrierGluing.smoothWallList
            ((selected r).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1), offset r)
            (tailHead :: tail)) D q ∧
        D (toEuclid (N.massActionVectorField κ (toEuclid.symm q))) ≤ 0) :
    ∃ D : EuclideanSpace ℝ S →L[ℝ] ℝ,
      HasFDerivAt
        (SmoothBarrierGluing.smoothMaxList
          (SmoothBarrierGluing.smoothWallList
            ((selected p).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1), offset p)
            (tailHead :: tail))
          (ps.map (fun r => SmoothBarrierGluing.smoothWallList
            ((selected r).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1), offset r)
            (tailHead :: tail)))) D q ∧
      D (toEuclid (N.massActionVectorField κ (toEuclid.symm q))) ≤ 0 := by
  let barrier (r : Σ i : ι,
      Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1)) :=
    SmoothBarrierGluing.smoothWallList
      ((selected r).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1), offset r)
      (tailHead :: tail)
  have hhead := hatlas p q hp
  have htail : ∀ g ∈ ps.map barrier, ∃ D : EuclideanSpace ℝ S →L[ℝ] ℝ,
      HasFDerivAt g D q ∧
        D (toEuclid (N.massActionVectorField κ (toEuclid.symm q))) ≤ 0 := by
    intro g hg
    obtain ⟨r, hr, hrg⟩ := List.mem_map.mp hg
    subst g
    exact hatlas r q (hps r hr)
  simpa [barrier] using
    (SmoothBarrierGluing.exists_fderiv_smoothMaxList_le
      (X := fun q : EuclideanSpace ℝ S =>
        toEuclid (N.massActionVectorField κ (toEuclid.symm q)))
      (barrier p) (ps.map barrier) hhead htail)

/-- The finite-overlap gluing theorem with its atlas constructed from strict inward wall labels.
Thus the local toric wall selection, compact barrier offsets, and arbitrary finite smooth maximum
are available together for each clipped common face. -/
theorem Network.exists_restrictedOneBitFiberPatch_finite_overlap_glue
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {baseTile : ι → Set (Fin n → ℝ)} {lower upper : (Fin n → ℝ) → ℝ}
    {epsilon : ℝ}
    (cover : CRNT.ZeroSeparatingInduction.CompactOneBitFiberPatchCover
      facePatch base baseTile lower upper epsilon)
    (domain : Set (Fin (n + 1) → ℝ)) (hdomain : IsClosed domain)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S) (hψ : Continuous ψ)
    {K : Set (EuclideanSpace ℝ S)} (z : K → N.euclideanStoichSubspace)
    (t : Finset K) {ε : ℝ} (hε : 0 < ε)
    (selected : (Σ i : ι,
      Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1)) → Option K)
    (hselected : ∀ p wall, selected p = some wall → wall ∈ t ∧ ∀ q ∈
      ψ '' (facePatch ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2),
      ε < ⟪(z wall).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ)
    (hlabels : ∀ p, (facePatch ∩
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2).Nonempty →
      ∃ wall, selected p = some wall)
    (tailHead : (EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ)
    (tail : List ((EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ))
    (p : Σ i : ι,
      Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1))
    (ps : List (Σ i : ι,
      Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1)))
    {q : EuclideanSpace ℝ S}
    (hp : q ∈ ψ '' ((facePatch ∩ domain) ∩
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2))
    (hps : ∀ r ∈ ps, q ∈ ψ '' ((facePatch ∩ domain) ∩
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile r.1) lower upper r.2)) :
    ∃ offset : (Σ i : ι,
        Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1)) → ℝ,
      ∃ D : EuclideanSpace ℝ S →L[ℝ] ℝ,
        HasFDerivAt
          (SmoothBarrierGluing.smoothMaxList
            (SmoothBarrierGluing.smoothWallList
              ((selected p).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1), offset p)
              (tailHead :: tail))
            (ps.map (fun r => SmoothBarrierGluing.smoothWallList
              ((selected r).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1), offset r)
              (tailHead :: tail)))) D q ∧
        D (toEuclid (N.massActionVectorField κ (toEuclid.symm q))) ≤ 0 := by
  let restricted := cover.restrict_to_closedDomain domain hdomain
  have hselectedRestricted : ∀ p wall, selected p = some wall → wall ∈ t ∧ ∀ q ∈
      ψ '' ((facePatch ∩ domain) ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2),
      ε < ⟪(z wall).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ := by
    intro p wall hp
    have hs := hselected p wall hp
    refine ⟨hs.1, ?_⟩
    intro q hq
    rcases hq with ⟨x, hx, rfl⟩
    exact hs.2 _ ⟨x, ⟨hx.1.1, hx.2⟩, rfl⟩
  have hlabelsRestricted : ∀ p,
      ((facePatch ∩ domain) ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2).Nonempty →
      ∃ wall, selected p = some wall := by
    intro p hne
    apply hlabels p
    exact hne.mono (by
      intro x hx
      exact ⟨hx.1.1, hx.2⟩)
  obtain ⟨offset, hatlas⟩ := N.exists_simultaneous_oneBitFiberPatch_barriers
    κ restricted ψ hψ z t hε selected hselectedRestricted hlabelsRestricted tailHead tail
  exact ⟨offset, N.restrictedOneBitFiberPatch_finite_overlap_glue
    κ cover domain hdomain ψ z selected offset tailHead tail p ps hp hps hatlas⟩

/-- Craciun v3, §8 Step 2: if a lower-dimensional point lies on the common endpoint graph and
the listed tile labels are incident to it, the finite smooth maximum of their barriers descends
along the mass-action field at the lifted seam point. This turns the projected seam incidence
into the finite-face compatibility needed by the recursive fill. -/
theorem Network.restrictedOneBitFiberPatch_finite_seam_glue
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {baseTile : ι → Set (Fin n → ℝ)} {lower upper : (Fin n → ℝ) → ℝ}
    {epsilon : ℝ}
    (cover : CRNT.ZeroSeparatingInduction.CompactOneBitFiberPatchCover
      facePatch base baseTile lower upper epsilon)
    (domain : Set (Fin (n + 1) → ℝ)) (hdomain : IsClosed domain)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S)
    {K : Set (EuclideanSpace ℝ S)} (z : K → N.euclideanStoichSubspace)
    (selected : (Σ i : ι,
      Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1)) → Option K)
    (offset : (Σ i : ι,
      Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1)) → ℝ)
    (tailHead : (EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ)
    (tail : List ((EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ))
    (hatlas : ∀ r q, q ∈ ψ '' ((facePatch ∩ domain) ∩
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile r.1) lower upper r.2) →
      ∃ D : EuclideanSpace ℝ S →L[ℝ] ℝ,
        HasFDerivAt
          (SmoothBarrierGluing.smoothWallList
            ((selected r).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1), offset r)
            (tailHead :: tail)) D q ∧
        D (toEuclid (N.massActionVectorField κ (toEuclid.symm q))) ≤ 0)
    (i : ι) (k : Fin (cover.tiling.subdivisionCount))
    (y : Fin n → ℝ) (horder : ∀ y ∈ base, lower y ≤ upper y)
    (hy : y ∈ baseTile i)
    (hgraph : CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
      lower upper k.succ.castSucc y ∈ facePatch ∩ domain)
    (ps : List (Σ j : ι,
      Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1)))
    (hincident : ∀ r ∈ ps, y ∈ baseTile r.1 ∧
      (r.2 = k.castSucc ∨ r.2 = k.succ)) :
    ∃ D : EuclideanSpace ℝ S →L[ℝ] ℝ,
      HasFDerivAt
        (SmoothBarrierGluing.smoothMaxList
          (SmoothBarrierGluing.smoothWallList
            ((selected ⟨i, k.castSucc⟩).elim tailHead.1
              (fun wall => innerSL ℝ (z wall).1), offset ⟨i, k.castSucc⟩)
            (tailHead :: tail))
          (ps.map (fun r => SmoothBarrierGluing.smoothWallList
            ((selected r).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1), offset r)
            (tailHead :: tail)))) D
        (ψ (CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
          lower upper k.succ.castSucc y)) ∧
      D (toEuclid (N.massActionVectorField κ (toEuclid.symm
        (ψ (CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
          lower upper k.succ.castSucc y))))) ≤ 0 := by
  let restricted := cover.restrict_to_closedDomain domain hdomain
  let x := CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
    lower upper k.succ.castSucc y
  let p : Σ j : ι, Fin (restricted.tiling.subdivisionCount + 1) := ⟨i, k.castSucc⟩
  have horderPair (j l : ι) (z₀ : Fin n → ℝ)
      (hz₀ : z₀ ∈ baseTile j ∩ baseTile l) : lower z₀ ≤ upper z₀ :=
    horder z₀ (cover.baseTile_subset j hz₀.1)
  have hrootSeam := restricted.adjacent_base_tiles_share_seam i i
    (fun z₀ hz₀ => horderPair i i z₀ hz₀) k
  have hrootGraph : x ∈ (facePatch ∩ domain) ∩
      (fun z₀ : Fin n → ℝ =>
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
          lower upper k.succ.castSucc z₀) '' (baseTile i ∩ baseTile i) :=
    ⟨hgraph, y, ⟨hy, hy⟩, rfl⟩
  have hrootAt := congrArg (fun A : Set (Fin (n + 1) → ℝ) => x ∈ A) hrootSeam
  have hpX := hrootAt.mpr hrootGraph
  have hp : ψ x ∈ ψ '' ((facePatch ∩ domain) ∩
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile i) lower upper k.castSucc) :=
    ⟨x, ⟨hpX.1.1, hpX.1.2⟩, rfl⟩
  have hps' : ∀ r ∈ ps, ψ x ∈ ψ '' ((facePatch ∩ domain) ∩
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile r.1) lower upper r.2) := by
    intro r hr
    rcases hincident r hr with ⟨hyr, hside⟩
    have hoverlap : x ∈ (facePatch ∩ domain) ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile r.1) lower upper r.2 := by
      rcases hside with hlow | hhigh
      · have hseam := restricted.adjacent_base_tiles_share_seam r.1 i
          (fun z₀ hz₀ => horderPair r.1 i z₀ hz₀) k
        have hgraph' : x ∈ (facePatch ∩ domain) ∩
            (fun z₀ : Fin n → ℝ =>
              CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
                lower upper k.succ.castSucc z₀) '' (baseTile r.1 ∩ baseTile i) :=
          ⟨hgraph, y, ⟨hyr, hy⟩, rfl⟩
        have hseamAt := congrArg (fun A : Set (Fin (n + 1) → ℝ) => x ∈ A) hseam
        have hmem := hseamAt.mpr hgraph'
        refine ⟨hmem.1.1, ?_⟩
        rw [hlow]
        exact hmem.1.2
      · have hseam := restricted.adjacent_base_tiles_share_seam i r.1
          (fun z₀ hz₀ => horderPair i r.1 z₀ hz₀) k
        have hgraph' : x ∈ (facePatch ∩ domain) ∩
            (fun z₀ : Fin n → ℝ =>
              CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
                lower upper k.succ.castSucc z₀) '' (baseTile i ∩ baseTile r.1) :=
          ⟨hgraph, y, ⟨hy, hyr⟩, rfl⟩
        have hseamAt := congrArg (fun A : Set (Fin (n + 1) → ℝ) => x ∈ A) hseam
        have hmem := hseamAt.mpr hgraph'
        refine ⟨hmem.2.1, ?_⟩
        rw [hhigh]
        exact hmem.2.2
    exact ⟨x, hoverlap, rfl⟩
  exact N.restrictedOneBitFiberPatch_finite_overlap_glue
    κ cover domain hdomain ψ z selected offset tailHead tail p ps hp hps' hatlas

/-- Craciun v3, §7.4.3 and §8 Step 2: a fan-labeled adjacent-strip seam carries both its
actual lower-face dependency and the finite smooth-barrier descent certificate at the same lifted
seam point. This is the geometric-to-dynamical seam datum for a face-by-face fill. -/
theorem Network.fanLabeled_restrictedOneBitFiberPatch_seam_dependency_and_glue
    {n : ℕ}
    (N : Network S) (κ : N.RateConstants)
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {lower upper : (Fin n → ℝ) → ℝ} {epsilon : ℝ}
    (F : Fan (EuclideanSpace ℝ (Fin n))) (hFdual : FanRefinement.HasDualFGCells F)
    [Fintype {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)}]
    (cover : CRNT.ZeroSeparatingInduction.CompactOneBitFiberPatchCover
      facePatch base (FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual)
      lower upper epsilon)
    (domain : Set (Fin (n + 1) → ℝ)) (hdomain : IsClosed domain)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S)
    {K : Set (EuclideanSpace ℝ S)} (z : K → N.euclideanStoichSubspace)
    (selected : (Σ i : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)},
      Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1)) → Option K)
    (offset : (Σ i : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)},
      Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1)) → ℝ)
    (tailHead : (EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ)
    (tail : List ((EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ))
    (hatlas : ∀ r q, q ∈ ψ '' ((facePatch ∩ domain) ∩
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual r.1)
        lower upper r.2) →
      ∃ D : EuclideanSpace ℝ S →L[ℝ] ℝ,
        HasFDerivAt
          (SmoothBarrierGluing.smoothWallList
            ((selected r).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1), offset r)
            (tailHead :: tail)) D q ∧
        D (toEuclid (N.massActionVectorField κ (toEuclid.symm q))) ≤ 0)
    (i j : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)}) (k : Fin (cover.tiling.subdivisionCount))
    (y : Fin n → ℝ) (horder : ∀ y ∈ base, lower y ≤ upper y)
    (hy : y ∈ FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual i)
    (hgraph : CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
      lower upper k.succ.castSucc y ∈ facePatch ∩ domain)
    (ps : List (Σ l : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)},
      Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1)))
    (hincident : ∀ r ∈ ps,
      y ∈ FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual r.1 ∧
        (r.2 = k.castSucc ∨ r.2 = k.succ)) :
    ∃ (G : ProperCone ℝ (EuclideanSpace ℝ (Fin n)))
      (hG : G ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)),
      (i.1 ≠ j.1 →
        FanRefinement.ProperExposedFaceDependency G i.1 ∨
          FanRefinement.ProperExposedFaceDependency G j.1) ∧
      FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual i ∩
        FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual j =
          FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual ⟨G, hG⟩ ∧
      ∃ D : EuclideanSpace ℝ S →L[ℝ] ℝ,
        HasFDerivAt
          (SmoothBarrierGluing.smoothMaxList
            (SmoothBarrierGluing.smoothWallList
              ((selected ⟨i, k.castSucc⟩).elim tailHead.1
                (fun wall => innerSL ℝ (z wall).1), offset ⟨i, k.castSucc⟩)
              (tailHead :: tail))
            (ps.map (fun r => SmoothBarrierGluing.smoothWallList
              ((selected r).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1), offset r)
              (tailHead :: tail)))) D
          (ψ (CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
            lower upper k.succ.castSucc y)) ∧
        D (toEuclid (N.massActionVectorField κ (toEuclid.symm
          (ψ (CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
            lower upper k.succ.castSucc y))))) ≤ 0 := by
  obtain ⟨G, hG, hintersection, hGC, hGD, _, _⟩ :=
    FanRefinement.euclideanHyperplaneArrangementBaseTile_intersection base F hFdual i j
  have hdependency : i.1 ≠ j.1 →
      FanRefinement.ProperExposedFaceDependency G i.1 ∨
        FanRefinement.ProperExposedFaceDependency G j.1 := by
    intro hne
    by_cases hGC' : G = i.1
    · right
      constructor
      · simpa [hGC'] using hGD
      · intro hGD'
        apply hne
        apply SetLike.coe_injective
        calc
          (i.1 : Set (EuclideanSpace ℝ (Fin n))) = G := by rw [hGC']
          _ = j.1 := congrArg (fun H : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) =>
            (H : Set (EuclideanSpace ℝ (Fin n)))) hGD'
    · exact Or.inl ⟨hGC, hGC'⟩
  have hbarrier := N.restrictedOneBitFiberPatch_finite_seam_glue
    κ cover domain hdomain ψ z selected offset tailHead tail hatlas i k y horder hy
      hgraph ps hincident
  exact ⟨G, hG, hdependency, hintersection, hbarrier⟩

/-- Craciun v3, §7.4.3 and §8 Step 2: for small fan-labeled base patches, the common lower fan
face and the finite smooth-barrier derivative are available at the same lifted seam point. The
returned base incidence retains the two small-patch labels, so the local chart scale and the
lexicographic geometric dependency survive the analytic gluing step. -/
theorem Network.fanSmallProductTile_restrictedSeam_dependency_and_glue
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {smallTile : ι → Set (Fin n → ℝ)} {lower upper : (Fin n → ℝ) → ℝ}
    {epsilon : ℝ} (F : Fan (EuclideanSpace ℝ (Fin n)))
    (hFdual : FanRefinement.HasDualFGCells F)
    [Fintype {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)}]
    (cover : CRNT.ZeroSeparatingInduction.CompactOneBitFiberPatchCover facePatch base
      (fun p : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
        C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)} × ι =>
          FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual p.1 ∩ smallTile p.2)
      lower upper epsilon)
    (domain : Set (Fin (n + 1) → ℝ)) (hdomain : IsClosed domain)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S)
    {K : Set (EuclideanSpace ℝ S)} (z : K → N.euclideanStoichSubspace)
    (selected : (Σ p : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)} × ι,
      Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1)) → Option K)
    (offset : (Σ p : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)} × ι,
      Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1)) → ℝ)
    (tailHead : (EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ)
    (tail : List ((EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ))
    (hatlas : ∀ r q, q ∈ ψ '' ((facePatch ∩ domain) ∩
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual r.1.1 ∩
          smallTile r.1.2) lower upper r.2) →
      ∃ D : EuclideanSpace ℝ S →L[ℝ] ℝ,
        HasFDerivAt
          (SmoothBarrierGluing.smoothWallList
            ((selected r).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1), offset r)
            (tailHead :: tail)) D q ∧
        D (toEuclid (N.massActionVectorField κ (toEuclid.symm q))) ≤ 0)
    (C D : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)})
    (i j : ι) (k : Fin (cover.tiling.subdivisionCount))
    (y : Fin n → ℝ) (horder : ∀ y ∈ base, lower y ≤ upper y)
    (hy : y ∈ FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual C ∩ smallTile i)
    (hgraph : CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
      lower upper k.succ.castSucc y ∈ facePatch ∩ domain)
    (ps : List (Σ p : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)} × ι,
      Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1)))
    (hincident : ∀ r ∈ ps,
      y ∈ FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual r.1.1 ∩
        smallTile r.1.2 ∧ (r.2 = k.castSucc ∨ r.2 = k.succ)) :
    ∃ (G : ProperCone ℝ (EuclideanSpace ℝ (Fin n)))
      (hG : G ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)),
      (C.1 ≠ D.1 →
        FanRefinement.ProperExposedFaceDependency G C.1 ∨
          FanRefinement.ProperExposedFaceDependency G D.1) ∧
      ((FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual C ∩ smallTile i) ∩
        (FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual D ∩ smallTile j) =
          FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual ⟨G, hG⟩ ∩
            (smallTile i ∩ smallTile j)) ∧
      ∃ D' : EuclideanSpace ℝ S →L[ℝ] ℝ,
        HasFDerivAt
          (SmoothBarrierGluing.smoothMaxList
            (SmoothBarrierGluing.smoothWallList
              ((selected ⟨(C, i), k.castSucc⟩).elim tailHead.1
                (fun wall => innerSL ℝ (z wall).1), offset ⟨(C, i), k.castSucc⟩)
              (tailHead :: tail))
            (ps.map (fun r => SmoothBarrierGluing.smoothWallList
              ((selected r).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1), offset r)
              (tailHead :: tail)))) D'
          (ψ (CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
            lower upper k.succ.castSucc y)) ∧
        D' (toEuclid (N.massActionVectorField κ (toEuclid.symm
          (ψ (CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
            lower upper k.succ.castSucc y))))) ≤ 0 := by
  obtain ⟨G, hG, hdependency, hbase, _⟩ :=
    FanRefinement.fanSmallProductTile_adjacentStrip_seam F hFdual cover horder C D i j k
  have hbarrier := N.restrictedOneBitFiberPatch_finite_seam_glue
    κ cover domain hdomain ψ z selected offset tailHead tail hatlas (C, i) k y horder hy
      hgraph ps hincident
  exact ⟨G, hG, hdependency, hbase, hbarrier⟩

/-- Craciun v3, §8 Step 2: a compact wall-chart cover supplies the local barriers needed to
glue every listed face incident to a clipped adjacent-strip seam. The shared projected basepoint
and endpoint-graph incidence are used to transfer each incident label to the same lifted seam
point before taking the finite smooth maximum. -/
theorem Network.exists_restrictedOneBitFiberPatch_finite_seam_glue_of_wallChart
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {baseTile : ι → Set (Fin n → ℝ)} {lower upper : (Fin n → ℝ) → ℝ}
    {epsilon : ℝ}
    (cover : CRNT.ZeroSeparatingInduction.CompactOneBitFiberPatchCover
      facePatch base baseTile lower upper epsilon)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S) (hψ : Continuous ψ)
    {K : Set (EuclideanSpace ℝ S)} (z : K → N.euclideanStoichSubspace)
    (t : Finset K) {ε δwall δcoord η tolerance : ℝ} (hε : 0 < ε)
    (hchart : ∀ y ∈ K, ∃ wall ∈ t, ∀ q ∈ Metric.ball y δwall,
      ε < ⟪(z wall).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ)
    (himage : ∀ p : Σ i : ι, Fin (cover.tiling.subdivisionCount + 1),
      ψ '' (facePatch ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2) ⊆ K)
    (hmapDiam : ∀ p : Σ i : ι, Fin (cover.tiling.subdivisionCount + 1),
      ∀ x ∈ facePatch ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2,
      ∀ y ∈ facePatch ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2,
      dist x y < δcoord → dist (ψ x) (ψ y) < δwall)
    (hprojectedSmall : ∀ p : Σ i : ι, Fin (cover.tiling.subdivisionCount + 1),
      ∀ a ∈ baseTile p.1, ∀ b ∈ baseTile p.1, dist a b < η)
    (hendpointVariation : ∀ p : Σ i : ι, Fin (cover.tiling.subdivisionCount + 1),
      ∀ a ∈ baseTile p.1, ∀ b ∈ baseTile p.1, dist a b < η →
        dist
          (CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpoint
            lower upper p.2.succ a)
          (CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpoint
            lower upper p.2.succ b) < tolerance)
    (hηsmall : η < δcoord) (hbudget : epsilon + tolerance < δcoord)
    (hδcoord : 0 < δcoord)
    (domain : Set (Fin (n + 1) → ℝ)) (hdomain : IsClosed domain)
    (tailHead : (EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ)
    (tail : List ((EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ))
    (i : ι) (k : Fin (cover.tiling.subdivisionCount))
    (y : Fin n → ℝ) (horder : ∀ y ∈ base, lower y ≤ upper y)
    (hy : y ∈ baseTile i)
    (hgraph : CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
      lower upper k.succ.castSucc y ∈ facePatch ∩ domain)
    (ps : List (Σ i : ι,
      Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1)))
    (hincident : ∀ r ∈ ps, y ∈ baseTile r.1 ∧
      (r.2 = k.castSucc ∨ r.2 = k.succ)) :
    ∃ selected : (Σ i : ι,
      Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1)) → Option K,
      ∃ offset : (Σ i : ι,
        Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1)) → ℝ,
      ∃ D : EuclideanSpace ℝ S →L[ℝ] ℝ,
        HasFDerivAt
          (SmoothBarrierGluing.smoothMaxList
            (SmoothBarrierGluing.smoothWallList
              ((selected ⟨i, k.castSucc⟩).elim tailHead.1
                (fun wall => innerSL ℝ (z wall).1), offset ⟨i, k.castSucc⟩)
              (tailHead :: tail))
            (ps.map (fun r => SmoothBarrierGluing.smoothWallList
              ((selected r).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1), offset r)
              (tailHead :: tail)))) D
        (ψ (CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
          lower upper k.succ.castSucc y)) ∧
        D (toEuclid (N.massActionVectorField κ (toEuclid.symm
          (ψ (CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
            lower upper k.succ.castSucc y))))) ≤ 0 := by
  obtain ⟨selected, _, hlabels, hselected⟩ := N.exists_oneBitFiberPatchWallSelection
    κ cover ψ z t hchart himage hmapDiam
    hprojectedSmall hendpointVariation hηsmall hbudget hδcoord
  let restricted := cover.restrict_to_closedDomain domain hdomain
  have hselectedRestricted : ∀ p wall, selected p = some wall → wall ∈ t ∧ ∀ q ∈
      ψ '' ((facePatch ∩ domain) ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2),
      ε < ⟪(z wall).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ := by
    intro p wall hp
    have hs := hselected p wall hp
    refine ⟨hs.1, ?_⟩
    intro q hq
    rcases hq with ⟨x, hx, rfl⟩
    exact hs.2 _ ⟨x, ⟨hx.1.1, hx.2⟩, rfl⟩
  have hlabelsRestricted : ∀ p,
      ((facePatch ∩ domain) ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2).Nonempty →
      ∃ wall, selected p = some wall := by
    intro p hne
    apply hlabels p
    exact hne.mono (by
      intro x hx
      exact ⟨hx.1.1, hx.2⟩)
  obtain ⟨offset, hatlas⟩ := N.exists_simultaneous_oneBitFiberPatch_barriers
    κ restricted ψ hψ z t hε selected hselectedRestricted hlabelsRestricted tailHead tail
  obtain ⟨D, hD⟩ := N.restrictedOneBitFiberPatch_finite_seam_glue
    κ cover domain hdomain ψ z selected offset tailHead tail hatlas
    i k y horder hy hgraph ps hincident
  exact ⟨selected, offset, D, hD⟩

/-- Craciun v3, §§7.4.3 and 8 Step 1: select the inward-wall atlas directly on the
fan-labeled product refinement, then glue that atlas across an adjacent fiber-strip seam. The
small-patch diameter controls the projected scale on each product tile, so the selected-wall
indices and the common fan-face incidence use the same cover and subdivision. -/
theorem Network.exists_fanSmallProductTile_restrictedSeam_dependency_and_glue_of_wallChart
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {smallTile : ι → Set (Fin n → ℝ)} {lower upper : (Fin n → ℝ) → ℝ}
    {epsilon : ℝ} (F : Fan (EuclideanSpace ℝ (Fin n)))
    (hFdual : FanRefinement.HasDualFGCells F)
    [Fintype {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)}]
    (cover : CRNT.ZeroSeparatingInduction.CompactOneBitFiberPatchCover facePatch base
      (fun p : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
        C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)} × ι =>
          FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual p.1 ∩
            smallTile p.2)
      lower upper epsilon)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S) (hψ : Continuous ψ)
    {K : Set (EuclideanSpace ℝ S)} (z : K → N.euclideanStoichSubspace)
    (t : Finset K) {ε δwall δcoord η tolerance : ℝ} (hε : 0 < ε)
    (hchart : ∀ y ∈ K, ∃ wall ∈ t, ∀ q ∈ Metric.ball y δwall,
      ε < ⟪(z wall).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ)
    (himage : ∀ p : Σ q : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)} × ι,
      Fin (cover.tiling.subdivisionCount + 1),
      ψ '' (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual p.1.1 ∩
          smallTile p.1.2) lower upper p.2) ⊆ K)
    (hmapDiam : ∀ p : Σ q : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)} × ι,
      Fin (cover.tiling.subdivisionCount + 1),
      ∀ x ∈ facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual p.1.1 ∩
            smallTile p.1.2) lower upper p.2,
      ∀ y ∈ facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual p.1.1 ∩
            smallTile p.1.2) lower upper p.2,
      dist x y < δcoord → dist (ψ x) (ψ y) < δwall)
    (hsmall : ∀ i, ∀ a ∈ smallTile i, ∀ b ∈ smallTile i, dist a b < η)
    (hendpointVariation : ∀ p : Σ q : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)} × ι,
      Fin (cover.tiling.subdivisionCount + 1),
      ∀ a ∈ FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual p.1.1 ∩
          smallTile p.1.2,
      ∀ b ∈ FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual p.1.1 ∩
          smallTile p.1.2,
      dist a b < η →
        dist (CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpoint
          lower upper p.2.succ a)
          (CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpoint
            lower upper p.2.succ b) < tolerance)
    (hηsmall : η < δcoord) (hbudget : epsilon + tolerance < δcoord)
    (hδcoord : 0 < δcoord)
    (domain : Set (Fin (n + 1) → ℝ)) (hdomain : IsClosed domain)
    (tailHead : (EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ)
    (tail : List ((EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ))
    (C D : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)})
    (i j : ι) (k : Fin cover.tiling.subdivisionCount)
    (y : Fin n → ℝ) (horder : ∀ y ∈ base, lower y ≤ upper y)
    (hy : y ∈ FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual C ∩
      smallTile i)
    (hgraph : CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
      lower upper k.succ.castSucc y ∈ facePatch ∩ domain)
    (ps : List (Σ q : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)} × ι,
      Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1)))
    (hincident : ∀ r ∈ ps,
      y ∈ FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual r.1.1 ∩
        smallTile r.1.2 ∧ (r.2 = k.castSucc ∨ r.2 = k.succ)) :
    ∃ (G : ProperCone ℝ (EuclideanSpace ℝ (Fin n)))
      (hG : G ∈ FanRefinement.hyperplaneArrangementFamily
        (FanRefinement.fanNormalSet F hFdual)),
      (C.1 ≠ D.1 → FanRefinement.ProperExposedFaceDependency G C.1 ∨
        FanRefinement.ProperExposedFaceDependency G D.1) ∧
      ((FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual C ∩
          smallTile i) ∩
        (FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual D ∩
          smallTile j) =
        FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual ⟨G, hG⟩ ∩
          (smallTile i ∩ smallTile j)) ∧
      ∃ selected : (Σ q : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
        C ∈ FanRefinement.hyperplaneArrangementFamily
          (FanRefinement.fanNormalSet F hFdual)} × ι,
        Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1)) →
          Option K,
      ∃ offset : (Σ q : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
        C ∈ FanRefinement.hyperplaneArrangementFamily
          (FanRefinement.fanNormalSet F hFdual)} × ι,
        Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1)) → ℝ,
      ∃ D' : EuclideanSpace ℝ S →L[ℝ] ℝ,
        HasFDerivAt
          (SmoothBarrierGluing.smoothMaxList
            (SmoothBarrierGluing.smoothWallList
              ((selected ⟨(C, i), k.castSucc⟩).elim tailHead.1
                (fun wall => innerSL ℝ (z wall).1), offset ⟨(C, i), k.castSucc⟩)
              (tailHead :: tail))
            (ps.map (fun r => SmoothBarrierGluing.smoothWallList
              ((selected r).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1), offset r)
              (tailHead :: tail)))) D'
          (ψ (CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
            lower upper k.succ.castSucc y)) ∧
        D' (toEuclid (N.massActionVectorField κ (toEuclid.symm
          (ψ (CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
            lower upper k.succ.castSucc y))))) ≤ 0 := by
  have hprojectedSmall : ∀ p : Σ q : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ FanRefinement.hyperplaneArrangementFamily (FanRefinement.fanNormalSet F hFdual)} × ι,
      Fin (cover.tiling.subdivisionCount + 1),
      ∀ a ∈ FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual p.1.1 ∩
          smallTile p.1.2,
      ∀ b ∈ FanRefinement.euclideanHyperplaneArrangementBaseTile base F hFdual p.1.1 ∩
          smallTile p.1.2,
      dist a b < η := by
    intro p a ha b hb
    exact hsmall p.1.2 a ha.2 b hb.2
  obtain ⟨selected, offset, _, hbarrier⟩ :=
    N.exists_restrictedOneBitFiberPatch_finite_seam_glue_of_wallChart
      κ cover ψ hψ z t hε hchart himage hmapDiam hprojectedSmall hendpointVariation
      hηsmall hbudget hδcoord domain hdomain tailHead tail (C, i) k y horder hy
      hgraph ps hincident
  obtain ⟨G, hG, hdependency, hbase, _⟩ :=
    FanRefinement.fanSmallProductTile_adjacentStrip_seam F hFdual cover horder C D i j k
  exact ⟨G, hG, hdependency, hbase, selected, offset, _, hbarrier⟩

/-- End-to-end local atlas step: a compact wall-chart cover selects one inward wall on each
nonempty one-bit patch, and the selected barriers then glue over any finite clipped common face.
This composes the compact-chart-to-tile argument with Craciun v3's restricted blueprint step. -/
theorem Network.exists_restrictedOneBitFiberPatch_finite_overlap_glue_of_wallChart
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {baseTile : ι → Set (Fin n → ℝ)} {lower upper : (Fin n → ℝ) → ℝ}
    {epsilon : ℝ}
    (cover : CRNT.ZeroSeparatingInduction.CompactOneBitFiberPatchCover
      facePatch base baseTile lower upper epsilon)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S) (hψ : Continuous ψ)
    {K : Set (EuclideanSpace ℝ S)} (z : K → N.euclideanStoichSubspace)
    (t : Finset K) {ε δwall δcoord η tolerance : ℝ} (hε : 0 < ε)
    (hchart : ∀ y ∈ K, ∃ wall ∈ t, ∀ q ∈ Metric.ball y δwall,
      ε < ⟪(z wall).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ)
    (himage : ∀ p : Σ i : ι, Fin (cover.tiling.subdivisionCount + 1),
      ψ '' (facePatch ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2) ⊆ K)
    (hmapDiam : ∀ p : Σ i : ι, Fin (cover.tiling.subdivisionCount + 1),
      ∀ x ∈ facePatch ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2,
      ∀ y ∈ facePatch ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2,
      dist x y < δcoord → dist (ψ x) (ψ y) < δwall)
    (hprojectedSmall : ∀ p : Σ i : ι, Fin (cover.tiling.subdivisionCount + 1),
      ∀ a ∈ baseTile p.1, ∀ b ∈ baseTile p.1, dist a b < η)
    (hendpointVariation : ∀ p : Σ i : ι, Fin (cover.tiling.subdivisionCount + 1),
      ∀ a ∈ baseTile p.1, ∀ b ∈ baseTile p.1, dist a b < η →
        dist
          (CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpoint
            lower upper p.2.succ a)
          (CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpoint
            lower upper p.2.succ b) < tolerance)
    (hηsmall : η < δcoord) (hbudget : epsilon + tolerance < δcoord)
    (hδcoord : 0 < δcoord)
    (domain : Set (Fin (n + 1) → ℝ)) (hdomain : IsClosed domain)
    (tailHead : (EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ)
    (tail : List ((EuclideanSpace ℝ S →L[ℝ] ℝ) × ℝ))
    (p : Σ i : ι,
      Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1))
    (ps : List (Σ i : ι,
      Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1)))
    {q : EuclideanSpace ℝ S}
    (hp : q ∈ ψ '' ((facePatch ∩ domain) ∩
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2))
    (hps : ∀ r ∈ ps, q ∈ ψ '' ((facePatch ∩ domain) ∩
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile r.1) lower upper r.2)) :
    ∃ selected : (Σ i : ι,
      Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1)) → Option K,
      ∃ offset : (Σ i : ι,
        Fin ((cover.restrict_to_closedDomain domain hdomain).tiling.subdivisionCount + 1)) → ℝ,
      ∃ D : EuclideanSpace ℝ S →L[ℝ] ℝ,
        HasFDerivAt
          (SmoothBarrierGluing.smoothMaxList
            (SmoothBarrierGluing.smoothWallList
              ((selected p).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1), offset p)
              (tailHead :: tail))
            (ps.map (fun r => SmoothBarrierGluing.smoothWallList
              ((selected r).elim tailHead.1 (fun wall => innerSL ℝ (z wall).1), offset r)
              (tailHead :: tail)))) D q ∧
        D (toEuclid (N.massActionVectorField κ (toEuclid.symm q))) ≤ 0 := by
  obtain ⟨selected, _, hlabels, hselected⟩ := N.exists_oneBitFiberPatchWallSelection
    κ cover ψ z t hchart himage hmapDiam
    hprojectedSmall hendpointVariation hηsmall hbudget hδcoord
  obtain ⟨offset, hglue⟩ := N.exists_restrictedOneBitFiberPatch_finite_overlap_glue
    κ cover domain hdomain ψ hψ z t hε
    selected hselected hlabels tailHead tail p ps hp hps
  exact ⟨selected, offset, hglue⟩

/-- Craciun v3, §7.4.3: any two labels selected on restricted tiles are simultaneously inward on
their overlap, including overlaps from degenerate fibers. Consequently their two-wall smooth
maximum descends there. This is the pairwise compatibility statement used when assembling the
tilewise barriers across the full face-patch complex. -/
theorem Network.overlapping_oneBitFiberPatchWalls_glue
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {baseTile : ι → Set (Fin n → ℝ)} {lower upper : (Fin n → ℝ) → ℝ}
    {epsilon : ℝ}
    (cover : CRNT.ZeroSeparatingInduction.CompactOneBitFiberPatchCover
      facePatch base baseTile lower upper epsilon)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S)
    {K : Set (EuclideanSpace ℝ S)} (z : K → N.euclideanStoichSubspace)
    (t : Finset K) {ε : ℝ} (hε : 0 < ε)
    (selected : (Σ i : ι, Fin (cover.tiling.subdivisionCount + 1)) → Option K)
    (hselected : ∀ p wall, selected p = some wall → wall ∈ t ∧ ∀ q ∈
      ψ '' (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2),
      ε < ⟪(z wall).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ)
    (p r : Σ i : ι, Fin (cover.tiling.subdivisionCount + 1))
    (wallP wallR : K)
    (hwP : selected p = some wallP) (hwR : selected r = some wallR)
    {q : EuclideanSpace ℝ S}
    (hq : q ∈ ψ ''
      ((facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2) ∩
        (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile r.1) lower upper r.2))) :
    wallP ∈ t ∧ wallR ∈ t ∧
      ∃ D : EuclideanSpace ℝ S →L[ℝ] ℝ,
        HasFDerivAt
          (SmoothBarrierGluing.smoothWallList
            (innerSL ℝ (z wallP).1, 0)
            [(innerSL ℝ (z wallR).1, 0)]) D q ∧
        D (toEuclid (N.massActionVectorField κ (toEuclid.symm q))) < 0 := by
  rcases hq with ⟨x, ⟨hxP, hxR⟩, rfl⟩
  have hspecP := hselected p wallP hwP
  have hspecR := hselected r wallR hwR
  have hinP : ε < ⟪(z wallP).1,
      toEuclid (N.massActionVectorField κ (toEuclid.symm (ψ x)))⟫_ℝ :=
    hspecP.2 _ ⟨x, hxP, rfl⟩
  have hinR : ε < ⟪(z wallR).1,
      toEuclid (N.massActionVectorField κ (toEuclid.symm (ψ x)))⟫_ℝ :=
    hspecR.2 _ ⟨x, hxR, rfl⟩
  have hhead : ε ≤ innerSL ℝ (z wallP).1
      (toEuclid (N.massActionVectorField κ (toEuclid.symm (ψ x)))) := by
    simpa only [innerSL_apply_apply] using le_of_lt hinP
  have htail : ∀ Mb ∈ [(innerSL ℝ (z wallR).1, (0 : ℝ))],
      ε ≤ Mb.1 (toEuclid (N.massActionVectorField κ (toEuclid.symm (ψ x)))) := by
    intro Mb hMb
    have hMb' : Mb = (innerSL ℝ (z wallR).1, (0 : ℝ)) := by simpa using hMb
    rw [hMb']
    simpa only [innerSL_apply_apply] using le_of_lt hinR
  obtain ⟨D, hD, hDmargin⟩ := SmoothBarrierGluing.smoothWallList_descends_strictly
    (X := fun q : EuclideanSpace ℝ S =>
      toEuclid (N.massActionVectorField κ (toEuclid.symm q)))
    (x := ψ x) (ε := ε)
    (innerSL ℝ (z wallP).1, (0 : ℝ)) [(innerSL ℝ (z wallR).1, (0 : ℝ))]
    hhead htail
  refine ⟨hspecP.1, hspecR.1, D, ?_, ?_⟩
  · simpa using hD
  · exact lt_of_le_of_lt hDmargin (neg_neg_of_pos hε)

/-- A selected wall for a restricted one-bit tile remains inward at its Craciun midpoint
representative whenever the parent patch is the corresponding full fiber band. The geometric
incidence lemma places the representative in the very restricted patch on which wall selection
was proved. -/
theorem Network.selected_oneBitFiberPatchWall_inward_at_center
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {baseTile : ι → Set (Fin n → ℝ)} {lower upper : (Fin n → ℝ) → ℝ}
    {epsilon : ℝ}
    (cover : CRNT.ZeroSeparatingInduction.CompactOneBitFiberPatchCover
      facePatch base baseTile lower upper epsilon)
    (hfaceEq : facePatch = CRNT.ZeroSeparatingInduction.projectionFiberBand base
      (fun y => some (lower y)) (fun y => some (upper y)))
    (horder : ∀ y ∈ base, lower y ≤ upper y)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S)
    {K : Set (EuclideanSpace ℝ S)} (z : K → N.euclideanStoichSubspace)
    (t : Finset K) {ε : ℝ}
    (selected : (Σ i : ι, Fin (cover.tiling.subdivisionCount + 1)) → Option K)
    (hselected : ∀ p wall, selected p = some wall → wall ∈ t ∧ ∀ q ∈
      ψ '' (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2),
      ε < ⟪(z wall).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ)
    (p : Σ i : ι, Fin (cover.tiling.subdivisionCount + 1))
    {y : Fin n → ℝ} (hy : y ∈ baseTile p.1) (wall : K)
    (hwall : selected p = some wall) :
    wall ∈ t ∧ ε < ⟪(z wall).1,
      toEuclid (N.massActionVectorField κ
        (toEuclid.symm (ψ (Fin.snoc y (cover.tiling.tile_center p.2 y)))))⟫_ℝ := by
  have hpatch := cover.center_lift_mem_band_patch hfaceEq horder p hy
  have hcenter : ψ (Fin.snoc y (cover.tiling.tile_center p.2 y)) ∈
      ψ '' (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2) :=
    ⟨Fin.snoc y (cover.tiling.tile_center p.2 y), hpatch, rfl⟩
  have hwallSpec := hselected p wall hwall
  exact ⟨hwallSpec.1, hwallSpec.2 _ hcenter⟩

/-- Craciun v3, §7.4.3, Step 2 followed by the local wall selection: every nonempty restricted
tile has an actual face-patch basepoint, the basepoint projects into the corresponding lower tile,
and the tile's selected toric wall points strictly inward at that point. -/
theorem Network.exists_oneBitFiberPatchInwardBasepoint
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {baseTile : ι → Set (Fin n → ℝ)} {lower upper : (Fin n → ℝ) → ℝ}
    {epsilon : ℝ}
    (cover : CRNT.ZeroSeparatingInduction.CompactOneBitFiberPatchCover
      facePatch base baseTile lower upper epsilon)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S)
    {K : Set (EuclideanSpace ℝ S)} (z : K → N.euclideanStoichSubspace)
    (t : Finset K) {ε : ℝ}
    (selected : (Σ i : ι, Fin (cover.tiling.subdivisionCount + 1)) → Option K)
    (hselected : ∀ p wall, selected p = some wall → wall ∈ t ∧ ∀ q ∈
      ψ '' (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2),
      ε < ⟪(z wall).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ)
    (p : Σ i : ι, Fin (cover.tiling.subdivisionCount + 1))
    (hne : (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
      (baseTile p.1) lower upper p.2).Nonempty)
    (hselectedNonempty : ∃ wall, selected p = some wall) :
    ∃ wall x, selected p = some wall ∧
      x ∈ facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2 ∧
      CRNT.ZeroSeparatingInduction.forgetLastCoordinate n x ∈ baseTile p.1 ∧
      wall ∈ t ∧ ε < ⟪(z wall).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm (ψ x)))⟫_ℝ := by
  obtain ⟨wall, hwall⟩ := hselectedNonempty
  obtain ⟨x, hx, hprojected⟩ := cover.exists_restricted_tile_basepoint_incidence p hne
  have hwallSpec := hselected p wall hwall
  have himage : ψ x ∈ ψ ''
      (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2) := ⟨x, hx, rfl⟩
  exact ⟨wall, x, hwall, hx, hprojected, hwallSpec.1, hwallSpec.2 _ himage⟩

/-- Craciun v3, §8 Step 1 followed by the local inward-wall condition: clipping a one-bit
blueprint to a closed domain preserves the tile-to-base incidence, and a wall selected on that
clipped tile is strictly inward at an actual point of the clipped tile. -/
theorem Network.exists_restrictedOneBitFiberPatchInwardBasepoint
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {baseTile : ι → Set (Fin n → ℝ)} {lower upper : (Fin n → ℝ) → ℝ}
    {epsilon : ℝ}
    (cover : CRNT.ZeroSeparatingInduction.CompactOneBitFiberPatchCover
      facePatch base baseTile lower upper epsilon)
    (domain : Set (Fin (n + 1) → ℝ)) (hdomain : IsClosed domain)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S)
    {K : Set (EuclideanSpace ℝ S)} (z : K → N.euclideanStoichSubspace)
    (t : Finset K) {ε : ℝ}
    (selected : (Σ i : ι, Fin (cover.tiling.subdivisionCount + 1)) → Option K)
    (hselected : ∀ p wall, selected p = some wall → wall ∈ t ∧ ∀ q ∈
      ψ '' ((facePatch ∩ domain) ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2),
      ε < ⟪(z wall).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ)
    (p : Σ i : ι, Fin (cover.tiling.subdivisionCount + 1))
    (hne : ((facePatch ∩ domain) ∩
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2).Nonempty)
    (hselectedNonempty : ∃ wall, selected p = some wall) :
    ∃ wall x, selected p = some wall ∧
      x ∈ (facePatch ∩ domain) ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2 ∧
      x ∈ domain ∧
      CRNT.ZeroSeparatingInduction.forgetLastCoordinate n x ∈ baseTile p.1 ∧
      wall ∈ t ∧ ε < ⟪(z wall).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm (ψ x)))⟫_ℝ := by
  obtain ⟨wall, hwall⟩ := hselectedNonempty
  obtain ⟨x, hx, hdomain_x, hprojected⟩ :=
    cover.exists_restrictedDomain_tile_basepoint_incidence domain hdomain p hne
  have hwallSpec := hselected p wall hwall
  have himage : ψ x ∈ ψ '' ((facePatch ∩ domain) ∩
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2) := ⟨x, hx, rfl⟩
  exact ⟨wall, x, hwall, hx, hdomain_x, hprojected, hwallSpec.1, hwallSpec.2 _ himage⟩

/-- A nonempty shared seam between two clipped neighboring patches supplies a lower-dimensional
basepoint whose endpoint lift lies in the clipped face. The two selected tile walls are both
strictly inward at that lift, so the compatibility data survives restriction to the projective
domain. -/
theorem Network.exists_restrictedAdjacentOneBitFiberPatchWalls_inward_on_seam
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {baseTile : ι → Set (Fin n → ℝ)} {lower upper : (Fin n → ℝ) → ℝ}
    {epsilon : ℝ}
    (cover : CRNT.ZeroSeparatingInduction.CompactOneBitFiberPatchCover
      facePatch base baseTile lower upper epsilon)
    (domain : Set (Fin (n + 1) → ℝ)) (hdomain : IsClosed domain)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S)
    {K : Set (EuclideanSpace ℝ S)} (z : K → N.euclideanStoichSubspace)
    (t : Finset K) {ε : ℝ}
    (selected : (Σ i : ι, Fin (cover.tiling.subdivisionCount + 1)) → Option K)
    (hselected : ∀ p wall, selected p = some wall → wall ∈ t ∧ ∀ q ∈
      ψ '' ((facePatch ∩ domain) ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile p.1) lower upper p.2),
      ε < ⟪(z wall).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ)
    (i j : ι)
    (horder : ∀ y ∈ baseTile i ∩ baseTile j, lower y ≤ upper y)
    (k : Fin cover.tiling.subdivisionCount)
    (wall₀ wall₁ : K)
    (hwall₀ : selected ⟨i, k.castSucc⟩ = some wall₀)
    (hwall₁ : selected ⟨j, k.succ⟩ = some wall₁)
    (hne : (((facePatch ∩ domain) ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile i) lower upper k.castSucc) ∩
      ((facePatch ∩ domain) ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile j) lower upper k.succ)).Nonempty) :
    ∃ y, y ∈ baseTile i ∩ baseTile j ∧
      ε < ⟪(z wall₀).1, toEuclid (N.massActionVectorField κ
        (toEuclid.symm (ψ (CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
          lower upper k.succ.castSucc y))))⟫_ℝ ∧
      ε < ⟪(z wall₁).1, toEuclid (N.massActionVectorField κ
        (toEuclid.symm (ψ (CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
          lower upper k.succ.castSucc y))))⟫_ℝ := by
  obtain ⟨y, hy, hface, _⟩ := cover.exists_restrictedDomain_adjacent_seam_basepoint
    domain hdomain i j horder k hne
  let x := CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
    lower upper k.succ.castSucc y
  let restricted := cover.restrict_to_closedDomain domain hdomain
  have hseam := restricted.adjacent_base_tiles_share_seam i j horder k
  have hxSeam : x ∈
      ((facePatch ∩ domain) ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile i) lower upper k.castSucc) ∩
      ((facePatch ∩ domain) ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile j) lower upper k.succ) := by
    have hxGraph : x ∈ (facePatch ∩ domain) ∩
        (fun z : Fin n → ℝ =>
          CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
            lower upper k.succ.castSucc z) '' (baseTile i ∩ baseTile j) := by
      refine ⟨hface, y, hy, ?_⟩
      rfl
    have hseamAt := congrArg (fun s : Set (Fin (n + 1) → ℝ) => x ∈ s) hseam
    exact hseamAt.mpr hxGraph
  have himage₀ : ψ x ∈ ψ '' ((facePatch ∩ domain) ∩
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile i) lower upper k.castSucc) := ⟨x, hxSeam.1, rfl⟩
  have himage₁ : ψ x ∈ ψ '' ((facePatch ∩ domain) ∩
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile j) lower upper k.succ) := ⟨x, hxSeam.2, rfl⟩
  exact ⟨y, hy, (hselected ⟨i, k.castSucc⟩ wall₀ hwall₀).2 _ himage₀,
    (hselected ⟨j, k.succ⟩ wall₁ hwall₁).2 _ himage₁⟩

/-- Adjacent fiber strips meet on their shared endpoint graph, and both selected tile walls remain
strictly inward at every point of that seam. This is the wall-orientation compatibility needed
when the Case 1.2 tile boundaries are assembled as a piecewise surface. -/
theorem Network.adjacent_oneBitFiberPatchWalls_inward_on_seam
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {baseTile : ι → Set (Fin n → ℝ)} {lower upper : (Fin n → ℝ) → ℝ}
    {epsilon : ℝ}
    (cover : CRNT.ZeroSeparatingInduction.CompactOneBitFiberPatchCover
      facePatch base baseTile lower upper epsilon)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S)
    {K : Set (EuclideanSpace ℝ S)} (z : K → N.euclideanStoichSubspace)
    (t : Finset K) {ε : ℝ}
    (selected : (Σ i : ι, Fin (cover.tiling.subdivisionCount + 1)) → Option K)
    (hselected : ∀ p wall, selected p = some wall → wall ∈ t ∧ ∀ q ∈
      ψ '' (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2),
      ε < ⟪(z wall).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ)
    (i j : ι)
    (horder : ∀ y ∈ baseTile i ∩ baseTile j, lower y ≤ upper y)
    (k : Fin cover.tiling.subdivisionCount)
    (wall₀ wall₁ : K)
    (hwall₀ : selected ⟨i, k.castSucc⟩ = some wall₀)
    (hwall₁ : selected ⟨j, k.succ⟩ = some wall₁)
    {q : EuclideanSpace ℝ S}
    (hq : q ∈ ψ '' (facePatch ∩
      (fun y : Fin n → ℝ =>
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
          lower upper k.succ.castSucc y) '' (baseTile i ∩ baseTile j))) :
    wall₀ ∈ t ∧ wall₁ ∈ t ∧
      ε < ⟪(z wall₀).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ ∧
      ε < ⟪(z wall₁).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ := by
  let patch₀ := facePatch ∩
    CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
      (baseTile i) lower upper k.castSucc
  let patch₁ := facePatch ∩
    CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
      (baseTile j) lower upper k.succ
  have hseam := cover.adjacent_base_tiles_share_seam i j horder k
  have hseam' : patch₀ ∩ patch₁ = facePatch ∩
      (fun y : Fin n → ℝ =>
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
          lower upper k.succ.castSucc y) '' (baseTile i ∩ baseTile j) := by
    simpa only [patch₀, patch₁] using hseam
  have hq₀ : q ∈ ψ '' patch₀ := by
    rcases hq with ⟨x, hx, rfl⟩
    have hxOverlap : x ∈ patch₀ ∩ patch₁ := by
      change x ∈ (facePatch ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile i) lower upper k.castSucc) ∩
        (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile j) lower upper k.succ)
      rw [hseam']
      exact hx
    exact ⟨x, hxOverlap.1, rfl⟩
  have hq₁ : q ∈ ψ '' patch₁ := by
    rcases hq with ⟨x, hx, rfl⟩
    have hxOverlap : x ∈ patch₀ ∩ patch₁ := by
      change x ∈ (facePatch ∩
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile i) lower upper k.castSucc) ∩
        (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
          (baseTile j) lower upper k.succ)
      rw [hseam']
      exact hx
    exact ⟨x, hxOverlap.2, rfl⟩
  have hspec₀ := hselected ⟨i, k.castSucc⟩ wall₀ hwall₀
  have hspec₁ := hselected ⟨j, k.succ⟩ wall₁ hwall₁
  exact ⟨hspec₀.1, hspec₁.1, hspec₀.2 q hq₀, hspec₁.2 q hq₁⟩

/-- On a positive shared seam, the two selected tile walls are active network walls as well as
strictly inward directions. This is the wall-activity certificate needed when the local seam data
is promoted to the finite active-wall family used by the zero-separating surface theorem. -/
theorem Network.adjacent_oneBitFiberPatchWalls_active_on_seam
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {baseTile : ι → Set (Fin n → ℝ)} {lower upper : (Fin n → ℝ) → ℝ}
    {epsilon : ℝ}
    (cover : CRNT.ZeroSeparatingInduction.CompactOneBitFiberPatchCover
      facePatch base baseTile lower upper epsilon)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S)
    {K : Set (EuclideanSpace ℝ S)} (z : K → N.euclideanStoichSubspace)
    (t : Finset K) {ε : ℝ} (hε : 0 < ε)
    (selected : (Σ i : ι, Fin (cover.tiling.subdivisionCount + 1)) → Option K)
    (hselected : ∀ p wall, selected p = some wall → wall ∈ t ∧ ∀ q ∈
      ψ '' (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2),
      ε < ⟪(z wall).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ)
    (i j : ι)
    (horder : ∀ y ∈ baseTile i ∩ baseTile j, lower y ≤ upper y)
    (k : Fin cover.tiling.subdivisionCount)
    (wall₀ wall₁ : K)
    (hwall₀ : selected ⟨i, k.castSucc⟩ = some wall₀)
    (hwall₁ : selected ⟨j, k.succ⟩ = some wall₁)
    {q : EuclideanSpace ℝ S}
    (hq : q ∈ ψ '' (facePatch ∩
      (fun y : Fin n → ℝ =>
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
          lower upper k.succ.castSucc y) '' (baseTile i ∩ baseTile j)))
    (hpositive : Concentration.Positive (toEuclid.symm q)) :
    N.ActiveWall (toEuclid.symm (z wall₀).1) ∧
      N.ActiveWall (toEuclid.symm (z wall₁).1) := by
  obtain ⟨_, _, hleft, hright⟩ := N.adjacent_oneBitFiberPatchWalls_inward_on_seam
    κ cover ψ z t selected hselected i j horder k wall₀ wall₁ hwall₀ hwall₁ hq
  constructor
  · apply hwr.activeWall_of_positive_toricField_pairing κ hpositive
    have hstrict := lt_trans hε hleft
    simpa [Network.toricMassActionField] using hstrict
  · apply hwr.activeWall_of_positive_toricField_pairing κ hpositive
    have hstrict := lt_trans hε hright
    simpa [Network.toricMassActionField] using hstrict

/-- The two inward wall labels on a compact shared seam admit a common smooth barrier there.
The seam compactness comes from the one-bit blueprint, while the strict inward inequalities on
both incident tiles make the two-wall smooth maximum decrease along the mass-action field. This
is the analytic gluing datum for crossing a Case 1.2 tile seam. -/
theorem Network.exists_adjacent_oneBitFiberPatch_seam_smoothBarrier
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {baseTile : ι → Set (Fin n → ℝ)} {lower upper : (Fin n → ℝ) → ℝ}
    {epsilon : ℝ}
    (cover : CRNT.ZeroSeparatingInduction.CompactOneBitFiberPatchCover
      facePatch base baseTile lower upper epsilon)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S) (hψ : Continuous ψ)
    {K : Set (EuclideanSpace ℝ S)} (z : K → N.euclideanStoichSubspace)
    (t : Finset K) {ε : ℝ} (hε : 0 < ε)
    (selected : (Σ i : ι, Fin (cover.tiling.subdivisionCount + 1)) → Option K)
    (hselected : ∀ p wall, selected p = some wall → wall ∈ t ∧ ∀ q ∈
      ψ '' (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2),
      ε < ⟪(z wall).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ)
    (i j : ι)
    (horder : ∀ y ∈ baseTile i ∩ baseTile j, lower y ≤ upper y)
    (k : Fin cover.tiling.subdivisionCount)
    (wall₀ wall₁ : K)
    (hwall₀ : selected ⟨i, k.castSucc⟩ = some wall₀)
    (hwall₁ : selected ⟨j, k.succ⟩ = some wall₁)
    (hseamNonempty : (ψ '' (facePatch ∩
      (fun y : Fin n → ℝ =>
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
          lower upper k.succ.castSucc y) '' (baseTile i ∩ baseTile j))).Nonempty)
    (hpositive : ∀ q ∈ ψ '' (facePatch ∩
      (fun y : Fin n → ℝ =>
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
          lower upper k.succ.castSucc y) '' (baseTile i ∩ baseTile j)),
      Concentration.Positive (toEuclid.symm q)) :
    N.ActiveWall (toEuclid.symm (z wall₀).1) ∧
    N.ActiveWall (toEuclid.symm (z wall₁).1) ∧
    IsCompact (ψ '' (facePatch ∩
      (fun y : Fin n → ℝ =>
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
          lower upper k.succ.castSucc y) '' (baseTile i ∩ baseTile j))) ∧
    (∀ q ∈ ψ '' (facePatch ∩
      (fun y : Fin n → ℝ =>
        CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
          lower upper k.succ.castSucc y) '' (baseTile i ∩ baseTile j)),
      ∃ D : EuclideanSpace ℝ S →L[ℝ] ℝ,
        HasFDerivAt
          (SmoothBarrierGluing.smoothWallList
            (innerSL ℝ (z wall₀).1, 0)
            [(innerSL ℝ (z wall₁).1, 0)]) D q ∧
        D (toEuclid (N.massActionVectorField κ (toEuclid.symm q))) < 0) := by
  let seam : Set (Fin (n + 1) → ℝ) := facePatch ∩
    (fun y : Fin n → ℝ =>
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
        lower upper k.succ.castSucc y) '' (baseTile i ∩ baseTile j)
  have hseamCompact : IsCompact (ψ '' seam) :=
    (cover.adjacent_base_tiles_shared_seam_compact i j horder k).image hψ
  obtain ⟨q₀, hq₀⟩ := hseamNonempty
  have hactive := N.adjacent_oneBitFiberPatchWalls_active_on_seam
    hwr κ cover ψ z t hε selected hselected i j horder k wall₀ wall₁
    hwall₀ hwall₁ hq₀ (hpositive q₀ hq₀)
  have hwall : ∀ q ∈ ψ '' seam,
      ε < ⟪(z wall₀).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ ∧
      ε < ⟪(z wall₁).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ := by
    intro q hq
    exact (N.adjacent_oneBitFiberPatchWalls_inward_on_seam κ cover ψ z t
      selected hselected i j horder k wall₀ wall₁ hwall₀ hwall₁ hq).2.2
  have hhead : ∀ q ∈ ψ '' seam,
      ε ≤ innerSL ℝ (z wall₀).1
        (toEuclid (N.massActionVectorField κ (toEuclid.symm q))) := by
    intro q hq
    simpa only [innerSL_apply_apply] using le_of_lt (hwall q hq).1
  have htail : ∀ Mb ∈ [(innerSL ℝ (z wall₁).1, (0 : ℝ))],
      ∀ q ∈ ψ '' seam,
        ε ≤ Mb.1 (toEuclid (N.massActionVectorField κ (toEuclid.symm q))) := by
    intro Mb hMb q hq
    have hMb' : Mb = (innerSL ℝ (z wall₁).1, (0 : ℝ)) := by simpa using hMb
    rw [hMb']
    simpa only [innerSL_apply_apply] using le_of_lt (hwall q hq).2
  refine ⟨hactive.1, hactive.2, hseamCompact, ?_⟩
  intro q hq
  obtain ⟨D, hD, hDmargin⟩ := SmoothBarrierGluing.smoothWallList_descends_strictly
    (X := fun q : EuclideanSpace ℝ S =>
      toEuclid (N.massActionVectorField κ (toEuclid.symm q)))
    (x := q) (ε := ε)
    (innerSL ℝ (z wall₀).1, (0 : ℝ)) [(innerSL ℝ (z wall₁).1, (0 : ℝ))]
    (hhead q hq) (fun Mb hMb => htail Mb hMb q hq)
  exact ⟨D, hD, lt_of_le_of_lt hDmargin (neg_neg_of_pos hε)⟩

/-- Craciun v3, §7.4.3: the two wall labels incident to a compact tile seam remain inward on an
open collar of that seam. Compactness promotes the strict seam inequalities to a single geometric
neighborhood radius; on the whole collar their smooth maximum still strictly decreases along the
toric field. This gives an actual overlap region for the neighboring tile barriers to glue across.
-/
theorem Network.exists_adjacent_oneBitFiberPatch_seam_barrier_collar
    {n : ℕ} {ι : Type*} [Fintype ι]
    (N : Network S) (κ : N.RateConstants)
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {baseTile : ι → Set (Fin n → ℝ)} {lower upper : (Fin n → ℝ) → ℝ}
    {epsilon : ℝ}
    (cover : CRNT.ZeroSeparatingInduction.CompactOneBitFiberPatchCover
      facePatch base baseTile lower upper epsilon)
    (ψ : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ S) (hψ : Continuous ψ)
    {K : Set (EuclideanSpace ℝ S)} (z : K → N.euclideanStoichSubspace)
    (t : Finset K) {ε : ℝ} (hε : 0 < ε)
    (selected : (Σ i : ι, Fin (cover.tiling.subdivisionCount + 1)) → Option K)
    (hselected : ∀ p wall, selected p = some wall → wall ∈ t ∧ ∀ q ∈
      ψ '' (facePatch ∩ CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionTile
        (baseTile p.1) lower upper p.2),
      ε < ⟪(z wall).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ)
    (i j : ι)
    (horder : ∀ y ∈ baseTile i ∩ baseTile j, lower y ≤ upper y)
    (k : Fin cover.tiling.subdivisionCount)
    (wall₀ wall₁ : K)
    (hwall₀ : selected ⟨i, k.castSucc⟩ = some wall₀)
    (hwall₁ : selected ⟨j, k.succ⟩ = some wall₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ Metric.thickening δ
        (ψ '' (facePatch ∩ (fun y : Fin n → ℝ =>
          CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
            lower upper k.succ.castSucc y) '' (baseTile i ∩ baseTile j))),
      (∃ D : EuclideanSpace ℝ S →L[ℝ] ℝ,
        HasFDerivAt
          (SmoothBarrierGluing.smoothWallList
            (innerSL ℝ (z wall₀).1, 0)
            [(innerSL ℝ (z wall₁).1, 0)]) D q ∧
        D (toEuclid (N.massActionVectorField κ (toEuclid.symm q))) < 0) ∧
      (ε / 2 < ⟪(z wall₀).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ ∧
       ε / 2 < ⟪(z wall₁).1,
        toEuclid (N.massActionVectorField κ (toEuclid.symm q))⟫_ℝ) := by
  let seam : Set (Fin (n + 1) → ℝ) := facePatch ∩
    (fun y : Fin n → ℝ =>
      CRNT.ZeroSeparatingInduction.projectionFiberSubdivisionEndpointGraphPoint
        lower upper k.succ.castSucc y) '' (baseTile i ∩ baseTile j)
  let seamImage : Set (EuclideanSpace ℝ S) := ψ '' seam
  let X : EuclideanSpace ℝ S → EuclideanSpace ℝ S := fun q =>
    toEuclid (N.massActionVectorField κ (toEuclid.symm q))
  let f₀ : EuclideanSpace ℝ S → ℝ := fun q => innerSL ℝ (z wall₀).1 (X q)
  let f₁ : EuclideanSpace ℝ S → ℝ := fun q => innerSL ℝ (z wall₁).1 (X q)
  have hsection : IsCompact seamImage := by
    exact (cover.adjacent_base_tiles_shared_seam_compact i j horder k).image hψ
  have hseamInward : ∀ q ∈ seamImage, ε < f₀ q ∧ ε < f₁ q := by
    intro q hq
    have h := N.adjacent_oneBitFiberPatchWalls_inward_on_seam κ cover ψ z t
      selected hselected i j horder k wall₀ wall₁ hwall₀ hwall₁ hq
    simpa [f₀, f₁, X, innerSL_apply_apply] using h.2.2
  have hX : Continuous X := by
    exact (LinearMap.continuous_of_finiteDimensional
      (toEuclid (ι := S)).toLinearMap).comp
        ((Network.continuous_massActionVectorField N κ).comp
          (LinearMap.continuous_of_finiteDimensional
            (toEuclid (ι := S)).symm.toLinearMap))
  have hf₀ : Continuous f₀ := by
    exact (innerSL ℝ (z wall₀).1).continuous.comp hX
  have hf₁ : Continuous f₁ := by
    exact (innerSL ℝ (z wall₁).1).continuous.comp hX
  let good : Set (EuclideanSpace ℝ S) :=
    {q | ε / 2 < f₀ q ∧ ε / 2 < f₁ q}
  have hgoodOpen : IsOpen good := by
    exact (isOpen_Ioi.preimage hf₀).inter (isOpen_Ioi.preimage hf₁)
  have hsectionGood : seamImage ⊆ good := by
    intro q hq
    have h := hseamInward q hq
    change ε / 2 < f₀ q ∧ ε / 2 < f₁ q
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  obtain ⟨δ, hδ, hcollar⟩ := hsection.exists_thickening_subset_open hgoodOpen hsectionGood
  refine ⟨δ, hδ, ?_⟩
  intro q hq
  have hgood : q ∈ good := hcollar hq
  change ε / 2 < f₀ q ∧ ε / 2 < f₁ q at hgood
  have hhead : ε / 2 ≤ innerSL ℝ (z wall₀).1 (X q) := le_of_lt hgood.1
  have htail : ∀ Mb ∈ [(innerSL ℝ (z wall₁).1, (0 : ℝ))],
      ε / 2 ≤ Mb.1 (X q) := by
    intro Mb hMb
    have hMb' : Mb = (innerSL ℝ (z wall₁).1, (0 : ℝ)) := by simpa using hMb
    rw [hMb']
    exact le_of_lt hgood.2
  obtain ⟨D, hD, hDmargin⟩ := SmoothBarrierGluing.smoothWallList_descends_strictly
    (X := X) (x := q) (ε := ε / 2)
    (innerSL ℝ (z wall₀).1, (0 : ℝ)) [(innerSL ℝ (z wall₁).1, (0 : ℝ))]
    hhead htail
  refine ⟨⟨D, ?_, ?_⟩, ?_⟩
  · simpa [X] using hD
  · simpa [X] using lt_of_le_of_lt hDmargin (neg_neg_of_pos (half_pos hε))
  · simpa [f₀, f₁, X, innerSL_apply_apply] using hgood

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

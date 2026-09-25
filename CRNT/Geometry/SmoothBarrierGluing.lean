import CRNT.Geometry.ZeroSeparatingSurface

/-!
# Smooth gluing of scalar barriers

A local zero-separating construction naturally produces several scalar barrier functions on
overlapping fan charts.  The log-sum-exp operation glues two such barriers smoothly.  Its derivative
is a positive weighted average of the two local derivatives; consequently every direction along
which both local barriers are nonincreasing is also a nonincreasing direction of the glued barrier.
This is the analytic seam lemma needed by a smooth alternative to ruled-patch gluing.
-/

namespace CRNT
namespace SmoothBarrierGluing
open scoped InnerProductSpace

/-- Binary smooth maximum (at unit temperature). -/
noncomputable def smoothMax (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.log (Real.exp (f t) + Real.exp (g t))

/-- Exact derivative of the binary smooth maximum. -/
theorem hasDerivAt_smoothMax {f g : ℝ → ℝ} {f' g' t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (smoothMax f g)
      ((Real.exp (f t) * f' + Real.exp (g t) * g') /
        (Real.exp (f t) + Real.exp (g t))) t := by
  have he1 := hf.exp
  have he2 := hg.exp
  have hsum := he1.add he2
  change HasDerivAt (fun u => Real.exp (f u) + Real.exp (g u))
      (Real.exp (f t) * f' + Real.exp (g t) * g') t at hsum
  have hne : Real.exp (f t) + Real.exp (g t) ≠ 0 := by
    positivity
  change HasDerivAt (fun u => Real.log (Real.exp (f u) + Real.exp (g u))) _ t
  exact hsum.log hne

/-- The derivative of a smooth maximum is nonpositive whenever both local derivatives are. -/
theorem smoothMax_deriv_nonpos {f g : ℝ → ℝ} {f' g' t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t)
    (hf' : f' ≤ 0) (hg' : g' ≤ 0) :
    (Real.exp (f t) * f' + Real.exp (g t) * g') /
        (Real.exp (f t) + Real.exp (g t)) ≤ 0 := by
  have hn1 : Real.exp (f t) * f' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hf'
  have hn2 : Real.exp (g t) * g' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hg'
  have hden : 0 < Real.exp (f t) + Real.exp (g t) := add_pos (Real.exp_pos _) (Real.exp_pos _)
  exact div_nonpos_of_nonpos_of_nonneg (add_nonpos hn1 hn2) hden.le

/-- Packaged seam rule: two differentiable local barriers that decrease along a trajectory glue to
one differentiable barrier that also decreases along that trajectory. -/
theorem exists_smoothMax_deriv_nonpos {f g : ℝ → ℝ} {f' g' t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t)
    (hf' : f' ≤ 0) (hg' : g' ≤ 0) :
    ∃ d : ℝ, HasDerivAt (smoothMax f g) d t ∧ d ≤ 0 := by
  refine ⟨(Real.exp (f t) * f' + Real.exp (g t) * g') /
      (Real.exp (f t) + Real.exp (g t)), hasDerivAt_smoothMax hf hg, ?_⟩
  exact smoothMax_deriv_nonpos hf hg hf' hg'

end SmoothBarrierGluing
end CRNT

namespace CRNT
namespace SmoothBarrierGluing
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Smooth maximum for scalar barriers on an arbitrary normed real vector space. -/
noncomputable def smoothMaxF (f g : E → ℝ) (x : E) : ℝ :=
  Real.log (Real.exp (f x) + Real.exp (g x))

/-- Fréchet derivative of the smooth maximum. -/
theorem hasFDerivAt_smoothMaxF {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ} {x : E}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (smoothMaxF f g)
      ((Real.exp (f x) + Real.exp (g x))⁻¹ •
        (Real.exp (f x) • f' + Real.exp (g x) • g')) x := by
  have he1 := hf.exp
  have he2 := hg.exp
  have hsum := he1.add he2
  have hne : Real.exp (f x) + Real.exp (g x) ≠ 0 := by positivity
  change HasFDerivAt (fun y => Real.log (Real.exp (f y) + Real.exp (g y))) _ x
  simpa [smul_add, smul_smul] using hsum.log hne

/-- Directional descent is preserved by smooth gluing in arbitrary dimension. -/
theorem smoothMaxF_fderiv_nonpos {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ} {x v : E}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x)
    (hf' : f' v ≤ 0) (hg' : g' v ≤ 0) :
    (((Real.exp (f x) + Real.exp (g x))⁻¹ •
        (Real.exp (f x) • f' + Real.exp (g x) • g')) v) ≤ 0 := by
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply]
  have hn1 : Real.exp (f x) * f' v ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hf'
  have hn2 : Real.exp (g x) * g' v ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hg'
  have hinv : 0 ≤ (Real.exp (f x) + Real.exp (g x))⁻¹ := by positivity
  exact mul_nonpos_of_nonneg_of_nonpos hinv (add_nonpos hn1 hn2)

/-- The exact seam lemma in the form required by `ZeroSeparatingSurfaceExists`: if both local
barriers descend along the vector field at a point, their smooth maximum descends there too. -/
theorem smoothMaxF_descends_along {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ}
    {X : E → E} {x : E}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x)
    (hfd : f' (X x) ≤ 0) (hgd : g' (X x) ≤ 0) :
    ∃ D : E →L[ℝ] ℝ, HasFDerivAt (smoothMaxF f g) D x ∧ D (X x) ≤ 0 := by
  let D : E →L[ℝ] ℝ := (Real.exp (f x) + Real.exp (g x))⁻¹ •
    (Real.exp (f x) • f' + Real.exp (g x) • g')
  exact ⟨D, hasFDerivAt_smoothMaxF hf hg,
    smoothMaxF_fderiv_nonpos hf hg hfd hgd⟩

end SmoothBarrierGluing
end CRNT

namespace CRNT
namespace SmoothBarrierGluing
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Scalar barrier attached to an oriented supporting wall functional. -/
noncomputable def wallBarrier (L : E →L[ℝ] ℝ) (a : ℝ) (x : E) : ℝ := a - L x

/-- The derivative field of a wall barrier is the negative wall functional. -/
noncomputable def wallBarrierDeriv (L : E →L[ℝ] ℝ) : E →L[ℝ] ℝ := -L

theorem hasFDerivAt_wallBarrier (L : E →L[ℝ] ℝ) (a : ℝ) (x : E) :
    HasFDerivAt (wallBarrier L a) (wallBarrierDeriv L) x := by
  change HasFDerivAt ((fun _ : E => a) - (fun y : E => L y)) _ x
  simpa [wallBarrierDeriv] using ((hasFDerivAt_const a x).sub L.hasFDerivAt)

theorem wallBarrierDeriv_nonpos {L : E →L[ℝ] ℝ} {v : E} (h : 0 ≤ L v) :
    wallBarrierDeriv L v ≤ 0 := by
  simpa [wallBarrierDeriv] using (neg_nonpos.mpr h)

/-- Fan-wall to local-barrier bridge, phrased for the continuous wall functional. -/
theorem wallBarrier_descends_along {X : E → E} {L : E →L[ℝ] ℝ} {a : ℝ} {x : E}
    (hin : 0 ≤ L (X x)) :
    HasFDerivAt (wallBarrier L a) (wallBarrierDeriv L) x ∧ wallBarrierDeriv L (X x) ≤ 0 :=
  ⟨hasFDerivAt_wallBarrier L a x, wallBarrierDeriv_nonpos hin⟩

/-- Two inward wall functionals glue smoothly while preserving descent. -/
theorem smoothWallPair_descends_along {X : E → E} {L₁ L₂ : E →L[ℝ] ℝ} {a₁ a₂ : ℝ} {x : E}
    (h₁ : 0 ≤ L₁ (X x)) (h₂ : 0 ≤ L₂ (X x)) :
    ∃ D : E →L[ℝ] ℝ,
      HasFDerivAt (smoothMaxF (wallBarrier L₁ a₁) (wallBarrier L₂ a₂)) D x ∧ D (X x) ≤ 0 := by
  exact smoothMaxF_descends_along
    (hasFDerivAt_wallBarrier L₁ a₁ x) (hasFDerivAt_wallBarrier L₂ a₂ x)
    (wallBarrierDeriv_nonpos h₁) (wallBarrierDeriv_nonpos h₂)

end SmoothBarrierGluing
end CRNT

namespace CRNT
namespace SmoothBarrierGluing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A uniform strict directional margin is preserved by binary smooth gluing. -/
theorem smoothMaxF_fderiv_le_neg {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ} {x v : E} {ε : ℝ}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x)
    (hf' : f' v ≤ -ε) (hg' : g' v ≤ -ε) :
    (((Real.exp (f x) + Real.exp (g x))⁻¹ •
        (Real.exp (f x) • f' + Real.exp (g x) • g')) v) ≤ -ε := by
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply]
  have hden : 0 < Real.exp (f x) + Real.exp (g x) := by positivity
  have hnum : Real.exp (f x) * f' v + Real.exp (g x) * g' v ≤
      (Real.exp (f x) + Real.exp (g x)) * (-ε) := by
    calc
      Real.exp (f x) * f' v + Real.exp (g x) * g' v
          ≤ Real.exp (f x) * (-ε) + Real.exp (g x) * (-ε) :=
            add_le_add (mul_le_mul_of_nonneg_left hf' (Real.exp_pos _).le)
              (mul_le_mul_of_nonneg_left hg' (Real.exp_pos _).le)
      _ = (Real.exp (f x) + Real.exp (g x)) * (-ε) := by ring
  change (Real.exp (f x) + Real.exp (g x))⁻¹ *
      (Real.exp (f x) * f' v + Real.exp (g x) * g' v) ≤ -ε
  rw [inv_mul_le_iff₀ hden]
  simpa [mul_comm] using hnum

/-- Nonempty finite smooth maximum, represented by a head and a tail list. -/
noncomputable def smoothMaxList (f : E → ℝ) : List (E → ℝ) → E → ℝ
  | [] => f
  | g :: gs => smoothMaxF f (smoothMaxList g gs)

/-- A finite smooth maximum has a derivative with the same uniform directional upper bound as all
of its constituent barriers.  This is the finite seam-gluing lemma needed for fan charts. -/
theorem exists_fderiv_smoothMaxList_le_neg
    {X : E → E} {x : E} {ε : ℝ}
    (f : E → ℝ) (fs : List (E → ℝ))
    (hf : ∃ D : E →L[ℝ] ℝ, HasFDerivAt f D x ∧ D (X x) ≤ -ε)
    (hfs : ∀ g ∈ fs, ∃ D : E →L[ℝ] ℝ, HasFDerivAt g D x ∧ D (X x) ≤ -ε) :
    ∃ D : E →L[ℝ] ℝ, HasFDerivAt (smoothMaxList f fs) D x ∧ D (X x) ≤ -ε := by
  induction fs generalizing f with
  | nil =>
      simpa [smoothMaxList] using hf
  | cons g gs ih =>
      obtain ⟨Df, hDf, hDfε⟩ := hf
      have hg := hfs g (by simp)
      have hgs : ∀ h ∈ gs, ∃ D : E →L[ℝ] ℝ, HasFDerivAt h D x ∧ D (X x) ≤ -ε := by
        intro h hh
        exact hfs h (by simp [hh])
      obtain ⟨Dg, hDg, hDgε⟩ := ih g hg hgs
      let D : E →L[ℝ] ℝ := (Real.exp (f x) + Real.exp (smoothMaxList g gs x))⁻¹ •
        (Real.exp (f x) • Df + Real.exp (smoothMaxList g gs x) • Dg)
      refine ⟨D, ?_, ?_⟩
      · simpa [smoothMaxList, D] using hasFDerivAt_smoothMaxF hDf hDg
      · exact smoothMaxF_fderiv_le_neg hDf hDg hDfε hDgε

end SmoothBarrierGluing
end CRNT

namespace CRNT
namespace SmoothBarrierGluing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Smoothly glue a nonempty finite list of oriented affine wall barriers. -/
noncomputable def smoothWallList (La : (E →L[ℝ] ℝ) × ℝ) :
    List ((E →L[ℝ] ℝ) × ℝ) → E → ℝ
  | [] => wallBarrier La.1 La.2
  | Mb :: rest => smoothMaxF (wallBarrier La.1 La.2) (smoothWallList Mb rest)

omit [CompleteSpace E] in
/-- **Finite offset selection at one point.** If the distinguished head wall is strictly below a
chosen level at `x`, offsets for any finite list of additional wall normals can be chosen so that
their nested smooth maximum remains strictly below that level at `x`. The offsets only control
the barrier values; they do not impose any sign condition on the wall derivatives. -/
theorem exists_smoothWallList_offsets_below_at
    (La : (E →L[ℝ] ℝ) × ℝ) (normals : List (E →L[ℝ] ℝ)) (x : E) {c : ℝ}
    (hhead : wallBarrier La.1 La.2 x < c) :
    ∃ walls : List ((E →L[ℝ] ℝ) × ℝ),
      walls.map Prod.fst = normals ∧ smoothWallList La walls x < c := by
  induction normals generalizing La c with
  | nil => exact ⟨[], rfl, by simpa [smoothWallList] using hhead⟩
  | cons M rest ih =>
      let f : E → ℝ := wallBarrier La.1 La.2
      have hgap : 0 < Real.exp c - Real.exp (f x) :=
        sub_pos.mpr (Real.exp_lt_exp.mpr hhead)
      let d : ℝ := Real.log ((Real.exp c - Real.exp (f x)) / 2)
      have hdarg : 0 < (Real.exp c - Real.exp (f x)) / 2 := half_pos hgap
      have hexpd : Real.exp d = (Real.exp c - Real.exp (f x)) / 2 := by
        dsimp [d]
        exact Real.exp_log hdarg
      have hbudget : Real.exp (f x) + Real.exp d < Real.exp c := by
        rw [hexpd]
        linarith
      let b : ℝ := M x + d - 1
      have hM : wallBarrier M b x < d := by
        dsimp [wallBarrier, b]
        linarith
      obtain ⟨tail, hmap, htail⟩ := ih (La := (M, b)) (c := d) hM
      have htailExp :
          Real.exp (smoothWallList (M, b) tail x) < Real.exp d :=
        Real.exp_lt_exp.mpr htail
      have hsum :
          Real.exp (f x) + Real.exp (smoothWallList (M, b) tail x) < Real.exp c := by
        calc
          Real.exp (f x) + Real.exp (smoothWallList (M, b) tail x) <
              Real.exp (f x) + Real.exp d := by
                simpa [add_comm] using add_lt_add_right htailExp (Real.exp (f x))
          _ < Real.exp c := hbudget
      refine ⟨(M, b) :: tail, ?_, ?_⟩
      · simp [hmap]
      · change smoothMaxF f (smoothWallList (M, b) tail) x < c
        unfold smoothMaxF
        rw [Real.log_lt_iff_lt_exp (by positivity)]
        exact hsum

/-- **Finite fan-wall gluing with a uniform strict margin.** If every oriented wall functional sees
at least `ε` of the vector field at `x`, their smooth affine barrier has directional derivative at
most `-ε`.  Thus finite seam gluing loses no strict inward margin. -/
theorem smoothWallList_descends_strictly
    {X : E → E} {x : E} {ε : ℝ}
    (La : (E →L[ℝ] ℝ) × ℝ) (walls : List ((E →L[ℝ] ℝ) × ℝ))
    (hhead : ε ≤ La.1 (X x))
    (hwalls : ∀ Mb ∈ walls, ε ≤ Mb.1 (X x)) :
    ∃ D : E →L[ℝ] ℝ,
      HasFDerivAt (smoothWallList La walls) D x ∧ D (X x) ≤ -ε := by
  induction walls generalizing La with
  | nil =>
      refine ⟨wallBarrierDeriv La.1, ?_, ?_⟩
      · simpa [smoothWallList] using hasFDerivAt_wallBarrier La.1 La.2 x
      · simp only [wallBarrierDeriv, ContinuousLinearMap.neg_apply]
        exact neg_le_neg hhead
  | cons Mb rest ih =>
      obtain ⟨Drest, hDrest, hrestε⟩ := ih Mb (hwalls Mb (by simp)) (by
        intro Q hQ
        exact hwalls Q (by simp [hQ]))
      have hheadD : wallBarrierDeriv La.1 (X x) ≤ -ε := by
        simp only [wallBarrierDeriv, ContinuousLinearMap.neg_apply]
        exact neg_le_neg hhead
      let D : E →L[ℝ] ℝ :=
        (Real.exp (wallBarrier La.1 La.2 x) + Real.exp (smoothWallList Mb rest x))⁻¹ •
          (Real.exp (wallBarrier La.1 La.2 x) • wallBarrierDeriv La.1 +
            Real.exp (smoothWallList Mb rest x) • Drest)
      refine ⟨D, ?_, ?_⟩
      · simpa [smoothWallList, D] using
          hasFDerivAt_smoothMaxF (hasFDerivAt_wallBarrier La.1 La.2 x) hDrest
      · exact smoothMaxF_fderiv_le_neg
          (hasFDerivAt_wallBarrier La.1 La.2 x) hDrest hheadD hrestε

end SmoothBarrierGluing
end CRNT

namespace CRNT
namespace SmoothBarrierGluing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Dominant-chart seam lemma.** A strictly descending local barrier may be smoothly glued to a
second barrier whose derivative is not known to descend, provided the latter's exponentially
weighted possible outward derivative is dominated by the former's strict inward margin.  This is
the useful form for fan charts: globally imposing every wall inequality is unnecessary. -/
theorem smoothMaxF_fderiv_nonpos_of_weighted_dominance
    {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ} {x v : E} {ε M : ℝ}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x)
    (hε : 0 ≤ ε) (hf' : f' v ≤ -ε) (hg' : g' v ≤ M)
    (hdom : Real.exp (g x) * M ≤ Real.exp (f x) * ε) :
    (((Real.exp (f x) + Real.exp (g x))⁻¹ •
        (Real.exp (f x) • f' + Real.exp (g x) • g')) v) ≤ 0 := by
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply]
  change (Real.exp (f x) + Real.exp (g x))⁻¹ *
      (Real.exp (f x) * f' v + Real.exp (g x) * g' v) ≤ 0
  have h1 : Real.exp (f x) * f' v ≤ Real.exp (f x) * (-ε) :=
    mul_le_mul_of_nonneg_left hf' (Real.exp_pos _).le
  have h2 : Real.exp (g x) * g' v ≤ Real.exp (g x) * M :=
    mul_le_mul_of_nonneg_left hg' (Real.exp_pos _).le
  have hnum : Real.exp (f x) * f' v + Real.exp (g x) * g' v ≤ 0 := by
    calc
      Real.exp (f x) * f' v + Real.exp (g x) * g' v
          ≤ Real.exp (f x) * (-ε) + Real.exp (g x) * M := add_le_add h1 h2
      _ ≤ Real.exp (f x) * (-ε) + Real.exp (f x) * ε := add_le_add_right hdom _
      _ = 0 := by ring
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hnum

end SmoothBarrierGluing
end CRNT

namespace CRNT
namespace SmoothBarrierGluing

/-- A value gap converts an ordinary bound on a competing chart's outward derivative into the
exponential weighted-dominance inequality used by smooth gluing. -/
theorem exp_weighted_dominance_of_gap {a b K M ε : ℝ}
    (hε : 0 ≤ ε) (hM : M ≤ Real.exp K * ε) (hgap : b + K ≤ a) :
    Real.exp b * M ≤ Real.exp a * ε := by
  calc
    Real.exp b * M ≤ Real.exp b * (Real.exp K * ε) :=
      mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le
    _ = Real.exp (b + K) * ε := by rw [Real.exp_add]; ring
    _ ≤ Real.exp a * ε :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hgap) hε

end SmoothBarrierGluing
end CRNT

namespace CRNT
namespace SmoothBarrierGluing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Each input lies below its binary log-sum-exp smooth maximum. -/
theorem le_smoothMaxF_left (f g : E → ℝ) (x : E) : f x ≤ smoothMaxF f g x := by
  unfold smoothMaxF
  rw [Real.le_log_iff_exp_le (by positivity)]
  exact le_add_of_nonneg_right (Real.exp_pos _).le

theorem le_smoothMaxF_right (f g : E → ℝ) (x : E) : g x ≤ smoothMaxF f g x := by
  unfold smoothMaxF
  rw [Real.le_log_iff_exp_le (by positivity)]
  exact le_add_of_nonneg_left (Real.exp_pos _).le

/-- The distinguished head wall remains below the finite smooth wall barrier. -/
theorem wallBarrier_le_smoothWallList
    (La : (E →L[ℝ] ℝ) × ℝ) (walls : List ((E →L[ℝ] ℝ) × ℝ)) (x : E) :
    wallBarrier La.1 La.2 x ≤ smoothWallList La walls x := by
  cases walls with
  | nil => simp [smoothWallList]
  | cons Mb rest =>
      simp only [smoothWallList]
      exact le_smoothMaxF_left _ _ _

/-- **Separation survives finite smooth gluing.** If one wall functional has operator norm at most
one and its affine offset sits at least `r` above the chosen sublevel, then the entire smooth-wall
sublevel misses the open `r`-ball.  Thus adding arbitrarily many smoothly glued fan charts cannot
destroy a separation margin already supplied by one distinguished wall. -/
theorem smoothWallList_sublevel_separated
    {L : E →L[ℝ] ℝ} {a c r : ℝ} (hL : ‖L‖ ≤ 1) (_hr : 0 < r)
    (hac : c + r ≤ a) (walls : List ((E →L[ℝ] ℝ) × ℝ)) :
    {x : E | smoothWallList (L, a) walls x ≤ c} ⊆ (Metric.ball (0 : E) r)ᶜ := by
  intro x hx
  rw [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt]
  have hwb : wallBarrier L a x ≤ c :=
    le_trans (wallBarrier_le_smoothWallList (L, a) walls x) hx
  have hLx : r ≤ L x := by
    dsimp [wallBarrier] at hwb
    linarith
  have hnorm : L x ≤ ‖x‖ := by
    calc
      L x ≤ |L x| := le_abs_self _
      _ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg x)
      _ = ‖x‖ := one_mul _
  exact le_trans hLx hnorm

/-- **Finite offsets with start inclusion and origin separation.** A distinguished head normal that
strictly supports the start beyond radius `r` fixes its offset at `c + r`; all tail offsets can then
be lowered until the smooth-wall value at the start is below `c`. The same head wall separates the
resulting sublevel from the open `r`-ball. -/
theorem exists_start_separating_smoothWallList_offsets
    (L : E →L[ℝ] ℝ) (normals : List (E →L[ℝ] ℝ)) (x₀ : E)
    {c r : ℝ} (hL : ‖L‖ ≤ 1) (hr : 0 < r) (hrx : r < L x₀) :
    ∃ walls : List ((E →L[ℝ] ℝ) × ℝ),
      walls.map Prod.fst = normals ∧
        smoothWallList (L, c + r) walls x₀ < c ∧
        {x | smoothWallList (L, c + r) walls x ≤ c} ⊆ (Metric.ball 0 r)ᶜ := by
  have hhead : wallBarrier L (c + r) x₀ < c := by
    simp [wallBarrier]
    linarith
  obtain ⟨walls, hmap, hstart⟩ :=
    exists_smoothWallList_offsets_below_at (L, c + r) normals x₀ hhead
  exact ⟨walls, hmap, hstart,
    smoothWallList_sublevel_separated hL hr le_rfl walls⟩

end SmoothBarrierGluing
end CRNT

namespace CRNT
namespace SmoothBarrierGluing
open DifferentialInclusion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A finite smooth wall barrier is already a genuine zero-separating surface whenever its wall
functionals share a global inward margin, the start is in the chosen sublevel, and one distinguished
wall supplies a metric separation margin.  This closes the analytic wiring from finite smooth fan
barriers to the repository's Nagumo/zero-separating interface. -/
theorem zeroSeparatingSurfaceExists_smoothWallList
    {X : E → E} {x₀ : E} {ε c r : ℝ}
    (La : (E →L[ℝ] ℝ) × ℝ) (walls : List ((E →L[ℝ] ℝ) × ℝ))
    (hε : 0 ≤ ε)
    (hhead : ∀ y, ε ≤ La.1 (X y))
    (hwalls : ∀ Mb ∈ walls, ∀ y, ε ≤ Mb.1 (X y))
    (hstart : smoothWallList La walls x₀ ≤ c)
    (hL : ‖La.1‖ ≤ 1) (hr : 0 < r) (hac : c + r ≤ La.2) :
    ZeroSeparatingSurfaceExists X x₀ := by
  let g : E → ℝ := smoothWallList La walls
  have hD : ∀ y : E, ∃ D : E →L[ℝ] ℝ, HasFDerivAt g D y ∧ D (X y) ≤ -ε := by
    intro y
    exact smoothWallList_descends_strictly La walls (hhead y) (by
      intro Mb hMb
      exact hwalls Mb hMb y)
  let gp : E → (E →L[ℝ] ℝ) := fun y => Classical.choose (hD y)
  have hgp : ∀ y, HasFDerivAt g (gp y) y ∧ gp y (X y) ≤ -ε := by
    intro y
    exact Classical.choose_spec (hD y)
  have hcont : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro y
    exact (hgp y).1.continuousAt
  refine ⟨⟨g, gp, c, 1, r, hcont, (fun y => (hgp y).1), by norm_num, ?_, hstart, hr, ?_⟩⟩
  · intro y _ _
    exact le_trans (hgp y).2 (neg_nonpos.mpr hε)
  · exact smoothWallList_sublevel_separated hL hr hac walls

end SmoothBarrierGluing
end CRNT

namespace CRNT
namespace SmoothBarrierGluing
open DifferentialInclusion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The finite smooth wall barrier is Fréchet differentiable everywhere, independently of any
inwardness assumptions. -/
theorem exists_fderiv_smoothWallList
    (La : (E →L[ℝ] ℝ) × ℝ) (walls : List ((E →L[ℝ] ℝ) × ℝ)) (x : E) :
    ∃ D : E →L[ℝ] ℝ, HasFDerivAt (smoothWallList La walls) D x := by
  induction walls generalizing La with
  | nil =>
      exact ⟨wallBarrierDeriv La.1, by
        simpa [smoothWallList] using hasFDerivAt_wallBarrier La.1 La.2 x⟩
  | cons Mb rest ih =>
      obtain ⟨Dr, hDr⟩ := ih Mb
      let D : E →L[ℝ] ℝ :=
        (Real.exp (wallBarrier La.1 La.2 x) + Real.exp (smoothWallList Mb rest x))⁻¹ •
          (Real.exp (wallBarrier La.1 La.2 x) • wallBarrierDeriv La.1 +
            Real.exp (smoothWallList Mb rest x) • Dr)
      exact ⟨D, by
        simpa [smoothWallList, D] using
          hasFDerivAt_smoothMaxF (hasFDerivAt_wallBarrier La.1 La.2 x) hDr⟩

/-- **Band-local finite-wall zero-separating theorem.** Global fan inequalities are unnecessary:
it is enough that all constituent walls are inward on the narrow level-set band where Nagumo needs
the derivative sign.  This is the direct finite smooth-wall implementation of the repository's
`ZeroSeparatingSurfaceExists` interface. -/
theorem zeroSeparatingSurfaceExists_smoothWallList_of_band
    {X : E → E} {x₀ : E} {c δ r : ℝ}
    (La : (E →L[ℝ] ℝ) × ℝ) (walls : List ((E →L[ℝ] ℝ) × ℝ))
    (hδ : 0 < δ)
    (hhead : ∀ y, c - δ ≤ smoothWallList La walls y →
      smoothWallList La walls y ≤ c + δ → 0 ≤ La.1 (X y))
    (hwalls : ∀ Mb ∈ walls, ∀ y, c - δ ≤ smoothWallList La walls y →
      smoothWallList La walls y ≤ c + δ → 0 ≤ Mb.1 (X y))
    (hstart : smoothWallList La walls x₀ ≤ c)
    (hL : ‖La.1‖ ≤ 1) (hr : 0 < r) (hac : c + r ≤ La.2) :
    ZeroSeparatingSurfaceExists X x₀ := by
  let g : E → ℝ := smoothWallList La walls
  have hD : ∀ y : E, ∃ D : E →L[ℝ] ℝ, HasFDerivAt g D y := by
    intro y
    exact exists_fderiv_smoothWallList La walls y
  let gp : E → (E →L[ℝ] ℝ) := fun y => Classical.choose (hD y)
  have hgp : ∀ y, HasFDerivAt g (gp y) y := fun y => Classical.choose_spec (hD y)
  have hcont : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro y
    exact (hgp y).continuousAt
  refine ⟨⟨g, gp, c, δ, r, hcont, hgp, hδ, ?_, hstart, hr, ?_⟩⟩
  · intro y hlo hhi
    have hs := smoothWallList_descends_strictly La walls (ε := 0)
      (hhead y hlo hhi) (by
        intro Mb hMb
        exact hwalls Mb hMb y hlo hhi)
    obtain ⟨D, hDy, hnonpos⟩ := hs
    have heq : gp y = D := (hgp y).unique hDy
    simpa [heq] using hnonpos
  · exact smoothWallList_sublevel_separated hL hr hac walls

end SmoothBarrierGluing
end CRNT

namespace CRNT
namespace SmoothBarrierGluing
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A strict positive continuous scalar inequality persists on a neighbourhood with a quantitative
half-margin.  This is the local compact-cover input for the fan barrier construction. -/
theorem exists_nhds_half_margin_of_continuousAt_pos
    {f : E → ℝ} {x : E} (hf : ContinuousAt f x) (hx : 0 < f x) :
    ∃ U ∈ 𝓝 x, ∀ y ∈ U, f x / 2 < f y := by
  have hhalf : f x / 2 < f x := by linarith
  have hev : ∀ᶠ y in 𝓝 x, f x / 2 < f y :=
    continuousAt_const.eventually_lt hf hhalf
  exact ⟨{y | f x / 2 < f y}, hev, fun y hy => hy⟩

/-- Applying a fixed continuous linear functional to a continuous vector field is continuous. -/
theorem continuousAt_apply_clm_field (L : E →L[ℝ] ℝ) {X : E → E} {x : E}
    (hX : ContinuousAt X x) : ContinuousAt (fun y => L (X y)) x := by
  exact L.continuous.continuousAt.comp hX

/-- Strict inwardness across one wall persists on a neighbourhood with an explicit half-margin. -/
theorem exists_nhds_wall_margin (L : E →L[ℝ] ℝ) {X : E → E} {x : E}
    (hX : ContinuousAt X x) (hx : 0 < L (X x)) :
    ∃ U ∈ 𝓝 x, ∀ y ∈ U, L (X x) / 2 < L (X y) := by
  exact exists_nhds_half_margin_of_continuousAt_pos (continuousAt_apply_clm_field L hX) hx

end SmoothBarrierGluing
end CRNT

namespace CRNT
namespace SmoothBarrierGluing

variable {E : Type*} [TopologicalSpace E]

/-- A positive continuous scalar field on a nonempty compact set has a uniform positive lower
margin.  This packages the compactness step needed after local strict fan-wall support has been
established. -/
theorem exists_uniform_pos_margin_on_compact {K : Set E} {f : E → ℝ}
    (hK : IsCompact K) (hne : K.Nonempty) (hf : ContinuousOn f K)
    (hpos : ∀ x ∈ K, 0 < f x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ε ≤ f x := by
  obtain ⟨x, hxK, hxMin⟩ := hK.exists_isMinOn hne hf
  refine ⟨f x, hpos x hxK, ?_⟩
  intro y hyK
  exact hxMin hyK

end SmoothBarrierGluing
end CRNT

namespace CRNT
namespace SmoothBarrierGluing

variable {E : Type*} [TopologicalSpace E]

/-- A compact set covered by point-indexed open neighbourhoods admits finitely many chart centres
from the compact set itself.  This is the finite-chart extraction used by the fan barrier argument. -/
theorem exists_finite_chart_centers {K : Set E} (hK : IsCompact K)
    (U : E → Set E) (hopen : ∀ x ∈ K, IsOpen (U x))
    (hmem : ∀ x ∈ K, x ∈ U x) :
    ∃ t : Finset K, K ⊆ ⋃ x ∈ t, U x.1 := by
  let V : K → Set E := fun x => U x.1
  have hVo : ∀ x : K, IsOpen (V x) := fun x => hopen x.1 x.2
  have hcover : K ⊆ ⋃ x : K, V x := by
    intro y hy
    exact Set.mem_iUnion.2 ⟨⟨y, hy⟩, hmem y hy⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover V hVo hcover
  exact ⟨t, ht⟩

end SmoothBarrierGluing
end CRNT

import CRNT.Graph.CirculationDecomposition
import CRNT.Equilibria.ComplexBalanceLinearStability
import CRNT.Theorems.DeficiencyZero.Toric
import CRNT.Dynamics.ToricEmbeddingOrder

namespace CRNT.Network
open scoped BigOperators InnerProductSpace
variable {S : Type} [DecidableEq S] [Fintype S]

/-- For a concrete closed reaction walk, the exponential source weights give a nonpositive
projected velocity in the same direction used in the exponent. This is the finite entropy
dissipation inequality for each cycle in a complex-balance decomposition. -/
theorem closedWalk_expProjectedVelocity_nonpos
    (N : Network S) {v : N.R → ℝ} {rs : List N.R} {c : N.ComplexIdx}
    (hp : N.IsPositiveFluxPath v rs c c) (z : S → ℝ) (q : ℝ) (hq : 0 ≤ q) :
    (∑ i : Fin rs.length,
      (q * Real.exp (⟪toEuclid z,
        toEuclid (CRNT.exponentVector (N.sourceIdx (rs.get i)).val)⟫_ℝ)) *
        ⟪toEuclid z,
          toEuclid (CRNT.exponentVector (N.targetIdx (rs.get i)).val) -
            toEuclid (CRNT.exponentVector (N.sourceIdx (rs.get i)).val)⟫_ℝ) ≤ 0 := by
  let source := rs.map N.sourceIdx
  let target := rs.map N.targetIdx
  let f : N.ComplexIdx → EuclideanSpace ℝ S :=
    fun c => toEuclid (CRNT.exponentVector c.val)
  have hperm : List.Perm target source := by
    exact IsPositiveFluxPath.targetList_perm_sourceList N hp
  have hcycle := CRNT.cyclicProjectedVelocity_nonpos_of_permutedList
    target source hperm f (toEuclid z) q hq
  have hsourceLen : source.length = rs.length := by simp [source]
  let e : Fin rs.length ≃ Fin source.length := finCongr hsourceLen.symm
  have hsum :
      (∑ i : Fin rs.length,
        (q * Real.exp (⟪toEuclid z, f (N.sourceIdx (rs.get i))⟫_ℝ)) *
          ⟪toEuclid z, f (N.targetIdx (rs.get i)) - f (N.sourceIdx (rs.get i))⟫_ℝ) =
      ∑ i : Fin source.length,
        (q * Real.exp (⟪toEuclid z, f (source.get i)⟫_ℝ)) *
          ⟪toEuclid z, f (target.get (finCongr hperm.length_eq.symm i)) -
            f (source.get i)⟫_ℝ := by
    apply Fintype.sum_equiv e
    intro i
    have hi : finCongr hperm.length_eq.symm (e i) =
        finCongr (by simp [target]) (i) := by
      apply Fin.ext
      simp [e, hsourceLen, target]
    simp [source, target, f, e, hi]
  rw [hsum]
  exact hcycle

/-- The same closed-walk sign bound in reaction-list coordinates. The reaction vector is the
target exponent minus the source exponent, so this is the projected entropy-dissipation term
that appears after expanding the full mass-action field. -/
theorem closedWalk_reactionListEntropy_nonpos
    (N : Network S) {v : N.R → ℝ} {rs : List N.R} {c : N.ComplexIdx}
    (hp : N.IsPositiveFluxPath v rs c c) (z : S → ℝ) (q : ℝ) (hq : 0 ≤ q) :
    q * (rs.map (fun r =>
      Real.exp (∑ s, ((N.sourceIdx r).val s : ℝ) * z s) *
        (∑ s, z s * N.reactionVector r s))).sum ≤ 0 := by
  let f : N.ComplexIdx → EuclideanSpace ℝ S :=
    fun c => toEuclid (CRNT.exponentVector c.val)
  let g : N.R → ℝ := fun r =>
    Real.exp (∑ s, ((N.sourceIdx r).val s : ℝ) * z s) *
      (∑ s, z s * N.reactionVector r s)
  have hsource (r : N.R) :
      ⟪toEuclid z, f (N.sourceIdx r)⟫_ℝ =
        ∑ s, ((N.sourceIdx r).val s : ℝ) * z s := by
    change ⟪toEuclid z,
      toEuclid (CRNT.exponentVector (N.sourceIdx r).val)⟫_ℝ = _
    rw [inner_toEuclid]
    apply Finset.sum_congr rfl
    intro s _
    simp [CRNT.exponentVector, mul_comm]
  have hvector (r : N.R) :
      f (N.targetIdx r) - f (N.sourceIdx r) = toEuclid (N.reactionVector r) := by
    ext s
    simp [f, CRNT.exponentVector, Network.sourceIdx, Network.targetIdx]
  have hinc (r : N.R) :
      ⟪toEuclid z, f (N.targetIdx r) - f (N.sourceIdx r)⟫_ℝ =
        ∑ s, z s * N.reactionVector r s := by
    rw [hvector, inner_toEuclid]
  have hcycle := N.closedWalk_expProjectedVelocity_nonpos hp z q hq
  have hsum :
      (∑ i : Fin rs.length,
        (q * Real.exp (⟪toEuclid z,
          f (N.sourceIdx (rs.get i))⟫_ℝ)) *
          ⟪toEuclid z,
            f (N.targetIdx (rs.get i)) - f (N.sourceIdx (rs.get i))⟫_ℝ) =
      q * (rs.map g).sum := by
    calc
      _ = ∑ i : Fin rs.length, q * g (rs.get i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hsource, hinc]
        ring
      _ = q * (rs.map g).sum := by
        rw [← Finset.mul_sum]
        rw [← List.sum_ofFn]
        have hlist :
            List.ofFn (fun i : Fin rs.length => g (rs.get i)) = rs.map g := by
          simpa only [List.get_eq_getElem] using (List.ofFn_getElem_eq_map rs g)
        exact congrArg (fun L : List ℝ => q * L.sum) hlist
  rw [hsum] at hcycle
  exact hcycle


theorem equilibriumReactionFlux_isPositiveGraphCirculation
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) :
    N.IsPositiveGraphCirculation (N.equilibriumReactionFlux κ xstar) := by
  constructor
  · intro r
    exact N.massActionRate_pos κ r hxs
  · have hk := (N.isComplexBalanced_iff_kineticMap κ xstar).1 hcb
    have heq := N.kineticMap_eq_incidenceMap κ (N.complexMonomialVector xstar)
    rw [hk] at heq
    have hfun : N.equilibriumReactionFlux κ xstar =
        (fun r => κ.k r * N.complexMonomialVector xstar (N.sourceIdx r)) := by
      funext r
      exact N.massActionRate_eq κ r xstar
    rw [hfun]
    exact heq.symm

theorem equilibriumReactionFlux_decomposes_into_cycles
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) :
    ∃ (m : ℕ) (c : Fin m → (N.R → ℝ)) (a : Fin m → ℝ),
      (∀ i, N.IsDirectedCycleFlow (c i)) ∧
      (∀ i, 0 ≤ a i) ∧
      N.equilibriumReactionFlux κ xstar = ∑ i, a i • c i := by
  have hp := N.equilibriumReactionFlux_isPositiveGraphCirculation κ hxs hcb
  exact N.graphCirculation_decomposes_into_cycles ⟨fun r => (hp.1 r).le, hp.2⟩

/-- A positive complex-balanced equilibrium flux decomposes into a finite family of concrete
closed reaction walks with nonnegative weights. This retains the edge order and multiplicities
needed by the toric projected-velocity estimate. -/
theorem equilibriumReactionFlux_decomposes_into_closedWalks
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) :
    ∃ (m : ℕ) (rs : Fin m → List N.R) (a : Fin m → ℝ),
      (∀ i, 0 ≤ a i) ∧
      (∀ i, ∃ c : N.R → ℝ, ∃ b : N.ComplexIdx,
        N.IsDirectedCycleFlow c ∧ N.IsPositiveFluxPath c (rs i) b b) ∧
      N.equilibriumReactionFlux κ xstar =
        ∑ i, a i • reactionListFlux N (rs i) := by
  have hp := N.equilibriumReactionFlux_isPositiveGraphCirculation κ hxs hcb
  exact N.graphCirculation_decomposes_into_closedWalkFluxes
    ⟨fun r => (hp.1 r).le, hp.2⟩

theorem massActionRate_eq_equilibriumFlux_mul_exp_logRatio
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (r : N.R) :
    N.massActionRate κ r x = N.equilibriumReactionFlux κ xstar r *
      Real.exp (∑ s, ((N.sourceIdx r).val s : ℝ) *
        (Real.log (x s) - Real.log (xstar s))) := by
  rw [N.massActionRate_eq κ r x]
  simp only [equilibriumReactionFlux]
  rw [N.massActionRate_eq κ r xstar]
  rw [N.complexMonomialVector_eq_mul_exp hx hxs (N.sourceIdx r)]
  ring


theorem massActionVectorField_eq_equilibriumFlux_exp_sum
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) :
    N.massActionVectorField κ x =
      ∑ r : N.R, (N.equilibriumReactionFlux κ xstar r *
        Real.exp (∑ s, ((N.sourceIdx r).val s : ℝ) *
          (Real.log (x s) - Real.log (xstar s)))) • N.reactionVector r := by
  funext s
  simp only [massActionVectorField_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro r _
  rw [N.massActionRate_eq_equilibriumFlux_mul_exp_logRatio κ hx hxs r]


theorem massActionVectorField_eq_cycleFlow_exp_sum
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive)
    {m : ℕ} {c : Fin m → (N.R → ℝ)} {a : Fin m → ℝ}
    (hdecomp : N.equilibriumReactionFlux κ xstar = ∑ i, a i • c i) :
    N.massActionVectorField κ x =
      ∑ i : Fin m, a i •
        (∑ r : N.R, (c i r *
          Real.exp (∑ s, ((N.sourceIdx r).val s : ℝ) *
            (Real.log (x s) - Real.log (xstar s)))) • N.reactionVector r) := by
  rw [N.massActionVectorField_eq_equilibriumFlux_exp_sum κ hx hxs]
  funext s
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  have hr := congrFun hdecomp r
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hr
  rw [hr, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- For a positive complex-balanced reference, every coordinate of the mass-action vector field
is a nonnegative weighted sum over the concrete closed walks in one fixed decomposition of the
equilibrium flux. Each list entry contributes its source monomial and reaction increment, with
repeated reactions retained according to their multiplicity. -/
theorem massActionVectorField_coord_eq_closedWalk_exp_sum
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) :
    ∃ (m : ℕ) (rs : Fin m → List N.R) (a : Fin m → ℝ),
      (∀ i, 0 ≤ a i) ∧
      (∀ i, ∃ c : N.R → ℝ, ∃ b : N.ComplexIdx,
        N.IsDirectedCycleFlow c ∧ N.IsPositiveFluxPath c (rs i) b b) ∧
      ∀ s, N.massActionVectorField κ x s =
        ∑ i, a i * ((rs i).map (fun r =>
          Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) *
            (Real.log (x t) - Real.log (xstar t))) * N.reactionVector r s)).sum := by
  obtain ⟨m, rs, a, ha, hwalks, hdecomp⟩ :=
    N.equilibriumReactionFlux_decomposes_into_closedWalks κ hxs hcb
  have hfield := N.massActionVectorField_eq_equilibriumFlux_exp_sum κ hx hxs
  refine ⟨m, rs, a, ha, hwalks, ?_⟩
  intro s
  have hweight := N.weighted_sum_eq_closedWalkSums_of_decomposition rs a hdecomp
    (fun r => Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) *
      (Real.log (x t) - Real.log (xstar t))) * N.reactionVector r s)
  have hcoord := congrFun hfield s
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hcoord
  calc
    N.massActionVectorField κ x s =
        ∑ r, (N.equilibriumReactionFlux κ xstar r *
          Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) *
            (Real.log (x t) - Real.log (xstar t)))) * N.reactionVector r s := hcoord
    _ = ∑ r, N.equilibriumReactionFlux κ xstar r *
          (Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) *
            (Real.log (x t) - Real.log (xstar t))) * N.reactionVector r s) := by
          apply Finset.sum_congr rfl
          intro r _
          ring
    _ = ∑ i, a i * ((rs i).map (fun r =>
          Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) *
            (Real.log (x t) - Real.log (xstar t))) * N.reactionVector r s)).sum := hweight

/-- Reproves the complex-balanced relative-entropy dissipation inequality by first decomposing
the positive equilibrium reaction flux into closed walks, then applying the projected sign bound
to each walk separately. -/
theorem dissipation_nonpos_via_closedWalkDecomposition
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) :
    (∑ s, (Real.log (x s) - Real.log (xstar s)) *
      N.massActionVectorField κ x s) ≤ 0 := by
  let z : S → ℝ := fun s => Real.log (x s) - Real.log (xstar s)
  let f : N.R → ℝ := fun r =>
    Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) * z t) *
      (∑ s, z s * N.reactionVector r s)
  have hflux : N.IsPositiveGraphCirculation (N.equilibriumReactionFlux κ xstar) := by
    constructor
    · intro r
      exact N.massActionRate_pos κ r hxs
    · have hk := (N.isComplexBalanced_iff_kineticMap κ xstar).1 hcb
      have heq := N.kineticMap_eq_incidenceMap κ (N.complexMonomialVector xstar)
      rw [hk] at heq
      have hfun : N.equilibriumReactionFlux κ xstar =
          (fun r => κ.k r * N.complexMonomialVector xstar (N.sourceIdx r)) := by
        funext r
        exact N.massActionRate_eq κ r xstar
      rw [hfun]
      exact heq.symm
  obtain ⟨m, rs, a, ha, hwalks, hdecomp⟩ :=
    N.graphCirculation_decomposes_into_closedWalkFluxes
      ⟨fun r => (hflux.1 r).le, hflux.2⟩
  have hcoord (s : S) :
      N.massActionVectorField κ x s =
        ∑ r, (N.equilibriumReactionFlux κ xstar r *
          Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) * z t)) *
          N.reactionVector r s := by
    have hfield := congrFun (N.massActionVectorField_eq_equilibriumFlux_exp_sum κ hx hxs) s
    simpa [z, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hfield
  have hpair :
      (∑ s, z s * N.massActionVectorField κ x s) =
        ∑ r, N.equilibriumReactionFlux κ xstar r * f r := by
    calc
      (∑ s, z s * N.massActionVectorField κ x s) =
          ∑ s, z s * ∑ r,
            (N.equilibriumReactionFlux κ xstar r *
              Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) * z t)) *
              N.reactionVector r s := by
                apply Finset.sum_congr rfl
                intro s _
                rw [hcoord s]
      _ = ∑ s, ∑ r,
            z s * ((N.equilibriumReactionFlux κ xstar r *
              Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) * z t)) *
              N.reactionVector r s) := by
                apply Finset.sum_congr rfl
                intro s _
                rw [Finset.mul_sum]
      _ = ∑ r, ∑ s,
            (N.equilibriumReactionFlux κ xstar r *
              Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) * z t)) *
              (z s * N.reactionVector r s) := by
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro r _
                apply Finset.sum_congr rfl
                intro s _
                ring
      _ = ∑ r, (N.equilibriumReactionFlux κ xstar r *
            Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) * z t)) *
            (∑ s, z s * N.reactionVector r s) := by
                apply Finset.sum_congr rfl
                intro r _
                rw [Finset.mul_sum]
      _ = ∑ r, N.equilibriumReactionFlux κ xstar r * f r := by
                apply Finset.sum_congr rfl
                intro r _
                simp only [f]
                ring
  have hweighted := N.weighted_sum_eq_closedWalkSums_of_decomposition
    rs a hdecomp f
  rw [hpair, hweighted]
  apply Finset.sum_nonpos
  intro i _
  obtain ⟨cycleFlow, base, hcycleFlow, hp⟩ := hwalks i
  exact N.closedWalk_reactionListEntropy_nonpos hp z (a i) (ha i)

/-- **Projected closed-walk estimate with perturbed monomial weights.** For a positive closed
reaction walk, let `p i` be the source-complex projection in a reference direction, and let `k i`
be a positive prefactor accounting for fixed equilibrium-rate factors. If the prefactors are
uniformly bounded, the reference gaps dominate their ratio, and every strict ordering in the test
direction agrees with the reference ordering, then the rate-weighted reaction vectors have
nonpositive projection. This is the closed-walk estimate used away from toric uncertainty walls. -/
theorem closedWalk_reactionList_projected_nonpos_of_rateSeparation
    (N : Network S) {v : N.R → ℝ} {rs : List N.R} {c : N.ComplexIdx}
    (hp : N.IsPositiveFluxPath v rs c c)
    (z₀ z : EuclideanSpace ℝ S) (k p : Fin rs.length → ℝ)
    {kmin kmax δ : ℝ}
    (hkmin : 0 ≤ kmin) (hscale : kmax ≤ kmin * Real.exp δ)
    (hk : ∀ i, kmin ≤ k i ∧ k i ≤ kmax)
    (hgap : ∀ i j, p i < p j → p i + δ ≤ p j)
    (hpSource : ∀ i, p i =
      ⟪z₀, toEuclid (CRNT.exponentVector (N.sourceIdx (rs.get i)).val)⟫_ℝ)
    (horder : ∀ i j,
      ⟪z, toEuclid (CRNT.exponentVector (N.sourceIdx (rs.get i)).val)⟫_ℝ <
        ⟪z, toEuclid (CRNT.exponentVector (N.sourceIdx (rs.get j)).val)⟫_ℝ → p i < p j) :
    (∑ i : Fin rs.length,
      (k i * Real.exp (p i)) *
        ⟪z, toEuclid (N.reactionVector (rs.get i))⟫_ℝ) ≤ 0 := by
  let f : N.ComplexIdx → EuclideanSpace ℝ S :=
    fun c => toEuclid (CRNT.exponentVector c.val)
  let source := rs.map N.sourceIdx
  let target := rs.map N.targetIdx
  let eSource : Fin rs.length ≃ Fin source.length := finCongr (by simp [source])
  have hperm : List.Perm target source :=
    IsPositiveFluxPath.targetList_perm_sourceList N hp
  have hsource (i : Fin source.length) :
      source.get i = N.sourceIdx (rs.get (eSource.symm i)) := by
    simp [source, eSource]
  have hindex (i : Fin source.length) :
      finCongr hperm.length_eq.symm i = finCongr (by simp [target]) (eSource.symm i) := by
    apply Fin.ext
    simp [eSource, source, target]
  have htarget (i : Fin source.length) :
      target.get (finCongr hperm.length_eq.symm i) =
        N.targetIdx (rs.get (eSource.symm i)) := by
    rw [hindex i]
    simp [target, eSource]
  let k' : Fin source.length → ℝ := fun i => k (eSource.symm i)
  let p' : Fin source.length → ℝ := fun i => p (eSource.symm i)
  have hp' : ∀ i : Fin source.length, p' i = ⟪z₀, f (source.get i)⟫_ℝ := by
    intro i
    change p (eSource.symm i) = ⟪z₀, f (source.get i)⟫_ℝ
    rw [hsource i]
    exact hpSource (eSource.symm i)
  have hvec (r : N.R) : f (N.targetIdx r) - f (N.sourceIdx r) =
      toEuclid (N.reactionVector r) := by
    ext s
    simp [f, CRNT.exponentVector, Network.sourceIdx, Network.targetIdx]
  have htransport :
      (∑ i : Fin rs.length,
        (k i * Real.exp (p i)) *
          ⟪z, toEuclid (N.reactionVector (rs.get i))⟫_ℝ) =
      ∑ i : Fin source.length,
        (k (eSource.symm i) * Real.exp (p (eSource.symm i))) *
          ⟪z, toEuclid (N.reactionVector (rs.get (eSource.symm i)))⟫_ℝ := by
    exact Fintype.sum_equiv eSource
      (fun i => (k i * Real.exp (p i)) *
        ⟪z, toEuclid (N.reactionVector (rs.get i))⟫_ℝ)
      (fun i => (k (eSource.symm i) * Real.exp (p (eSource.symm i))) *
        ⟪z, toEuclid (N.reactionVector (rs.get (eSource.symm i)))⟫_ℝ)
      (fun _ => rfl)
  have hwalk := cyclicProjectedVelocity_nonpos_of_permutedList_rateSeparation
    target source hperm f k' p' z₀ z hkmin hscale
    (fun i => hk (eSource.symm i))
    (fun i j hij => hgap (eSource.symm i) (eSource.symm j) hij)
    hp' (by
      intro i j hij
      change p (eSource.symm i) < p (eSource.symm j)
      apply horder (eSource.symm i) (eSource.symm j)
      rw [hsource i, hsource j] at hij
      change _ < _ at hij
      exact hij)
  rw [htransport]
  apply le_of_eq_of_le ?_ hwalk
  apply Finset.sum_congr rfl
  intro i _
  rw [htarget i, hsource i, ← hvec (rs.get (eSource.symm i))]

/-- **Closed-walk projection under a pure exponential source order.** When a cycle's edge
coefficients are a common nonnegative cycle-flow weight times the exponential of source levels,
no gap estimate is needed: strict order preservation alone makes the coefficients monotone. -/
theorem closedWalk_reactionList_projected_nonpos_of_order
    (N : Network S) {v : N.R → ℝ} {rs : List N.R} {c : N.ComplexIdx}
    (hp : N.IsPositiveFluxPath v rs c c)
    (z₀ z : EuclideanSpace ℝ S)
    (horder : ∀ i j,
      ⟪z, toEuclid (CRNT.exponentVector (N.sourceIdx (rs.get i)).val)⟫_ℝ <
        ⟪z, toEuclid (CRNT.exponentVector (N.sourceIdx (rs.get j)).val)⟫_ℝ →
      ⟪z₀, toEuclid (CRNT.exponentVector (N.sourceIdx (rs.get i)).val)⟫_ℝ <
        ⟪z₀, toEuclid (CRNT.exponentVector (N.sourceIdx (rs.get j)).val)⟫_ℝ) :
    (∑ i : Fin rs.length,
      Real.exp (⟪z₀, toEuclid (CRNT.exponentVector (N.sourceIdx (rs.get i)).val)⟫_ℝ) *
        ⟪z, toEuclid (N.reactionVector (rs.get i))⟫_ℝ) ≤ 0 := by
  have h := N.closedWalk_reactionList_projected_nonpos_of_rateSeparation
    hp z₀ z (fun _ => 1)
    (fun i => ⟪z₀, toEuclid (CRNT.exponentVector (N.sourceIdx (rs.get i)).val)⟫_ℝ)
    (kmin := 1) (kmax := 1) (δ := 0)
    (by norm_num) (by norm_num)
    (fun _ => by constructor <;> norm_num)
    (by intro i j hij; simpa using hij.le)
    (fun _ => rfl) horder
  simpa only [one_mul] using h

/-- The source-complex pairing with a logarithmic direction. -/
def sourceLogProjection (N : Network S) (w : S → ℝ) (r : N.R) : ℝ :=
  ∑ s, ((N.sourceIdx r).val s : ℝ) * w s

/-- The fixed equilibrium factor attached to one reaction source monomial. -/
noncomputable def equilibriumSourceFactor (N : Network S) (xstar : Concentration S) (r : N.R) : ℝ :=
  Real.exp (-(N.sourceLogProjection (fun s => Real.log (xstar s)) r))

/-- **Complex-balanced velocity points into a separated source-order chamber.** Suppose source
monomial prefactors induced by the positive complex-balanced reference are bounded by one common
exponential gap. If the test direction respects the source ordering selected by `log x`, and all
strict source gaps in that ordering exceed the gap margin, then the mass-action velocity has
nonpositive projection in the test direction.

The proof decomposes the positive equilibrium flux into concrete closed walks. The rate-separation
estimate proved above handles each walk, and nonnegative cycle weights preserve the sign. The
hypotheses describe a chamber away from its uncertainty walls; the remaining GAC step is to build
forward-invariant zero-separating surfaces from these chamberwise signs. -/
theorem massActionVectorField_projected_nonpos_of_rateSeparatedSourceOrder
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (z : S → ℝ) {kmin kmax δ : ℝ}
    (hkmin : 0 ≤ kmin) (hscale : kmax ≤ kmin * Real.exp δ)
    (hk : ∀ r, kmin ≤ N.equilibriumSourceFactor xstar r ∧
      N.equilibriumSourceFactor xstar r ≤ kmax)
    (hgap : ∀ r q,
      N.sourceLogProjection (fun s => Real.log (x s)) r <
        N.sourceLogProjection (fun s => Real.log (x s)) q →
      N.sourceLogProjection (fun s => Real.log (x s)) r + δ ≤
        N.sourceLogProjection (fun s => Real.log (x s)) q)
    (horder : ∀ r q,
      N.sourceLogProjection z r < N.sourceLogProjection z q →
        N.sourceLogProjection (fun s => Real.log (x s)) r <
          N.sourceLogProjection (fun s => Real.log (x s)) q) :
    (∑ s, z s * N.massActionVectorField κ x s) ≤ 0 := by
  let logx : S → ℝ := fun s => Real.log (x s)
  let logstar : S → ℝ := fun s => Real.log (xstar s)
  let p : N.R → ℝ := fun r => N.sourceLogProjection logx r
  let k : N.R → ℝ := fun r => N.equilibriumSourceFactor xstar r
  let f : N.R → ℝ := fun r =>
    Real.exp (∑ s, ((N.sourceIdx r).val s : ℝ) * (logx s - logstar s)) *
      (∑ s, z s * N.reactionVector r s)
  have hprojection (w : S → ℝ) (r : N.R) :
      ⟪toEuclid w, toEuclid (CRNT.exponentVector (N.sourceIdx r).val)⟫_ℝ =
        N.sourceLogProjection w r := by
    rw [inner_toEuclid]
    apply Finset.sum_congr rfl
    intro s _
    simp [CRNT.exponentVector, mul_comm]
  have hreactionProjection (r : N.R) :
      ⟪toEuclid z, toEuclid (N.reactionVector r)⟫_ℝ =
        ∑ s, z s * N.reactionVector r s := by
    rw [inner_toEuclid]
  have hsumExponent (r : N.R) :
      (∑ s, ((N.sourceIdx r).val s : ℝ) * (logx s - logstar s)) =
        -(N.sourceLogProjection logstar r) + N.sourceLogProjection logx r := by
    dsimp [sourceLogProjection]
    calc
      (∑ s, ((N.sourceIdx r).val s : ℝ) * (logx s - logstar s)) =
          ∑ s, (((N.sourceIdx r).val s : ℝ) * logx s -
            ((N.sourceIdx r).val s : ℝ) * logstar s) := by
              apply Finset.sum_congr rfl
              intro s _
              ring
      _ = (∑ s, ((N.sourceIdx r).val s : ℝ) * logx s) -
          ∑ s, ((N.sourceIdx r).val s : ℝ) * logstar s := by
            rw [Finset.sum_sub_distrib]
      _ = -(∑ s, ((N.sourceIdx r).val s : ℝ) * logstar s) +
          ∑ s, ((N.sourceIdx r).val s : ℝ) * logx s := by ring
  have hexpFactor (r : N.R) :
      Real.exp (∑ s, ((N.sourceIdx r).val s : ℝ) * (logx s - logstar s)) =
        k r * Real.exp (p r) := by
    dsimp [k, p, equilibriumSourceFactor]
    calc
      Real.exp (∑ s, ((N.sourceIdx r).val s : ℝ) * (logx s - logstar s)) =
          Real.exp (-(N.sourceLogProjection logstar r) +
            N.sourceLogProjection logx r) := by rw [hsumExponent]
      _ = Real.exp (-(N.sourceLogProjection logstar r)) *
          Real.exp (N.sourceLogProjection logx r) := Real.exp_add _ _
  have hterm (r : N.R) : f r = (k r * Real.exp (p r)) *
      ⟪toEuclid z, toEuclid (N.reactionVector r)⟫_ℝ := by
    change Real.exp (∑ s, ((N.sourceIdx r).val s : ℝ) * (logx s - logstar s)) *
        (∑ s, z s * N.reactionVector r s) = _
    rw [hexpFactor r, ← hreactionProjection r]
  have hfield := N.massActionVectorField_eq_equilibriumFlux_exp_sum κ hx hxs
  have hcoord (s : S) : N.massActionVectorField κ x s =
      ∑ r, (N.equilibriumReactionFlux κ xstar r *
        Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) *
          (Real.log (x t) - Real.log (xstar t)))) * N.reactionVector r s := by
    have h := congrFun hfield s
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
  have hpair :
      (∑ s, z s * N.massActionVectorField κ x s) =
        ∑ r, N.equilibriumReactionFlux κ xstar r * f r := by
    calc
      (∑ s, z s * N.massActionVectorField κ x s) =
          ∑ s, z s * ∑ r, (N.equilibriumReactionFlux κ xstar r *
            Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) *
              (Real.log (x t) - Real.log (xstar t)))) * N.reactionVector r s := by
                apply Finset.sum_congr rfl
                intro s _
                rw [hcoord s]
      _ = ∑ s, ∑ r, z s * ((N.equilibriumReactionFlux κ xstar r *
            Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) *
              (Real.log (x t) - Real.log (xstar t)))) * N.reactionVector r s) := by
                apply Finset.sum_congr rfl
                intro s _
                rw [Finset.mul_sum]
      _ = ∑ r, ∑ s, (N.equilibriumReactionFlux κ xstar r *
            Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) *
              (Real.log (x t) - Real.log (xstar t)))) *
            (z s * N.reactionVector r s) := by
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro r _
                apply Finset.sum_congr rfl
                intro s _
                ring
      _ = ∑ r, (N.equilibriumReactionFlux κ xstar r *
            Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) *
              (Real.log (x t) - Real.log (xstar t)))) *
            (∑ s, z s * N.reactionVector r s) := by
                apply Finset.sum_congr rfl
                intro r _
                rw [Finset.mul_sum]
      _ = ∑ r, N.equilibriumReactionFlux κ xstar r * f r := by
                apply Finset.sum_congr rfl
                intro r _
                simp only [f]
                ring
  obtain ⟨m, rs, a, ha, hwalks, hdecomp⟩ :=
    N.equilibriumReactionFlux_decomposes_into_closedWalks κ hxs hcb
  have hweighted := N.weighted_sum_eq_closedWalkSums_of_decomposition rs a hdecomp f
  have hlistSum (L : List N.R) :
      (L.map f).sum = ∑ j : Fin L.length, f (L.get j) := by
    rw [← List.sum_ofFn]
    have hlist : List.ofFn (fun j : Fin L.length => f (L.get j)) = L.map f := by
      simpa only [List.get_eq_getElem] using (List.ofFn_getElem_eq_map L f)
    rw [hlist]
  rw [hpair, hweighted]
  apply Finset.sum_nonpos
  intro i _
  obtain ⟨cycleFlow, base, hcycleFlow, hpath⟩ := hwalks i
  have hcycle := N.closedWalk_reactionList_projected_nonpos_of_rateSeparation
    hpath (toEuclid logx) (toEuclid z)
    (fun j => k ((rs i).get j)) (fun j => p ((rs i).get j))
    hkmin hscale
    (fun j => hk ((rs i).get j))
    (fun j l hjl => hgap ((rs i).get j) ((rs i).get l) hjl)
    (fun j => (hprojection logx ((rs i).get j)).symm)
    (by
      intro j l hjl
      exact horder ((rs i).get j) ((rs i).get l) (by
        rw [← hprojection z ((rs i).get j), ← hprojection z ((rs i).get l)]
        exact hjl))
  have hcycleSum : ((rs i).map f).sum ≤ 0 := by
    calc
      ((rs i).map f).sum = ∑ j : Fin (rs i).length, f ((rs i).get j) := hlistSum (rs i)
      _ = ∑ j : Fin (rs i).length,
          (k ((rs i).get j) * Real.exp (p ((rs i).get j))) *
            ⟪toEuclid z,
              toEuclid (N.reactionVector ((rs i).get j))⟫_ℝ := by
            apply Finset.sum_congr rfl
            intro j _
            exact hterm ((rs i).get j)
      _ ≤ 0 := hcycle
  exact mul_nonpos_of_nonneg_of_nonpos (ha i) hcycleSum

/-- The equilibrium source factors of a finite nonempty reaction family admit a positive common
lower bound, a common upper bound, and one exponential separation margin. This discharges the
scalar prefactor bounds in `massActionVectorField_projected_nonpos_of_rateSeparatedSourceOrder`;
the remaining assumptions there are the geometric chamber-order conditions. -/
theorem exists_uniform_equilibriumSourceFactor_bounds
    (N : Network S) (xstar : Concentration S) [Nonempty N.R] :
    ∃ kmin kmax δ : ℝ, 0 < kmin ∧
      (∀ r, kmin ≤ N.equilibriumSourceFactor xstar r ∧
        N.equilibriumSourceFactor xstar r ≤ kmax) ∧
      kmax ≤ kmin * Real.exp δ := by
  apply exists_uniform_exp_prefactor_separation
    (fun r : N.R => N.equilibriumSourceFactor xstar r)
  intro r
  exact Real.exp_pos _

/-- **Relative-source-order dissipation for the full complex-balanced field.** Let
`w = log(x / xstar)` be the relative logarithmic state. If a test direction `z` preserves the
strict ordering of source complexes induced by `w`, then the full mass-action vector field has
nonpositive projection onto `z`.

The proof decomposes the positive equilibrium flux into closed walks. On each walk the coefficient
is a common nonnegative cycle-flow weight times the exact exponential `exp(source · w)`, so strict
order preservation alone makes coefficients monotone; no uncertain prefactor or gap condition is
needed. This is the finite toric differential-inclusion sign at the point `x`. -/
theorem massActionVectorField_projected_nonpos_of_relativeSourceOrder
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (z : S → ℝ)
    (horder : ∀ r q,
      N.sourceLogProjection z r < N.sourceLogProjection z q →
        N.sourceLogProjection (fun s => Real.log (x s) - Real.log (xstar s)) r <
          N.sourceLogProjection (fun s => Real.log (x s) - Real.log (xstar s)) q) :
    (∑ s, z s * N.massActionVectorField κ x s) ≤ 0 := by
  let logrel : S → ℝ := fun s => Real.log (x s) - Real.log (xstar s)
  let phase : N.R → ℝ := fun r => N.sourceLogProjection logrel r
  let f : N.R → ℝ := fun r =>
    Real.exp (phase r) * (∑ s, z s * N.reactionVector r s)
  have hprojection (w : S → ℝ) (r : N.R) :
      ⟪toEuclid w, toEuclid (CRNT.exponentVector (N.sourceIdx r).val)⟫_ℝ =
        N.sourceLogProjection w r := by
    rw [inner_toEuclid]
    apply Finset.sum_congr rfl
    intro s _
    simp [CRNT.exponentVector, mul_comm]
  have hreactionProjection (r : N.R) :
      ⟪toEuclid z, toEuclid (N.reactionVector r)⟫_ℝ =
        ∑ s, z s * N.reactionVector r s := by
    rw [inner_toEuclid]
  have hterm (r : N.R) : f r =
      Real.exp (⟪toEuclid logrel,
        toEuclid (CRNT.exponentVector (N.sourceIdx r).val)⟫_ℝ) *
        ⟪toEuclid z, toEuclid (N.reactionVector r)⟫_ℝ := by
    calc
      f r = Real.exp (N.sourceLogProjection logrel r) *
          (∑ s, z s * N.reactionVector r s) := rfl
      _ = Real.exp (⟪toEuclid logrel,
            toEuclid (CRNT.exponentVector (N.sourceIdx r).val)⟫_ℝ) *
          ⟪toEuclid z, toEuclid (N.reactionVector r)⟫_ℝ := by
            rw [← hprojection logrel r, ← hreactionProjection r]
  have hfield := N.massActionVectorField_eq_equilibriumFlux_exp_sum κ hx hxs
  have hcoord (s : S) : N.massActionVectorField κ x s =
      ∑ r, (N.equilibriumReactionFlux κ xstar r * Real.exp (phase r)) *
        N.reactionVector r s := by
    have h := congrFun hfield s
    simpa [phase, logrel, sourceLogProjection, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] using h
  have hpair :
      (∑ s, z s * N.massActionVectorField κ x s) =
        ∑ r, N.equilibriumReactionFlux κ xstar r * f r := by
    calc
      (∑ s, z s * N.massActionVectorField κ x s) =
          ∑ s, z s * ∑ r,
            (N.equilibriumReactionFlux κ xstar r * Real.exp (phase r)) *
              N.reactionVector r s := by
                apply Finset.sum_congr rfl
                intro s _
                rw [hcoord s]
      _ = ∑ s, ∑ r, z s *
            ((N.equilibriumReactionFlux κ xstar r * Real.exp (phase r)) *
              N.reactionVector r s) := by
                apply Finset.sum_congr rfl
                intro s _
                rw [Finset.mul_sum]
      _ = ∑ r, ∑ s,
            (N.equilibriumReactionFlux κ xstar r * Real.exp (phase r)) *
              (z s * N.reactionVector r s) := by
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro r _
                apply Finset.sum_congr rfl
                intro s _
                ring
      _ = ∑ r, (N.equilibriumReactionFlux κ xstar r * Real.exp (phase r)) *
            (∑ s, z s * N.reactionVector r s) := by
                apply Finset.sum_congr rfl
                intro r _
                rw [Finset.mul_sum]
      _ = ∑ r, N.equilibriumReactionFlux κ xstar r * f r := by
                apply Finset.sum_congr rfl
                intro r _
                simp only [f]
                ring
  obtain ⟨m, rs, a, ha, hwalks, hdecomp⟩ :=
    N.equilibriumReactionFlux_decomposes_into_closedWalks κ hxs hcb
  have hweighted := N.weighted_sum_eq_closedWalkSums_of_decomposition rs a hdecomp f
  have hlistSum (L : List N.R) :
      (L.map f).sum = ∑ j : Fin L.length, f (L.get j) := by
    rw [← List.sum_ofFn]
    have hlist : List.ofFn (fun j : Fin L.length => f (L.get j)) = L.map f := by
      simpa only [List.get_eq_getElem] using (List.ofFn_getElem_eq_map L f)
    rw [hlist]
  rw [hpair, hweighted]
  apply Finset.sum_nonpos
  intro i _
  obtain ⟨cycleFlow, base, hcycleFlow, hpath⟩ := hwalks i
  have hcycle := N.closedWalk_reactionList_projected_nonpos_of_order
    hpath (toEuclid logrel) (toEuclid z)
    (by
      intro j l hjl
      have hz : N.sourceLogProjection z ((rs i).get j) <
          N.sourceLogProjection z ((rs i).get l) := by
        rw [← hprojection z ((rs i).get j), ← hprojection z ((rs i).get l)]
        exact hjl
      have hrel := horder ((rs i).get j) ((rs i).get l) hz
      rw [hprojection logrel ((rs i).get j), hprojection logrel ((rs i).get l)]
      exact hrel)
  have hcycleSum : ((rs i).map f).sum ≤ 0 := by
    calc
      ((rs i).map f).sum = ∑ j : Fin (rs i).length, f ((rs i).get j) := hlistSum (rs i)
      _ = ∑ j : Fin (rs i).length,
          Real.exp (⟪toEuclid logrel,
            toEuclid (CRNT.exponentVector (N.sourceIdx ((rs i).get j)).val)⟫_ℝ) *
              ⟪toEuclid z, toEuclid (N.reactionVector ((rs i).get j))⟫_ℝ := by
            apply Finset.sum_congr rfl
            intro j _
            exact hterm ((rs i).get j)
      _ ≤ 0 := hcycle
  exact mul_nonpos_of_nonneg_of_nonpos (ha i) hcycleSum

/-- The closed cone of test directions whose source-complex projections preserve the weak order
of a reference direction `w`. Its inequalities are the non-strict closure of the corresponding
source-order chamber. -/
noncomputable def relativeSourceOrderCone (N : Network S) (w : S → ℝ) :
    PointedCone ℝ (EuclideanSpace ℝ S) where
  carrier :=
    {z | ∀ r q, N.sourceLogProjection w r ≤ N.sourceLogProjection w q →
      N.sourceLogProjection (CRNT.toEuclid.symm z) r ≤
        N.sourceLogProjection (CRNT.toEuclid.symm z) q}
  add_mem' := by
    intro z z' hz hz' r q hp
    simp only [Set.mem_setOf_eq] at hz hz' ⊢
    have hsum (i : N.R) (v v' : S → ℝ) :
        N.sourceLogProjection (v + v') i =
          N.sourceLogProjection v i + N.sourceLogProjection v' i := by
      unfold sourceLogProjection
      calc
        (∑ s, ((N.sourceIdx i).val s : ℝ) * (v s + v' s)) =
            ∑ s, (((N.sourceIdx i).val s : ℝ) * v s +
              ((N.sourceIdx i).val s : ℝ) * v' s) := by
                apply Finset.sum_congr rfl
                intro s _
                ring
        _ = (∑ s, ((N.sourceIdx i).val s : ℝ) * v s) +
              ∑ s, ((N.sourceIdx i).val s : ℝ) * v' s := Finset.sum_add_distrib
    change N.sourceLogProjection (CRNT.toEuclid.symm (z + z')) r ≤
      N.sourceLogProjection (CRNT.toEuclid.symm (z + z')) q
    rw [LinearEquiv.map_add]
    rw [hsum r _ _, hsum q _ _]
    exact add_le_add (hz r q hp) (hz' r q hp)
  zero_mem' := by
    intro r q _
    simp [sourceLogProjection]
  smul_mem' := by
    intro c z hz r q hp
    simp only [Set.mem_setOf_eq] at hz ⊢
    have hproj (i : N.R) :
        N.sourceLogProjection (CRNT.toEuclid.symm (c • z)) i =
          (c : ℝ) * N.sourceLogProjection (CRNT.toEuclid.symm z) i := by
      rw [show c • z = (c : ℝ) • z from rfl, LinearEquiv.map_smul]
      unfold sourceLogProjection
      calc
        (∑ s, ((N.sourceIdx i).val s : ℝ) *
            ((c : ℝ) * (CRNT.toEuclid.symm z) s)) =
            ∑ s, (c : ℝ) *
              (((N.sourceIdx i).val s : ℝ) * (CRNT.toEuclid.symm z) s) := by
                apply Finset.sum_congr rfl
                intro s _
                ring
        _ = (c : ℝ) * ∑ s,
              ((N.sourceIdx i).val s : ℝ) * (CRNT.toEuclid.symm z) s := by
                rw [Finset.mul_sum]
    rw [hproj r, hproj q]
    exact mul_le_mul_of_nonneg_left (hz r q hp) c.2

/-- In a weakly reversible network, every reaction target is also a reaction source. The
length-zero return path is handled by the original reaction; otherwise the first edge of the
return path starts at the target. -/
theorem exists_sourceIdx_eq_targetIdx_of_weaklyReversible
    (N : Network S) (hwr : N.WeaklyReversible) (r : N.R) :
    ∃ q : N.R, N.sourceIdx q = N.targetIdx r := by
  have hback : N.Reaches (N.reaction r).target (N.reaction r).source := hwr r
  have hfirst {c d : Complex S} (h : N.Reaches c d) (hne : c ≠ d) :
      ∃ q : N.R, (N.reaction q).source = c := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact False.elim (hne rfl)
    | @head a b hab _ ih =>
        obtain ⟨q, hsource, _⟩ := hab
        exact ⟨q, hsource⟩
  by_cases heq : (N.reaction r).target = (N.reaction r).source
  · refine ⟨r, ?_⟩
    apply Subtype.ext
    exact heq.symm
  · obtain ⟨q, hsource⟩ := hfirst hback heq
    refine ⟨q, ?_⟩
    apply Subtype.ext
    exact hsource

/-- **The relative source-order chamber has no line in the stoichiometric directions.**
If both a test direction and its negative preserve the source order selected by `w`, then
all source-complex projections of that direction agree. Weak reversibility makes every
reaction target a source, so the direction annihilates every reaction vector. A vector in
the stoichiometric subspace that annihilates all reaction vectors must therefore vanish.

This is the required reduction before treating the finite source-order chambers as a fan in
the stoichiometric subspace: conservation directions have been removed, and the restricted
order cone is salient. -/
theorem relativeSourceOrderCone_lineality_eq_zero
    (N : Network S) (w : S → ℝ) {z : EuclideanSpace ℝ S}
    (hz : z ∈ N.relativeSourceOrderCone w)
    (hnegz : -z ∈ N.relativeSourceOrderCone w)
    (hstoich : CRNT.toEuclid.symm z ∈ N.stoichSubspace)
    (hwr : N.WeaklyReversible) :
    z = 0 := by
  let u : S → ℝ := CRNT.toEuclid.symm z
  let p : N.R → ℝ := fun r => N.sourceLogProjection u r
  have hproj : ∀ r q : N.R, p r = p q := by
    intro r q
    change (∀ r q,
      N.sourceLogProjection w r ≤ N.sourceLogProjection w q →
        N.sourceLogProjection (CRNT.toEuclid.symm z) r ≤
          N.sourceLogProjection (CRNT.toEuclid.symm z) q) at hz
    change (∀ r q,
      N.sourceLogProjection w r ≤ N.sourceLogProjection w q →
        N.sourceLogProjection (CRNT.toEuclid.symm (-z)) r ≤
          N.sourceLogProjection (CRNT.toEuclid.symm (-z)) q) at hnegz
    have hnegproj (i : N.R) :
        N.sourceLogProjection (CRNT.toEuclid.symm (-z)) i = -p i := by
      simp [p, u, sourceLogProjection, Finset.sum_neg_distrib]
    rcases le_total (N.sourceLogProjection w r) (N.sourceLogProjection w q) with hrq | hqr
    · have h₁ := hz r q hrq
      have h₂ := hnegz r q hrq
      rw [hnegproj r, hnegproj q] at h₂
      change p r ≤ p q at h₁
      linarith
    · have h₁ := hz q r hqr
      have h₂ := hnegz q r hqr
      rw [hnegproj q, hnegproj r] at h₂
      change p q ≤ p r at h₁
      linarith
  have hreact : ∀ r : N.R, ∑ s, u s * N.reactionVector r s = 0 := by
    intro r
    obtain ⟨q, hq⟩ := N.exists_sourceIdx_eq_targetIdx_of_weaklyReversible hwr r
    have hqval := congrArg Subtype.val hq
    have hp :
        (∑ s, ((N.targetIdx r).val s : ℝ) * u s) =
          ∑ s, ((N.sourceIdx r).val s : ℝ) * u s := by
      simpa [p, sourceLogProjection, hqval, u] using hproj q r
    calc
      (∑ s, u s * N.reactionVector r s) =
          ∑ s, u s * (((N.reaction r).target s : ℝ) -
            ((N.reaction r).source s : ℝ)) := by
              apply Finset.sum_congr rfl
              intro s _
              rw [reactionVector_apply]
      _ = (∑ s, ((N.reaction r).target s : ℝ) * u s) -
            ∑ s, ((N.reaction r).source s : ℝ) * u s := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro s _
              ring
      _ = 0 := by
            simpa [sourceIdx, targetIdx] using sub_eq_zero.mpr hp
  have huorth : ∀ v ∈ N.stoichSubspace, ∑ s, u s * v s = 0 := by
    intro v hv
    rw [stoichSubspace] at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨r, rfl⟩ := hv
        exact hreact r
    | zero => simp
    | add v₁ v₂ _ _ ih₁ ih₂ =>
        calc
          (∑ s, u s * (v₁ + v₂) s) =
              ∑ s, (u s * v₁ s + u s * v₂ s) := by
                apply Finset.sum_congr rfl
                intro s _
                simp only [Pi.add_apply]
                ring
          _ = 0 := by rw [Finset.sum_add_distrib, ih₁, ih₂, add_zero]
    | smul a v _ ih =>
        calc
          (∑ s, u s * (a • v) s) = ∑ s, a * (u s * v s) := by
            apply Finset.sum_congr rfl
            intro s _
            simp only [Pi.smul_apply, smul_eq_mul]
            ring
          _ = 0 := by rw [← Finset.mul_sum, ih, mul_zero]
  have hnorm : ∑ s, u s * u s = 0 := huorth u hstoich
  have hterms : ∀ s, u s * u s = 0 := by
    intro s
    have hnonneg : ∀ t ∈ (Finset.univ : Finset S), 0 ≤ u t * u t :=
      fun t _ => mul_self_nonneg (u t)
    have hs := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hnorm
    exact hs s (Finset.mem_univ s)
  have hu : u = 0 := by
    funext s
    exact mul_self_eq_zero.mp (hterms s)
  calc
    z = CRNT.toEuclid (CRNT.toEuclid.symm z) :=
      (CRNT.toEuclid.apply_symm_apply z).symm
    _ = 0 := by simp [u, hu]

/-- The finite weak-order signature of the reaction-source projections selected by `w`. -/
noncomputable def relativeSourceOrderSignature (N : Network S) (w : S → ℝ) :
    N.R → N.R → Bool :=
  fun r q => decide (N.sourceLogProjection w r ≤ N.sourceLogProjection w q)

theorem relativeSourceOrderSignature_le_iff (N : Network S) (w : S → ℝ)
    (r q : N.R) :
    N.relativeSourceOrderSignature w r q = true ↔
      N.sourceLogProjection w r ≤ N.sourceLogProjection w q := by
  simp [relativeSourceOrderSignature]

/-- Any realized finite weak-order signature has a representative direction. The chosen
representative is only used to index the finite family; its chamber is independent of the
choice by `relativeSourceOrderCone_eq_of_sameSourceOrder`. -/
noncomputable def relativeSourceOrderWitness (N : Network S)
    (σ : N.R → N.R → Bool) : S → ℝ :=
  by
    classical
    exact if h : ∃ w, N.relativeSourceOrderSignature w = σ then
      Classical.choose h else 0

theorem relativeSourceOrderSignature_witness_eq (N : Network S)
    {σ : N.R → N.R → Bool}
    (h : ∃ w, N.relativeSourceOrderSignature w = σ) :
    N.relativeSourceOrderSignature (N.relativeSourceOrderWitness σ) = σ := by
  classical
  unfold relativeSourceOrderWitness
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- A chamber is determined by its weak ordering of source projections, including ties. -/
theorem relativeSourceOrderCone_eq_of_sameSourceOrder (N : Network S)
    {w₁ w₂ : S → ℝ}
    (h : ∀ r q : N.R,
      (N.sourceLogProjection w₁ r ≤ N.sourceLogProjection w₁ q) ↔
        (N.sourceLogProjection w₂ r ≤ N.sourceLogProjection w₂ q)) :
    N.relativeSourceOrderCone w₁ = N.relativeSourceOrderCone w₂ := by
  ext z
  change (∀ r q,
      N.sourceLogProjection w₁ r ≤ N.sourceLogProjection w₁ q →
        N.sourceLogProjection (CRNT.toEuclid.symm z) r ≤
          N.sourceLogProjection (CRNT.toEuclid.symm z) q) ↔
    (∀ r q,
      N.sourceLogProjection w₂ r ≤ N.sourceLogProjection w₂ q →
        N.sourceLogProjection (CRNT.toEuclid.symm z) r ≤
          N.sourceLogProjection (CRNT.toEuclid.symm z) q)
  constructor
  · intro hz r q horder
    exact hz r q ((h r q).2 horder)
  · intro hz r q horder
    exact hz r q ((h r q).1 horder)

/-- There are only finitely many relative source-order chambers: a chamber depends only on a
Boolean weak-order signature on the finite reaction-index type, and each realized signature
has a representative direction. This establishes finiteness of the candidate chamber family;
the face-intersection and covering axioms still need to be proved before it is a fan. -/
theorem finite_relativeSourceOrderCone_range (N : Network S) :
    (Set.range (N.relativeSourceOrderCone)).Finite := by
  classical
  let f : (N.R → N.R → Bool) → PointedCone ℝ (EuclideanSpace ℝ S) :=
    fun σ => N.relativeSourceOrderCone (N.relativeSourceOrderWitness σ)
  have hfinite : (Set.range f).Finite := by
    simpa [Set.range] using
      (Set.toFinite (Set.univ : Set (N.R → N.R → Bool))).image f
  have hsub : Set.range (N.relativeSourceOrderCone) ⊆ Set.range f := by
    rintro C ⟨w, rfl⟩
    let σ := N.relativeSourceOrderSignature w
    have hreal : ∃ v, N.relativeSourceOrderSignature v = σ := ⟨w, rfl⟩
    have hsig := N.relativeSourceOrderSignature_witness_eq hreal
    have horder : ∀ r q : N.R,
        (N.sourceLogProjection (N.relativeSourceOrderWitness σ) r ≤
          N.sourceLogProjection (N.relativeSourceOrderWitness σ) q) ↔
        (N.sourceLogProjection w r ≤ N.sourceLogProjection w q) := by
      intro r q
      rw [← N.relativeSourceOrderSignature_le_iff
          (N.relativeSourceOrderWitness σ) r q, hsig,
        N.relativeSourceOrderSignature_le_iff w r q]
    refine ⟨σ, ?_⟩
    change N.relativeSourceOrderCone (N.relativeSourceOrderWitness σ) =
      N.relativeSourceOrderCone w
    exact N.relativeSourceOrderCone_eq_of_sameSourceOrder horder
  exact hfinite.subset hsub

/-- **Pointwise toric inclusion for a complex-balanced field.** At every positive state `x`, the
mass-action vector field lies in the polar cone of the source-order cone determined by
`log(x/xstar)`. This is the exact finite-dimensional toric differential-inclusion statement: the
full field, not just one reaction or one cycle, has nonpositive pairing with every direction in the
closed source-order chamber. -/
theorem massActionVectorField_mem_polar_relativeSourceOrderCone
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) :
    CRNT.toEuclid (N.massActionVectorField κ x) ∈
      polarCone (N.relativeSourceOrderCone
        (fun s => Real.log (x s) - Real.log (xstar s))) := by
  rw [mem_polarCone]
  intro z hz
  change (∀ r q,
    N.sourceLogProjection (fun s => Real.log (x s) - Real.log (xstar s)) r ≤
      N.sourceLogProjection (fun s => Real.log (x s) - Real.log (xstar s)) q →
    N.sourceLogProjection (CRNT.toEuclid.symm z) r ≤
      N.sourceLogProjection (CRNT.toEuclid.symm z) q) at hz
  have horder : ∀ r q,
      N.sourceLogProjection (CRNT.toEuclid.symm z) r <
        N.sourceLogProjection (CRNT.toEuclid.symm z) q →
      N.sourceLogProjection (fun s => Real.log (x s) - Real.log (xstar s)) r <
        N.sourceLogProjection (fun s => Real.log (x s) - Real.log (xstar s)) q := by
    intro r q htest
    by_contra hnot
    have hreverse :
        N.sourceLogProjection (fun s => Real.log (x s) - Real.log (xstar s)) q ≤
          N.sourceLogProjection (fun s => Real.log (x s) - Real.log (xstar s)) r :=
      le_of_not_gt hnot
    have hcompat := hz q r hreverse
    exact (not_lt_of_ge hcompat) htest
  have hproj := N.massActionVectorField_projected_nonpos_of_relativeSourceOrder
    κ hx hxs hcb (CRNT.toEuclid.symm z) horder
  have hinner :
      ⟪z, CRNT.toEuclid (N.massActionVectorField κ x)⟫_ℝ =
        ∑ s, (CRNT.toEuclid.symm z) s * N.massActionVectorField κ x s := by
    calc
      ⟪z, CRNT.toEuclid (N.massActionVectorField κ x)⟫_ℝ =
          ⟪CRNT.toEuclid (CRNT.toEuclid.symm z),
            CRNT.toEuclid (N.massActionVectorField κ x)⟫_ℝ := by
              rw [LinearEquiv.apply_symm_apply]
      _ = ∑ s, (CRNT.toEuclid.symm z) s * N.massActionVectorField κ x s :=
            CRNT.inner_toEuclid _ _
  rw [hinner]
  exact hproj

/-- **Eventual order-cone dissipation on every logarithmic ray.** Fix a positive complex-balanced
equilibrium and any direction `w` in log-concentration space. Along `xₜ = exp(t w)`, the field
has nonpositive projection against every test direction `z` whose strict source-complex order is
preserved by `w`.

This follows from the chamberwise estimate above because every strictly ordered pair of source
levels has a positive minimum gap in this finite network, while the equilibrium source factors
have a fixed finite range. If there are no strict source-level gaps, both ordering hypotheses are
vacuous and the same estimate applies immediately. This gives the field's polar-cone sign on the
closed source-order chamber at infinity; it does not provide the global glued separating surface
needed for permanence. -/
theorem eventually_orderCompatible_projected_nonpos_on_exp_ray
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) [Nonempty N.R]
    (w : S → ℝ) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → ∀ z : S → ℝ,
      (∀ r q, N.sourceLogProjection z r < N.sourceLogProjection z q →
        N.sourceLogProjection w r < N.sourceLogProjection w q) →
      (∑ s, z s * N.massActionVectorField κ (fun s => Real.exp (t * w s)) s) ≤ 0 := by
  obtain ⟨kmin, kmax, δ, hkmin, hk, hscale⟩ :=
    N.exists_uniform_equilibriumSourceFactor_bounds xstar
  obtain ⟨r₀⟩ := ‹Nonempty N.R›
  have hminlemax : kmin ≤ kmax := (hk r₀).1.trans (hk r₀).2
  have hratio : 1 ≤ kmax / kmin := (one_le_div hkmin).2 hminlemax
  have hratioExp : 1 ≤ Real.exp δ :=
    hratio.trans ((div_le_iff₀ hkmin).2 (by simpa [mul_comm] using hscale))
  have hδnonneg : 0 ≤ δ := by
    rw [← Real.exp_zero, Real.exp_le_exp] at hratioExp
    exact hratioExp
  let p : N.R → ℝ := fun r => N.sourceLogProjection w r
  let xt (t : ℝ) : Concentration S := fun s => Real.exp (t * w s)
  have hlogproj (t : ℝ) (r : N.R) :
      N.sourceLogProjection (fun s => Real.log (xt t s)) r = t * p r := by
    have hlog : (fun s => Real.log (xt t s)) = fun s => t * w s := by
      funext s
      simp [xt, Real.log_exp]
    rw [hlog]
    unfold sourceLogProjection p
    calc
      (∑ s, ((N.sourceIdx r).val s : ℝ) * (t * w s)) =
          ∑ s, t * (((N.sourceIdx r).val s : ℝ) * w s) := by
            apply Finset.sum_congr rfl
            intro s _
            ring
      _ = t * ∑ s, ((N.sourceIdx r).val s : ℝ) * w s := by
            rw [Finset.mul_sum]
  by_cases hstrict : ∃ r q : N.R, p r < p q
  · obtain ⟨ε, hεpos, hεgap⟩ := exists_positive_uniform_strict_gap hstrict
    let T : ℝ := δ / ε + 1
    refine ⟨T, ?_, ?_⟩
    · dsimp [T]
      positivity
    · intro t ht
      have hdivnonneg : 0 ≤ δ / ε := div_nonneg hδnonneg (le_of_lt hεpos)
      have htpos : 0 < t := by dsimp [T] at ht; linarith
      have hδt : δ ≤ t * ε := by
        apply (div_le_iff₀ hεpos).mp
        dsimp [T] at ht
        linarith
      have hgap : ∀ r q : N.R,
          N.sourceLogProjection (fun s => Real.log (xt t s)) r <
            N.sourceLogProjection (fun s => Real.log (xt t s)) q →
          N.sourceLogProjection (fun s => Real.log (xt t s)) r + δ ≤
            N.sourceLogProjection (fun s => Real.log (xt t s)) q := by
        intro r q hrq
        have hpq : p r < p q := by
          rw [hlogproj t r, hlogproj t q] at hrq
          exact (mul_lt_mul_iff_of_pos_left htpos).mp hrq
        have hscaled : δ ≤ t * (p q - p r) := by
          calc
            δ ≤ t * ε := hδt
            _ ≤ t * (p q - p r) :=
              mul_le_mul_of_nonneg_left (hεgap r q hpq) (le_of_lt htpos)
        rw [hlogproj t r, hlogproj t q]
        nlinarith [hscaled]
      intro z hzorder
      have horder : ∀ r q : N.R,
          N.sourceLogProjection z r < N.sourceLogProjection z q →
          N.sourceLogProjection (fun s => Real.log (xt t s)) r <
            N.sourceLogProjection (fun s => Real.log (xt t s)) q := by
        intro r q hrq
        have hworder := hzorder r q hrq
        rw [hlogproj t r, hlogproj t q]
        exact mul_lt_mul_of_pos_left (by simpa [p] using hworder) htpos
      have hxt : (xt t).Positive := fun s => Real.exp_pos _
      exact N.massActionVectorField_projected_nonpos_of_rateSeparatedSourceOrder
        κ hxt hxs hcb z hkmin.le hscale (fun r => hk r) hgap horder
  · let T : ℝ := 1
    refine ⟨T, by norm_num [T], ?_⟩
    intro t ht
    have htpos : 0 < t := by dsimp [T] at ht; linarith
    have hno : ∀ r q : N.R, ¬ p r < p q := by
      intro r q hpq
      exact hstrict ⟨r, q, hpq⟩
    have hgap : ∀ r q : N.R,
        N.sourceLogProjection (fun s => Real.log (xt t s)) r <
          N.sourceLogProjection (fun s => Real.log (xt t s)) q →
        N.sourceLogProjection (fun s => Real.log (xt t s)) r + δ ≤
          N.sourceLogProjection (fun s => Real.log (xt t s)) q := by
      intro r q hrq
      rw [hlogproj t r, hlogproj t q] at hrq
      exact (hno r q ((mul_lt_mul_iff_of_pos_left htpos).mp hrq)).elim
    intro z hzorder
    have horder : ∀ r q : N.R,
        N.sourceLogProjection z r < N.sourceLogProjection z q →
        N.sourceLogProjection (fun s => Real.log (xt t s)) r <
          N.sourceLogProjection (fun s => Real.log (xt t s)) q := by
      intro r q hrq
      have hpq := hzorder r q hrq
      exact (hno r q (by simpa [p] using hpq)).elim
    have hxt : (xt t).Positive := fun s => Real.exp_pos _
    exact N.massActionVectorField_projected_nonpos_of_rateSeparatedSourceOrder
      κ hxt hxs hcb z hkmin.le hscale (fun r => hk r) hgap horder

/-- The radial specialization of `eventually_orderCompatible_projected_nonpos_on_exp_ray`.
The ray direction itself always preserves its own source order. -/
theorem eventually_radially_nonpos_on_exp_ray
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) [Nonempty N.R]
    (w : S → ℝ) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      (∑ s, w s * N.massActionVectorField κ (fun s => Real.exp (t * w s)) s) ≤ 0 := by
  obtain ⟨T, hT, hprojected⟩ :=
    N.eventually_orderCompatible_projected_nonpos_on_exp_ray κ hxs hcb w
  refine ⟨T, hT, ?_⟩
  intro t ht
  apply hprojected t ht w
  intro r q hrq
  exact hrq

end CRNT.Network

import CRNT.Graph.CirculationDecomposition
import CRNT.Equilibria.ComplexBalanceLinearStability
import CRNT.Theorems.DeficiencyZero.Toric

namespace CRNT.Network
open scoped BigOperators
variable {S : Type} [DecidableEq S] [Fintype S]

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

end CRNT.Network

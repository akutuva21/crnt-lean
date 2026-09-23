import CRNT.Graph.PositiveCirculation
import CRNT.Flux.Elementary
import CRNT.Deficiency.CycleExactSequence
import CRNT.LinearAlgebra.ConformalDecomposition

/-!
# Directed-cycle decomposition of graph circulations

Nonnegative graph circulations form an s-cone `ker ∂ ∩ ℝ_{≥0}^R`.  Its extreme rays
are the directed-cycle flows.  Consequently every nonnegative graph circulation is a
finite nonnegative sum of directed-cycle flows, and a strictly positive circulation is
exactly a positive cycle cover of all reaction channels.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Nonnegative graph circulation. -/
def IsNonnegativeGraphCirculation (N : Network S) (v : N.R → ℝ) : Prop :=
  (∀ r, 0 ≤ v r) ∧ N.incidenceMap v = 0

/-- Support-minimal nonzero nonnegative graph circulation: algebraic directed cycle flow. -/
def IsDirectedCycleFlow (N : Network S) (v : N.R → ℝ) : Prop :=
  N.IsNonnegativeGraphCirculation v ∧ v ≠ 0 ∧
    ∀ w : N.R → ℝ,
      N.IsNonnegativeGraphCirculation w → w ≠ 0 →
      N.fluxSupport w ⊆ N.fluxSupport v →
      N.fluxSupport v ⊆ N.fluxSupport w

private theorem nonnegElementary_incidence_iff_cycle (N : Network S) (v : N.R → ℝ) :
    CRNT.NonnegElementary (LinearMap.ker N.incidenceMap) v ↔ N.IsDirectedCycleFlow v := by
  constructor
  · rintro ⟨hvker, hv0, hvnn, hmin⟩
    refine ⟨⟨hvnn, hvker⟩, hv0, ?_⟩
    intro w hw hw0 hsub
    have hsub' : CRNT.support w ⊆ CRNT.support v := by
      simpa [CRNT.support, Network.fluxSupport] using hsub
    have hrev := hmin w hw.2 hw0 hw.1 hsub'
    simpa [CRNT.support, Network.fluxSupport] using hrev
  · rintro ⟨hv, hv0, hmin⟩
    refine ⟨hv.2, hv0, hv.1, ?_⟩
    intro w hwker hw0 hwnn hsub
    have hw : N.IsNonnegativeGraphCirculation w := ⟨hwnn, hwker⟩
    have hsub' : N.fluxSupport w ⊆ N.fluxSupport v := by
      simpa [CRNT.support, Network.fluxSupport] using hsub
    have hrev := hmin w hw hw0 hsub'
    simpa [CRNT.support, Network.fluxSupport] using hrev

/-- At deficiency zero, every directed-cycle flow is also an elementary stoichiometric
flux mode.  The deficiency-zero hypothesis is necessary in general: without it a graph-cycle
support can contain a smaller stoichiometrically stationary support that is not a graph
circulation. -/
theorem directedCycleFlow_isElementaryFluxMode (N : Network S) (hδ : N.DeficiencyZero)
    {v : N.R → ℝ} (hv : N.IsDirectedCycleFlow v) :
    N.IsElementaryFluxMode v := by
  refine ⟨?_, hv.2.1, ?_⟩
  · exact ⟨hv.1.1, by
      have hfac := congrArg (fun f => f v) N.complexMap_comp_incidenceMap
      simpa [IsStationaryFlux, hv.1.2] using hfac.symm⟩
  · intro w hw hw0 hsub
    have hcycle : N.IsNonnegativeGraphCirculation w := by
      refine ⟨hw.1, ?_⟩
      exact (N.deficiencyZero_iff_stoichCycle_is_graphCycle.mp hδ) w hw.2
    exact hv.2.2 w hcycle hw0 hsub

/-- Every nonnegative graph circulation is a finite sum of directed-cycle flows. -/
theorem graphCirculation_decomposes_into_cycles (N : Network S)
    {v : N.R → ℝ} (hv : N.IsNonnegativeGraphCirculation v) :
    ∃ (m : ℕ) (c : Fin m → (N.R → ℝ)) (a : Fin m → ℝ),
      (∀ i, N.IsDirectedCycleFlow (c i)) ∧
      (∀ i, 0 ≤ a i) ∧
      v = ∑ i, a i • c i := by
  by_cases hv0 : v = 0
  · subst v
    exact ⟨0, Fin.elim0, Fin.elim0, (fun i => Fin.elim0 i),
      (fun i => Fin.elim0 i), by simp⟩
  · obtain ⟨L, hsum, hL⟩ :=
      CRNT.exists_nonnegElementarySum (S := LinearMap.ker N.incidenceMap) hv.2 hv0 hv.1
    let c : Fin L.length → (N.R → ℝ) := fun i => L.get i
    let a : Fin L.length → ℝ := fun _ => 1
    refine ⟨L.length, c, a, ?_, ?_, ?_⟩
    · intro i
      exact (nonnegElementary_incidence_iff_cycle N (c i)).1
        (hL (c i) (List.get_mem L i)).1
    · intro i; exact zero_le_one
    · calc
        v = L.sum := hsum.symm
        _ = ∑ i : Fin L.length, L.get i := (CRNT.sum_get_eq_list_sum L).symm
        _ = ∑ i : Fin L.length, a i • c i := by simp [a, c]

/-- Weak reversibility is equivalent to existence of a directed-cycle-flow cover of all
reaction channels. -/
theorem weaklyReversible_iff_cycleFlow_cover (N : Network S) :
    N.WeaklyReversible ↔
      ∀ r : N.R, ∃ c : N.R → ℝ,
        N.IsDirectedCycleFlow c ∧ c r > 0 := by
  constructor
  · intro hwr r
    obtain ⟨v, hv⟩ := N.exists_positiveGraphCirculation_of_weaklyReversible hwr
    obtain ⟨m, c, a, hc, ha, hsum⟩ :=
      N.graphCirculation_decomposes_into_cycles ⟨fun q => (hv.1 q).le, hv.2⟩
    have hcoord := congrFun hsum r
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hcoord
    have hex : ∃ i : Fin m, 0 < c i r := by
      by_contra hnone
      push Not at hnone
      have hz : ∀ i : Fin m, c i r = 0 := by
        intro i
        exact le_antisymm (hnone i) ((hc i).1.1 r)
      have hsum0 : (∑ i : Fin m, a i * c i r) = 0 := by simp [hz]
      rw [hsum0] at hcoord
      exact (hv.1 r).ne' hcoord
    obtain ⟨i, hi⟩ := hex
    exact ⟨c i, hc i, hi⟩
  · intro hcover
    classical
    choose c hc hcr using hcover
    let v : N.R → ℝ := ∑ q : N.R, c q
    exact N.weaklyReversible_of_positiveGraphCirculation (α := v) ⟨by
      intro r
      simp only [v, Finset.sum_apply]
      apply Finset.sum_pos'
      · intro q _
        exact (hc q).1.1 r
      · exact ⟨r, Finset.mem_univ r, hcr r⟩, by
      simp only [v, map_sum]
      apply Finset.sum_eq_zero
      intro q _
      exact (hc q).1.2⟩

end Network
end CRNT

import CRNT.Dynamics.BoundaryOmegaSiphon
import CRNT.Dynamics.ConservationLaw

/-!
# A boundary ω-limit point's zero set is a *critical* siphon

`isSiphon_zeroSet_of_mem_omegaLimit` shows the zero set `Z(w)` of an ω-limit point is a siphon.
This module sharpens it to *criticality* — `Z(w)` carries no positive conservation law supported
exactly on it — when the trajectory starts at a strictly positive point and `w` lies on the
boundary.

The mechanism is mass conservation. A conservation law `v` (nonnegative, strictly positive
exactly on `Z(w)`, orthogonal to the stoichiometric subspace) has `∑ s, v s · z s` constant on
the affine compatibility class, so `∑ s, v s · w s = ∑ s, v s · x₀ s`. The left side is `0`
(`v` is supported on `Z(w)`, where `w` vanishes; off `Z(w)`, `v` is `0`), while the right side is
strictly positive (`x₀` is positive and `v` is positive somewhere on the nonempty `Z(w)`) — a
contradiction. Hence no such `v`, and `Z(w)` is critical.

This is the second Angeli–De Leenheer–Sontag ingredient: a boundary ω-limit point of a positive
trajectory forces a *critical* siphon. Contrapositively, a network with no critical siphon has no
boundary ω-limit points — every ω-point is strictly positive, which is persistence.

The affine-invariance hypothesis `hωaff` (`ω ⊆ x₀ + stoichSubspace`) and the genuine-field /
nonnegativity / boundedness hypotheses are exactly what the mass-action semiflow construction
supplies.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.BoundaryOmegaSiphon`,
`CRNT.Dynamics.ConservationLaw`.
-/

open Filter Topology
open scoped BigOperators NNReal

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **A boundary ω-limit point of a positive trajectory has a critical zero set.** For a
mass-action semiflow with the genuine-field / nonnegativity / boundedness data of
`isSiphon_zeroSet_of_mem_omegaLimit`, affine invariance of the ω-limit set (`hωaff`), and a
strictly positive start `x₀`, the zero set `P` of any ω-limit point `w` with `P` nonempty is a
*critical* siphon. -/
theorem isCriticalSiphon_zeroSet_of_mem_omegaLimit (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, (y : Concentration S).Nonnegative)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx0pos : x₀.Positive)
    {w : Concentration S} (hw : w ∈ omegaLimit atTop ϕ {x₀})
    {P : Finset S} (hP : ∀ s, s ∈ P ↔ w s = 0) (hPne : P.Nonempty) :
    N.IsCriticalSiphon P := by
  rw [isCriticalSiphon_iff_mem_orthSum]
  refine ⟨hPne, N.isSiphon_zeroSet_of_mem_omegaLimit κ hϕγ hK hmaps hωnn hgenω hw hP, ?_⟩
  rintro ⟨v, hv0, hvP, hvorth⟩
  -- mass conservation pins the `v`-weighted total of `w` to that of `x₀`
  have hconsv : ∑ s, v s * w s = ∑ s, v s * x₀ s := by
    have h0 : ∑ s, v s * (w - x₀) s = 0 := (mem_orthSum.mp hvorth) _ (hωaff w hw)
    have hsplit : ∑ s, (v s * w s - v s * x₀ s) = 0 := by
      rw [← h0]; exact Finset.sum_congr rfl fun s _ => by rw [Pi.sub_apply]; ring
    rw [Finset.sum_sub_distrib] at hsplit; linarith
  -- the total at `w` is zero: `v` is supported on `P`, where `w` vanishes
  have hwz : ∑ s, v s * w s = 0 := by
    refine Finset.sum_eq_zero fun s _ => ?_
    by_cases hsP : s ∈ P
    · rw [(hP s).mp hsP, mul_zero]
    · rw [le_antisymm (not_lt.mp fun h => hsP ((hvP s).mp h)) (hv0 s), zero_mul]
  -- but the total at `x₀` is strictly positive
  have hx0z : 0 < ∑ s, v s * x₀ s := by
    obtain ⟨s₀, hs₀⟩ := hPne
    refine Finset.sum_pos' (fun s _ => mul_nonneg (hv0 s) (hx0pos s).le)
      ⟨s₀, Finset.mem_univ s₀, mul_pos ((hvP s₀).mpr hs₀) (hx0pos s₀)⟩
  have hx0eq : ∑ s, v s * x₀ s = 0 := by rw [← hconsv]; exact hwz
  rw [hx0eq] at hx0z
  exact lt_irrefl 0 hx0z

end Network

end CRNT

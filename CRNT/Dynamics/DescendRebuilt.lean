import CRNT.Dynamics.SiphonDimensionDescent

namespace CRNT

namespace Network

variable {S : Type*}

/-- Round-1's mistake, reproduced deliberately: the same theorem, re-landed. -/
theorem comparableGrowthDescent_iff_omegaPointPositive (N : Network S)
    {ϕ : Flow ℝ≥0 (Concentration S)} {x₀ : Concentration S} {P₀ : Finset S}
    (hP₀crit : N.IsCriticalSiphon P₀) (hP₀carr : N.SiphonCarried ϕ x₀ P₀) :
    N.ComparableGrowthDescent ϕ x₀ ↔
      (∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive) := by
  constructor
  · intro hdesc
    exact N.omegaLimit_positive_of_descend hdesc hP₀crit.1 hP₀crit hP₀carr
  · intro h
    exact ⟨fun _P _hne _hcrit _hcarr => Or.inl h⟩

end Network

end CRNT

import CRNT.Analysis.ConcentrationZero
import CRNT.Dynamics.MassActionField
import CRNT.Equilibria.SteadyState

/-!
# Brouwer mass-action steady state on an invariant convex set

Brouwer's fixed-point theorem, transported to concentration space as the zero-of-field
corollary `CRNT.Analysis.exists_zero_of_displacement_mapsTo_concentration`, specialized to the
mass-action vector field. The field is `C^∞`, hence continuous, so the only remaining input is
that its inward displacement `x ↦ x - massActionVectorField κ x` preserves a nonempty compact
convex set of concentrations; on such a set a mass-action steady state exists.

Depends on: `CRNT.Analysis.ConcentrationZero`,
`CRNT.Dynamics.MassActionField`, `CRNT.Equilibria.SteadyState`.
-/

namespace CRNT.Network

open CRNT

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Brouwer mass-action steady state: a nonempty compact convex set of concentrations whose
mass-action inward displacement maps it into itself contains a mass-action steady state. -/
theorem exists_isMassActionSteadyState_of_displacement_mapsTo
    (N : Network S) (κ : N.RateConstants) {K : Set (Concentration S)}
    (hne : K.Nonempty) (hconv : Convex ℝ K) (hcomp : IsCompact K)
    (hmaps : Set.MapsTo (fun x => x - N.massActionVectorField κ x) K K) :
    ∃ x ∈ K, N.IsMassActionSteadyState κ x := by
  obtain ⟨x, hxK, hx0⟩ := CRNT.Analysis.exists_zero_of_displacement_mapsTo_concentration
    hne hconv hcomp (N.massActionVectorField κ)
    ((N.massActionVectorField_contDiff κ (n := 1)).continuous).continuousOn hmaps
  exact ⟨x, hxK, fun s => congrFun hx0 s⟩

end CRNT.Network

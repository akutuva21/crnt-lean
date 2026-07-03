import CRNT.Dynamics.DifferentialInclusion
import CRNT.Geometry.PolyhedralFan
import CRNT.Kinetics.MassAction

/-!
# Toric inclusion: mass-action flow as a reaction-cone differential inclusion

The mass-action velocity at a point is a nonnegative combination of the reaction vectors, so
it lies in the reaction cone `Network.reactionCone N`. This embeds the genuine mass-action
flow into the crude, constant differential inclusion whose admissible velocities at every
point are exactly the reaction cone — the simplest toric differential inclusion, the substrate
for the program toward the Global Attractor Conjecture of Craciun, _Toric differential
inclusions and a proof of the global attractor conjecture_.

## The reaction-cone inclusion

`massActionVectorField_mem_reactionCone` is the central geometric fact: at any nonnegative
concentration `x`,

```
massActionVectorField κ x = ∑ r, (massActionRate κ r x) • reactionVector r ∈ reactionCone N,
```

because each rate `massActionRate κ r x` is nonnegative there and a pointed cone is closed under
nonnegative-scalar combination of its generators.

The constant field `reactionConeInclusion N := fun _ => reactionCone N` is the reaction-cone
differential inclusion, and `isInclusionSolution_reactionCone` shows that any genuine mass-action
integral curve that stays nonnegative is a selection of it, via
`DifferentialInclusion.IsInclusionSolution.of_ode`.

## Scope

The full toric differential inclusion — the `x`-dependent assignment of dual cones to the cells
of a polyhedral fan, and the trapping of solutions inside invariant regions — is not constructed
here. Only the constant reaction-cone inclusion and the selection embedding are built.

Depends on: `CRNT.Dynamics.DifferentialInclusion`,
`CRNT.Geometry.PolyhedralFan`, `CRNT.Kinetics.MassAction`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The mass-action velocity, written as a single vector of `S → ℝ`, is the nonnegative-rate
combination of the reaction vectors. -/
theorem massActionVectorField_eq_sum (N : Network S) (κ : RateConstants N)
    (x : Concentration S) :
    N.massActionVectorField κ x = ∑ r : N.R, (N.massActionRate κ r x) • (N.reactionVector r) := by
  funext s
  rw [massActionVectorField_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun r _ => rfl

/-- **The mass-action velocity lies in the reaction cone.** At a nonnegative concentration the
mass-action vector field is a nonnegative combination of the reaction vectors, hence a member of
the pointed cone they generate. -/
theorem massActionVectorField_mem_reactionCone (N : Network S) (κ : RateConstants N)
    {x : Concentration S} (hx : Concentration.Nonnegative x) :
    N.massActionVectorField κ x ∈ N.reactionCone := by
  rw [massActionVectorField_eq_sum]
  refine Submodule.sum_mem _ fun r _ => ?_
  exact PointedCone.smul_mem _ (N.massActionRate_nonneg κ r hx)
    (N.reactionVector_mem_reactionCone r)

/-- The **reaction-cone differential inclusion**: the constant set-valued field whose admissible
velocities at every point are exactly the reaction cone. The simplest toric differential
inclusion of the network. -/
def reactionConeInclusion (N : Network S) :
    DifferentialInclusion.Field (S → ℝ) :=
  fun _ => (N.reactionCone : Set (S → ℝ))

@[simp] theorem reactionConeInclusion_apply (N : Network S) (y : S → ℝ) :
    N.reactionConeInclusion y = (N.reactionCone : Set (S → ℝ)) :=
  rfl

/-- **Selection embedding.** A genuine mass-action integral curve that stays nonnegative is a
solution of the reaction-cone differential inclusion: its velocity, being the mass-action field
at a nonnegative point, always lies in the reaction cone. -/
theorem isInclusionSolution_reactionCone (N : Network S) (κ : RateConstants N) {γ : ℝ → (S → ℝ)}
    (hderiv : ∀ t, HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hnonneg : ∀ t, Concentration.Nonnegative (γ t)) :
    DifferentialInclusion.IsInclusionSolution N.reactionConeInclusion γ := by
  intro t
  have hd : deriv γ t = N.massActionVectorField κ (γ t) := (hderiv t).deriv
  refine ⟨?_, ?_⟩
  · rw [hd]; exact hderiv t
  · rw [hd, reactionConeInclusion_apply]
    exact N.massActionVectorField_mem_reactionCone κ (hnonneg t)

end Network

end CRNT

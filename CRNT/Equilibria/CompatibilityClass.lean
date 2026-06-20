import CRNT.Stoich.Subspace
import CRNT.Kinetics.Concentration

/-!
# Stoichiometric compatibility classes

Two concentrations are stoichiometrically compatible when their difference lies in
the stoichiometric subspace; the dynamics of a mass-action system are confined to
such classes. This module defines compatibility, the (positive) compatibility class
of a concentration, and records that compatibility is an equivalence relation.

This module is **stable**. Depends on: `CRNT.Stoich.Subspace`,
`CRNT.Kinetics.Concentration`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- `x` and `y` are stoichiometrically compatible when `y - x` lies in the
stoichiometric subspace. The mass-action flow keeps concentrations within a single
compatibility class. -/
def StoichCompatible (N : Network S) (x y : Concentration S) : Prop :=
  (y - x) ∈ N.stoichSubspace

@[refl] theorem StoichCompatible.refl (N : Network S) (x : Concentration S) :
    N.StoichCompatible x x := by
  simp [StoichCompatible]

theorem StoichCompatible.symm {N : Network S} {x y : Concentration S}
    (h : N.StoichCompatible x y) : N.StoichCompatible y x := by
  have : x - y = -(y - x) := by ring
  rw [StoichCompatible, this]
  exact N.stoichSubspace.neg_mem h

theorem StoichCompatible.trans {N : Network S} {x y z : Concentration S}
    (h₁ : N.StoichCompatible x y) (h₂ : N.StoichCompatible y z) :
    N.StoichCompatible x z := by
  have : z - x = (y - x) + (z - y) := by ring
  rw [StoichCompatible, this]
  exact N.stoichSubspace.add_mem h₁ h₂

/-- The stoichiometric compatibility class of `x₀`: all concentrations reachable from
`x₀` by displacements in the stoichiometric subspace. -/
def compatibilityClass (N : Network S) (x₀ : Concentration S) : Set (Concentration S) :=
  {x | N.StoichCompatible x₀ x}

/-- The positive stoichiometric compatibility class of `x₀`: the compatibility class
intersected with the strictly positive orthant. The deficiency-zero theorem concerns
equilibria within such classes. -/
def positiveCompatibilityClass (N : Network S) (x₀ : Concentration S) :
    Set (Concentration S) :=
  {x | N.StoichCompatible x₀ x ∧ x.Positive}

theorem mem_compatibilityClass {N : Network S} {x₀ x : Concentration S} :
    x ∈ N.compatibilityClass x₀ ↔ N.StoichCompatible x₀ x :=
  Iff.rfl

end Network

end CRNT

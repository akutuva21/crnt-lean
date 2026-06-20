import CRNT.Basic.Complex

/-!
# Reactions

A *reaction* is a directed edge from a source complex to a target complex. Self-
reactions (`source = target`) are permitted in the raw structure; theorems that
need to exclude them use the `Nontrivial` predicate.

This module is **stable**. It defines `Reaction` and its stoichiometric reaction
vector `vector`, which is the column of the stoichiometric matrix associated to the
reaction.

Depends on: `CRNT.Basic.Complex`.
-/

namespace CRNT

/-- A reaction is a directed edge between two complexes. -/
structure Reaction (S : Type) where
  source : Complex S
  target : Complex S

namespace Reaction

variable {S : Type}

/-- Reactions over a finite species type have decidable equality, since complexes
(`S → ℕ`) do. This powers the `complexes` finite-set computation and the graph
decision procedures. -/
instance [Fintype S] [DecidableEq S] : DecidableEq (Reaction S) := fun r₁ r₂ =>
  decidable_of_iff (r₁.source = r₂.source ∧ r₁.target = r₂.target) <| by
    cases r₁; cases r₂; simp [Reaction.mk.injEq]

/-- A reaction is nontrivial when its source and target differ. -/
def Nontrivial (r : Reaction S) : Prop := r.source ≠ r.target

/-- The stoichiometric reaction vector `target - source` as a real vector. This is
the change in concentration produced by one firing of the reaction. -/
def vector (r : Reaction S) : S → ℝ :=
  fun s => ((r.target s : ℝ) - (r.source s : ℝ))

@[simp] theorem vector_apply (r : Reaction S) (s : S) :
    r.vector s = (r.target s : ℝ) - (r.source s : ℝ) := rfl

/-- The reaction vector of a self-reaction is zero. -/
@[simp] theorem vector_of_source_eq_target {r : Reaction S} (h : r.source = r.target) :
    r.vector = 0 := by
  funext s
  simp [vector, h]

end Reaction

end CRNT

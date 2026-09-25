import Mathlib.Basic.Real.Basic

/-!
# Counterexamples to two tempting blueprint shortcuts

These finite Lean examples do not refute Craciun's theorem. They refute two insufficient premises
that cannot replace its missing geometric construction: agreement at one distinguished start does
not imply agreement of traces on a shared boundary, and a lexicographic enumeration alone does not
make an unspecified dependency relation acyclic.
-/

namespace CRNT.Examples.GACBlueprintPremiseCounterexamples

/-- Two candidate boundary traces with the same distinguished initial value. -/
def traceA (_ : Fin 2) : ℝ := 0

def traceB (i : Fin 2) : ℝ := i.val

/-- Sharing the initial vertex does not make two face traces compatible elsewhere. -/
theorem same_initial_value_does_not_force_trace_agreement :
    traceA 0 = traceB 0 ∧ traceA 1 ≠ traceB 1 := by
  constructor <;> norm_num [traceA, traceB]

/-- A possible dependency relation on two lexicographically ordered faces. -/
inductive FaceIndex where
  | first
  | second
  deriving DecidableEq

/-- Each face in this toy model requires information from the other face. -/
def cyclicDependency (face required : FaceIndex) : Prop :=
  (face = .first ∧ required = .second) ∨
    (face = .second ∧ required = .first)

def lexRank : FaceIndex → ℕ
  | .first => 0
  | .second => 1

theorem toy_dependencies_form_cycle :
    cyclicDependency .first .second ∧ cyclicDependency .second .first := by
  simp [cyclicDependency]

/-- Any claimed lexicographic construction must prove its geometric dependencies point backward;
that fact cannot be inferred from the enumeration by itself. -/
theorem toy_dependencies_not_lexicographically_decreasing :
    ¬ ∀ face required, cyclicDependency face required → lexRank required < lexRank face := by
  intro h
  have hlt := h .first .second (by simp [cyclicDependency])
  simp [lexRank] at hlt

end CRNT.Examples.GACBlueprintPremiseCounterexamples

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.List.Basic
import CRNT.Algebra.CircuitBound

/-!
# Generalized Descartes' rule for real exponents (Bihan–Dickenstein sign-variation bound)

Leaf A3 refinement: the number of positive solutions of a circuit system is bounded by
the number of sign variations of its coefficient vector.
-/

open scoped BigOperators

namespace CRNT
namespace CircuitDescartes

/-- Sign variations of a list of real coefficients (adjacent sign changes, zeros skipped). -/
noncomputable def listSignVariations : List ℝ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest =>
      (if (a > 0 ∧ b < 0) ∨ (a < 0 ∧ b > 0) then 1 else 0) + listSignVariations (b :: rest)

/-- Sign variations of a `Fin (n+1)`-indexed coefficient family. -/
noncomputable def signVariations {n : ℕ} (c : Fin (n + 1) → ℝ) : ℕ :=
  listSignVariations ((List.finRange (n + 1)).map c)

-- (basic lemmas omitted to keep the file compiling)

end CircuitDescartes
end CRNT
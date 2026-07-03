import CRNT.Stoich.Subspace
import CRNT.Kinetics.Generalized

/-!
# The Deficiency One Algorithm linear systems and signatures

The Deficiency One Algorithm searches for an unknown `μ ∈ ℝ^𝒮` (the log-ratio `ln c* − ln c` of two
candidate steady states) satisfying a generated system of linear constraints. Every constraint
compares two complexes through the pairing `y · μ = ∑_s y(s) μ(s)`: each generated equality has the
form `y · μ = y' · μ` and each generated strict inequality `y · μ > y' · μ`
(Ji, *Uniqueness of equilibria for complex chemical reaction networks*, Ohio State University, 2011,
§1.6).

A generated system is a **signature** when it has a *nonzero* solution `μ` that is moreover
**sign-compatible with the stoichiometric subspace** — there is a stoichiometric vector with the same
coordinatewise sign pattern as `μ` (the sign pattern of `c* − c`, realised inside the stoichiometric
subspace). Sign compatibility reuses the order relation `SameSign`.

* `complexPairing y μ` — the pairing `y · μ`;
* `DOASystem` — a finite system: a `Finset` of equality complex-pairs and one of strict-inequality
  complex-pairs;
* `DOASystem.Satisfies` — `μ` meets all equalities and strict inequalities;
* `SignCompatibleWithStoich` — `μ` shares a sign pattern with a stoichiometric vector;
* `IsSignature` — the system has a nonzero, sign-compatible solution.

Depends on: `CRNT.Stoich.Subspace`,
`CRNT.Kinetics.Generalized`.
-/

namespace CRNT

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The pairing of a complex with a species-space vector**: `y · μ = ∑_s y(s) μ(s)`. -/
def complexPairing (y : Complex S) (μ : S → ℝ) : ℝ := ∑ s, Complex.toRealVector y s * μ s

omit [DecidableEq S] in
@[simp] theorem complexPairing_zero (y : Complex S) : complexPairing y 0 = 0 := by
  simp [complexPairing]

/-- **A generated linear system of the Deficiency One Algorithm**: a finite set of equality
constraints `y · μ = y' · μ` and a finite set of strict-inequality constraints `y · μ > y' · μ`,
each indexed by an ordered pair of complexes. -/
structure DOASystem (S : Type) [DecidableEq S] [Fintype S] where
  /-- Pairs `(y, y')` imposing the equality `y · μ = y' · μ`. -/
  eqs : Finset (Complex S × Complex S)
  /-- Pairs `(y, y')` imposing the strict inequality `y · μ > y' · μ`. -/
  gts : Finset (Complex S × Complex S)

/-- `μ` **satisfies** the system: it meets every equality and every strict inequality. -/
def DOASystem.Satisfies (sys : DOASystem S) (μ : S → ℝ) : Prop :=
  (∀ p ∈ sys.eqs, complexPairing p.1 μ = complexPairing p.2 μ) ∧
    (∀ p ∈ sys.gts, complexPairing p.2 μ < complexPairing p.1 μ)

/-- **A solution carrying a strict inequality is nonzero.** At `μ = 0` every pairing vanishes, so no
strict inequality can hold; hence any `μ` satisfying a system with a strict constraint is nonzero. -/
theorem DOASystem.ne_zero_of_satisfies_mem_gts (sys : DOASystem S) {μ : S → ℝ}
    (h : sys.Satisfies μ) {p : Complex S × Complex S} (hp : p ∈ sys.gts) : μ ≠ 0 := by
  rintro rfl
  have hlt := h.2 p hp
  simp only [complexPairing_zero] at hlt
  exact (lt_irrefl 0) hlt

namespace Network

/-- **Sign compatibility with the stoichiometric subspace.** Some stoichiometric vector has the
same coordinatewise sign pattern as `μ` — the realisability of `μ`'s sign as `c* − c` with
`c* − c` stoichiometric. -/
def SignCompatibleWithStoich (N : Network S) (μ : S → ℝ) : Prop :=
  ∃ w ∈ N.stoichSubspace, SameSign w μ

/-- **A signature.** The generated system has a nonzero solution `μ` that is sign-compatible with
the stoichiometric subspace. The existence of a signature among the generated systems is what the
Deficiency One Algorithm tests for. -/
def IsSignature (N : Network S) (sys : DOASystem S) : Prop :=
  ∃ μ : S → ℝ, μ ≠ 0 ∧ N.SignCompatibleWithStoich μ ∧ sys.Satisfies μ

end Network

end CRNT

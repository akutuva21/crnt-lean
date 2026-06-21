import CRNT
import CRNT.Examples.Minimal
import CRNT.Examples.ReversiblePair
import CRNT.Examples.IrreversibleChain
import CRNT.Examples.GeneExpression
import CRNT.Examples.Enzyme

/-!
# Smoke tests

Compilation-level tests that exercise the library API on the example networks:
computed complex counts, weak reversibility (and its failure), deficiency zero, and
the structural conservation laws. Building this file (`lake test`) checks that all
stated example properties hold.
-/

open CRNT

-- Computed complex counts reduce as expected.
example : Examples.ReversiblePair.N.numComplexes = 2 := by decide
example : Examples.IrreversibleChain.N.numComplexes = 3 := by decide
example : Examples.Enzyme.N.numComplexes = 3 := by decide
example : Examples.GeneExpression.N.numComplexes = 6 := by decide

#eval Examples.ReversiblePair.N.numComplexes
#eval Examples.IrreversibleChain.N.numComplexes
#eval Examples.Enzyme.N.numComplexes
#eval Examples.GeneExpression.N.numComplexes

-- Weak reversibility holds for the reversible pair and fails for the chain.
example : Examples.ReversiblePair.N.WeaklyReversible := Examples.ReversiblePair.weaklyReversible
example : ¬ Examples.IrreversibleChain.N.WeaklyReversible :=
  Examples.IrreversibleChain.not_weaklyReversible
example : ¬ Examples.Minimal.N.WeaklyReversible := Examples.Minimal.not_weaklyReversible

-- The reversible pair has deficiency zero and satisfies the deficiency-zero hypotheses.
example : Examples.ReversiblePair.N.DeficiencyZero := Examples.ReversiblePair.deficiencyZero
example : Examples.ReversiblePair.N.SatisfiesDeficiencyZeroHypotheses :=
  Examples.ReversiblePair.satisfiesDeficiencyZeroHypotheses

-- Structural conservation laws (parameter-independent).
example (κ : Network.RateConstants Examples.GeneExpression.N)
    (x : Concentration Examples.GeneExpression.Species) :
    Examples.GeneExpression.N.massActionVectorField κ x .DNA = 0 :=
  Examples.GeneExpression.dDNA_dt_eq_zero κ x

example (κ : Network.RateConstants Examples.Enzyme.N)
    (x : Concentration Examples.Enzyme.Species) :
    Examples.Enzyme.N.massActionVectorField κ x .E +
      Examples.Enzyme.N.massActionVectorField κ x .ES = 0 :=
  Examples.Enzyme.total_enzyme_conserved κ x

-- Algebraic reformulation: complex-balanced concentrations are steady states.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (κ : Network.RateConstants N) (x : Concentration S) (h : N.IsComplexBalanced κ x) :
    N.IsMassActionSteadyState κ x :=
  Network.IsComplexBalanced.isMassActionSteadyState N κ h

-- The mass-action vector field factors through the complex space as `Y ∘ A_k ∘ Ψ`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (κ : Network.RateConstants N) (x : Concentration S) :
    N.massActionVectorField κ x =
      N.complexMap (N.kineticMap κ (N.complexMonomialVector x)) :=
  N.massActionVectorField_eq κ x

-- Deficiency rank bridge: rank(∂) = s + dim(ker Y ∩ Im ∂).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) :
    N.incidenceRank = N.stoichRank + Module.finrank ℝ N.deficiencySubspace :=
  N.incidenceRank_eq_stoichRank_add

-- Fact B: the incidence-rank identity rank(∂) = n − ℓ.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) :
    N.incidenceRank + N.numLinkageClasses = N.numComplexes :=
  N.incidenceRank_add_numLinkageClasses

-- Deficiency as a kernel dimension: δ = dim(ker Y ∩ Im ∂).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) :
    N.deficiencyInt = (Module.finrank ℝ N.deficiencySubspace : ℤ) :=
  N.deficiencyInt_eq_finrank_deficiencySubspace

-- Deficiency zero ⟺ the deficiency subspace `ker Y ∩ Im ∂` vanishes (unconditional).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) :
    N.DeficiencyZero ↔ N.deficiencySubspace = ⊥ :=
  N.deficiencyZero_iff_deficiencySubspace_eq_bot

-- Laplacian/conservation property of the kinetic matrix: columns sum to zero.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (κ : Network.RateConstants N) (v : N.ComplexIdx → ℝ) :
    (∑ c : N.ComplexIdx, N.kineticMap κ v c) = 0 :=
  N.kineticMap_sum_eq_zero κ v

-- Reactions stay within a linkage class.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (r : N.R) :
    N.Linked (N.reaction r).source (N.reaction r).target :=
  N.linked_of_reaction r

-- Perron–Frobenius positivity: a nonnegative nonzero fixed vector of a nonnegative,
-- strongly connected matrix is strictly positive.
example {ι : Type} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i) (hb0 : b ≠ 0)
    (hfix : P.mulVec b = b) (hsc : ∀ i j, CRNT.supportReaches P i j) :
    ∀ i, 0 < b i :=
  CRNT.pos_of_nonneg_mulVec_fixed_of_stronglyConnected P hP b hb hb0 hfix hsc

-- Perron–Frobenius existence: a column-stochastic nonnegative matrix has a nonnegative
-- nonzero fixed vector.
example {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (P : Matrix ι ι ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hcol : ∀ j, ∑ i, P i j = 1) :
    ∃ b : ι → ℝ, (∀ i, 0 ≤ b i) ∧ b ≠ 0 ∧ P.mulVec b = b :=
  CRNT.exists_nonneg_mulVec_fixed_of_colStochastic P hP hcol

-- Perron–Frobenius (combined): a strongly connected column-stochastic nonnegative
-- matrix has a strictly positive fixed vector.
example {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (P : Matrix ι ι ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hcol : ∀ j, ∑ i, P i j = 1)
    (hsc : ∀ i j, CRNT.supportReaches P i j) :
    ∃ b : ι → ℝ, (∀ i, 0 < b i) ∧ P.mulVec b = b :=
  CRNT.exists_pos_mulVec_fixed_of_stronglyConnected P hP hcol hsc

-- Milestone 3: a weakly reversible network's kinetic matrix has a strictly positive
-- kernel vector.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (hwr : N.WeaklyReversible) (κ : Network.RateConstants N) :
    ∃ b : N.ComplexIdx → ℝ, (∀ c, 0 < b c) ∧ N.kineticMap κ b = 0 :=
  CRNT.PositiveKernel.weaklyReversible_exists_positive_kernelVector N hwr κ

-- Milestone 4 (uniqueness half of Birch): positive vectors in the same coset of `S`
-- with `S`-orthogonal log-ratio are equal.
example {ι : Type} [Fintype ι] (S : Submodule ℝ (ι → ℝ)) {x y : ι → ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hxy : x - y ∈ S)
    (horth : ∀ s ∈ S, ∑ i, (Real.log (x i) - Real.log (y i)) * s i = 0) :
    x = y :=
  CRNT.birch_uniqueness S hx hy hxy horth

-- Horn–Jackson Lyapunov function: positive-definite about the reference equilibrium.
example {ι : Type} [Fintype ι] {xstar x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hxs : ∀ i, 0 < xstar i) (hne : x ≠ xstar) :
    0 < CRNT.relEntropy xstar x :=
  CRNT.relEntropy_pos_of_ne hx hxs hne

-- Fenchel–Young / Birch dual objective bounded below (well-posedness anchor for the
-- minimization underlying Birch existence).
example {ι : Type} [Fintype ι] {xstar c : ι → ℝ}
    (hxs : ∀ i, 0 < xstar i) (hc : ∀ i, 0 < c i) (w : ι → ℝ) :
    (∑ i, (c i - c i * Real.log (c i / xstar i))) ≤ CRNT.birchDual xstar c w :=
  CRNT.birchDual_ge hxs hc w

-- Coercivity of the Birch dual objective: bounded sublevel sets.
example {ι : Type} [Fintype ι] {xstar c : ι → ℝ}
    (hxs : ∀ i, 0 < xstar i) (hc : ∀ i, 0 < c i) (M : ℝ) :
    ∃ R : ℝ, ∀ w : ι → ℝ, CRNT.birchDual xstar c w ≤ M → ∀ i, |w i| ≤ R :=
  CRNT.birchDual_coercive hxs hc M

-- The Birch dual objective attains a minimum over any (finite-dimensional) subspace.
example {ι : Type} [Fintype ι] {xstar c : ι → ℝ}
    (hxs : ∀ i, 0 < xstar i) (hc : ∀ i, 0 < c i) (T : Submodule ℝ (ι → ℝ)) :
    ∃ ŵ ∈ T, ∀ w ∈ T, CRNT.birchDual xstar c ŵ ≤ CRNT.birchDual xstar c w :=
  CRNT.birchDual_exists_isMinOn hxs hc T

-- First-order optimality of the dual minimizer: the gradient `x* ⊙ exp(ŵ) − c` is
-- orthogonal to the minimization subspace.
example {ι : Type} [Fintype ι] {xstar c : ι → ℝ} (T : Submodule ℝ (ι → ℝ))
    {ŵ : ι → ℝ} (hŵT : ŵ ∈ T)
    (hŵmin : ∀ w ∈ T, CRNT.birchDual xstar c ŵ ≤ CRNT.birchDual xstar c w) :
    ∀ v ∈ T, ∑ i, (xstar i * Real.exp (ŵ i) - c i) * v i = 0 :=
  CRNT.birchDual_firstOrder T hŵT hŵmin

-- The dot-product double orthogonal complement returns the original subspace.
example {ι : Type} [Fintype ι] (S : Submodule ℝ (ι → ℝ)) :
    CRNT.orthSum (CRNT.orthSum S) = S :=
  CRNT.orthSum_orthSum S

-- Existence half of Birch's theorem: every positive compatibility class `c + S` contains
-- a positive point with `S`-orthogonal log-ratio (the complex-balanced equilibrium).
example {ι : Type} [Fintype ι] (S : Submodule ℝ (ι → ℝ)) {xstar c : ι → ℝ}
    (hxs : ∀ i, 0 < xstar i) (hc : ∀ i, 0 < c i) :
    ∃ x : ι → ℝ, (∀ i, 0 < x i) ∧ x - c ∈ S ∧
      ∀ s ∈ S, ∑ i, (Real.log (x i) - Real.log (xstar i)) * s i = 0 :=
  CRNT.birch_existence S hxs hc

-- Birch's theorem (existence + uniqueness): the positive compatibility class `c + S` has
-- a unique point with `S`-orthogonal log-ratio relative to a positive reference `x*`.
example {ι : Type} [Fintype ι] (S : Submodule ℝ (ι → ℝ)) {xstar c : ι → ℝ}
    (hxs : ∀ i, 0 < xstar i) (hc : ∀ i, 0 < c i) :
    ∃ x : ι → ℝ, (∀ i, 0 < x i) ∧ x - c ∈ S ∧
      (∀ s ∈ S, ∑ i, (Real.log (x i) - Real.log (xstar i)) * s i = 0) ∧
      ∀ y : ι → ℝ, (∀ i, 0 < y i) → y - c ∈ S →
        (∀ s ∈ S, ∑ i, (Real.log (y i) - Real.log (xstar i)) * s i = 0) → y = x :=
  CRNT.birch S hxs hc

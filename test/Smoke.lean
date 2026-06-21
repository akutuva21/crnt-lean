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
open scoped NNReal

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

-- Toric inclusion: relative to a complex-balanced reference, positive points with
-- `S`-orthogonal log-ratio are complex-balanced.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {x xstar : Concentration S} (hx : x.Positive) (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (horth : (fun s => Real.log (x s) - Real.log (xstar s)) ∈ CRNT.orthSum N.stoichSubspace) :
    N.IsComplexBalanced κ x :=
  N.complexBalanced_of_logRatio_orthogonal κ hx hxs hcb horth

-- Given one complex-balanced equilibrium, every positive compatibility class contains a
-- complex-balanced equilibrium.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) :
    ∃ x ∈ N.positiveCompatibilityClass x₀, N.IsComplexBalanced κ x :=
  N.exists_isComplexBalanced_in_positiveClass κ hxs hcb hx0

-- Perron–Frobenius uniqueness: a strongly connected nonnegative matrix's positive fixed
-- vector is unique up to scaling.
example {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (P : Matrix ι ι ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (a v : ι → ℝ) (ha : ∀ i, 0 < a i)
    (hfa : P.mulVec a = a) (hfv : P.mulVec v = v) (hsc : ∀ i j, CRNT.supportReaches P i j) :
    ∃ t : ℝ, v = t • a :=
  CRNT.mulVec_fixed_unique_of_stronglyConnected P hP a v ha hfa hfv hsc

-- Converse toric inclusion: for a weakly reversible network, two positive complex-balanced
-- concentrations have `S`-orthogonal log-ratio.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : Network.RateConstants N) {x xstar : Concentration S} (hx : x.Positive)
    (hxs : xstar.Positive) (hcbx : N.IsComplexBalanced κ x) (hcbs : N.IsComplexBalanced κ xstar) :
    (fun s => Real.log (x s) - Real.log (xstar s)) ∈ CRNT.orthSum N.stoichSubspace :=
  N.logRatio_orthogonal_of_complexBalanced hwr κ hx hxs hcbx hcbs

-- Uniqueness of the complex-balanced equilibrium in a positive compatibility class.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : Network.RateConstants N) {x₀ x y : Concentration S}
    (hx : x ∈ N.positiveCompatibilityClass x₀) (hy : y ∈ N.positiveCompatibilityClass x₀)
    (hcbx : N.IsComplexBalanced κ x) (hcby : N.IsComplexBalanced κ y) : x = y :=
  N.isComplexBalanced_unique_in_positiveClass hwr κ hx hy hcbx hcby

-- Existence of a complex-balanced equilibrium for a weakly reversible deficiency-zero
-- network (the step that consumes δ = 0).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (hδ : N.DeficiencyZero) (κ : Network.RateConstants N) :
    ∃ x : Concentration S, x.Positive ∧ N.IsComplexBalanced κ x :=
  N.exists_isComplexBalanced hwr hδ κ

-- **The Feinberg–Horn–Jackson deficiency-zero theorem.**
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) :
    N.SatisfiesDeficiencyZeroHypotheses → N.DeficiencyZeroConclusion :=
  N.deficiencyZeroTheorem

-- The reversible pair `A ⇌ B` satisfies the deficiency-zero conclusion: each positive
-- compatibility class has a unique complex-balanced equilibrium.
example : Examples.ReversiblePair.N.DeficiencyZeroConclusion :=
  Examples.ReversiblePair.N.deficiencyZeroTheorem
    Examples.ReversiblePair.satisfiesDeficiencyZeroHypotheses

-- Dissipation: the relative entropy's directional derivative along the vector field is ≤ 0.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {x xstar : Concentration S} (hx : x.Positive) (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) :
    (∑ s, (Real.log (x s) - Real.log (xstar s)) * N.massActionVectorField κ x s) ≤ 0 :=
  N.dissipation_nonpos κ hx hxs hcb

-- Vanishing dissipation characterizes complex balance.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {x xstar : Concentration S} (hx : x.Positive) (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (h0 : (∑ s, (Real.log (x s) - Real.log (xstar s)) * N.massActionVectorField κ x s) = 0) :
    N.IsComplexBalanced κ x :=
  N.complexBalanced_of_dissipation_eq_zero κ hx hxs hcb h0

-- Lyapunov descent: relEntropy is nonincreasing along positive mass-action solutions.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {γ : ℝ → Concentration S} (hpos : ∀ t, (γ t).Positive)
    (hsol : ∀ t s, HasDerivAt (fun τ => γ τ s) (N.massActionVectorField κ (γ t) s) t) :
    Antitone (fun t => CRNT.relEntropy xstar (γ t)) :=
  N.relEntropy_antitone_along_solution κ hxs hcb hpos hsol

-- The mass-action vector field is smooth (regularity for ODE existence theory).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N) :
    ContDiff ℝ ⊤ (N.massActionVectorField κ) :=
  N.massActionVectorField_contDiff κ

-- Boundary faces of the orthant are non-attracting.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {x : Concentration S} (hx : x.Nonnegative) {s : S} (hs : x s = 0) :
    0 ≤ N.massActionVectorField κ x s :=
  N.massActionVectorField_nonneg_of_zero κ hx hs

-- Local existence of mass-action solutions.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (x₀ : Concentration S) (t₀ : ℝ) :
    ∃ γ : ℝ → Concentration S, γ t₀ = x₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), HasDerivAt γ (N.massActionVectorField κ (γ t)) t :=
  N.exists_local_solution κ x₀ t₀

-- Global existence: a bounded Lipschitz autonomous field has a global integral curve.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : E → E}
    {K M : ℝ≥0} (hl : LipschitzWith K f) (hb : ∀ x, ‖f x‖ ≤ M) (x₀ : E) :
    ∃ γ : ℝ → E, γ 0 = x₀ ∧ ∀ t : ℝ, HasDerivAt γ (f (γ t)) t :=
  ODE.exists_isIntegralCurve hl hb x₀

-- The flow of a bounded Lipschitz autonomous field: a forward semiflow whose orbits solve
-- the ODE.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : E → E}
    {K M : ℝ≥0} (hl : LipschitzWith K f) (hb : ∀ x, ‖f x‖ ≤ M) :
    ∃ (ϕ : Flow ℝ≥0 E) (γ : E → ℝ → E), (∀ x, γ x 0 = x) ∧
      (∀ x t, HasDerivAt (γ x) (f (γ x t)) t) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) :=
  ODE.exists_flow hl hb

-- Continuous dependence on initial conditions for an autonomous Lipschitz ODE.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → E} {K : ℝ≥0}
    (hf : LipschitzWith K f) {γ₁ γ₂ : ℝ → E} (h₁ : ∀ t, HasDerivAt γ₁ (f (γ₁ t)) t)
    (h₂ : ∀ t, HasDerivAt γ₂ (f (γ₂ t)) t) {t : ℝ} (ht : 0 ≤ t) :
    dist (γ₁ t) (γ₂ t) ≤ dist (γ₁ 0) (γ₂ 0) * Real.exp (K * t) :=
  ODE.dist_le_of_isIntegralCurve hf h₁ h₂ ht

-- LaSalle's invariance principle for forward semiflows.
example {α : Type} [TopologicalSpace α] (ϕ : Flow ℝ≥0 α) {V : α → ℝ} (hV : Continuous V)
    (x : α) {K : Set α} (hK : IsCompact K)
    (habs : ∃ v ∈ (Filter.atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x}) ⊆ K)
    (hmono : ∀ s t : ℝ≥0, s ≤ t → V (ϕ t x) ≤ V (ϕ s x)) :
    ∃ c : ℝ, (omegaLimit Filter.atTop ϕ {x}).Nonempty ∧
      IsInvariant ϕ (omegaLimit Filter.atTop ϕ {x}) ∧
      ∀ y ∈ omegaLimit Filter.atTop ϕ {x}, V y = c :=
  Flow.laSalle ϕ hV x hK habs hmono

-- Coercivity of the relative entropy: sublevel sets are bounded coordinatewise.
example {S : Type} [DecidableEq S] [Fintype S] {xstar x : Concentration S}
    (hxs : xstar.Positive) (hx : x.Nonnegative) {C : ℝ} (h : CRNT.relEntropy xstar x ≤ C)
    (s : S) : x s ≤ max (Real.exp 2 * xstar s) C :=
  Network.relEntropy_coord_le hxs hx h s

-- First-crossing positivity: `y' ≥ −L·y` (where positive) keeps `y` positive on `[0, ∞)`.
example {y : ℝ → ℝ} {L : ℝ} (hd : ∀ t, HasDerivAt y (deriv y t) t)
    (hineq : ∀ t, 0 < y t → -L * y t ≤ deriv y t) (h0 : 0 < y 0) :
    ∀ t, 0 ≤ t → 0 < y t :=
  CRNT.pos_of_forward_deriv_ge hd hineq h0

-- Bounded-Lipschitz cutoff of the mass-action field (so the flow construction applies).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ (K M : ℝ≥0), LipschitzWith K (N.massActionVectorField κ ∘ Network.clampBox B) ∧
      (∀ x, ‖(N.massActionVectorField κ ∘ Network.clampBox B) x‖ ≤ M) :=
  N.exists_cutoff κ hB

-- Local asymptotic stability: the complex-balanced equilibrium's ω-limit set is `{x*}`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : Network.RateConstants N) {xstar x₀ : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) (hx0 : x₀.Positive)
    (hx0compat : N.StoichCompatible x₀ xstar)
    (hloc : ∀ s, CRNT.relEntropy xstar x₀ < xstar s) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit Filter.atTop ϕ {x₀} = {xstar} :=
  N.omegaLimit_eq_singleton_of_local hwr κ hxs hcb hx0 hx0compat hloc

-- Deficiency-one statement interface: the existence conclusion refines uniqueness.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) :
    N.DeficiencyOneExistence → N.DeficiencyOneUniqueness :=
  N.deficiencyOneUniqueness_of_existence

-- Deficiency-one condition (iii): the number of terminal strong linkage classes equals the
-- number of linkage classes.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (h : N.OneTerminalSLCPerLinkageClass) : N.numTerminalSLC = N.numLinkageClasses :=
  N.numTerminalSLC_eq_numLinkageClasses h

-- The kinetic map is block diagonal over linkage classes: restriction to a class commutes
-- with `A_k`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (q : Quotient N.linkedSetoid) (v : N.ComplexIdx → ℝ) :
    N.kineticMap κ (N.restrictToClass q v) = N.restrictToClass q (N.kineticMap κ v) :=
  N.kineticMap_restrictToClass κ q v

-- The kernel of the kinetic map decomposes over linkage classes.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (v : N.ComplexIdx → ℝ) :
    N.kineticMap κ v = 0 ↔ ∀ q, N.kineticMap κ (N.restrictToClass q v) = 0 :=
  N.kineticMap_eq_zero_iff_forall_restrictToClass κ v

-- A steady state's kinetic image lies in the deficiency subspace `ker Y ⊓ Im ∂`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {x : Concentration S} (hx : N.IsMassActionSteadyState κ x) :
    N.kineticMap κ (N.complexMonomialVector x) ∈ N.deficiencySubspace :=
  N.kineticMap_complexMonomial_mem_deficiencySubspace κ hx

-- In a deficiency-zero network every mass-action steady state is complex-balanced.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hδ : N.DeficiencyZero)
    (κ : Network.RateConstants N) {x : Concentration S} (hx : N.IsMassActionSteadyState κ x) :
    N.IsComplexBalanced κ x :=
  N.isComplexBalanced_of_steadyState_of_deficiencyZero hδ κ hx

-- Deficiency one pins every steady state's kinetic image to a common line through 0.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (hδ : N.DeficiencyOne) :
    ∃ g : N.ComplexIdx → ℝ, g ≠ 0 ∧ ∀ ⦃x : Concentration S⦄,
      N.IsMassActionSteadyState κ x →
        ∃ c : ℝ, N.kineticMap κ (N.complexMonomialVector x) = c • g :=
  N.exists_kineticImage_smul_of_deficiencyOne κ hδ

-- A deficiency vector sums to zero over each linkage class.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) {g : N.ComplexIdx → ℝ}
    (hg : g ∈ N.deficiencySubspace) (q : Quotient N.linkedSetoid) :
    ∑ c, N.restrictToClass q g c = 0 :=
  N.sum_restrictToClass_eq_zero_of_mem_deficiencySubspace hg q

-- Each linkage class supports a nonnegative nonzero kernel vector of the kinetic map.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (θ : Quotient N.linkedSetoid) :
    ∃ b : N.ComplexIdx → ℝ, (∀ c, 0 ≤ b c) ∧ b ≠ 0 ∧
      (∀ c, N.classOf c ≠ θ → b c = 0) ∧ N.kineticMap κ b = 0 :=
  N.exists_nonneg_kernelVector_on_class κ θ

-- The kinetic-map kernel has dimension at least the number of linkage classes.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N) :
    N.numLinkageClasses ≤ Module.finrank ℝ (LinearMap.ker (N.kineticMap κ)) :=
  N.numLinkageClasses_le_finrank_ker_kineticMap κ

-- Dually, the rank of the kinetic map is at most `n − ℓ`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N) :
    Module.finrank ℝ (LinearMap.range (N.kineticMap κ)) + N.numLinkageClasses ≤ N.numComplexes :=
  N.finrank_range_kineticMap_add_numLinkageClasses_le κ

-- Every linkage class of a weakly reversible network carries a strictly positive kernel
-- vector of the kinetic map.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : Network.RateConstants N) (θ : Quotient N.linkedSetoid) :
    ∃ b : N.ComplexIdx → ℝ, (∀ c, N.classOf c = θ → 0 < b c) ∧
      (∀ c, N.classOf c ≠ θ → b c = 0) ∧ N.kineticMap κ b = 0 :=
  N.exists_pos_kernelVector_on_class_of_weaklyReversible hwr κ θ

-- On a strongly connected class the per-class kernel mode is unique up to scaling.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (θ : Quotient N.linkedSetoid)
    (hθ : ∀ c c' : N.ComplexIdx, N.classOf c = θ → N.classOf c' = θ → N.Reaches c.val c'.val)
    {a v : N.ComplexIdx → ℝ}
    (hapos : ∀ c, N.classOf c = θ → 0 < a c) (haoff : ∀ c, N.classOf c ≠ θ → a c = 0)
    (haker : N.kineticMap κ a = 0)
    (hvoff : ∀ c, N.classOf c ≠ θ → v c = 0) (hvker : N.kineticMap κ v = 0) :
    ∃ t : ℝ, v = t • a :=
  N.perClass_kernel_unique κ θ hθ hapos haoff haker hvoff hvker

-- For a weakly reversible network, the kinetic-map kernel has dimension exactly ℓ.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : Network.RateConstants N) :
    Module.finrank ℝ (LinearMap.ker (N.kineticMap κ)) = N.numLinkageClasses :=
  N.finrank_ker_kineticMap_eq_of_weaklyReversible hwr κ

-- For a weakly reversible network, the kinetic image fills the cut space `Im ∂`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : Network.RateConstants N) :
    LinearMap.range (N.kineticMap κ) = LinearMap.range N.incidenceMap :=
  N.range_kineticMap_eq_range_incidenceMap_of_weaklyReversible hwr κ

-- A reaction-closed set of complexes supports a nonnegative nonzero kernel vector of `A_k`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (D : N.ComplexIdx → Prop) (hclosed : ∀ r, D (N.sourceIdx r) → D (N.targetIdx r))
    {c0 : N.ComplexIdx} (hc0 : D c0) :
    ∃ b : N.ComplexIdx → ℝ, (∀ c, 0 ≤ b c) ∧ b ≠ 0 ∧
      (∀ c, ¬ D c → b c = 0) ∧ N.kineticMap κ b = 0 :=
  N.exists_nonneg_kernelVector_on_closed κ D hclosed hc0

-- In particular, each terminal strong linkage class supports such a kernel vector.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {c : N.ComplexIdx} (hc : N.IsTerminalSLC c.val) :
    ∃ b : N.ComplexIdx → ℝ, (∀ c', 0 ≤ b c') ∧ b ≠ 0 ∧
      (∀ c', ¬ N.StronglyLinked c.val c'.val → b c' = 0) ∧ N.kineticMap κ b = 0 :=
  N.exists_nonneg_kernelVector_on_terminalSLC κ hc

-- The terminal-SLC kernel mode is strictly positive on the class and zero off it.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {c : N.ComplexIdx} (hc : N.IsTerminalSLC c.val) :
    ∃ b : N.ComplexIdx → ℝ, (∀ c', N.StronglyLinked c.val c'.val → 0 < b c') ∧
      (∀ c', ¬ N.StronglyLinked c.val c'.val → b c' = 0) ∧ N.kineticMap κ b = 0 :=
  N.exists_pos_kernelVector_on_terminalSLC κ hc

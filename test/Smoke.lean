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
open scoped Finset

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

-- The kinetic-map kernel has dimension at least the number of terminal strong linkage classes.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N) :
    N.numTerminalSLC ≤ Module.finrank ℝ (LinearMap.ker (N.kineticMap κ)) :=
  N.numTerminalSLC_le_finrank_ker_kineticMap κ

-- Every complex reaches a terminal strong linkage class.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (c : N.ComplexIdx) :
    ∃ d : N.ComplexIdx, N.Reaches c.val d.val ∧ N.IsTerminalSLC d.val :=
  N.exists_terminal_reachable c

-- A nonnegative kernel vector of the kinetic map drains to terminal strong linkage classes.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {b : N.ComplexIdx → ℝ} (hbnn : ∀ c, 0 ≤ b c) (hbker : N.kineticMap κ b = 0)
    {c : N.ComplexIdx} (hbc : 0 < b c) : N.IsTerminalSLC c.val :=
  N.isTerminalSLC_of_pos_kernel κ hbnn hbker hbc

-- Weak reversibility ⟺ the kinetic map has a strictly positive kernel vector.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N) :
    N.WeaklyReversible ↔ ∃ b : N.ComplexIdx → ℝ, (∀ c, 0 < b c) ∧ N.kineticMap κ b = 0 :=
  N.weaklyReversible_iff_exists_pos_kernelVector κ

-- The terminal-SLC kernel mode is unique up to scaling.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {c : N.ComplexIdx} {a v : N.ComplexIdx → ℝ}
    (hapos : ∀ c', N.StronglyLinked c.val c'.val → 0 < a c')
    (haoff : ∀ c', ¬ N.StronglyLinked c.val c'.val → a c' = 0) (haker : N.kineticMap κ a = 0)
    (hvoff : ∀ c', ¬ N.StronglyLinked c.val c'.val → v c' = 0) (hvker : N.kineticMap κ v = 0) :
    ∃ t : ℝ, v = t • a :=
  N.terminalSLC_kernel_unique κ hapos haoff haker hvoff hvker

-- Parallel wave: the new structural modules exercised on the library API.

-- Track K.1 (ACR): a pinned monomial ratio yields absolute concentration robustness in `s`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (s : S)
    (H : N.ShinarFeinbergHypotheses s) (hpin : H.PinnedRatio)
    (hne : ∃ (κ : Network.RateConstants N) (x : Concentration S),
      x.Positive ∧ N.IsMassActionSteadyState κ x) :
    N.HasACR s :=
  Network.HasACR.of_pinnedRatio H hpin hne

-- Track M: the computable stoichiometric-rank lower bound is sound.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) :
    N.computeStoichRankLB ≤ N.stoichRank :=
  N.computeStoichRankLB_le_stoichRank

-- Track B: the fully open extension satisfies `n⁺ = ℓ⁺ + card S + δ⁺`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) :
    N.fullyOpen.numComplexes
      = N.fullyOpen.numLinkageClasses + Fintype.card S + N.fullyOpen.deficiency :=
  N.numComplexes_fullyOpen_eq_add

-- Track H.1: the generalized (kinetic-order) Birch existence statement.
example {ι : Type} [Fintype ι] (T : Submodule ℝ (ι → ℝ)) {xstar c : ι → ℝ}
    (hxs : ∀ i, 0 < xstar i) (hc : ∀ i, 0 < c i) :
    ∃ x : ι → ℝ, (∀ i, 0 < x i) ∧ x - c ∈ T ∧
      (fun i => Real.log (x i) - Real.log (xstar i)) ∈ CRNT.orthSum T :=
  CRNT.gen_birch_existence T hxs hc

-- Track D.2: the species-reaction graph is bipartite.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) : N.srGraph.IsBipartite :=
  N.srGraph_isBipartite

-- Track D.1: an injective mass-action network has at most one steady state per positive class.
example {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {κ : Network.RateConstants N}
    (h : (N.massActionKinetics κ).Injective) {x₀ x y : Concentration S}
    (hx : x ∈ N.positiveCompatibilityClass x₀) (hy : y ∈ N.positiveCompatibilityClass x₀)
    (hsx : N.IsMassActionSteadyState κ x) (hsy : N.IsMassActionSteadyState κ y) : x = y :=
  Network.massAction_subsingleton_steadyState_of_injective h hx hy hsx hsy

-- Parallel wave 2: deciders, motifs, siphons, composition exercised on the API.

-- Track K.2 (adaptation): the antithetic motif pins its output to a setpoint at steady state.
example (κ : Network.RateConstants CRNT.Design.Adaptation.N)
    (x : Concentration CRNT.Design.Adaptation.Species)
    (hss : CRNT.Design.Adaptation.N.IsMassActionSteadyState κ x) :
    κ.k .sense * x CRNT.Design.Adaptation.Species.X = κ.k .ref :=
  CRNT.Design.Adaptation.setpoint κ x hss

-- Track M (ACR companion): the Shinar-Feinberg structural hypotheses imply the decidable pair.
example {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {s : S}
    (H : N.ShinarFeinbergHypotheses s) : N.HasShinarFeinbergPair s :=
  Network.HasShinarFeinbergPair.of_hypotheses H

-- Track E (siphons): siphons are closed under union.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) {P Q : Finset S}
    (hP : N.IsSiphon P) (hQ : N.IsSiphon Q) : N.IsSiphon (P ∪ Q) :=
  N.union_isSiphon hP hQ

-- Track L (composition): the stoichiometric subspace of an interconnection is the join.
example {S : Type} [DecidableEq S] [Fintype S] (N₁ N₂ : Network S) :
    (N₁.interconnect N₂).stoichSubspace = N₁.stoichSubspace ⊔ N₂.stoichSubspace :=
  N₁.stoichSubspace_interconnect N₂

-- Track D.2 (decidable cycles): undirected cycle existence is decidable on a finite graph.
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Decidable G.HasCycle :=
  inferInstance

-- Track C.2: the one-terminal-SLC-per-linkage-class condition is decidable.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) :
    Decidable N.OneTerminalSLCPerLinkageClass :=
  inferInstance

-- Phase 2 localization: a mass-action steady state is complex-balanced on every
-- deficiency-zero linkage class (deficiency-one analysis localizes to the deficient class).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (h : N.DeficiencyOneConditions)
    (κ : Network.RateConstants N) {x : Concentration S} (hx : N.IsMassActionSteadyState κ x)
    {q : Quotient N.linkedSetoid} (hq : N.linkageDeficiency q = 0) :
    N.restrictToClass q (N.kineticMap κ (N.complexMonomialVector x)) = 0 :=
  N.restrictToClass_kineticImage_eq_zero h κ hx hq

-- The deficiency subspace decomposes over linkage classes (the structural backbone).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (h : N.DeficiencyOneConditions) :
    N.deficiencySubspace = ⨆ q, N.linkageDeficiencySubspace q :=
  N.deficiencySubspace_eq_iSup h

-- Sign-vector layer: the sign vectors of a subspace and its dot-product orthogonal
-- complement are orthogonal (oriented-matroid covector orthogonality).
example {ι : Type} [Fintype ι] {S : Submodule ℝ (ι → ℝ)} {u w : ι → ℝ}
    (hu : u ∈ S) (hw : w ∈ CRNT.orthSum S) :
    CRNT.SignVector.Orthogonal (CRNT.signVector u) (CRNT.signVector w) :=
  CRNT.orthogonal_signVector_of_mem_orthSum hu hw

-- Conformal vectors in complementary subspaces have pointwise-vanishing products.
example {ι : Type} [Fintype ι] {S : Submodule ℝ (ι → ℝ)} {u w : ι → ℝ}
    (hu : u ∈ S) (hw : w ∈ CRNT.orthSum S) (hc : CRNT.Conformal u w) (i : ι) :
    u i * w i = 0 :=
  CRNT.mul_eq_zero_of_conformal_mem_orthSum hu hw hc i

-- Same-sign is equality of sign vectors.
example {ι : Type} {u v : ι → ℝ} : CRNT.SameSign u v ↔ CRNT.signVector u = CRNT.signVector v :=
  CRNT.sameSign_iff_signVector_eq

-- Deficiency-one uniqueness reduces to the log-ratio (toric) characterization, via the
-- Birch sign argument. This isolates the substantive remaining obligation.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (h : N.LogRatioCharacterization) : N.DeficiencyOneUniqueness :=
  N.deficiencyOneUniqueness_of_logRatio h

-- The toric condition equals constancy of the log-monomial ratio along reactions:
-- log-ratio ⊥ stoichiometric subspace ↔ Φ(target) = Φ(source) for every reaction.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) {x y : Concentration S}
    (hx : x.Positive) (hy : y.Positive) :
    (fun s => Real.log (x s) - Real.log (y s)) ∈ CRNT.orthSum N.stoichSubspace ↔
      ∀ r, N.logMonomialRatio x y (N.targetIdx r) = N.logMonomialRatio x y (N.sourceIdx r) :=
  N.logRatio_mem_orthSum_iff hx hy

-- On a deficiency-zero linkage class the log-monomial ratio is constant (complex balancing).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (h : N.DeficiencyOneHypotheses)
    (κ : Network.RateConstants N) {x y : Concentration S} (hx : x.Positive) (hy : y.Positive)
    (hxss : N.IsMassActionSteadyState κ x) (hyss : N.IsMassActionSteadyState κ y)
    {q : Quotient N.linkedSetoid} (hq : N.linkageDeficiency q = 0)
    {c c' : N.ComplexIdx} (hc : N.classOf c = q) (hc' : N.classOf c' = q) :
    N.logMonomialRatio x y c = N.logMonomialRatio x y c' :=
  N.logMonomialRatio_const_of_deficiencyZeroClass h κ hx hy hxss hyss hq hc hc'

-- Deficiency-one uniqueness reduces to log-ratio constancy on the single deficient class.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (h : N.DeficiencyOneHypotheses)
    (hdef : N.DeficientClassRatioConst) : N.DeficiencyOneUniqueness :=
  N.deficiencyOneUniqueness_of_deficientClassRatioConst h hdef

-- Signed drainage: a kernel vector of A_k vanishes at every non-terminal complex.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {v : N.ComplexIdx → ℝ} (hv : N.kineticMap κ v = 0)
    {c : N.ComplexIdx} (hc : ¬ N.IsTerminalSLC c.val) : v c = 0 :=
  N.kineticMap_eq_zero_of_not_terminal κ hv hc

-- The deficient-class kernel relation (no strong-connectivity hypothesis): on the
-- deficiency-one class, two steady states satisfy cy·Ψx − cx·Ψy = λ·b pointwise, with b
-- positive on the terminal strong linkage class — reducing the sign argument to forcing λ = 0.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hδ : N.DeficiencyOne)
    (h : N.DeficiencyOneHypotheses) (κ : Network.RateConstants N) {θ : Quotient N.linkedSetoid}
    {x y : Concentration S} (hxss : N.IsMassActionSteadyState κ x)
    (hyss : N.IsMassActionSteadyState κ y) :
    ∃ (b : N.ComplexIdx → ℝ) (cx cy lam : ℝ),
      (∀ c, N.classOf c = θ → N.IsTerminalSLC c.val → 0 < b c) ∧
      ∀ c, N.classOf c = θ →
        cy * N.complexMonomialVector x c - cx * N.complexMonomialVector y c = lam * b c :=
  N.deficientClass_kernel_relation hδ h κ hxss hyss

-- Substochastic Perron–Frobenius: a column-substochastic matrix whose every index reaches a
-- leak (a strictly-substochastic column) has only the zero fixed vector.
example {ι : Type} [Fintype ι] (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (hcol : ∀ j, ∑ i, M i j ≤ 1)
    (hreach : ∀ j, ∃ ℓ, CRNT.supportReaches M ℓ j ∧ ∑ i, M i ℓ < 1)
    {v : ι → ℝ} (hv : M.mulVec v = v) : v = 0 :=
  CRNT.mulVec_fixed_eq_zero_of_substochastic M hM hcol hreach hv

-- Feinberg's Lemma (the deficiency-one analytic linchpin): a product of power functions with
-- exponents summing to zero, a 0 > 0, antitone shifts, and the partial-sum sign condition is
-- strictly decreasing — so the equilibrium-parameter equation has at most one solution.
example {k : ℕ} (hk : 1 ≤ k) {q a : ℕ → ℝ}
    (hq : ∀ i j, 1 ≤ i → i ≤ j → j ≤ k → q j ≤ q i)
    (ha0 : 0 < a 0) (hsum : ∑ i ∈ Finset.range (k + 1), a i = 0)
    (hpartial : ∀ i, 1 ≤ i → i < k → q (i + 1) < q i → 0 ≤ ∑ j ∈ Finset.range (i + 1), a j) :
    StrictAntiOn (fun β => ∏ i ∈ Finset.range k, (β + q (i + 1)) ^ a (i + 1))
      (Set.Ioi (- q k)) :=
  CRNT.powerProd_strictAntiOn hk hq ha0 hsum hpartial

-- Digraph excess additivity: the net boundary flux of a vertex set equals the sum of the
-- per-vertex net fluxes (internal arcs cancel) — the backbone of the kernel balance argument.
example {V E : Type} [DecidableEq V] [Fintype E] (src tgt : E → V) (z : E → ℝ) (U : Finset V) :
    CRNT.excessSet src tgt z U = ∑ i ∈ U, CRNT.excessVertex src tgt z i :=
  CRNT.excessSet_eq_sum_excessVertex src tgt z U

-- Lemma II.6 (per-class kernel mode): a deficiency-one linkage class carries a kernel mode of
-- A_k, positive on its terminal strong linkage class, and every kernel vector supported on the
-- class is a scalar multiple of it (the per-class kernel is one-dimensional).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (h : N.DeficiencyOneHypotheses) (κ : Network.RateConstants N) (θ : Quotient N.linkedSetoid) :
    ∃ b : N.ComplexIdx → ℝ,
      (∀ c, N.classOf c = θ → N.IsTerminalSLC c.val → 0 < b c) ∧
      N.kineticMap κ b = 0 ∧
      ∀ v : N.ComplexIdx → ℝ, N.kineticMap κ v = 0 →
        (∀ c, N.classOf c ≠ θ → v c = 0) → ∃ t : ℝ, v = t • b :=
  N.exists_kernel_mode_of_deficiencyOne h κ θ

-- Prop II.5 (kinetic map as digraph excess): on the reaction graph, the per-vertex excess of the
-- mass-action flux is the negative of the kinetic map at that complex.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (v : N.ComplexIdx → ℝ) (c : N.ComplexIdx) :
    CRNT.excessVertex N.sourceIdx N.targetIdx (N.kineticFlux κ v) c = - N.kineticMap κ v c :=
  N.excessVertex_eq_neg_kineticMap κ v c

-- A path into a complex set crosses its boundary: from reachability into a set (start outside,
-- end inside), some reaction runs from outside the set to inside it.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (P : Complex S → Prop)
    {c d : Complex S} (h : N.Reaches c d) (hc : ¬ P c) (hd : P d) :
    ∃ r : N.R, ¬ P (N.reaction r).source ∧ P (N.reaction r).target :=
  N.exists_crossing_reaction P h hc hd

-- Prop II.8 (net inflow positivity): if v vanishes on U and some reaction enters U from a complex
-- where v is positive, the kinetic-map total over U is strictly positive.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (v : N.ComplexIdx → ℝ) (U : Finset N.ComplexIdx) (hvnn : ∀ c, 0 ≤ v c)
    (hv : ∀ c ∈ U, v c = 0) {r₀ : N.R}
    (hsrc : N.sourceIdx r₀ ∉ U) (htgt : N.targetIdx r₀ ∈ U) (hpos : 0 < v (N.sourceIdx r₀)) :
    0 < ∑ c ∈ U, N.kineticMap κ v c :=
  N.sum_kineticMap_pos_of_inflow κ v U hvnn hv hsrc htgt hpos

-- The structured preimage with a zero coordinate: from the terminal-class kernel mode b and a
-- preimage z, the vector y* = z − t·b is a preimage of A_k z, nonnegative on the class, equal to
-- z off it, and zero at the arg-min complex.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {c0 : N.ComplexIdx} (b z : N.ComplexIdx → ℝ)
    (hbpos : ∀ c', N.StronglyLinked c0.val c'.val → 0 < b c')
    (hboff : ∀ c', ¬ N.StronglyLinked c0.val c'.val → b c' = 0)
    (hbker : N.kineticMap κ b = 0) :
    ∃ (ystar : N.ComplexIdx → ℝ) (cm : N.ComplexIdx),
      N.kineticMap κ ystar = N.kineticMap κ z ∧
      N.StronglyLinked c0.val cm.val ∧ ystar cm = 0 ∧
      (∀ c', N.StronglyLinked c0.val c'.val → 0 ≤ ystar c') ∧
      (∀ c', ¬ N.StronglyLinked c0.val c'.val → ystar c' = z c') :=
  N.exists_zeroCoord_preimage κ b z hbpos hboff hbker

-- Order-free power-product monotonicity: with a positive lump a0, total a0 + ∑a = 0, a lower
-- bound qmin, and the level-set sign condition, β ↦ ∏ (β + q i)^(a i) is strictly decreasing.
example {ι : Type} [DecidableEq ι] (s : Finset ι) (q a : ι → ℝ) (a0 qmin : ℝ)
    (ha0 : 0 < a0) (hsum : a0 + ∑ i ∈ s, a i = 0) (hqmin : ∀ i ∈ s, qmin ≤ q i)
    (hlevel : ∀ v : ℝ, 0 ≤ a0 + ∑ i ∈ s.filter (fun i => v < q i), a i) :
    StrictAntiOn (fun β => ∏ i ∈ s, (β + q i) ^ a i) (Set.Ioi (- qmin)) :=
  CRNT.powerProd_strictAntiOn_finset s q a a0 qmin ha0 hsum hqmin hlevel

-- Level-set sign of the kinetic map: for v>0 and a kernel vector b, the A_k y*-total over the
-- super-level set {c : v·y*_c < b_c} is nonnegative.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (b ystar : N.ComplexIdx → ℝ) {v : ℝ} (hv : 0 < v) (hb : N.kineticMap κ b = 0) :
    0 ≤ ∑ c ∈ Finset.univ.filter (fun c => v * ystar c < b c), N.kineticMap κ ystar c :=
  N.sum_kineticMap_superlevel_nonneg κ b ystar hv hb

-- Nonnegativity of the A_k-total over an absorbing (reaction-closed) set, for w ≥ 0.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (w : N.ComplexIdx → ℝ) (U : Finset N.ComplexIdx)
    (hclosed : ∀ r, N.sourceIdx r ∈ U → N.targetIdx r ∈ U) (hw : ∀ c, 0 ≤ w c) :
    0 ≤ ∑ c ∈ U, N.kineticMap κ w c :=
  N.sum_kineticMap_closed_nonneg κ w U hclosed hw

-- Log-sum form of the order-free monotonicity.
example {ι : Type} [DecidableEq ι] (s : Finset ι) (q a : ι → ℝ) (a0 qmin : ℝ)
    (ha0 : 0 < a0) (hsum : a0 + ∑ i ∈ s, a i = 0) (hqmin : ∀ i ∈ s, qmin ≤ q i)
    (hlevel : ∀ v : ℝ, 0 ≤ a0 + ∑ i ∈ s.filter (fun i => v < q i), a i) :
    StrictAntiOn (fun β => ∑ i ∈ s, a i * Real.log (β + q i)) (Set.Ioi (- qmin)) :=
  CRNT.powerProd_logSum_strictAntiOn s q a a0 qmin ha0 hsum hqmin hlevel

-- Injectivity of the shifted-monomial log-sum: H β₁ = H β₂ ⟹ β₁ = β₂.
example {ι : Type} [DecidableEq ι] (s U : Finset ι) (hdisj : Disjoint s U) (ystar b G : ι → ℝ)
    (hys : ∀ c ∈ s, 0 < ystar c) (hyU : ∀ c ∈ U, ystar c = 0) (ha0 : 0 < ∑ c ∈ U, G c)
    (hsum : (∑ c ∈ U, G c) + ∑ c ∈ s, G c = 0)
    (hlevel : ∀ v : ℝ, 0 ≤ (∑ c ∈ U, G c) + ∑ c ∈ s.filter (fun c => v < b c / ystar c), G c)
    {β₁ β₂ : ℝ} (hd₁ : ∀ c ∈ s, - (b c / ystar c) < β₁) (hd₂ : ∀ c ∈ s, - (b c / ystar c) < β₂)
    (hH : (∑ c ∈ s ∪ U, G c * Real.log (β₁ * ystar c + b c))
        = ∑ c ∈ s ∪ U, G c * Real.log (β₂ * ystar c + b c)) :
    β₁ = β₂ :=
  CRNT.eq_of_shiftedLogSum_eq s U hdisj ystar b G hys hyU ha0 hsum hlevel hd₁ hd₂ hH

-- The deficiency-one uniqueness theorem: a deficiency-one network meeting Feinberg's structural
-- hypotheses has at most one positive mass-action steady state per positive compatibility class.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (h : N.DeficiencyOneHypotheses)
    (hδ : N.DeficiencyOne) : N.DeficiencyOneUniqueness :=
  N.deficiencyOneUniqueness h hδ

-- Multi-deficient-class generalization: uniqueness holds under Feinberg's structural hypotheses
-- alone, dropping the single-deficient-class restriction (the total deficiency may exceed one).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (h : N.DeficiencyOneHypotheses) :
    N.DeficiencyOneUniqueness :=
  N.deficiencyOneUniqueness_multiClass h

-- The fully open extension carries no boundary equilibria: every nonnegative mass-action steady
-- state of `N⁺` is strictly positive (interior to the orthant).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (κ : Network.RateConstants N.fullyOpen) {x : Concentration S} (hx : x.Nonnegative)
    (hss : N.fullyOpen.IsMassActionSteadyState κ x) : x.Positive :=
  N.fullyOpen_steadyState_positive κ hx hss

-- Routh–Hurwitz in degree two: a monic real quadratic is Hurwitz (both roots in the open left
-- half-plane) iff both lower coefficients are positive.
open Polynomial in
example (a₁ a₀ : ℝ) :
    IsHurwitz (X ^ 2 + C (a₁ : ℂ) * X + C (a₀ : ℂ)) ↔ 0 < a₁ ∧ 0 < a₀ :=
  CRNT.hurwitz_quadratic_iff a₁ a₀

-- Single-linkage-class global stability from relative-entropy confinement: under a positive
-- complex-balanced reference and a start whose relative entropy is below every reference
-- coordinate, the genuine mass-action semiflow's ω-limit is the equilibrium.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : N.RateConstants) {xstar x₀ : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) (hx0 : x₀.Positive)
    (hx0compat : N.StoichCompatible x₀ xstar) (hloc : ∀ s, relEntropy xstar x₀ < xstar s) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} :=
  N.gac_of_local_confinement hwr κ hxs hcb hx0 hx0compat hloc

-- Anderson–Craciun–Kurtz: for a complex-balanced network the product-of-Poissons density
-- satisfies the stochastic master-equation stationarity condition.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (c : Concentration S) (hcb : N.IsComplexBalanced κ c) : N.IsMasterStationary κ c :=
  N.productPoisson_isStationary_of_complexBalanced κ c hcb

-- Degree-free deficiency-one existence: a per-rate-constant complex-balanced witness yields a
-- positive steady state in every positive compatibility class.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (h : N.DeficiencyOneHypotheses)
    (hδ : N.DeficiencyOne)
    (hCB : ∀ (κ : Network.RateConstants N), ∃ x : Concentration S,
      x.Positive ∧ N.IsComplexBalanced κ x) :
    N.DeficiencyOneExistence :=
  N.deficiencyOneExistence_of_complexBalancedExistence h hδ hCB

-- Degree-free 1-D Brouwer fixed point: a continuous self-map of a closed interval has a fixed point.
example {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    (hmaps : Set.MapsTo f (Set.Icc a b) (Set.Icc a b)) : ∃ x ∈ Set.Icc a b, f x = x :=
  CRNT.Analysis.fixedPoint_Icc hab hf hmaps

-- Nagumo inward condition: the mass-action field points inward on every orthant boundary face.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N) :
    Network.InwardOnBoundary (N.massActionVectorField κ) :=
  N.massActionVectorField_inwardOnBoundary κ

-- Generator-level Anderson–Craciun–Kurtz: a complex-balanced product-Poisson density is a
-- stationary state of the chemical-master-equation generator (`πQ = 0`).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (c : Concentration S) (hcb : N.IsComplexBalanced κ c) : N.IsGeneratorStationary κ c :=
  N.productPoisson_isGeneratorStationary_of_complexBalanced κ c hcb

-- Oriented matroid of a subspace: the zero covector is realizable.
example {ι : Type} [Fintype ι] (S : Submodule ℝ (ι → ℝ)) :
    (fun _ => 0) ∈ CRNT.RealizableSignVector S :=
  CRNT.realizable_zero S

-- Hurwitz determinant interface: the second Hurwitz determinant of a cubic is `a₂a₁ − a₀`.
example (a : ℕ → ℝ) : CRNT.hurwitzDet a 3 2 (by norm_num) = a 2 * a 1 - a 0 :=
  CRNT.hurwitzDet_two_cubic a

-- Singular-perturbation boundary layer: a one-sided contraction toward its equilibrium decays
-- exponentially.
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → E} {z : ℝ → E}
    {zstar : E} {lam : ℝ} (hz : ∀ t, HasDerivAt z (f (z t)) t) (hstat : f zstar = 0)
    (hcon : ODE.OneSidedContraction f zstar lam) (hlam : 0 ≤ lam) :
    ∀ t, 0 ≤ t → ‖z t - zstar‖ ≤ ‖z 0 - zstar‖ * Real.exp (-lam * t) :=
  ODE.norm_sub_le_exp_neg_mul hz hstat hcon hlam

-- Computable matrix rank over ℚ agrees with Mathlib's `Matrix.rank`.
example {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A : Matrix m n ℚ) :
    CRNT.GaussianRank.computeRank A = A.rank :=
  CRNT.GaussianRank.computeRank_eq_rank A

-- ACR cross-class bridge: under the toric/orthogonality property the log-monomial ratio is
-- constant on every linkage class.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) {x y : Concentration S}
    (hx : x.Positive) (hy : y.Positive) (h : N.ToricRelated x y) {c d : N.ComplexIdx}
    (hcd : N.Linked c.val d.val) : N.logMonomialRatio x y c = N.logMonomialRatio x y d :=
  N.logMonomialRatio_eqOn_linked hx hy h hcd

-- Signed species-reaction graph: every cycle in the SR-graph has even length.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) {u : N.SRVertex S}
    {w : N.srGraph.Walk u u} (hw : w.IsCycle) : Even w.length :=
  N.cycle_even_length hw

-- Higher-deficiency localization: under tightness each per-class deficiency subspace has
-- dimension exactly `δ_θ`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (h : N.TightLinkageDeficiency)
    (q : Quotient N.linkedSetoid) :
    Module.finrank ℝ (N.linkageDeficiencySubspace q) = (N.linkageDeficiency q).toNat :=
  N.finrank_linkageDeficiencySubspace_eq_of_tight h q

-- Exact computable deficiency over ℚ: the network deficiency equals its Gaussian-rank value.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) :
    N.deficiency = N.computeDeficiency :=
  N.deficiency_eq_computeDeficiency

-- Nagumo-based persistence: a genuine mass-action orbit with an inward dissipativity bound stays
-- in the closed nonnegative orthant for all forward time.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants) {L : ℝ}
    {γ : ℝ → Concentration S} (hderiv : ∀ t, HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hLip : ∀ t s, -L * (γ t s) ≤ N.massActionVectorField κ (γ t) s ∨ 0 ≤ γ t s)
    (h0 : (γ 0).Nonnegative) : ∀ t, 0 ≤ t → (γ t).Nonnegative :=
  N.massAction_orbit_nonneg κ hderiv hLip h0

-- Michaelis–Menten boundary layer: the enzyme fast subsystem is a bundled fast subsystem.
example : ODE.FastSubsystem CRNT.MichaelisMenten.E :=
  CRNT.MichaelisMenten.enzymeFastSubsystem 1 (by norm_num) 0

-- Stochastic jump chain: the jump probabilities sum to one wherever the exit rate is positive.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (n : S → ℕ) (h : 0 < N.exitRate κ n) : (∑ r : N.R, N.jumpProb κ n r) = 1 :=
  N.sum_jumpProb_eq_one κ n h

-- Conformal decomposition: every nonzero vector of a subspace is a sum of conforming dominators.
example {ι : Type} [Fintype ι] {S : Submodule ℝ (ι → ℝ)} {v : ι → ℝ} (hv : v ∈ S) (hv0 : v ≠ 0) :
    ∃ L : List (ι → ℝ), L.sum = v ∧ ∀ w ∈ L, CRNT.ConfDom S v w :=
  CRNT.exists_conformalSum hv hv0

-- Hopf crossing gate: at the boundary of the cubic Hurwitz region (`a₂a₁ = a₀`) the conjugate
-- pair is purely imaginary and the real root is negative.
example (z₁ z₂ : ℂ) (a₂ a₁ a₀ : ℝ) (hz₁im : z₁.im = 0)
    (e₂ : (a₂ : ℂ) = -(z₁ + z₂ + (starRingEnd ℂ) z₂))
    (e₁ : (a₁ : ℂ) = z₁ * z₂ + z₁ * ((starRingEnd ℂ) z₂) + z₂ * ((starRingEnd ℂ) z₂))
    (e₀ : (a₀ : ℂ) = -(z₁ * z₂ * ((starRingEnd ℂ) z₂)))
    (H₂ : 0 < a₂) (H₀ : 0 < a₀) (HΔ : a₂ * a₁ = a₀) :
    z₁.re < 0 ∧ z₂.re = 0 ∧ z₂.im ≠ 0 :=
  CRNT.hopf_crossing_gate z₁ z₂ a₂ a₁ a₀ hz₁im e₂ e₁ e₀ H₂ H₀ HΔ

-- One-dimensional Sperner lemma: a Sperner-colored path (false at 0, true at n) has a
-- color-change edge — the base case of the Sperner→Brouwer ladder.
example {n : ℕ} {c : ℕ → Bool} (h : CRNT.Analysis.Sperner.IsSpernerColoring n c) :
    ∃ i < n, c (i + 1) ≠ c i :=
  CRNT.Analysis.Sperner.sperner_exists_rainbow h

-- Persistence substrate: the siphon-face distance functional is nonnegative on nonnegative
-- concentrations (the Lyapunov functional behind face forward-invariance).
example {S : Type} [DecidableEq S] [Fintype S] {P : Finset S} {x : Concentration S}
    (hx : x.Nonnegative) : 0 ≤ Network.faceSum P x :=
  Network.faceSum_nonneg hx

-- Fenichel slow manifold: each layer fibre of fast-equilibria is the single point of the graph
-- (uniqueness of the attracting slow manifold).
example {Y E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (M : ODE.SlowManifold Y E)
    (y : Y) : {w : E | M.fast y w = 0} = {M.h y} :=
  M.fiber_eq_singleton y

-- 2-D Sperner core: a triangle has an odd number of {0,1}-doors iff it is rainbow (3-colored).
example (a b c : CRNT.Analysis.Sperner2D.Color) :
    Odd (CRNT.Analysis.Sperner2D.doorCount a b c) ↔ CRNT.Analysis.Sperner2D.isRainbow a b c :=
  CRNT.Analysis.Sperner2D.doorCount_odd_iff a b c

-- Unconditional confined persistence: a box-confined nonnegative mass-action orbit starting on a
-- siphon face stays on it for all forward time (the dissipativity hypothesis is discharged).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {P : Finset S} (hP : N.IsSiphon P) {γ : ℝ → Concentration S} {B : ℝ}
    (hderiv : ∀ t, HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hnn : ∀ t, 0 ≤ t → (γ t).Nonnegative) (hbox : ∀ t, 0 ≤ t → ∀ s, γ t s ≤ B)
    (h0 : γ 0 ∈ N.SiphonFace P) : ∀ t, 0 ≤ t → γ t ∈ N.SiphonFace P :=
  N.siphonFace_forwardInvariant_confined κ hP hderiv hnn hbox h0

-- Constructed Fenichel slow manifold: the fibre-equilibrium graph map is stationary by construction.
example {Y E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (M : ODE.SlowManifoldSeed Y E)
    (y : Y) : M.fast y (M.manifoldMap y) = 0 :=
  M.manifoldMap_stat y

-- Confined invariance closed: a genuine mass-action orbit with bounded relative entropy that starts
-- on a siphon face stays on it for all forward time (the box hypothesis is discharged).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {P : Finset S} (hP : N.IsSiphon P) {xstar : Concentration S} (hxs : xstar.Positive)
    {γ : ℝ → Concentration S} {C : ℝ}
    (hderiv : ∀ t, HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hnn : ∀ t, 0 ≤ t → (γ t).Nonnegative) (hrele : ∀ t, 0 ≤ t → relEntropy xstar (γ t) ≤ C)
    (h0 : γ 0 ∈ N.SiphonFace P) : ∀ t, 0 ≤ t → γ t ∈ N.SiphonFace P :=
  N.siphonFace_forwardInvariant_of_relEntropy_le κ hP hxs hderiv hnn hrele h0

-- True Michaelis–Menten slow-manifold reduction: the substrate-dependent complex equilibrium is the
-- Michaelis–Menten rate law `V_max·s/(K_m+s)`.
example (Km Vmax s : ℝ) :
    CRNT.MichaelisMenten.mmComplexEquil Km Vmax s = Vmax * s / (Km + s) :=
  rfl

-- Full 2-D Sperner over any door incidence: a Sperner-colored triangulation has a rainbow triangle.
example {Cell : Type*} [Fintype Cell] (D : CRNT.Analysis.SpernerTriangulation.DoorIncidence Cell) :
    ∃ t : Cell, D.IsRainbowCell t :=
  D.exists_rainbow

-- Boundary relative-entropy descent: a complex-balanced-referenced orbit positive on (0,∞) and
-- nonnegative at 0, starting on a siphon face, stays on it (positivity only away from t=0).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {P : Finset S} (hP : N.IsSiphon P) {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) {γ : ℝ → Concentration S}
    (hderiv : ∀ t, HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hpos : ∀ t, 0 < t → (γ t).Positive) (hnn0 : (γ 0).Nonnegative)
    (h0 : γ 0 ∈ N.SiphonFace P) : ∀ t, 0 ≤ t → γ t ∈ N.SiphonFace P :=
  N.siphonFace_forwardInvariant_of_complexBalanced_pos_pos κ hP hxs hcb hderiv hpos hnn0 h0

-- Michaelis–Menten reduced field: the substrate slow-flow field is the MM rate law `-V_max·s/(K_m+s)`
-- on the forward ray (extended by 0 for s < 0).
example (Km Vmax s : ℝ) :
    CRNT.MichaelisMenten.mmReducedField Km Vmax s = (if 0 ≤ s then -(Vmax * s / (Km + s)) else 0) :=
  rfl

-- Concrete 2-D Sperner: the explicitly-constructed single-cell triangulation has a rainbow triangle
-- (the full DoorIncidence → rainbow pipeline on a genuine `Fintype` cell type).
example : ∃ t : CRNT.Analysis.SpernerGrid.Cell,
    CRNT.Analysis.SpernerGrid.doorIncidence.IsRainbowCell t :=
  CRNT.Analysis.SpernerGrid.exists_rainbow_cell

-- Multi-outer-vertex 2-D Sperner handshaking: over a door graph on `Cell ⊕ Outer` (one outer vertex
-- per boundary sub-edge, no single-vertex collapse), odd-degree cells matching `rainbow` plus an odd
-- number of odd-degree outer vertices force an odd rainbow-triangle count.
example {Cell Outer : Type*} [Fintype Cell] [Fintype Outer]
    (G : SimpleGraph (Cell ⊕ Outer)) [DecidableRel G.Adj]
    (rainbow : Cell → Prop) [DecidablePred rainbow]
    (hcell : ∀ x : Cell, Odd (G.degree (Sum.inl x)) ↔ rainbow x)
    (houter : Odd #{o : Outer | Odd (G.degree (Sum.inr o))}) :
    ∃ x : Cell, rainbow x :=
  CRNT.Analysis.Sperner2D.multiDoorGraph_exists_rainbow G rainbow hcell houter

-- Ladder 2 (persistence): the conservation-law clause of siphon criticality equals membership in the
-- dot-product orthogonal complement of the stoichiometric subspace (the Farkas-feasibility entry point).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (v : S → ℝ) :
    (∀ r : N.R, ∑ s, v s * N.reactionVector r s = 0) ↔ v ∈ CRNT.orthSum N.stoichSubspace :=
  N.conservationLaw_iff_mem_orthSum v

-- Ladder 3 (Fenichel/QSSA): on the constructed slow manifold, an ε-slow slow path drives the slaved
-- fast variable with O(ε) displacement — the QSSA drift bound at the Lipschitz tier.
example {Y E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [PseudoMetricSpace Y]
    (S : ODE.SlowManifoldSeed Y E) {L ε : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y y' z, ‖S.fast y z - S.fast y' z‖ ≤ L * dist y y')
    {y : ℝ → Y} (hy : ∀ t t', dist (y t) (y t') ≤ ε * |t - t'|) (t t' : ℝ) :
    ‖S.manifoldMap (y t) - S.manifoldMap (y t')‖ ≤ (L / S.rate) * ε * |t - t'| :=
  S.manifoldMap_slowDrift_le hL hlip hy t t'

-- Ladder 4 (CTMC): over a finite closed enabled region with positive mass, the normalized restricted
-- stationary measure is an invariant probability measure for the embedded jump kernel.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (c : Concentration S) (hc : c.Nonnegative) (hcb : N.IsComplexBalanced κ c)
    {T : Set (S → ℕ)} (hT : N.ClosedEnabledRegion κ T) (hTfin : T.Finite)
    (hpos : N.restrictedStationaryMeasure κ c T Set.univ ≠ 0) :
    MeasureTheory.IsProbabilityMeasure
      ((N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ • N.restrictedStationaryMeasure κ c T) :=
  (N.jumpKernel_normalized_isInvariant_probabilityMeasure κ c hc hcb hT hTfin hpos).2

import CRNT
import CRNT.Examples.Minimal
import CRNT.Examples.ReversiblePair
import CRNT.Examples.GACReversiblePair
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

-- Weak reversibility holds for the reversible pair and fails for the chain.
example : Examples.ReversiblePair.N.WeaklyReversible := Examples.ReversiblePair.weaklyReversible
example : ¬ Examples.IrreversibleChain.N.WeaklyReversible :=
  Examples.IrreversibleChain.not_weaklyReversible
example : ¬ Examples.Minimal.N.WeaklyReversible := Examples.Minimal.not_weaklyReversible

-- The reversible pair has deficiency zero and satisfies the deficiency-zero hypotheses.
example : Examples.ReversiblePair.N.DeficiencyZero := Examples.ReversiblePair.deficiencyZero
example : Examples.ReversiblePair.N.SatisfiesDeficiencyZeroHypotheses :=
  Examples.ReversiblePair.satisfiesDeficiencyZeroHypotheses

-- The computable linkage count reduces under `decide`; the computable deficiency assembly
-- agrees with the deficiency via the axiom-clean bridge (the value itself is `#eval`-only).
example : Examples.ReversiblePair.N.computeNumLinkageClasses = 1 := by decide
example : Examples.ReversiblePair.N.deficiency = Examples.ReversiblePair.N.computableDeficiency :=
  Network.deficiency_eq_computableDeficiency _

-- A data-driven reversible pair `A ⇌ B` reconstructs to a 2-complex, 2-reaction network.
def interopRevData : NetworkData :=
  { numSpecies := 2,
    reactions := #[ { source := #[1, 0], target := #[0, 1] },
                    { source := #[0, 1], target := #[1, 0] } ] }
example : interopRevData.toNetwork.numComplexes = 2 := by decide
example : interopRevData.toNetwork.numReactions = 2 := by decide

-- The one-call analysis reports the right invariants, with the deficiency bridged to `N.deficiency`.
example : interopRevData.analyze.numComplexes = 2 := by decide
example : interopRevData.analyze.weaklyReversible = true := by decide
example : interopRevData.analyze.deficiency = interopRevData.toNetwork.deficiency :=
  NetworkData.analyze_deficiency_eq _
-- The conservation-law dimension is bridged to the cokernel dimension (`numSpecies − s`).
example : interopRevData.analyze.conservationLawDim
    = Module.finrank ℝ (CRNT.orthSum interopRevData.toNetwork.stoichSubspace) :=
  NetworkData.analyze_conservationLawDim_eq _

-- The reversible pair carries no structural ACR witness.
example : interopRevData.analyze.acrSpecies = #[] := by decide

-- A reported ACR species index is exactly one carrying a structural Shinar–Feinberg witness.
example (d : NetworkData) (s : Fin d.numSpecies) :
    s.val ∈ d.analyze.acrSpecies ↔ d.toNetwork.HasShinarFeinbergPair s :=
  NetworkData.analyze_acrSpecies_eq d s

-- `mem_acrSpecies` characterizes the structural ACR species set: species `A` of the toy network
-- (`A → P`, `2A → Q`) carries a witness.
example : Examples.ACRPair.Species.A ∈ Examples.ACRPair.N.acrSpecies :=
  (Examples.ACRPair.N.mem_acrSpecies _).mpr (by decide)

-- The reversible pair has a nonempty siphon (the full species set `{A, B}`).
example : interopRevData.analyze.hasSiphon = true := by decide

-- The siphon flag is `true` exactly when a nonempty siphon exists, and `false` soundly excludes
-- every critical siphon (the Farkas-free persistence design filter).
example (d : NetworkData) :
    d.analyze.hasSiphon = true
      ↔ ∃ P : Finset (Fin d.numSpecies), P.Nonempty ∧ d.toNetwork.IsSiphon P :=
  NetworkData.analyze_hasSiphon_eq d
example (d : NetworkData) (h : d.analyze.hasSiphon = false) :
    d.toNetwork.HasNoCriticalSiphon :=
  NetworkData.analyze_hasNoCriticalSiphon_of_hasSiphon_false d h

-- The full species set `{A, B}` is the (unique) minimal siphon of the reversible pair.
example : Examples.SiphonReversiblePair.N.IsMinimalSiphon (Finset.univ) := by decide

-- The data-driven reversible pair reports `{0, 1}` as its only minimal siphon.
example : interopRevData.analyze.minimalSiphons = #[#[0, 1]] := by decide

-- Each `minimalSiphons` entry is the ascending index image of a minimal siphon.
example (d : NetworkData) (arr : Array Nat) :
    arr ∈ d.analyze.minimalSiphons ↔
      ∃ l : List (Fin d.numSpecies), l ∈ (List.finRange d.numSpecies).sublists ∧
        d.toNetwork.IsMinimalSiphon l.toFinset ∧ arr = (l.map Fin.val).toArray :=
  NetworkData.mem_analyze_minimalSiphons d arr

-- The `crnt_deficiency_zero` tactic certifies deficiency zero from an explicit minor witness:
-- a 1×1 minor for the reversible pair, a 2×2 minor for the irreversible chain.
example : Examples.ReversiblePair.N.DeficiencyZero := by
  crnt_deficiency_zero ![Examples.ReversiblePair.Rxn.fwd], ![Examples.ReversiblePair.Species.A]
example : Examples.IrreversibleChain.N.DeficiencyZero := by
  crnt_deficiency_zero ![Examples.IrreversibleChain.Rxn.r1, Examples.IrreversibleChain.Rxn.r2],
    ![Examples.IrreversibleChain.Species.A, Examples.IrreversibleChain.Species.B]

-- The argument-free form finds the nonsingular minor itself.
example : Examples.ReversiblePair.N.DeficiencyZero := by crnt_deficiency_zero
example : Examples.IrreversibleChain.N.DeficiencyZero := by crnt_deficiency_zero

-- The generalized minor-rank tactic bounds the stoichiometric rank below from a witness.
example : 2 ≤ Examples.IrreversibleChain.N.stoichRank := by
  crnt_stoich_rank_ge ![Examples.IrreversibleChain.Rxn.r1, Examples.IrreversibleChain.Rxn.r2],
    ![Examples.IrreversibleChain.Species.A, Examples.IrreversibleChain.Species.B]

-- The reversible pair has no critical siphon, so the no-critical-siphon global-attraction
-- theorem applies to it: every hypothesis is met on this concrete network.
example : Examples.ReversiblePair.N.HasNoCriticalSiphon :=
  Examples.ReversiblePair.hasNoCriticalSiphon

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

-- The mass-action vector field is a polynomial map, hence differentiable everywhere.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N) :
    Differentiable ℝ (fun x => N.massActionVectorField κ x) :=
  N.massActionVectorField_differentiable κ

-- The source monomial's Fréchet derivative is the dot product with its gradient.
example {S : Type} [DecidableEq S] [Fintype S] (y : Complex S) (x : Concentration S) :
    HasFDerivAt (fun x => y.massActionMonomial x)
      (∑ j, CRNT.massActionMonomialGrad y x j •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) j) x :=
  CRNT.massActionMonomial_hasFDerivAt y x

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

-- The dot-product complement has codimension `dim S`: `dim Sᗮ = card ι − dim S`.
example {ι : Type} [Fintype ι] (S : Submodule ℝ (ι → ℝ)) :
    Module.finrank ℝ (CRNT.orthSum S) = Fintype.card ι - Module.finrank ℝ S :=
  CRNT.finrank_orthSum S

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

-- The partial-open (CFSTR) extension can carry boundary equilibria, but only on closed species:
-- the face supporting any nonnegative steady state is disjoint from the open set `O`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (O : Finset S)
    (κ : Network.RateConstants (N.partialOpen O)) {x : Concentration S} (hx : x.Nonnegative)
    (hss : (N.partialOpen O).IsMassActionSteadyState κ x) : Disjoint (Network.faceOf x) O :=
  N.faceOf_partialOpen_steadyState_disjoint O κ hx hss

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

-- Single-linkage-class GAC, conditional on single-linkage persistence: the conjecture for a
-- single-linkage network reduces to the hypothesis `SingleLinkageClass → PersistentFrom`.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (hslc : N.SingleLinkageClass) (κ : N.RateConstants) {xstar x₀ : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) (hx0 : x₀.Positive)
    (hx0compat : N.StoichCompatible x₀ xstar)
    (hpers : N.SingleLinkageClass → N.PersistentFrom κ x₀) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} :=
  N.singleLinkageClass_gac hwr hslc κ hxs hcb hx0 hx0compat hpers

-- The reversible pair `A ⇌ B` has a single linkage class.
example : Examples.ReversiblePair.N.SingleLinkageClass :=
  Examples.ReversiblePair.numLinkageClasses_eq

-- Negative (backward) invariance of the ω-limit set: for a semiflow whose orbit through `x₀`
-- stays in a compact set, every ω-point has a `ϕ t`-preimage inside the ω-limit set.
open Filter in
example {α : Type} [TopologicalSpace α] [T2Space α] (ϕ : Flow ℝ≥0 α) (x₀ : α) {K : Set α}
    (hK : IsCompact K) (hmaps : ∀ s : ℝ≥0, ϕ s x₀ ∈ K) (t : ℝ≥0) {w : α}
    (hw : w ∈ omegaLimit atTop ϕ {x₀}) :
    ∃ w' ∈ omegaLimit atTop ϕ {x₀}, ϕ t w' = w :=
  CRNT.omegaLimit_negInvariant ϕ x₀ hK hmaps t hw

-- Strict inflow at a non-siphon zero set: if the zero set of a nonnegative concentration is not
-- a siphon, the mass-action field is strictly positive at some empty species.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {w : Concentration S} (hwnn : w.Nonnegative) {P : Finset S} (hP : ∀ s, s ∈ P ↔ w s = 0)
    (hns : ¬ N.IsSiphon P) : ∃ s ∈ P, 0 < N.massActionVectorField κ w s :=
  N.massActionVectorField_pos_of_not_isSiphon κ hwnn hP hns

-- Boundary ω-limit ⇒ siphon: for a bounded mass-action semiflow whose ω-orbits solve the genuine
-- field and are nonnegative, the zero set of any ω-limit point is a siphon.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, (y : Concentration S).Nonnegative)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    {w : Concentration S} (hw : w ∈ omegaLimit atTop ϕ {x₀})
    {P : Finset S} (hP : ∀ s, s ∈ P ↔ w s = 0) : N.IsSiphon P :=
  N.isSiphon_zeroSet_of_mem_omegaLimit κ hϕγ hK hmaps hωnn hgenω hw hP

-- Boundary ω-limit ⇒ CRITICAL siphon: for a positive start, a boundary ω-limit point's zero set
-- carries no positive conservation law, so it is a critical siphon.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, (y : Concentration S).Nonnegative)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx0pos : x₀.Positive) {w : Concentration S} (hw : w ∈ omegaLimit atTop ϕ {x₀})
    {P : Finset S} (hP : ∀ s, s ∈ P ↔ w s = 0) (hPne : P.Nonempty) : N.IsCriticalSiphon P :=
  N.isCriticalSiphon_zeroSet_of_mem_omegaLimit κ hϕγ hK hmaps hωnn hgenω hωaff hx0pos hw hP hPne

-- No critical siphon ⇒ persistence at the ω-limit: every ω-limit point is strictly positive.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, (y : Concentration S).Nonnegative)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx0pos : x₀.Positive) (hncs : N.HasNoCriticalSiphon)
    {w : Concentration S} (hw : w ∈ omegaLimit atTop ϕ {x₀}) : w.Positive :=
  N.omegaLimit_positive_of_hasNoCriticalSiphon κ hϕγ hK hmaps hωnn hgenω hωaff hx0pos hncs hw

-- Unconditional GAC for no-critical-siphon networks: a weakly reversible, no-critical-siphon,
-- complex-balanced network converges to the unique equilibrium of any positive class — no
-- persistence or closeness hypothesis.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : N.RateConstants) (hncs : N.HasNoCriticalSiphon) {xstar x₀ : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) (hx0 : x₀.Positive)
    (hx0compat : N.StoichCompatible x₀ xstar) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} :=
  N.gac_of_hasNoCriticalSiphon hwr κ hncs hxs hcb hx0 hx0compat

-- Broader reduction: a single positive ω-limit point forces ω = {x*} (no structural hypothesis).
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : N.RateConstants) {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0compat : N.StoichCompatible x₀ xstar) (hγ0 : ∀ x, γ x 0 = x)
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    {c : ℝ} (hωc : ∀ z ∈ omegaLimit atTop ϕ {x₀}, relEntropy xstar z = c)
    (hposorbit : ∀ p ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive p →
      ∀ t : ℝ, 0 ≤ t → Concentration.Positive (γ p t))
    (hex : ∃ p ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive p) :
    omegaLimit atTop ϕ {x₀} = {xstar} :=
  N.omegaLimit_eq_singleton_of_mem_positive hwr κ hxs hcb hx0compat hγ0 hϕγ hgenω hωnn hωaff hωc
    hposorbit hex

-- GAC-frontier foundation F1: the maximal invariant subset of a set is invariant.
example {α : Type} [TopologicalSpace α] (ϕ : Flow ℝ≥0 α) (N : Set α) :
    IsInvariant ϕ (maximalInvariantSubset ϕ N) :=
  isInvariant_maximalInvariantSubset ϕ N

-- GAC-frontier foundation F3: an ODE solution embeds as a solution of any inclusion it selects.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : DifferentialInclusion.Field E) {f : E → E} {γ : ℝ → E}
    (hderiv : ∀ t, HasDerivAt γ (f (γ t)) t) (hsel : ∀ x, f x ∈ F x) :
    DifferentialInclusion.IsInclusionSolution F γ :=
  DifferentialInclusion.IsInclusionSolution.of_ode hderiv hsel

-- GAC-frontier foundation F4: dissipation is strictly negative at a positive non-equilibrium.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {x xstar : Concentration S} (hx : Concentration.Positive x) (hxs : Concentration.Positive xstar)
    (hcb : N.IsComplexBalanced κ xstar) (hnotcb : ¬ N.IsComplexBalanced κ x) :
    (∑ s, (Real.log (x s) - Real.log (xstar s)) * N.massActionVectorField κ x s) < 0 :=
  N.dissipation_neg_of_not_complexBalanced κ hx hxs hcb hnotcb

-- GAC-frontier foundation F2: reaction vectors lie in the reaction cone; Newton polytope is convex.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (r : N.R) :
    N.reactionVector r ∈ N.reactionCone :=
  N.reactionVector_mem_reactionCone r

example {S : Type} [DecidableEq S] [Fintype S] (Y : Finset (Complex S)) :
    Convex ℝ (newtonPolytope Y) :=
  newtonPolytope_convex Y

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

-- Per-linkage-class deficiency in exact computable form: `δ_θ = n_θ − 1 − computeRank (class matrix)`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (q : Quotient N.linkedSetoid) :
    N.linkageDeficiency q = N.computeLinkageDeficiency q :=
  N.linkageDeficiency_eq_computeLinkageDeficiency q

-- The per-class deficiency-one test `δ_θ ≤ 1` carries a total `Decidable` instance.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (q : Quotient N.linkedSetoid) :
    Decidable (N.linkageDeficiency q ≤ 1) :=
  N.decidableLinkageDeficiency_le_one q

-- Multistationarity capacity is ruled out by injectivity for all rate constants.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (h : ∀ κ : Network.RateConstants N, (N.massActionKinetics κ).Injective) :
    ¬ N.HasMultistationarityCapacity :=
  N.not_hasMultistationarityCapacity_of_injective h

-- Consistency (positive dependence of reaction vectors): a functional nonnegative on every
-- reaction vector is forced to vanish on all of them.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (h : N.IsConsistent)
    {w : S → ℝ} (hw : ∀ r, 0 ≤ ∑ s, w s * N.reactionVector r s) (r : N.R) :
    ∑ s, w s * N.reactionVector r s = 0 :=
  N.inner_reactionVector_eq_zero_of_isConsistent_of_nonneg h hw r

-- A weakly reversible network is consistent (regular's first clause holds for WR networks).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible) :
    N.IsConsistent :=
  N.isConsistent_of_weaklyReversible hwr

-- Cut pairs of the linkage graph are symmetric.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    {y y' : {c : Complex S // c ∈ N.complexes}} (h : N.CutPair y y') : N.CutPair y' y :=
  h.symm

-- A regular network is consistent and has one terminal SLC per linkage class.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (h : N.RegularNetwork) :
    N.IsConsistent ∧ N.OneTerminalSLCPerLinkageClass :=
  ⟨h.isConsistent, h.oneTerminalSLCPerLinkageClass⟩

-- A DOA-system solution carrying a strict inequality is nonzero.
example {S : Type} [DecidableEq S] [Fintype S] (sys : DOASystem S) {μ : S → ℝ}
    (h : sys.Satisfies μ) {p : Complex S × Complex S} (hp : p ∈ sys.gts) : μ ≠ 0 :=
  sys.ne_zero_of_satisfies_mem_gts h hp

-- The cut-pair functional of a confluence vector is antisymmetric.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) {g : N.ComplexIdx → ℝ}
    (hg : N.IsConfluenceVector g) {y y' : N.ComplexIdx} (h : N.CutPair y y') :
    N.cutSum g y y' = - N.cutSum g y' y :=
  N.cutSum_antisymm hg h

-- A shelf partition's strict height constraint forces μ ≠ 0.
example {S : Type} [DecidableEq S] [Fintype S] {N : Network S} (sp : N.ShelfPartition)
    {g : N.ComplexIdx → ℝ} {μ : S → ℝ} (h : sp.imposes g μ)
    {y y' : N.ComplexIdx} (hr : (sp.shelf y').rank < (sp.shelf y).rank) : μ ≠ 0 :=
  sp.ne_zero_of_imposes_of_higher h hr

-- The Deficiency One Algorithm verdict is non-vacuous: affirming capacity yields a nonzero
-- stoichiometric vector. (The capacity ⟺ signature theorem itself is the stated target.)
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (h : N.DOAAffirmsCapacity) : N.stoichSubspace ≠ ⊥ :=
  N.stoichSubspace_ne_bot_of_doaAffirmsCapacity h

-- DOA forward direction (entry step): capacity yields a nonzero sign-compatible vector.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (h : N.HasMultistationarityCapacity) : ∃ μ : S → ℝ, μ ≠ 0 ∧ N.SignCompatibleWithStoich μ :=
  N.exists_signCompatible_of_hasMultistationarityCapacity h

-- Colinearity of reactions is transitive.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) {r r' r'' : N.R}
    (h₁ : N.ColinearReactions r r') (h₂ : N.ColinearReactions r' r'') : N.ColinearReactions r r'' :=
  h₁.trans h₂

-- The Advanced Deficiency Algorithm verdict is non-vacuous: it yields a nonzero stoichiometric vector.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (h : N.ADAAffirmsCapacity) : N.stoichSubspace ≠ ⊥ :=
  N.stoichSubspace_ne_bot_of_adaAffirmsCapacity h

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

-- Multi-outer-vertex door-incidence interface: the uncollapsed `DoorIncidence` (one outer vertex per
-- boundary sub-edge) yields the 2-D Sperner conclusion from bundled degree/parity facts.
example {Cell Outer : Type*} [Fintype Cell] [Fintype Outer]
    (D : CRNT.Analysis.SpernerTriangulation.MultiDoorIncidence Cell Outer) :
    ∃ t : Cell, D.IsRainbowCell t :=
  D.exists_rainbow

-- Concrete multi-triangle 2-D Sperner: the N=2 barycentric subdivision (four cells, one interior door
-- and one boundary door) has a rainbow triangle — the full multi-outer pipeline on a real triangulation.
example : ∃ t : CRNT.Analysis.SpernerN2.Cell,
    CRNT.Analysis.SpernerN2.multiDoorIncidence.IsRainbowCell t :=
  CRNT.Analysis.SpernerN2.exists_rainbow_cell

-- The rainbow triangle is exactly the central inverted triangle `dn`.
example : CRNT.Analysis.SpernerN2.multiDoorIncidence.IsRainbowCell CRNT.Analysis.SpernerN2.Cell.dn := by
  decide

-- Geometric derivation: the N=2 door graph built from vertices+coloring (not a hand-listed edge set)
-- still yields a rainbow triangle, with the lattice-edge incidence lemma proved from `triVerts`.
example : ∃ t : CRNT.Analysis.SpernerN2Geo.Cell,
    CRNT.Analysis.SpernerN2Geo.multiDoorIncidence.IsRainbowCell t :=
  CRNT.Analysis.SpernerN2Geo.exists_rainbow_cell

-- The lattice-edge incidence lemma: the interior door edge `mAB–mAC` borders exactly two triangles.
example (t : CRNT.Analysis.SpernerN2Geo.Cell) :
    (CRNT.Analysis.SpernerN2Geo.Vertex.mAB ∈ CRNT.Analysis.SpernerN2Geo.triVerts t ∧
      CRNT.Analysis.SpernerN2Geo.Vertex.mAC ∈ CRNT.Analysis.SpernerN2Geo.triVerts t) ↔
      (t = .up1 ∨ t = .dn) :=
  CRNT.Analysis.SpernerN2Geo.interior_doorEdge_borders_two t

-- Arbitrary-N parametric subdivision (geometry layer): every triangle of the N-subdivision has
-- exactly three vertices — the basis for its three edges and door count.
example {N : ℕ} (c : CRNT.Analysis.SpernerLattice.Cell N) :
    (CRNT.Analysis.SpernerLattice.triVerts c).card = 3 :=
  CRNT.Analysis.SpernerLattice.triVerts_card c

-- Arbitrary-N Sperner boundary conditions: the corner (N,0) is colored 0 under any proper coloring.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N) :
    κ.color (CRNT.Analysis.SpernerLattice.mkPt N 0 (by omega)) = 0 :=
  CRNT.Analysis.SpernerLattice.corner_color_i κ

-- ...and a boundary side omits the opposite color: on `i + j = N` the color is never 2.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N) (i j : ℕ) (h : i + j = N) :
    κ.color (CRNT.Analysis.SpernerLattice.mkPt i j (by omega)) ≠ 2 :=
  CRNT.Analysis.SpernerLattice.side_ij_ne_two κ i j h

-- Lattice-edge incidence lemma (any N): an interior diagonal edge borders exactly two triangles,
-- `up(i,j)` and `down(i,j)`.
example (N i j : ℕ) (hd : i + j + 2 ≤ N) (c : CRNT.Analysis.SpernerLattice.Cell N) :
    (CRNT.Analysis.SpernerLattice.mkPt (i + 1) j (by omega) ∈
        CRNT.Analysis.SpernerLattice.triVerts c ∧
      CRNT.Analysis.SpernerLattice.mkPt i (j + 1) (by omega) ∈
        CRNT.Analysis.SpernerLattice.triVerts c) ↔
      (c = Sum.inl ⟨(i, j), by rw [CRNT.Analysis.SpernerLattice.mem_upCarrier]; omega⟩ ∨
        c = Sum.inr ⟨(i, j), by rw [CRNT.Analysis.SpernerLattice.mem_downCarrier]; omega⟩) :=
  CRNT.Analysis.SpernerLattice.diag_incidence_interior N i j hd c

-- Lattice-edge incidence (vertical, any N): a boundary vertical edge on the left side bounds exactly
-- one triangle, `up(0,j)`.
example (N j : ℕ) (hj : j + 1 ≤ N) (c : CRNT.Analysis.SpernerLattice.Cell N) :
    (CRNT.Analysis.SpernerLattice.mkPt 0 j (by omega) ∈ CRNT.Analysis.SpernerLattice.triVerts c ∧
      CRNT.Analysis.SpernerLattice.mkPt 0 (j + 1) (by omega) ∈
        CRNT.Analysis.SpernerLattice.triVerts c) ↔
      c = Sum.inl ⟨(0, j), by rw [CRNT.Analysis.SpernerLattice.mem_upCarrier]; omega⟩ :=
  CRNT.Analysis.SpernerLattice.vert_incidence_boundary N j hj c

-- Door confinement (any N): a horizontal edge on the bottom side is never a {0,1} door, so boundary
-- doors are confined to the k=0 side (the setup that collapses the door graph's outer vertices).
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N) (a : ℕ) (ha : a + 1 ≤ N) :
    CRNT.Analysis.Sperner2D.isDoor (κ.color (CRNT.Analysis.SpernerLattice.mkPt a 0 (by omega)))
      (κ.color (CRNT.Analysis.SpernerLattice.mkPt (a + 1) 0 (by omega))) = false :=
  CRNT.Analysis.SpernerLattice.bottom_H_not_door κ a ha

-- Door graph assembly: the cell adjacency (sharing a {0,1} door edge) is symmetric.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N)
    {t t' : CRNT.Analysis.SpernerLattice.Cell N} (h : CRNT.Analysis.SpernerLattice.CellDoor κ t t') :
    CRNT.Analysis.SpernerLattice.CellDoor κ t' t :=
  CRNT.Analysis.SpernerLattice.cellDoor_symm κ h

-- Door graph bipartite: two up-triangles are never door-adjacent (same orientation shares ≤1 vertex).
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N)
    (u u' : CRNT.Analysis.SpernerLattice.Up N) :
    ¬ CRNT.Analysis.SpernerLattice.CellDoor κ (Sum.inl u) (Sum.inl u') :=
  CRNT.Analysis.SpernerLattice.not_cellDoor_inl_inl κ u u'

-- Neighbor locator: a door-neighbor of an up-triangle is a down-triangle.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N)
    {u : CRNT.Analysis.SpernerLattice.Up N} {t' : CRNT.Analysis.SpernerLattice.Cell N}
    (h : CRNT.Analysis.SpernerLattice.CellDoor κ (Sum.inl u) t') :
    ∃ d : CRNT.Analysis.SpernerLattice.Down N, t' = Sum.inr d :=
  CRNT.Analysis.SpernerLattice.cellDoor_inl_isRight κ h

-- Ladder 2 (persistence): the conservation-law clause of siphon criticality equals membership in the
-- dot-product orthogonal complement of the stoichiometric subspace (the Farkas-feasibility entry point).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (v : S → ℝ) :
    (∀ r : N.R, ∑ s, v s * N.reactionVector r s = 0) ↔ v ∈ CRNT.orthSum N.stoichSubspace :=
  N.conservationLaw_iff_mem_orthSum v

-- Ladder 2 (persistence): a conservation law (orthogonal to the stoichiometric subspace) is a constant
-- of motion — its weighted total is unchanged along every mass-action solution.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {w : S → ℝ} (hw : w ∈ CRNT.orthSum N.stoichSubspace)
    {γ : ℝ → Concentration S} {t : ℝ} (ht : 0 ≤ t)
    (hsol : ∀ τ ∈ Set.Icc (0 : ℝ) t, HasDerivAt γ (N.massActionVectorField κ (γ τ)) τ) :
    ∑ s, w s * γ t s = ∑ s, w s * γ 0 s :=
  N.conservationLaw_const_along_solution κ hw ht hsol

-- Ladder 3 (Fenichel/QSSA): on the constructed slow manifold, an ε-slow slow path drives the slaved
-- fast variable with O(ε) displacement — the QSSA drift bound at the Lipschitz tier.
example {Y E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [PseudoMetricSpace Y]
    (S : ODE.SlowManifoldSeed Y E) {L ε : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y y' z, ‖S.fast y z - S.fast y' z‖ ≤ L * dist y y')
    {y : ℝ → Y} (hy : ∀ t t', dist (y t) (y t') ≤ ε * |t - t'|) (t t' : ℝ) :
    ‖S.manifoldMap (y t) - S.manifoldMap (y t')‖ ≤ (L / S.rate) * ε * |t - t'| :=
  S.manifoldMap_slowDrift_le hL hlip hy t t'

-- Ladder 3 (Fenichel/MM): the constructed Michaelis-Menten substrate curve is monotonically depleted
-- (antitone) — a qualitative property of the reduced flow.
example (Km Vmax : ℝ) (hKm : 0 < Km) (hV : 0 ≤ Vmax) (s₀ : ℝ) :
    Antitone (CRNT.MichaelisMenten.mmSubstrate Km Vmax hKm hV s₀) :=
  CRNT.MichaelisMenten.mmSubstrate_antitone Km Vmax hKm hV s₀

-- Ladder 4 (CTMC): over a finite closed enabled region with positive mass, the normalized restricted
-- stationary measure is an invariant probability measure for the embedded jump kernel.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (c : Concentration S) (hc : c.Nonnegative) (hcb : N.IsComplexBalanced κ c)
    {T : Set (S → ℕ)} (hT : N.ClosedEnabledRegion κ T) (hTfin : T.Finite)
    (hpos : N.restrictedStationaryMeasure κ c T Set.univ ≠ 0) :
    MeasureTheory.IsProbabilityMeasure
      ((N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ • N.restrictedStationaryMeasure κ c T) :=
  (N.jumpKernel_normalized_isInvariant_probabilityMeasure κ c hc hcb hT hTfin hpos).2

-- Ladder 4 (CTMC): the canonical maximal closed enabled region is itself a closed enabled region
-- (arbitrary union of such regions is one), so it carries the invariant restricted stationary measure.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N) :
    N.ClosedEnabledRegion κ (N.maximalClosedEnabledRegion κ) :=
  N.closedEnabledRegion_maximal κ

-- An isolated invariant set cannot trap an ω-limit set without containing it (the Butler–McGehee
-- escape core) — here the ω-limit set is invariant.
open Filter in
example {α : Type} [TopologicalSpace α] (ϕ : Flow ℝ≥0 α) (x₀ : α) :
    IsInvariant ϕ (omegaLimit atTop ϕ {x₀}) :=
  omegaLimit_isInvariant_two_sided ϕ x₀

-- Strongly endotactic networks are endotactic.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (h : N.StronglyEndotactic) :
    N.Endotactic :=
  h.endotactic

-- The mass-action velocity always lies in the cone generated by the reaction vectors (the embedding
-- substrate for toric differential inclusions, Craciun, Toric differential inclusions…).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : Concentration.Nonnegative x) :
    N.massActionVectorField κ x ∈ N.reactionCone :=
  N.massActionVectorField_mem_reactionCone κ hx

-- The cyclic monomial-ordered velocity lies in the cone of consecutive differences (Abel summation;
-- the hypothesis is monotonicity of the coefficients).
example {S : Type} [DecidableEq S] [Fintype S] (u : ℕ → S → ℝ) (a : ℕ → ℝ) (n : ℕ)
    (hcyc : u n = u 0) (hmono : Monotone a) :
    (∑ i ∈ Finset.range n, a i • (u (i + 1) - u i)) ∈
      generatedCone (fun i : Fin (n - 1) => u 0 - u (i + 1)) :=
  cycle_velocity_mem_generatedCone u a n hcyc hmono

-- The toric differential-inclusion field F_{F,δ}(X) is monotone in δ.
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (F : Fan E) {δ₁ δ₂ : ℝ} (X : E) (hδ : δ₁ ≤ δ₂) :
    (toricField F δ₁ X : Set E) ⊆ (toricField F δ₂ X : Set E) :=
  toricField_mono_delta X hδ

-- A strongly endotactic network has a strictly descending direction at any non-constant functional
-- on its source complexes (Gopalkrishnan–Miller–Shiu).
example {S : Type} [DecidableEq S] [Fintype S] {N : Network S} (h : N.StronglyEndotactic)
    (w : S → ℝ) (hncon : ∃ r₁ r₂ : N.R, N.wValue w r₁ ≠ N.wValue w r₂) :
    ∃ r : N.R, N.IsMaxSource w r ∧ N.wRate w r < 0 :=
  Network.stronglyEndotactic_strict_dissipation_direction h w hncon

-- A non-siphon codimension-1 facet repels: strictly positive inflow at the empty species
-- (Anderson–Shiu facet repulsion).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {sstar : S} (hns : ¬ N.IsSiphon ({sstar} : Finset S)) {w : Concentration S}
    (hwnn : Concentration.Nonnegative w) (hzero : ∀ s, w s = 0 ↔ s = sstar) :
    0 < N.massActionVectorField κ w sstar :=
  N.massActionVectorField_pos_on_facet_of_not_isSiphon κ hns hwnn hzero

-- The monomial-ordered cyclic velocity lies in the polar cone of any cone for which the cycle's base
-- vertex is minimal (single-cycle toric embedding).
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {C : Set E}
    (u : ℕ → E) (a : ℕ → ℝ) (n : ℕ) (hcyc : u n = u 0) (hmono : Monotone a) (hmin : CMinimal C u) :
    (∑ i ∈ Finset.range n, a i • (u (i + 1) - u i)) ∈ polarCone C :=
  cycle_velocity_mem_polarCone u a n hcyc hmono hmin

-- A ray [P₀,∞) is a zero-separating region for any 1-D inclusion whose field points nonnegatively —
-- invariance holds with no viability theory.
example {F : DifferentialInclusion.Field ℝ} {P₀ : ℝ} (hP₀ : 0 < P₀)
    (hF : ∀ y, F y ⊆ Set.Ici (0 : ℝ)) :
    DifferentialInclusion.ZeroSeparatingRegion F (Set.Ici P₀) P₀ P₀ :=
  DifferentialInclusion.zeroSeparatingRegion_Ici hP₀ hF

-- A solution staying in s witnesses its velocity in the Bouligand tangent cone — the
-- invariance ⇒ subtangency half of Nagumo's theorem.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {γ : ℝ → E} {x v : E} {s : Set E}
    (hx : γ 0 = x) (hd : HasDerivAt γ v 0) (hs : ∀ t, 0 ≤ t → γ t ∈ s) :
    v ∈ tangentConeAt ℝ s x :=
  DifferentialInclusion.mem_tangentConeAt_of_solution hx hd hs

-- A finite sum of polar-cone vectors stays in the polar cone — the assembly turning per-cycle
-- embeddings into the full weakly-reversible velocity.
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type} [Fintype ι]
    {s : Set E} (v : ι → E) (hv : ∀ j, v j ∈ polarCone s) :
    (∑ j, v j) ∈ polarCone s :=
  sum_univ_mem_polarCone v hv

-- Before the first exit time, a curve stays in the closed set.
example {α : Type} [TopologicalSpace α] {γ : ℝ → α} {R : Set α} {s : ℝ}
    (hs0 : 0 ≤ s) (hsτ : s < exitTime γ R) : γ s ∈ R :=
  mem_of_lt_exitTime hs0 hsτ

-- A sublevel set is forward-invariant under a Lyapunov-descent condition.
example {V : ℝ → ℝ} {c : ℝ} (hcont : ContinuousOn V (Set.Ici 0))
    (hdiff : ∀ t > 0, DifferentiableAt ℝ V t) (hderiv : ∀ t > 0, deriv V t ≤ 0) (h0 : V 0 ≤ c) :
    ∀ t ≥ 0, V t ≤ c :=
  sublevel_invariant_of_deriv_nonpos hcont hdiff hderiv h0

-- Subtangency ⇒ descent bridge: a positive-tangent-cone direction at a sublevel boundary has
-- nonpositive derivative of g.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → ℝ} {g' : E →L[ℝ] ℝ} {x : E}
    {c : ℝ} (hg : HasFDerivAt g g' x) (hx : g x = c) {v : E}
    (hv : v ∈ posTangentConeAt {y | g y ≤ c} x) : g' v ≤ 0 :=
  DifferentialInclusion.inner_le_zero_of_mem_posTangentConeAt_sublevel hg hx hv

-- Closed-set Nagumo via distance: if distance to a closed set is nonincreasing along a curve
-- starting inside, the curve stays inside.
example {α : Type} [PseudoMetricSpace α] {γ : ℝ → α} {R : Set α} (hR : IsClosed R) (hne : R.Nonempty)
    (h0 : γ 0 ∈ R) (hanti : AntitoneOn (fun t => Metric.infDist (γ t) R) (Set.Ici 0))
    {t : ℝ} (ht : 0 ≤ t) : γ t ∈ R :=
  invariant_of_infDist_antitoneOn hR hne h0 hanti ht

-- Under neighborhood descent, the genuine flow stays in the sublevel zero-separating region for all
-- forward time.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → E} {γ : ℝ → E} {g : E → ℝ}
    {g' : E → (E →L[ℝ] ℝ)} {c δ : ℝ} (hgc : Continuous g) (hg : ∀ y, HasFDerivAt g (g' y) y)
    (hγcont : Continuous γ) (hγderiv : ∀ t, 0 ≤ t → HasDerivAt γ (f (γ t)) t) (hδ : 0 < δ)
    (hdescent : ∀ y, c - δ ≤ g y → g y ≤ c + δ → g' y (f y) ≤ 0) (h0 : g (γ 0) ≤ c) :
    ∀ t, 0 ≤ t → g (γ t) ≤ c :=
  DifferentialInclusion.genuine_sublevel_invariant hgc hg hγcont hγderiv hδ hdescent h0

-- In a weakly reversible network every reaction lies on a directed cycle.
example {S : Type} [DecidableEq S] [Fintype S] {N : Network S} (h : N.WeaklyReversible) (r : N.R) :
    N.OnDirectedCycle r :=
  h.onDirectedCycle r

-- A 1-D field that is nonnegative near P₀ admits a zero-separating surface (wired into the
-- genuine-flow persistence layer).
example {f : ℝ → ℝ} {P₀ : ℝ} (hP₀ : 0 < P₀) (hf : ∀ y, P₀ - y ≤ 1 → 0 ≤ f y) :
    DifferentialInclusion.ZeroSeparatingSurfaceExists f P₀ :=
  DifferentialInclusion.zeroSeparatingSurfaceExists_one_dim hP₀ hf

-- The exposed face of a cone in the zero direction is the whole cone.
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : PointedCone ℝ E) : exposedFace C 0 = C :=
  exposedFace_zero C

-- The polygonal zero-separating region (intersection of region-side half-planes) is closed — the
-- load-bearing property for the distance-based Nagumo invariance.
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (faces : List (E × ℝ)) :
    IsClosed (ZeroSeparatingCurve2D.polyRegion faces) :=
  ZeroSeparatingCurve2D.isClosed_polyRegion faces

-- At a deep-interior point of a fan cell the toric field is exactly that cell's polar cone — the
-- explicit polar-cone description.
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {F : Fan E}
    {δ : ℝ} {X : E} {C₀ : ProperCone ℝ E} (hC₀F : C₀ ∈ F) (hC₀d : Metric.infDist X (C₀ : Set E) < δ)
    (hiso : ∀ C ∈ F, Metric.infDist X (C : Set E) < δ → C = C₀) :
    toricField F δ X = (coneDual (C₀ : Set E)).toPointedCone :=
  toricField_eq_coneDual_of_isolated hC₀F hC₀d hiso

-- If the region normal lies in every δ-near cell, the toric field is a support face — the
-- uncertainty-region subtangency condition.
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {F : Fan E}
    {δ : ℝ} {X n : E} (h : ∀ C ∈ F, Metric.infDist X (C : Set E) < δ → n ∈ (C : Set E))
    {a : ℝ} {faces : List (E × ℝ)} {v : E} (hv : v ∈ toricField F δ X) :
    ZeroSeparatingCurve2D.IsSupportFace (fun _ => v) faces n a :=
  isSupportFace_of_mem_forall h hv

-- If distance to the convex polygonal region is nonincreasing, the curve stays in it (the
-- support ⇒ invariance half, for the convex region).
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {faces : List (E × ℝ)} {γ : ℝ → E}
    (h0 : γ 0 ∈ ZeroSeparatingCurve2D.polyRegion faces)
    (hanti : AntitoneOn (fun t => Metric.infDist (γ t) (ZeroSeparatingCurve2D.polyRegion faces)) (Set.Ici 0))
    {t : ℝ} (ht : 0 ≤ t) : γ t ∈ ZeroSeparatingCurve2D.polyRegion faces :=
  ZeroSeparatingCurve2D.stays_in_polyRegion_of_support h0 hanti ht

-- The diagonal direction is attracting for every cell of the cross-fan — a worked instance of the
-- support-segment geometry.
example (δ : ℝ) (X : FaithfulCurveExample.Plane) :
    Faithful.AttractsTowardAll FaithfulCurveExample.crossFan δ X ZeroSeparatingCurve2D.diagNormal :=
  FaithfulCurveExample.diagNormal_attractsTowardAll δ X

-- Under per-face support the genuine curve stays in the convex polygonal region for all forward
-- time — via per-half-plane invariance (no Hoffman bound).
open scoped InnerProductSpace in
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {faces : List (E × ℝ)} {γ : ℝ → E}
    {f : E → E} (hγcont : Continuous γ) (hγ : ∀ t > 0, HasDerivAt γ (f (γ t)) t)
    (hsupp : ∀ na ∈ faces, ∀ t > 0, 0 ≤ ⟪na.1, f (γ t)⟫_ℝ)
    (h0 : γ 0 ∈ ZeroSeparatingCurve2D.polyRegion faces) {t : ℝ} (ht : 0 ≤ t) :
    γ t ∈ ZeroSeparatingCurve2D.polyRegion faces :=
  ZeroSeparatingCurve2D.polyRegion_invariant_of_support hγcont hγ hsupp h0 ht

-- A genuine trajectory of the cross-fan toric inclusion, started in the zero-separating region,
-- stays distance 1 from the origin for all time — the full chain (support → invariance →
-- separation → persistence) composed in a worked case.
open ZeroSeparatingCurve2D FaithfulCurveExample FaithfulCurveExistence in
example {δ : ℝ} {f : Plane → Plane} {γ : ℝ → Plane}
    (hsel : ∀ x : Plane, f x ∈ toricField crossFan δ (logCoords x))
    (hγcont : Continuous γ) (hγ : ∀ t > 0, HasDerivAt γ (f (γ t)) t)
    (h0 : γ 0 ∈ polyRegion crossFaces) {t : ℝ} (ht : 0 ≤ t) :
    (1 : ℝ) ≤ dist (γ t) 0 :=
  crossFan_genuine_persistent hsel hγcont hγ h0 ht

-- Two distinct chaining normals (the axis normals) cut a corner zero-separating region; the genuine
-- toric trajectory stays distance 1 from 0.
open ZeroSeparatingCurve2D FaithfulCurveExample FaithfulCurveExistence FaithfulCurveGeneral in
example {δ : ℝ} {x₀ : Plane} {f : Plane → Plane} {γ : ℝ → Plane}
    (hsel : ∀ x, f x ∈ toricField crossFan δ (logCoords x₀))
    (hγcont : Continuous γ) (hγ : ∀ t > 0, HasDerivAt γ (f (γ t)) t)
    (h0 : γ 0 ∈ polyRegion twoWallFaces) {t : ℝ} (ht : 0 ≤ t) :
    (1 : ℝ) ≤ dist (γ t) 0 :=
  twoWall_genuine_persistent hsel hγcont hγ h0 ht

-- Boundary-local strict subtangency — checked only at active faces at the curve's actual position —
-- forces the polygonal region to be forward-invariant, so distinct/conflicting segment normals are
-- handled without any global all-faces condition.
open scoped InnerProductSpace in
open ZeroSeparatingCurve2D in
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {faces : List (E × ℝ)} {γ : ℝ → E}
    {f : E → E} (hγcont : Continuous γ) (hγ : ∀ t > 0, HasDerivAt γ (f (γ t)) t)
    (hsupp : IsStrictSupportField f faces) (hstart : ∀ nf ∈ faces, nf.2 < ⟪nf.1, γ 0⟫_ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    γ t ∈ polyRegion faces :=
  polyRegion_invariant_of_strictSupport hγcont hγ hsupp hstart ht

-- The Euclidean inner product of two attracting-direction unit vectors is the cosine of the angle
-- between them — the bridge driving the monotone rotation of the faithful curve's edge normals.
open scoped InnerProductSpace in
open FaithfulCurve2D in
example (θ₁ θ₂ : ℝ) : ⟪dir θ₁, dir θ₂⟫_ℝ = Real.cos (θ₁ - θ₂) :=
  inner_dir θ₁ θ₂

-- For fan walls fitting in a sector of width < π with one positive-offset wall, the constructed
-- angular region has a nonempty strict interior AND excludes a ball about 0 — both halves of
-- "zero-separating" built outright (no abstract existence assumed).
open scoped InnerProductSpace in
open FaithfulCurve2D ZeroSeparatingCurve2D in
example (walls : List (ℝ × ℝ)) {φ θ₀ a : ℝ} (hsec : ∀ w ∈ walls, |w.1 - φ| < Real.pi / 2)
    (hmem : (θ₀, a) ∈ walls) (hpos : 0 < a) :
    (∃ x : Plane, ∀ nf ∈ facesOfAngles walls, nf.2 < ⟪nf.1, x⟫_ℝ) ∧
      polyRegion (facesOfAngles walls) ⊆ (Metric.ball (0 : Plane) a)ᶜ :=
  exists_faithful_separating_region walls hsec hmem hpos

-- Three distinct conflicting attracting directions (angles 0, π/4, π/2) chain into one constructed
-- zero-separating region — a non-degenerate instance, not a single collapsed direction.
open scoped InnerProductSpace in
open FaithfulCurve2D ZeroSeparatingCurve2D in
example :
    (∃ x : Plane, ∀ nf ∈ facesOfAngles threeWalls, nf.2 < ⟪nf.1, x⟫_ℝ) ∧
      polyRegion (facesOfAngles threeWalls) ⊆ (Metric.ball (0 : Plane) 1)ᶜ :=
  threeWall_separating_region

-- The wall direction dir θ₁ is a genuine attracting direction of the adjacent two-cell fan, so the
-- toric field lies in the wall's region-side half-plane — support from concrete planar fan geometry.
open scoped InnerProductSpace in
open FaithfulCurve2D FaithfulCurve2DFan in
example {θ₀ θ₁ θ₂ : ℝ} (h₀₁ : |θ₁ - θ₀| ≤ Real.pi / 2) (h₁₂ : |θ₂ - θ₁| ≤ Real.pi / 2)
    (δ : ℝ) (X : Plane) :
    (toricField (adjacentFan θ₀ θ₁ θ₂) δ X : Set Plane) ⊆ {y : Plane | 0 ≤ ⟪dir θ₁, y⟫_ℝ} :=
  toricField_subset_wall_halfPlane h₀₁ h₁₂ δ X

-- A ruled patch's surface normal must be orthogonal to its active tangency directions; below finrank
-- such a normal exists (3 in ℝ⁴), once they span it is killed (4 in ℝ⁴). The threshold dichotomy for
-- the surface-normal constraint system; whether a patch is forced to carry 4 directions is not decided here.
open scoped InnerProductSpace in
open ZeroSeparatingInduction in
example :
    (∀ v : Fin 3 → EuclideanSpace ℝ (Fin 4),
        ∃ n : EuclideanSpace ℝ (Fin 4), n ≠ 0 ∧ ∀ i, ⟪v i, n⟫_ℝ = 0) ∧
      (∀ n : EuclideanSpace ℝ (Fin 4),
        (∀ i, ⟪EuclideanSpace.basisFun (Fin 4) ℝ i, n⟫_ℝ = 0) → n = 0) :=
  over_determined_in_dim_four

-- Fan refinement transfers faithfulness to a coarser fan: a normal admissible for a finer cell
-- C' ⊆ C is admissible for the coarse cell C, so the finer surface is faithful for the coarse fan.
open CRNT.Faithful FanRefinement in
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : E} {C C' : ProperCone ℝ E}
    (hsub : (C' : Set E) ⊆ (C : Set E)) (h : AttractsToward n C') : AttractsToward n C :=
  attractsToward_coarse_of_fine hsub h

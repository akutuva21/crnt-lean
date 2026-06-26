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

-- The deficiency-one linkage conditions carry a (total, axiom-clean, `#eval`-only) decidability
-- instance, assembled from the per-class and tightness deciders.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) :
    Decidable N.DeficiencyOneConditions := inferInstance

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

-- The mass-action Jacobian operator is the Fréchet derivative of the vector field.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (x : Concentration S) :
    HasFDerivAt (fun x => N.massActionVectorField κ x) (N.massActionJacobianCLM κ x) x :=
  N.massActionVectorField_hasFDerivAt κ x

-- The Jacobian operator acts as the explicit Jacobian matrix.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (x v : Concentration S) :
    N.massActionJacobianCLM κ x v = (N.massActionJacobian κ x).mulVec v :=
  N.massActionJacobianCLM_apply κ x v

-- A C¹ map with positive-definite Jacobian along a convex set is injective there.
example {ι : Type} [Fintype ι] {f : (ι → ℝ) → (ι → ℝ)}
    {f' : (ι → ℝ) → ((ι → ℝ) →L[ℝ] (ι → ℝ))} {C : Set (ι → ℝ)} (hC : Convex ℝ C)
    (hf : ∀ x ∈ C, HasFDerivAt f (f' x) x)
    (hpos : ∀ x ∈ C, ∀ v : ι → ℝ, v ≠ 0 → 0 < ∑ i, v i * (f' x v) i) :
    Set.InjOn f C :=
  CRNT.injOn_of_hasFDerivAt_dotProduct_pos hC hf hpos

-- The positive compatibility class is convex.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (x₀ : Concentration S) :
    Convex ℝ (N.positiveCompatibilityClass x₀) :=
  N.convex_positiveCompatibilityClass x₀

-- Positive-definite mass-action Jacobian on a class ⇒ injective on that class.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (x₀ : Concentration S)
    (hpos : ∀ x ∈ N.positiveCompatibilityClass x₀, ∀ v : Concentration S, v ≠ 0 →
      0 < ∑ i, v i * ((N.massActionJacobian κ x).mulVec v) i) :
    (N.massActionKinetics κ).InjectiveOnClass x₀ :=
  N.massActionInjectiveOnClass_of_jacobian_pos κ x₀ hpos

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

-- Compactness of the ω-limit set of an orbit absorbed by a compact set.
example {α : Type*} [TopologicalSpace α] (ϕ : Flow ℝ≥0 α) (x₀ : α) {K : Set α}
    (hK : IsCompact K) (habs : ∃ v ∈ (Filter.atTop : Filter ℝ≥0),
      closure (Set.image2 ϕ v {x₀}) ⊆ K) :
    IsCompact (omegaLimit Filter.atTop ϕ {x₀}) :=
  (CRNT.isCompact_isInvariant_omegaLimit ϕ x₀ hK habs).1

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

-- Routh–Hurwitz in degree four (Liénard–Chipart necessity): four negative real roots of the
-- monic quartic force the five sign conditions, including the third Hurwitz determinant.
example (r₁ r₂ r₃ r₄ a₃ a₂ a₁ a₀ : ℝ)
    (hr₁ : r₁ < 0) (hr₂ : r₂ < 0) (hr₃ : r₃ < 0) (hr₄ : r₄ < 0)
    (e₃ : a₃ = -(r₁ + r₂ + r₃ + r₄))
    (e₂ : a₂ = r₁ * r₂ + r₁ * r₃ + r₁ * r₄ + r₂ * r₃ + r₂ * r₄ + r₃ * r₄)
    (e₁ : a₁ = -(r₁ * r₂ * r₃ + r₁ * r₂ * r₄ + r₁ * r₃ * r₄ + r₂ * r₃ * r₄))
    (e₀ : a₀ = r₁ * r₂ * r₃ * r₄) :
    0 < a₃ ∧ 0 < a₂ ∧ 0 < a₁ ∧ 0 < a₀ ∧ a₁ ^ 2 + a₃ ^ 2 * a₀ < a₃ * a₂ * a₁ :=
  CRNT.hurwitz_quartic_necessary_allReal r₁ r₂ r₃ r₄ a₃ a₂ a₁ a₀ hr₁ hr₂ hr₃ hr₄ e₃ e₂ e₁ e₀

-- Routh–Hurwitz in degree four (Liénard–Chipart full criterion): the five sign conditions
-- on the monic quartic hold iff all four complex roots lie in the open left half-plane.
example (z₁ z₂ z₃ z₄ : ℂ) (a₃ a₂ a₁ a₀ : ℝ)
    (e₃ : (a₃ : ℂ) = -(z₁ + z₂ + z₃ + z₄))
    (e₂ : (a₂ : ℂ) = z₁ * z₂ + z₁ * z₃ + z₁ * z₄ + z₂ * z₃ + z₂ * z₄ + z₃ * z₄)
    (e₁ : (a₁ : ℂ) = -(z₁ * z₂ * z₃ + z₁ * z₂ * z₄ + z₁ * z₃ * z₄ + z₂ * z₃ * z₄))
    (e₀ : (a₀ : ℂ) = z₁ * z₂ * z₃ * z₄)
    (hstruct : (z₁.im = 0 ∧ z₂.im = 0 ∧ z₃.im = 0 ∧ z₄.im = 0)
      ∨ (z₂ = (starRingEnd ℂ) z₁ ∧ z₃.im = 0 ∧ z₄.im = 0)
      ∨ (z₂ = (starRingEnd ℂ) z₁ ∧ z₄ = (starRingEnd ℂ) z₃)) :
    (0 < a₃ ∧ 0 < a₂ ∧ 0 < a₁ ∧ 0 < a₀ ∧ a₁ ^ 2 + a₃ ^ 2 * a₀ < a₃ * a₂ * a₁) ↔
      (z₁.re < 0 ∧ z₂.re < 0 ∧ z₃.re < 0 ∧ z₄.re < 0) :=
  CRNT.hurwitz_quartic_root_iff z₁ z₂ z₃ z₄ a₃ a₂ a₁ a₀ e₃ e₂ e₁ e₀ hstruct

-- Bridge: the third Hurwitz determinant of a quartic is the Liénard–Chipart `Δ₃`.
example (a : ℕ → ℝ) :
    CRNT.hurwitzDet a 4 3 (by norm_num) = a 3 * a 2 * a 1 - a 1 ^ 2 - a 3 ^ 2 * a 0 :=
  CRNT.hurwitzDet_three_quartic a

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

-- Colinearity classes form a genuine quotient: same class iff reaction vectors collinear.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) {r r' : N.NonzeroReaction} :
    N.colinearityClass r = N.colinearityClass r' ↔ N.ColinearReactions r.val r'.val :=
  N.colinearityClass_eq

-- Orientation dichotomy: the scalar relating two collinear nonzero vectors is signed.
example {S : Type} {v w : S → ℝ} (hw : w ≠ 0) {a : ℝ} (ha : w = a • v) : 0 < a ∨ a < 0 :=
  ColinearVec.orientation_dichotomy hw ha

-- An interconnection's vector field is the sum of the component vector fields.
example {S : Type} [DecidableEq S] [Fintype S] {N₁ N₂ : Network S}
    (K₁ : Network.Kinetics N₁) (K₂ : Network.Kinetics N₂) :
    (K₁.sum K₂).vectorField = fun x => K₁.vectorField x + K₂.vectorField x :=
  K₁.sum_vectorField K₂

-- A set is a siphon of an interconnection iff it is a siphon of each component.
example {S : Type} [DecidableEq S] [Fintype S] (N₁ N₂ : Network S) (P : Finset S) :
    (N₁.interconnect N₂).IsSiphon P ↔ N₁.IsSiphon P ∧ N₂.IsSiphon P :=
  N₁.interconnect_isSiphon_iff N₂ P

-- Injectivity of the composed field ⇒ ≤1 steady state per class of the interconnection.
example {S : Type} [DecidableEq S] [Fintype S] {N₁ N₂ : Network S}
    {K₁ : Network.Kinetics N₁} {K₂ : Network.Kinetics N₂} {x₀ : Concentration S}
    (h : (K₁.sum K₂).InjectiveOnClass x₀) {x y : Concentration S}
    (hx : x ∈ (N₁.interconnect N₂).positiveCompatibilityClass x₀)
    (hy : y ∈ (N₁.interconnect N₂).positiveCompatibilityClass x₀)
    (hsx : (N₁.interconnect N₂).IsKineticSteadyState (K₁.sum K₂) x)
    (hsy : (N₁.interconnect N₂).IsKineticSteadyState (K₁.sum K₂) y) : x = y :=
  h.sum_subsingleton_steadyState hx hy hsx hsy

-- Stoichiometrically independent components: injectivity of one lifts to the interconnection.
example {S : Type} [DecidableEq S] [Fintype S] {N₁ N₂ : Network S}
    {K₁ : Network.Kinetics N₁} {K₂ : Network.Kinetics N₂} {x₀ : Concentration S}
    (hind : N₁.StoichIndependent N₂)
    (h₁ : Set.InjOn K₁.vectorField ((N₁.interconnect N₂).positiveCompatibilityClass x₀)) :
    (K₁.sum K₂).InjectiveOnClass x₀ :=
  Network.Kinetics.InjectiveOnClass.interconnect_of_stoichIndependent_left hind h₁

-- A concordant network is monostationary under any weakly monotonic kinetics.
example {S : Type} [DecidableEq S] [Fintype S] {N : Network S} (hN : N.Concordant)
    {K : Network.Kinetics N} (hwm : K.WeaklyMonotonic) {x₀ x y : Concentration S}
    (hx : x ∈ N.positiveCompatibilityClass x₀) (hy : y ∈ N.positiveCompatibilityClass x₀)
    (hsx : N.IsKineticSteadyState K x) (hsy : N.IsKineticSteadyState K y) : x = y :=
  hN.subsingleton_steadyState hwm hx hy hsx hsy

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

-- Degree-4 Hopf crossing gate: at the boundary of the quartic Hurwitz region (`Δ₃ = 0`) one
-- conjugate pair goes purely imaginary while the other stays in the open left half-plane.
example (z₁ z₃ : ℂ) (a₃ a₂ a₁ a₀ : ℝ)
    (e₃ : (a₃ : ℂ) = -(z₁ + (starRingEnd ℂ) z₁ + z₃ + (starRingEnd ℂ) z₃))
    (e₂ : (a₂ : ℂ) = z₁ * (starRingEnd ℂ) z₁ + z₁ * z₃ + z₁ * (starRingEnd ℂ) z₃
      + (starRingEnd ℂ) z₁ * z₃ + (starRingEnd ℂ) z₁ * (starRingEnd ℂ) z₃ + z₃ * (starRingEnd ℂ) z₃)
    (e₁ : (a₁ : ℂ) = -(z₁ * (starRingEnd ℂ) z₁ * z₃ + z₁ * (starRingEnd ℂ) z₁ * (starRingEnd ℂ) z₃
      + z₁ * z₃ * (starRingEnd ℂ) z₃ + (starRingEnd ℂ) z₁ * z₃ * (starRingEnd ℂ) z₃))
    (e₀ : (a₀ : ℂ) = z₁ * (starRingEnd ℂ) z₁ * z₃ * (starRingEnd ℂ) z₃)
    (H₃ : 0 < a₃) (H₀ : 0 < a₀) (HΔ : a₁ ^ 2 + a₃ ^ 2 * a₀ = a₃ * a₂ * a₁) :
    (z₁.re = 0 ∧ z₁.im ≠ 0 ∧ z₃.re < 0) ∨ (z₃.re = 0 ∧ z₃.im ≠ 0 ∧ z₁.re < 0) :=
  CRNT.hopf_crossing_gate_quartic z₁ z₃ a₃ a₂ a₁ a₀ e₃ e₂ e₁ e₀ H₃ H₀ HΔ

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

-- The constructed Michaelis–Menten slow manifold is C¹ on the substrate ray `s ≥ 0`.
example (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) (hKm : 0 < Km) :
    ContDiffOn ℝ 1 (CRNT.MichaelisMenten.mmSlowManifoldSeed rate hrate Km Vmax).manifoldMap
      (Set.Ici 0) :=
  CRNT.MichaelisMenten.mmManifoldMap_contDiffOn rate hrate Km Vmax hKm

-- The Michaelis–Menten fast field has the invertible fibre derivative `-rate • id`.
example (rate : ℝ) (hrate : 0 < rate) (Km Vmax s : ℝ) :
    HasFDerivAt (CRNT.MichaelisMenten.mmFastField rate Km Vmax s)
      (CRNT.MichaelisMenten.mmFibreDeriv rate hrate : CRNT.MichaelisMenten.E →L[ℝ]
        CRNT.MichaelisMenten.E)
      (CRNT.MichaelisMenten.mmComplexEquil Km Vmax s • CRNT.MichaelisMenten.e0) :=
  CRNT.MichaelisMenten.mmFastField_hasFDerivAt_fibre rate hrate Km Vmax s

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

-- The cell–cell door graph's adjacency is the `CellDoor` relation.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N)
    (t t' : CRNT.Analysis.SpernerLattice.Cell N) :
    (CRNT.Analysis.SpernerLattice.cellDoorGraph κ).Adj t t'
      ↔ CRNT.Analysis.SpernerLattice.CellDoor κ t t' :=
  CRNT.Analysis.SpernerLattice.cellDoorGraph_adj κ t t'

-- The full door graph: cell–cell adjacency is `CellDoor`; cell–outer adjacency joins an outer
-- vertex to its up-triangle exactly when its hypotenuse sub-edge is a door.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N)
    (t t' : CRNT.Analysis.SpernerLattice.Cell N) :
    (CRNT.Analysis.SpernerLattice.fullDoorGraph κ).Adj (Sum.inl t) (Sum.inl t')
      ↔ CRNT.Analysis.SpernerLattice.CellDoor κ t t' :=
  CRNT.Analysis.SpernerLattice.fullDoorGraph_adj_inl_inl κ t t'
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N)
    (t : CRNT.Analysis.SpernerLattice.Cell N) (k : CRNT.Analysis.SpernerLattice.Outer N) :
    (CRNT.Analysis.SpernerLattice.fullDoorGraph κ).Adj (Sum.inl t) (Sum.inr k)
      ↔ t = CRNT.Analysis.SpernerLattice.outerTri k ∧ CRNT.Analysis.SpernerLattice.BoundaryDoor κ k :=
  CRNT.Analysis.SpernerLattice.fullDoorGraph_adj_inl_inr κ t k

-- An outer vertex has degree 1 if its hypotenuse sub-edge is a door, else 0.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N)
    (k : CRNT.Analysis.SpernerLattice.Outer N) :
    (CRNT.Analysis.SpernerLattice.fullDoorGraph κ).degree (Sum.inr k)
      = if CRNT.Analysis.SpernerLattice.BoundaryDoor κ k then 1 else 0 :=
  CRNT.Analysis.SpernerLattice.outer_degree κ k

-- An outer vertex has odd degree exactly when its sub-edge is a door.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N)
    (k : CRNT.Analysis.SpernerLattice.Outer N) :
    Odd ((CRNT.Analysis.SpernerLattice.fullDoorGraph κ).degree (Sum.inr k))
      ↔ CRNT.Analysis.SpernerLattice.BoundaryDoor κ k :=
  CRNT.Analysis.SpernerLattice.odd_degree_outer_iff κ k

-- The `outer_odd` obligation: the number of odd-degree outer vertices is odd (1-D Sperner on the
-- hypotenuse).
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N) :
    Odd #{o : CRNT.Analysis.SpernerLattice.Outer N |
      Odd ((CRNT.Analysis.SpernerLattice.fullDoorGraph κ).degree (Sum.inr o))} :=
  CRNT.Analysis.SpernerLattice.outer_odd_count κ

-- A door-neighbour of an up-triangle is pinned to one of its three lattice partners.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N)
    {u : CRNT.Analysis.SpernerLattice.Up N} {d : CRNT.Analysis.SpernerLattice.Down N}
    (h : CRNT.Analysis.SpernerLattice.CellDoor κ (Sum.inl u) (Sum.inr d)) :
    (d.1.1 = u.1.1 ∧ d.1.2 = u.1.2) ∨ (d.1.1 = u.1.1 ∧ d.1.2 + 1 = u.1.2) ∨
      (d.1.1 + 1 = u.1.1 ∧ d.1.2 = u.1.2) :=
  CRNT.Analysis.SpernerLattice.up_cellDoor_partner κ h
-- A down-triangle is never adjacent to an outer vertex.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N)
    (d : CRNT.Analysis.SpernerLattice.Down N) (k : CRNT.Analysis.SpernerLattice.Outer N) :
    ¬ (CRNT.Analysis.SpernerLattice.fullDoorGraph κ).Adj (Sum.inl (Sum.inr d)) (Sum.inr k) :=
  CRNT.Analysis.SpernerLattice.down_not_adj_outer κ d k

-- A down-triangle's door-graph degree equals its local door count.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N) (a b : ℕ) (hd : a + b + 2 ≤ N) :
    (CRNT.Analysis.SpernerLattice.fullDoorGraph κ).degree
        (Sum.inl (Sum.inr ⟨(a, b), by rw [CRNT.Analysis.SpernerLattice.mem_downCarrier]; omega⟩))
      = CRNT.Analysis.Sperner2D.doorCount
          (κ.color (CRNT.Analysis.SpernerLattice.mkPt (a + 1) b (by omega)))
          (κ.color (CRNT.Analysis.SpernerLattice.mkPt a (b + 1) (by omega)))
          (κ.color (CRNT.Analysis.SpernerLattice.mkPt (a + 1) (b + 1) (by omega))) :=
  CRNT.Analysis.SpernerLattice.down_cell_degree κ a b hd

-- An up-triangle's door-graph degree equals its local door count.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N) (a b : ℕ) (hu : a + b + 1 ≤ N) :
    (CRNT.Analysis.SpernerLattice.fullDoorGraph κ).degree
        (Sum.inl (Sum.inl ⟨(a, b), by rw [CRNT.Analysis.SpernerLattice.mem_upCarrier]; omega⟩))
      = CRNT.Analysis.Sperner2D.doorCount
          (κ.color (CRNT.Analysis.SpernerLattice.mkPt a b (by omega)))
          (κ.color (CRNT.Analysis.SpernerLattice.mkPt (a + 1) b (by omega)))
          (κ.color (CRNT.Analysis.SpernerLattice.mkPt a (b + 1) (by omega))) :=
  CRNT.Analysis.SpernerLattice.up_cell_degree κ a b hu

-- **The cell-degree obligation**: every triangle's door-graph degree equals its door count.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N)
    (t : CRNT.Analysis.SpernerLattice.Cell N) :
    (CRNT.Analysis.SpernerLattice.fullDoorGraph κ).degree (Sum.inl t)
      = CRNT.Analysis.Sperner2D.doorCount (CRNT.Analysis.SpernerLattice.col κ t).1
          (CRNT.Analysis.SpernerLattice.col κ t).2.1 (CRNT.Analysis.SpernerLattice.col κ t).2.2 :=
  CRNT.Analysis.SpernerLattice.cell_degree κ t

-- **Two-dimensional Sperner lemma (parametric N)**: every proper Sperner coloring of the
-- N-subdivision of the 2-simplex has a rainbow triangle.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N) :
    ∃ t : CRNT.Analysis.SpernerLattice.Cell N,
      CRNT.Analysis.Sperner2D.isRainbow (CRNT.Analysis.SpernerLattice.col κ t).1
        (CRNT.Analysis.SpernerLattice.col κ t).2.1
        (CRNT.Analysis.SpernerLattice.col κ t).2.2 = true :=
  CRNT.Analysis.SpernerLattice.exists_rainbow_cell κ

-- The barycentric realization lands in the standard 2-simplex.
example : CRNT.Analysis.SpernerLattice.realize
      (CRNT.Analysis.SpernerLattice.mkPt 1 1 (by omega) : CRNT.Analysis.SpernerLattice.Pt 3)
    ∈ stdSimplex ℝ (Fin 3) :=
  CRNT.Analysis.SpernerLattice.realize_mem_stdSimplex (by norm_num) _

-- Meshing sequences along which a continuous self-map is coordinate-non-increasing yield a fixed pt.
example (f : ↥(stdSimplex ℝ (Fin 3)) → ↥(stdSimplex ℝ (Fin 3))) (hf : Continuous f)
    (x : Fin 3 → ℕ → ↥(stdSimplex ℝ (Fin 3)))
    (hmesh : ∀ i j : Fin 3, Filter.Tendsto (fun n => dist (x i n) (x j n)) Filter.atTop (nhds 0))
    (hdec : ∀ (n : ℕ) (i : Fin 3), (f (x i n) : Fin 3 → ℝ) i ≤ ((x i n : Fin 3 → ℝ) i)) :
    ∃ z : ↥(stdSimplex ℝ (Fin 3)), f z = z :=
  CRNT.Analysis.brouwer_of_meshing_sequences f hf x hmesh hdec

-- **Two-dimensional Brouwer fixed-point theorem**: every continuous self-map of the standard
-- 2-simplex has a fixed point.
example (f : ↥(stdSimplex ℝ (Fin 3)) → ↥(stdSimplex ℝ (Fin 3))) (hf : Continuous f) :
    ∃ z, f z = z :=
  CRNT.Analysis.SpernerLattice.brouwer_stdSimplex_fin3 f hf
-- **The n-dimensional Brouwer fixed-point theorem**: every continuous self-map of the standard
-- n-simplex `stdSimplex ℝ (Fin (n+1))` has a fixed point, for every `n`.
example (n : ℕ) (f : ↥(stdSimplex ℝ (Fin (n + 1))) → ↥(stdSimplex ℝ (Fin (n + 1))))
    (hf : Continuous f) : ∃ z, f z = z :=
  CRNT.Analysis.SpernerN.brouwer_stdSimplex_fin n f hf
-- **Brouwer on the unit cube**: every continuous self-map of `Set.Icc 0 1 ⊆ Fin n → ℝ` has a fixed point.
example (n : ℕ) (f : (Fin n → ℝ) → (Fin n → ℝ)) (hf : ContinuousOn f (Set.Icc 0 1))
    (hmaps : Set.MapsTo f (Set.Icc (0 : Fin n → ℝ) 1) (Set.Icc 0 1)) :
    ∃ x ∈ Set.Icc (0 : Fin n → ℝ) 1, f x = x :=
  CRNT.Analysis.brouwer_cube f hf hmaps
-- **The Poincaré–Miranda theorem**: a continuous map on the cube with the standard boundary sign
-- conditions on each pair of opposite faces has a zero.
example (n : ℕ) (f : (Fin n → ℝ) → (Fin n → ℝ)) (hf : ContinuousOn f (Set.Icc 0 1))
    (hlo : ∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1, ∀ i, x i = 0 → f x i ≤ 0)
    (hhi : ∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1, ∀ i, x i = 1 → 0 ≤ f x i) :
    ∃ x ∈ Set.Icc (0 : Fin n → ℝ) 1, f x = 0 :=
  CRNT.Analysis.poincare_miranda f hf hlo hhi
-- **Brouwer for compact convex sets**: every continuous self-map of a nonempty compact convex
-- subset of `EuclideanSpace ℝ (Fin n)` has a fixed point.
example {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hne : K.Nonempty)
    (hconv : Convex ℝ K) (hcomp : IsCompact K)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : ContinuousOn f K) (hmaps : Set.MapsTo f K K) :
    ∃ x ∈ K, f x = x :=
  CRNT.Analysis.brouwer_compact_convex hne hconv hcomp f hf hmaps
example {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hne : K.Nonempty)
    (hconv : Convex ℝ K) (hcomp : IsCompact K)
    (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hv : ContinuousOn v K)
    (hmaps : Set.MapsTo (fun x => x - v x) K K) : ∃ x ∈ K, v x = 0 :=
  CRNT.Analysis.exists_zero_of_displacement_mapsTo hne hconv hcomp v hv hmaps

-- n-D Kuhn-triangulation framework: every cell has exactly n+1 vertices; lattice points realize
-- into the standard n-simplex; the corners realize to the basis vectors.
example {n N : ℕ} (c : CRNT.Analysis.SpernerN.Cell n N) : c.simplexVerts.card = n + 1 :=
  c.simplexVerts_card
example {n N : ℕ} (hN : 0 < N) (p : CRNT.Analysis.SpernerN.Pt n N) :
    CRNT.Analysis.SpernerN.realize p ∈ stdSimplex ℝ (Fin (n + 1)) :=
  CRNT.Analysis.SpernerN.realize_mem_stdSimplex hN p
example {n N : ℕ} (hN : 0 < N) (i : Fin (n + 1)) :
    CRNT.Analysis.SpernerN.realize (CRNT.Analysis.SpernerN.corner n N i) = Pi.single i 1 :=
  CRNT.Analysis.SpernerN.realize_corner hN i

-- n-D Kuhn cell mesh bound: any two vertices of a cell realize within sup-distance 1/N.
example {n N : ℕ} (hN : 0 < N) (c : CRNT.Analysis.SpernerN.Cell n N) (k k' : Fin (n + 1)) :
    dist (CRNT.Analysis.SpernerN.realize (c.vertex k))
        (CRNT.Analysis.SpernerN.realize (c.vertex k')) ≤ 1 / N :=
  CRNT.Analysis.SpernerN.cell_vertex_dist_le hN c k k'

-- n-D local Sperner parity: a colored cell has an odd door count iff it is fully labeled.
example {n : ℕ} (c : Fin (n + 1) → Fin (n + 1)) :
    Odd (CRNT.Analysis.SpernerN.doorCount c) ↔ Function.Bijective c :=
  CRNT.Analysis.SpernerN.doorCount_odd_iff c

-- n-D Kuhn facet incidence: the adjacent-transposition flip shares the dropped facet and is distinct.
example {n N : ℕ} (c : CRNT.Analysis.SpernerN.Cell n N) (m : Fin (n + 1))
    (hm0 : 0 < (m : ℕ)) (hmn : (m : ℕ) < n)
    (hv : ∀ i, 0 ≤ (c.base i : ℤ) +
      CRNT.Analysis.SpernerN.voff (CRNT.Analysis.SpernerN.flipPerm c.perm m hm0 hmn) m i) :
    CRNT.Analysis.SpernerN.facetVerts (CRNT.Analysis.SpernerN.flipCell c m hm0 hmn hv) m
        = CRNT.Analysis.SpernerN.facetVerts c m
      ∧ CRNT.Analysis.SpernerN.flipCell c m hm0 hmn hv ≠ c :=
  ⟨CRNT.Analysis.SpernerN.flipCell_facet c m hm0 hmn hv,
    CRNT.Analysis.SpernerN.flipCell_ne c m hm0 hmn hv⟩

-- A Kuhn cell is determined by its vertex function.
example {n N : ℕ} {c c' : CRNT.Analysis.SpernerN.Cell n N}
    (h : ∀ k, c.vertex k = c'.vertex k) : c = c' :=
  CRNT.Analysis.SpernerN.Cell.ext_of_vertex_eq h
-- Facet-incidence index rigidity: a shared interior-chain facet forces the dropped index and base sum.
example {n N : ℕ} (c c' : CRNT.Analysis.SpernerN.Cell n N) (m m' : Fin (n + 1))
    (hm0 : 0 < (m : ℕ)) (hmn : (m : ℕ) < n)
    (heq : CRNT.Analysis.SpernerN.facetVerts c m = CRNT.Analysis.SpernerN.facetVerts c' m') :
    m' = m ∧ CRNT.Analysis.SpernerN.Wb c = CRNT.Analysis.SpernerN.Wb c' :=
  CRNT.Analysis.SpernerN.facet_eq_index c c' m m' hm0 hmn heq
-- Two permutations agreeing off a 2-element set are equal or differ by that transposition.
example {α : Type} [DecidableEq α] (σ σ' : Equiv.Perm α) (a b : α) (hab : a ≠ b)
    (h : ∀ l, l ≠ a → l ≠ b → σ' l = σ l) : σ' = σ ∨ σ' = σ * Equiv.swap a b :=
  CRNT.Analysis.SpernerN.perm_eq_or_swap σ σ' a b hab h
-- Facet-incidence rigidity: any cell sharing an interior-chain facet is the cell or its flip.
example {n N : ℕ} (c c' : CRNT.Analysis.SpernerN.Cell n N) (m : Fin (n + 1))
    (hm0 : 0 < (m : ℕ)) (hmn : (m : ℕ) < n)
    (heq : CRNT.Analysis.SpernerN.facetVerts c m = CRNT.Analysis.SpernerN.facetVerts c' m) :
    c' = c ∨ ∃ hv, c' = CRNT.Analysis.SpernerN.flipCell c m hm0 hmn hv :=
  CRNT.Analysis.SpernerN.facet_eq_imp c c' m hm0 hmn heq
-- n-D Sperner extreme-facet rigidity: a cell sharing the vertex-0 facet is the cell itself or its
-- base-change neighbour (the shiftCell), the extreme analogue of facet_eq_imp.
example {n N : ℕ} (c c' : CRNT.Analysis.SpernerN.Cell (n + 1) N) (m' : Fin (n + 2))
    (heq : CRNT.Analysis.SpernerN.facetVerts c 0 = CRNT.Analysis.SpernerN.facetVerts c' m') :
    c' = c ∨ ∃ h : CRNT.Analysis.SpernerN.ShiftValid c, c' = CRNT.Analysis.SpernerN.shiftCell c h :=
  CRNT.Analysis.SpernerN.facet0_eq_imp c c' m' heq
-- n-D Sperner boundary reduction: dropping the last coordinate is a bijection from the boundary
-- face {x_last = 0} of the (n+1)-simplex to the n-dimensional lattice.
example {n N : ℕ} (q : CRNT.Analysis.SpernerN.Pt n N) (i : Fin (n + 1)) :
    ((CRNT.Analysis.SpernerN.boundaryEquiv n N).symm q).1.1 i.castSucc = q.1 i :=
  CRNT.Analysis.SpernerN.boundaryEquiv_symm_apply_castSucc q i
-- A door facet lying on a boundary face `{x_j = 0}` must lie on the face opposite the top color.
example {n N : ℕ} (c : CRNT.Analysis.SpernerN.Cell n N) (m : Fin (n + 1))
    (col : CRNT.Analysis.SpernerN.SpernerColoring n N) (j : Fin (n + 1))
    (hdoor : (CRNT.Analysis.SpernerN.facetVerts c m).image col.color
      = CRNT.Analysis.SpernerN.lowColors n)
    (hface : ∀ p ∈ CRNT.Analysis.SpernerN.facetVerts c m, p.1 j = 0) : j = Fin.last n :=
  CRNT.Analysis.SpernerN.door_face_eq_last c m col j hdoor hface
-- Restricting an (n+1)-D Sperner coloring along the boundary face yields an n-D Sperner coloring;
-- on the face, its color (recast up) matches the original.
example {n N : ℕ} (col : CRNT.Analysis.SpernerN.SpernerColoring (n + 1) N)
    (p : CRNT.Analysis.SpernerN.Pt (n + 1) N) (hp : p.1 (Fin.last (n + 1)) = 0) :
    ((CRNT.Analysis.SpernerN.restrictColoring col).color
        (CRNT.Analysis.SpernerN.boundaryEquiv n N ⟨p, hp⟩)).castSucc = col.color p :=
  CRNT.Analysis.SpernerN.restrictColoring_color_of_boundary col p hp
-- n-D Sperner boundary geometry: a cell vertex lies on the face x_last=0 iff the cell touches the
-- face (base_last=1) and the vertex comes after the d_last step.
example {n N : ℕ} (c : CRNT.Analysis.SpernerN.Cell (n + 1) N) (k : Fin (n + 2)) :
    (c.vertex k).1 (Fin.last (n + 1)) = 0
      ↔ (c.base (Fin.last (n + 1)) = 1
          ∧ ((c.perm⁻¹ (Fin.last n) : Fin (n + 1)) : ℕ) < (k : ℕ)) :=
  CRNT.Analysis.SpernerN.vertex_last_zero_iff c k
-- The recursion crux: a boundary door facet of an (n+1)-cell ⟺ its (n-1)-cell is rainbow under the
-- restricted coloring — the bridge that makes #boundary doors = #rainbow (n-1)-cells.
example {n N : ℕ} (c : CRNT.Analysis.SpernerN.Cell (n + 1) N) (hb : c.base (Fin.last (n + 1)) = 1)
    (hp0 : c.perm 0 = Fin.last n) (col : CRNT.Analysis.SpernerN.SpernerColoring (n + 1) N) :
    (CRNT.Analysis.SpernerN.facetVerts c 0).image col.color = CRNT.Analysis.SpernerN.lowColors (n + 1)
      ↔ Function.Bijective
          (fun k => (CRNT.Analysis.SpernerN.restrictColoring col).color
            ((CRNT.Analysis.SpernerN.bcell c hb hp0).vertex k)) :=
  CRNT.Analysis.SpernerN.door_iff_rainbow c hb hp0 col
-- n-D Kuhn cells form a finite type (the counting infrastructure for the handshaking induction).
noncomputable example {n N : ℕ} : Fintype (CRNT.Analysis.SpernerN.Cell n N) := inferInstance
-- An interior (flip-valid) facet borders exactly two Kuhn cells (the handshaking multiplicity).
noncomputable example {n N : ℕ} (c : CRNT.Analysis.SpernerN.Cell n N) (m : Fin (n + 1))
    (hm0 : 0 < (m : ℕ)) (hmn : (m : ℕ) < n)
    (hv : CRNT.Analysis.SpernerN.FlipValid c m hm0 hmn) :
    (CRNT.Analysis.SpernerN.facetSharers c m).card = 2 :=
  CRNT.Analysis.SpernerN.facet_shared_by_two c m hm0 hmn hv
-- n-D Sperner geometric crux (G1): an interior-chain door facet is always flip valid, so it borders a
-- second cell (the door's color structure forbids it from lying on an interior coordinate face).
example {n N : ℕ} (col : CRNT.Analysis.SpernerN.SpernerColoring (n + 1) N)
    (c : CRNT.Analysis.SpernerN.Cell (n + 1) N) (m : Fin (n + 2))
    (h0 : 0 < (m : ℕ)) (hn : (m : ℕ) < n + 1)
    (hdoor : CRNT.Analysis.SpernerN.IsDoorFacet col c m) :
    CRNT.Analysis.SpernerN.FlipValid c m h0 hn :=
  CRNT.Analysis.SpernerN.flipValid_of_doorFacet col c m h0 hn hdoor
-- An odd number of rainbow cells yields one (the final step of the n-D Sperner induction).
example {n N : ℕ} (col : CRNT.Analysis.SpernerN.SpernerColoring n N)
    (h : Odd (Finset.univ.filter (CRNT.Analysis.SpernerN.IsRainbowCell col)).card) :
    ∃ c, CRNT.Analysis.SpernerN.IsRainbowCell col c :=
  CRNT.Analysis.SpernerN.exists_rainbow_of_odd col h
-- n-D Sperner base case (dimension 0): the single cell is rainbow.
example {N : ℕ} (col : CRNT.Analysis.SpernerN.SpernerColoring 0 N) :
    ∃ c : CRNT.Analysis.SpernerN.Cell 0 N,
      Function.Bijective (fun k => col.color (c.vertex k)) :=
  CRNT.Analysis.SpernerN.sperner_exists_rainbow_zero col
-- n-D Sperner inductive bridge: the boundary door cells biject with the rainbow n-cells on the face,
-- so their counts agree (feeds the inductive hypothesis into the handshake).
example {n N : ℕ} (col : CRNT.Analysis.SpernerN.SpernerColoring (n + 1) N) (hN : 0 < N) :
    (Finset.univ.filter (CRNT.Analysis.SpernerN.isBoundaryDoorCell col)).card
      = (Finset.univ.filter
          (CRNT.Analysis.SpernerN.IsRainbowCell (CRNT.Analysis.SpernerN.restrictColoring col))).card :=
  CRNT.Analysis.SpernerN.boundary_doors_eq_rainbow col hN
-- The n-dimensional Sperner lemma (unconditional): every proper Sperner coloring of the N-subdivided
-- n-simplex has a rainbow Kuhn cell, and the number of rainbow cells is odd.
example {m N : ℕ} (col : CRNT.Analysis.SpernerN.SpernerColoring m N) (hN : 0 < N) :
    ∃ c : CRNT.Analysis.SpernerN.Cell m N, CRNT.Analysis.SpernerN.IsRainbowCell col c :=
  CRNT.Analysis.SpernerN.sperner_exists_rainbow col hN
example {m N : ℕ} (col : CRNT.Analysis.SpernerN.SpernerColoring m N) (hN : 0 < N) :
    Odd (Finset.univ.filter (CRNT.Analysis.SpernerN.IsRainbowCell col)).card :=
  CRNT.Analysis.SpernerN.sperner_odd_rainbow col hN
-- n-D Sperner handshake: the door incidences have the same parity as the rainbow cells (the cell side
-- of the double-count).
example {n N : ℕ} (col : CRNT.Analysis.SpernerN.SpernerColoring n N) :
    (CRNT.Analysis.SpernerN.doorIncidences col).card % 2
      = (#{c : CRNT.Analysis.SpernerN.Cell n N | CRNT.Analysis.SpernerN.IsRainbowCell col c}) % 2 :=
  CRNT.Analysis.SpernerN.card_doorIncidences_mod_two col
-- n-D Sperner last-facet rigidity: a cell sharing the last-vertex facet is the cell or its
-- base-change predecessor.
example {n N : ℕ} (c c' : CRNT.Analysis.SpernerN.Cell (n + 1) N) (m' : Fin (n + 2))
    (heq : CRNT.Analysis.SpernerN.facetVerts c (Fin.last (n + 1))
      = CRNT.Analysis.SpernerN.facetVerts c' m') :
    c' = c ∨ (m' = 0 ∧ ∃ h : CRNT.Analysis.SpernerN.ShiftValid c',
      CRNT.Analysis.SpernerN.shiftCell c' h = c) :=
  CRNT.Analysis.SpernerN.facetLast_eq_imp c c' m' heq
-- n-D Sperner: granting the handshake at every dimension, a rainbow cell exists in every dimension.
example (H : ∀ {N : ℕ}, CRNT.Analysis.SpernerN.SpernerHandshake (N := N)) {m N : ℕ}
    (col : CRNT.Analysis.SpernerN.SpernerColoring m N) (hN : 0 < N) :
    ∃ c : CRNT.Analysis.SpernerN.Cell m N, CRNT.Analysis.SpernerN.IsRainbowCell col c :=
  CRNT.Analysis.SpernerN.sperner_exists_rainbow_of_handshake H col hN

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

-- Ladder 3 (Fenichel/QSSA): the slaved slow-manifold curve's QSSA slaving defect decomposes into a
-- curve-velocity bound plus the full field's manifold residual, bounded by their sum εv + εr.
example {Y E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : ODE.SlowManifoldSeed Y E) (full : E → E) {y : ℝ → Y} {γᵣ' : ℝ → E} {a b εv εr : ℝ}
    (hvel : ∀ t ∈ Set.Ico a b, ‖γᵣ' t‖ ≤ εv)
    (hres : ∀ t ∈ Set.Ico a b, ‖full (S.manifoldMap (y t))‖ ≤ εr) :
    ODE.QssaDefect full (fun t => S.manifoldMap (y t)) γᵣ' a b (εv + εr) :=
  S.manifoldMap_qssaDefect_le full hvel hres

-- Ladder 3 (Fenichel/QSSA): when the slaved slow-manifold curve is differentiable, the converse
-- mean-value inequality derives an O(ε) velocity bound ‖γᵣ'‖ ≤ (L / rate) · ε.
example {Y E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [PseudoMetricSpace Y]
    (S : ODE.SlowManifoldSeed Y E) {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hlip : ∀ y y' z, ‖S.fast y z - S.fast y' z‖ ≤ L * dist y y')
    {y : ℝ → Y} (hy : ∀ t t', dist (y t) (y t') ≤ ε * |t - t'|)
    {γᵣ' : ℝ → E} (t₀ : ℝ) (hd : HasDerivAt (fun t => S.manifoldMap (y t)) (γᵣ' t₀) t₀) :
    ‖γᵣ' t₀‖ ≤ (L / S.rate) * ε :=
  S.manifoldMap_slowDrift_velocity_le hL hε hlip hy t₀ hd

-- Fenichel C¹: a jointly-C¹ fast field with invertible fibre derivative makes the constructed
-- slow-manifold map genuinely C¹ via the implicit function theorem.
example {Y E : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : ODE.SlowManifoldC1Seed Y E) : ContDiff ℝ 1 S.manifoldMap :=
  S.contDiff_manifoldMap

-- Ladder 3 (Fenichel/QSSA): composing the derived O(ε) defect with the Grönwall QSSA engine, the
-- full integral curve tracks the slaved slow-manifold curve within a Grönwall ball on [0, T].
example {Y E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [PseudoMetricSpace Y]
    (S : ODE.SlowManifoldSeed Y E) (full : E → E) {K : ℝ≥0} (hl : LipschitzWith K full)
    {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hlip : ∀ y y' z, ‖S.fast y z - S.fast y' z‖ ≤ L * dist y y')
    {y : ℝ → Y} (hcy : Continuous y) (hy : ∀ t t', dist (y t) (y t') ≤ ε * |t - t'|)
    {γ γᵣ' : ℝ → E} {T εr δ : ℝ} (hT : 0 ≤ T) (hδ : 0 ≤ δ) (hεr : 0 ≤ εr)
    (hγd : ∀ t, HasDerivAt γ (full (γ t)) t)
    (hd : ∀ t ∈ Set.Ico (0:ℝ) T, HasDerivAt (fun u => S.manifoldMap (y u)) (γᵣ' t) t)
    (hres : ∀ t ∈ Set.Ico (0:ℝ) T, ‖full (S.manifoldMap (y t))‖ ≤ εr)
    (h0 : dist (γ 0) (S.manifoldMap (y 0)) ≤ δ) :
    ∀ t ∈ Set.Icc (0:ℝ) T,
      dist (γ t) (S.manifoldMap (y t)) ≤ gronwallBound δ K ((L / S.rate) * ε + εr) T :=
  S.manifoldMap_qssa_tracking_le full hl hL hε hlip hcy hy hT hδ hεr hγd hd hres h0

-- Ladder 3 (Fenichel/QSSA): the compact-time tracking ball vanishes as (δ, ε, εr) → (0, 0, 0).
example {Y E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : ODE.SlowManifoldSeed Y E) (L : ℝ) (K : ℝ≥0) (T : ℝ) :
    Filter.Tendsto
      (fun p : ℝ × ℝ × ℝ => gronwallBound p.1 K ((L / S.rate) * p.2.1 + p.2.2) T)
      (nhds (0, 0, 0)) (nhds 0) :=
  S.manifoldMap_qssa_tracking_tendsto_zero L K T

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

-- Ladder 4 (CTMC): at a positive concentration on a nonempty finite closed enabled region the
-- positive-mass gate is discharged, so the normalized restricted stationary measure is an
-- unconditional invariant probability measure for the embedded jump kernel.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (c : Concentration S) (hc : c.Positive) (hcb : N.IsComplexBalanced κ c)
    {T : Set (S → ℕ)} (hT : N.ClosedEnabledRegion κ T) (hTfin : T.Finite) (hne : T.Nonempty) :
    MeasureTheory.IsProbabilityMeasure
      ((N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ • N.restrictedStationaryMeasure κ c T) :=
  (N.jumpKernel_isInvariant_probabilityMeasure_of_nonempty κ c hc hcb hT hTfin hne).2

-- Ladder 4 (CTMC): at a positive concentration the normalized invariant jump-chain probability
-- measure is strictly positive on every singleton inside a nonempty finite closed enabled region.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (c : Concentration S) (hc : c.Positive)
    {T : Set (S → ℕ)} (hT : N.ClosedEnabledRegion κ T) (hTfin : T.Finite) (hne : T.Nonempty)
    {m : S → ℕ} (hm : m ∈ T) :
    0 < ((N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ •
        N.restrictedStationaryMeasure κ c T) {m} :=
  N.jumpKernel_invariantProb_singleton_pos κ c hc hT hTfin hne hm

-- Ladder 4 (CTMC): the normalized invariant jump-chain singleton masses inside a closed enabled
-- region are cross-multiplied proportional through the jump-chain stationary weights (the discrete
-- shadow of the Anderson–Craciun–Kurtz product form).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (c : Concentration S) {T : Set (S → ℕ)} {m m' : S → ℕ} (hm : m ∈ T) (hm' : m' ∈ T) :
    ((N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ • N.restrictedStationaryMeasure κ c T) {m}
        * ENNReal.ofReal (N.jumpStationaryMass κ c m')
      = ((N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ • N.restrictedStationaryMeasure κ c T) {m'}
        * ENNReal.ofReal (N.jumpStationaryMass κ c m) :=
  N.jumpKernel_invariantProb_singleton_ratio κ c hm hm'

-- Ladder 4 (CTMC): the normalized invariant jump-chain probability measure is nonzero on a
-- singleton exactly when the count lies in the nonempty finite closed enabled region.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (c : Concentration S) (hc : c.Positive)
    {T : Set (S → ℕ)} (hT : N.ClosedEnabledRegion κ T) (hTfin : T.Finite) (hne : T.Nonempty)
    (m : S → ℕ) :
    ((N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ •
        N.restrictedStationaryMeasure κ c T) {m} ≠ 0 ↔ m ∈ T :=
  N.jumpKernel_invariantProb_singleton_ne_zero_iff κ c hc hT hTfin hne m

-- Ladder 4 (CTMC): the canonical maximal closed enabled region is itself a closed enabled region
-- (arbitrary union of such regions is one), so it carries the invariant restricted stationary measure.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N) :
    N.ClosedEnabledRegion κ (N.maximalClosedEnabledRegion κ) :=
  N.closedEnabledRegion_maximal κ

-- Ladder 5 (CTMC semigroup): the uniformized transition kernel P_t = exp(tQ) on a finite region is
-- a Markov kernel for every time t.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {T : Set (S → ℕ)} (hTfin : T.Finite) (t : ℝ≥0) :
    ProbabilityTheory.IsMarkovKernel (N.cmeSemigroup κ hTfin t) :=
  N.instIsMarkovKernel_cmeSemigroup κ hTfin t

-- Ladder 5 (CTMC semigroup): the semigroup starts at the identity kernel, P_0 = id.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {T : Set (S → ℕ)} (hTfin : T.Finite) :
    N.cmeSemigroup κ hTfin 0 = ProbabilityTheory.Kernel.id :=
  N.cmeSemigroup_zero κ hTfin

-- Ladder 5 (CTMC semigroup): the normalized product-Poisson law is invariant under every P_t — the
-- process-level companion of the generator stationarity πQ = 0.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (c : Concentration S) (hc : c.Nonnegative) (hcb : N.IsComplexBalanced κ c)
    {T : Set (S → ℕ)} (hTfin : T.Finite) (hT : N.ClosedEnabledRegion κ T) (t : ℝ≥0) :
    ProbabilityTheory.Kernel.Invariant (N.cmeSemigroup κ hTfin t)
      ((Network.cmeStationaryMeasure c T Set.univ)⁻¹ • Network.cmeStationaryMeasure c T) :=
  N.cmeSemigroup_preserves_stationarity κ c hc hcb hTfin hT t

-- The uniformized CME semigroup obeys the Chapman–Kolmogorov composition law P_{s+t} = P_s ∘ₖ P_t.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {T : Set (S → ℕ)} (hTfin : T.Finite) (s t : ℝ≥0) :
    N.cmeSemigroup κ hTfin (s + t) =
      ProbabilityTheory.Kernel.comp (N.cmeSemigroup κ hTfin s) (N.cmeSemigroup κ hTfin t) :=
  N.cmeSemigroup_comp κ hTfin s t

-- The Poisson point masses convolve over the step-count antidiagonal.
example (r₁ r₂ : ℝ≥0) (m : ℕ) :
    ∑ p ∈ Finset.antidiagonal m,
        ProbabilityTheory.poissonMeasure r₁ {p.1} * ProbabilityTheory.poissonMeasure r₂ {p.2} =
      ProbabilityTheory.poissonMeasure (r₁ + r₂) {m} :=
  Network.poissonMeasure_singleton_conv r₁ r₂ m

-- An isolated invariant set cannot trap an ω-limit set without containing it (the Butler–McGehee
-- escape core) — here the ω-limit set is invariant.
open Filter in
example {α : Type} [TopologicalSpace α] (ϕ : Flow ℝ≥0 α) (x₀ : α) :
    IsInvariant ϕ (omegaLimit atTop ϕ {x₀}) :=
  omegaLimit_isInvariant_two_sided ϕ x₀

-- The forward limit of any ω-point of a compact ω-limit set is again contained in it.
open Filter in
example {α : Type} [TopologicalSpace α] (ϕ : Flow ℝ≥0 α) (x₀ : α) {K : Set α} (hK : IsCompact K)
    (habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K)
    {q : α} (hq : q ∈ omegaLimit atTop ϕ {x₀}) :
    omegaLimit atTop ϕ {q} ⊆ omegaLimit atTop ϕ {x₀} :=
  (CRNT.isCompact_isInvariant_nonempty_omegaLimit_of_mem ϕ x₀ hK habs hq).2.2.2

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

-- A singleton critical-siphon facet has a linear near-facet influx bound: on a region bounded by M,
-- the s*-component of the field is at least -(c · x s*) (Anderson–Shiu near-facet estimate).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {sstar : S} (hsiph : N.IsSiphon ({sstar} : Finset S)) {x : Concentration S}
    (hxnn : x.Nonnegative) {M : ℝ} (hxM : ∀ s, x s ≤ M) :
    -((∑ r : N.R, κ.k r * ((N.reaction r).source sstar : ℝ)
          * (max M 1) ^ ((∑ s, (N.reaction r).source s) - 1)) * x sstar)
      ≤ N.massActionVectorField κ x sstar :=
  N.massActionVectorField_singleton_facet_ge κ hsiph hxnn hxM

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

-- The Schur complement of a P-matrix (at the last coordinate) is a P-matrix — the dimension-drop
-- step for the inductive Gale–Nikaido theorem.
example {n : ℕ} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (h : M.IsPMatrix) :
    (Matrix.schurLast M).IsPMatrix :=
  h.schurLast
-- The Schur determinant identity at the last coordinate.
example {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hd : M (Fin.last n) (Fin.last n) ≠ 0) :
    M.det = M (Fin.last n) (Fin.last n) * (Matrix.schurLast M).det :=
  Matrix.det_schurLast M hd

-- Gale–Nikaido rung 1: a map with everywhere-strict derivative whose Jacobian is a P-matrix at every
-- point is a local homeomorphism (local injectivity).
example {n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)}
    {f' : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))}
    (hf : ∀ x, HasStrictFDerivAt f (f' x) x)
    (hP : ∀ x, (CRNT.jacobianMatrix (f' x)).IsPMatrix) : IsLocalHomeomorph f :=
  CRNT.isLocalHomeomorph_of_pmatrix_fderiv hf hP
-- Gale–Nikaido rung 2: the one-dimensional base case — a P-matrix Jacobian on a 1-D box gives
-- injectivity.
example {f : (Fin 1 → ℝ) → (Fin 1 → ℝ)} {f' : (Fin 1 → ℝ) → ((Fin 1 → ℝ) →L[ℝ] (Fin 1 → ℝ))}
    {a b : Fin 1 → ℝ} (hf : ∀ x ∈ Set.Icc a b, HasFDerivAt f (f' x) x)
    (hP : ∀ x ∈ Set.Icc a b, (CRNT.jacobianMatrix (f' x)).IsPMatrix) :
    Set.InjOn f (Set.Icc a b) :=
  CRNT.injOn_of_pmatrix_fderiv_dim_one hf hP
-- Gale–Nikaido rung 3: a P-matrix stays a P-matrix under ±1 diagonal (signature) conjugation —
-- the coordinatewise sign-flip reduction.
example {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (h : M.IsPMatrix)
    {ε : Fin n → ℝ} (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    (Matrix.of (fun i j => ε i * M i j * ε j)).IsPMatrix :=
  h.signatureConj hε
-- Gale–Nikaido rung 4: the reduced map (last coordinate solved by `φ`) has Jacobian equal to the
-- Schur complement of the full Jacobian — the dimension-drop step.
example {n : ℕ} {Dφ : (Fin n → ℝ) →L[ℝ] ℝ}
    {L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)}
    (himp : ∀ Δ : Fin n → ℝ, Dφ Δ = -(CRNT.jacobianMatrix L (Fin.last n) (Fin.last n))⁻¹ *
        ∑ j, CRNT.jacobianMatrix L (Fin.last n) j.castSucc * Δ j) :
    CRNT.jacobianMatrix ((ContinuousLinearMap.pi (fun i : Fin n =>
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) i.castSucc)).comp
      (L.comp (ContinuousLinearMap.pi
        (Fin.lastCases Dφ (fun j => ContinuousLinearMap.proj j)))))
      = Matrix.schurLast (CRNT.jacobianMatrix L) :=
  CRNT.jacobianMatrix_reduced_eq_schurLast himp
-- Gale–Nikaido on a box (conditional): a C¹ map with everywhere P-matrix Jacobian is injective, given
-- last-coordinate sections through each colliding pair along which the reduced map is injective.
example {n : ℕ} {F : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)}
    {F' : (Fin (n + 1) → ℝ) → ((Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))}
    {a b : Fin (n + 1) → ℝ}
    (hF : ∀ z ∈ Set.Icc a b, HasFDerivAt F (F' z) z)
    (hP : ∀ z ∈ Set.Icc a b, (CRNT.jacobianMatrix (F' z)).IsPMatrix)
    (hsec : ∀ p ∈ Set.Icc a b, ∀ q ∈ Set.Icc a b, F p = F q →
      ∃ φ : (Fin n → ℝ) → ℝ,
        φ (Fin.init p) ∈ Set.Icc (a (Fin.last n)) (b (Fin.last n)) ∧
        φ (Fin.init q) ∈ Set.Icc (a (Fin.last n)) (b (Fin.last n)) ∧
        F (Fin.snoc (Fin.init p) (φ (Fin.init p))) (Fin.last n) = F p (Fin.last n) ∧
        F (Fin.snoc (Fin.init q) (φ (Fin.init q))) (Fin.last n) = F q (Fin.last n) ∧
        Set.InjOn (fun x => fun i : Fin n => F (Fin.snoc x (φ x)) i.castSucc)
          (Set.Icc (Fin.init a) (Fin.init b))) :
    Set.InjOn F (Set.Icc a b) :=
  CRNT.injOn_of_pmatrix_fderiv_of_sections hF hP hsec
-- **The Gale–Nikaido global univalence theorem (unconditional):** a C¹ map whose Jacobian is a
-- P-matrix at every point of a box is injective on that box. (Degree-free.)
example {n : ℕ} {F : (Fin n → ℝ) → (Fin n → ℝ)}
    {F' : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))} {lo hi : Fin n → ℝ}
    (hF : ∀ z ∈ Set.Icc lo hi, HasFDerivAt F (F' z) z)
    (hP : ∀ z ∈ Set.Icc lo hi, (CRNT.jacobianMatrix (F' z)).IsPMatrix) :
    Set.InjOn F (Set.Icc lo hi) :=
  CRNT.injOn_of_pmatrix_fderiv hF hP

-- The determinant expands as a sum over permutations with the sign read off the cycle type.
example {n : Type} [DecidableEq n] [Fintype n] {R : Type} [CommRing R] (M : Matrix n n R) :
    M.det = ∑ σ : Equiv.Perm n,
      ((σ.cycleType.map fun k => -(-1 : ℤˣ) ^ k).prod) • ∏ i, M (σ i) i :=
  CRNT.det_eq_sum_over_perm_cycleType M

-- Every species–reaction-graph cycle has even length `2k` (bipartite alternation).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) {u : N.SRVertex S}
    {w : N.srGraph.Walk u u} (hcyc : w.IsCycle) : ∃ k, w.length = 2 * k :=
  N.srCycle_length_eq_two_mul hcyc

-- The stoichiometric-subspace chart recovers a class point from its coordinate.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) {x₀ x : Concentration S}
    (h : N.StoichCompatible x₀ x) : N.affineChart x₀ (N.chartCoord x₀ x) = x :=
  N.affineChart_chartCoord h

-- A P-matrix reduced Jacobian on a class ⇒ mass-action injectivity on that class, binding the
-- box Gale–Nikaido theorem to CRN compatibility classes via coordinate reduction.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (x₀ : Concentration S) {lo hi : Fin N.stoichRank → ℝ}
    (hbox : ∀ x ∈ N.positiveCompatibilityClass x₀, N.chartCoord x₀ x ∈ Set.Icc lo hi)
    (hpm : ∀ y ∈ Set.Icc lo hi, (N.reducedJacobian κ x₀ y).IsPMatrix) :
    (N.massActionKinetics κ).InjectiveOnClass x₀ :=
  N.massActionInjectiveOnClass_of_jacobian_pmatrix κ x₀ hbox hpm

-- Brouwer zero-of-field in concentration space: an inward-displacement-preserving continuous
-- vector field on a nonempty compact convex set of concentrations has a zero there.
example {S : Type} [Fintype S] {K : Set (CRNT.Concentration S)} (hne : K.Nonempty)
    (hconv : Convex ℝ K) (hcomp : IsCompact K)
    (v : CRNT.Concentration S → CRNT.Concentration S) (hv : ContinuousOn v K)
    (hmaps : Set.MapsTo (fun x => x - v x) K K) : ∃ x ∈ K, v x = 0 :=
  CRNT.Analysis.exists_zero_of_displacement_mapsTo_concentration hne hconv hcomp v hv hmaps
-- The forward limit of an omega-point is contained in the omega-limit set, and every boundary
-- point of it carries a critical siphon on its zero set.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hKcl : IsClosed K)
    (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit Filter.atTop ϕ {x₀}, (y : Concentration S).Nonnegative)
    (hgenω : ∀ y ∈ omegaLimit Filter.atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit Filter.atTop ϕ {x₀},
      (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx0pos : x₀.Positive) {q : Concentration S}
    (hq : q ∈ omegaLimit Filter.atTop ϕ {x₀}) :
    omegaLimit Filter.atTop ϕ {q} ⊆ omegaLimit Filter.atTop ϕ {x₀} ∧
      ∀ w ∈ omegaLimit Filter.atTop ϕ {q}, ∀ P : Finset S,
        (∀ s, s ∈ P ↔ w s = 0) → P.Nonempty → N.IsCriticalSiphon P :=
  let ⟨_, _, _, hsub, hface⟩ := N.forwardLimit_subOmega_criticalSiphonFace κ hϕγ hK hKcl hmaps
    hωnn hgenω hωaff hx0pos hq
  ⟨hsub, hface⟩

example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {K : Set (CRNT.Concentration S)} (hne : K.Nonempty) (hconv : Convex ℝ K) (hcomp : IsCompact K)
    (hmaps : Set.MapsTo (fun x => x - N.massActionVectorField κ x) K K) :
    ∃ x ∈ K, N.IsMassActionSteadyState κ x :=
  N.exists_isMassActionSteadyState_of_displacement_mapsTo κ hne hconv hcomp hmaps
-- The ω-limit set of a precompact orbit contains a minimal compact invariant subset: a nonempty
-- compact closed invariant set with no proper nonempty compact closed invariant subset.
open Filter in
example {α : Type} [TopologicalSpace α] [T2Space α] (ϕ : Flow ℝ≥0 α) (x₀ : α) {K : Set α}
    (hK : IsCompact K)
    (habs : ∃ v ∈ (Filter.atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K) :
    ∃ M, M ⊆ omegaLimit atTop ϕ {x₀} ∧
      Minimal (fun C => C.Nonempty ∧ IsCompact C ∧ IsClosed C ∧ IsInvariant ϕ C) M :=
  CRNT.exists_minimal_compact_invariant_subOmega ϕ x₀ hK habs
-- Two minimal nonempty compact closed invariant sets are either equal or disjoint: the minimal
-- sets form a pairwise-disjoint antichain.
example {α : Type} [TopologicalSpace α] [T2Space α] (ϕ : Flow ℝ≥0 α) {M₁ M₂ : Set α}
    (h₁ : Minimal (fun C => C.Nonempty ∧ IsCompact C ∧ IsClosed C ∧ IsInvariant ϕ C) M₁)
    (h₂ : Minimal (fun C => C.Nonempty ∧ IsCompact C ∧ IsClosed C ∧ IsInvariant ϕ C) M₂) :
    M₁ = M₂ ∨ Disjoint M₁ M₂ :=
  CRNT.eq_or_disjoint_of_minimal_compact_invariant ϕ h₁ h₂
-- Planar trace–determinant stability test: a real 2×2 matrix has both characteristic-polynomial
-- roots in the open left half-plane iff its trace is negative and its determinant is positive.
example (M : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ z : ℂ, z * z + (-M.trace : ℂ) * z + (M.det : ℂ) = 0 → z.re < 0) ↔
      (M.trace < 0 ∧ 0 < M.det) :=
  hurwitz_matrix_fin_two_iff M
-- Stampacchia variational inequality for mass action: on a nonempty compact convex set of
-- concentrations the mass-action field lies in the outward normal cone at some point.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {K : Set (CRNT.Concentration S)} (hne : K.Nonempty) (hconv : Convex ℝ K) (hcomp : IsCompact K) :
    ∃ x ∈ K, ∀ w ∈ K, 0 ≤ ∑ s, N.massActionVectorField κ x s * (w s - x s) :=
  N.exists_steadyState_normalCone_of_compact κ hne hconv hcomp

-- Gershgorin diagonal-dominance Hurwitz test: strict row diagonal dominance with negative diagonal
-- forces every eigenvalue into the open left half-plane, in any finite dimension.
example {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (h : ∀ k, (A k k).re + ∑ j ∈ Finset.univ.erase k, ‖A k j‖ < 0) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' A) μ → μ.re < 0 :=
  hurwitz_of_strict_diag_dominance A h

-- Column form of the Gershgorin diagonal-dominance Hurwitz test: strict column diagonal dominance
-- with negative diagonal forces every eigenvalue into the open left half-plane, in any finite
-- dimension.
example {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (h : ∀ k, (A k k).re + ∑ i ∈ Finset.univ.erase k, ‖A i k‖ < 0) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' A) μ → μ.re < 0 :=
  hurwitz_of_strict_col_diag_dominance A h

-- Routh–Hurwitz, degree 3 (matrix form): a real 3×3 matrix has all three characteristic-polynomial
-- roots in the open left half-plane iff the four Routh–Hurwitz coefficient conditions on its trace,
-- second invariant, and determinant hold.
example (M : Matrix (Fin 3) (Fin 3) ℝ) :
    (∀ z : ℂ, z ^ 3 + (-M.trace : ℂ) * z ^ 2 + (M.c₂Fin3 : ℂ) * z + (-M.det : ℂ) = 0 →
        z.re < 0) ↔
      (0 < -M.trace ∧ 0 < M.c₂Fin3 ∧ 0 < -M.det ∧ -M.det < (-M.trace) * M.c₂Fin3) :=
  hurwitz_matrix_fin_three_iff M
-- Spatial Hopf eigenvalue-crossing gate: a real 3×3 matrix on the boundary of the cubic Hurwitz
-- region carries a purely imaginary conjugate eigenvalue pair (im² = c₂Fin3) and a negative real
-- eigenvalue — the algebraic precondition for a Hopf bifurcation.
example (M : Matrix (Fin 3) (Fin 3) ℝ) (z₁ z₂ : ℂ)
    (hz₁im : z₁.im = 0)
    (e₂ : (-M.trace : ℂ) = -(z₁ + z₂ + (starRingEnd ℂ) z₂))
    (e₁ : (M.c₂Fin3 : ℂ) = z₁ * z₂ + z₁ * ((starRingEnd ℂ) z₂) + z₂ * ((starRingEnd ℂ) z₂))
    (e₀ : (-M.det : ℂ) = -(z₁ * z₂ * ((starRingEnd ℂ) z₂)))
    (H₂ : 0 < -M.trace) (H₀ : 0 < -M.det) (HΔ : (-M.det) = (-M.trace) * M.c₂Fin3) :
    z₁.re < 0 ∧ z₂.re = 0 ∧ z₂.im ≠ 0 ∧ z₂.im ^ 2 = M.c₂Fin3 :=
  CRNT.hurwitz_matrix_fin_three_hopf_crossing M z₁ z₂ hz₁im e₂ e₁ e₀ H₂ H₀ HΔ
-- Hopf transversality: on the cubic Hopf boundary, with the eigenvalue real part p, real eigenvalue
-- r, and squared imaginary part q differentiable at the crossing μ₀ (p μ₀ = 0, q μ₀ ≥ 0, a₀ > 0), a
-- nonzero boundary-function velocity g'(μ₀) forces a transversal imaginary-axis crossing, p' ≠ 0.
example {r p q : ℝ → ℝ} {μ₀ r' p' q' : ℝ}
    (hr : HasDerivAt r r' μ₀) (hp : HasDerivAt p p' μ₀) (hq : HasDerivAt q q' μ₀)
    (hp0 : p μ₀ = 0) (hqnn : 0 ≤ q μ₀)
    (H₀ : 0 < -(r μ₀ * (p μ₀ ^ 2 + q μ₀)))
    (hg : deriv (fun μ => CRNT.hopfBoundaryFn (r μ) (p μ) (q μ)) μ₀ ≠ 0) :
    p' ≠ 0 :=
  CRNT.hopf_transversal_crossing hr hp hq hp0 hqnn H₀ hg
-- Critical-siphon feasibility under Farkas duality: a species vector lies in the conservation cone
-- (nonnegative, orthogonal to the stoichiometric subspace) iff every direction nonnegative on the
-- cone is nonnegative on it.
open scoped RealInnerProductSpace in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (b : EuclideanSpace ℝ S) :
    b ∈ N.conservationCone ↔
      ∀ y : EuclideanSpace ℝ S, (∀ x ∈ N.conservationCone, 0 ≤ ⟪x, y⟫) → 0 ≤ ⟪b, y⟫ :=
  N.mem_conservationCone_iff_farkas b
-- Cauchy–Binet formula: the determinant of a product of rectangular matrices expands as a sum
-- over the m-element subsets of the inner index set, one minor-product per subset.
example {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) :
    (A * B).det = ∑ S ∈ ((Finset.univ : Finset (Fin n)).powersetCard m).attach,
      (A.submatrix id (S.1.orderEmbOfFin (Finset.mem_powersetCard.mp S.2).2)).det *
        (B.submatrix (S.1.orderEmbOfFin (Finset.mem_powersetCard.mp S.2).2) id).det :=
  Matrix.det_mul_eq_sum_powersetCard A B
-- Sign-definiteness from cycle-cover terms: if every Leibniz cycle-cover term of a real square
-- matrix is nonnegative and its diagonal (identity-permutation) term is strictly positive, the
-- determinant is nonzero — the determinant-level form of the consistent-cycle-sign criterion.
example {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ)
    (hnn : ∀ σ : Equiv.Perm n, 0 ≤ CRNT.coverTerm M σ)
    (hd : 0 < CRNT.coverTerm M (1 : Equiv.Perm n)) :
    M.det ≠ 0 :=
  CRNT.det_ne_zero_of_coverTerm_signDefinite M (Or.inl ⟨hnn, hd⟩)
-- Stiemke/Gordan strict alternative: a critical siphon is a nonempty siphon for which some species
-- of it admits no supported conservation vector positive there — the strict-support feasibility
-- obstruction recast as a finite conjunction of single-coordinate Farkas problems.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (P : Finset S) :
    N.IsCriticalSiphon P ↔
      P.Nonempty ∧ N.IsSiphon P ∧
        ∃ s ∈ P, ¬ ∃ w : S → ℝ, N.SupportedConservationVector P w ∧ 0 < w s :=
  N.isCriticalSiphon_iff_exists_pointwise P
-- Jacobian cycle-sign bridge: a one-reaction cover product of the factored mass-action Jacobian
-- splits into its nonnegative rate-and-gradient magnitude times the real cast of the product of
-- the cover's signed SR-graph incidence signs.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) (σ : Equiv.Perm S) (ρ : S → N.R) :
    N.coverProductSingle κ x σ ρ =
      N.coverMagnitudeSingle κ x σ ρ *
        ((∏ i, N.signedEdge (σ i) (ρ i) : SignType) : ℝ) :=
  N.coverProductSingle_eq_magnitude_mul_sign κ x σ ρ

# Roadmap

The stable core is intentionally narrow. The items below extend it without disturbing
the existing API.

## Toward the deficiency-zero theorem

The Feinberg–Horn–Jackson deficiency-zero theorem is the headline target. Its proof is
staged as follows.

1. **Algebraic reformulation** *(in place)* — the complex space `ComplexIdx → ℝ`, the
   complex matrix `Y` (`complexMap`), the kinetic Laplacian `A_k` (`kineticMap`), and
   the monomial map `Ψ` (`complexMonomialVector`), with the factorization
   `ẋ = Y (A_k (Ψ x))`, the complex-balancing characterization `A_k (Ψ x) = 0`, and
   the corollary that complex-balanced concentrations are steady states. See
   `CRNT/Dynamics/MassActionAlgebra.lean`.
2. **Deficiency as a kernel dimension** *(complete)* — the stoichiometric map
   `stoichMap` and incidence map `incidenceMap` (`∂`), the factorization
   `stoichMap = Y ∘ ∂`, `range stoichMap = stoichSubspace`, the rank bridge
   `rank(∂) = s + dim(ker Y ∩ Im ∂)` (`incidenceRank_eq_stoichRank_add`), and the
   incidence-rank identity `rank(∂) = n − ℓ` (`incidenceRank_add_numLinkageClasses`),
   proved via the matrix-transpose route (`Matrix.rank_transpose`) with
   `ker ∂ᵀ ≅ (Quotient linkedSetoid → ℝ)` of dimension `ℓ`. These yield the
   unconditional `δ = dim(ker Y ∩ Im ∂)`
   (`deficiencyInt_eq_finrank_deficiencySubspace`) and the deficiency-zero theorem's
   structural input `DeficiencyZero ⟺ deficiencySubspace = ⊥`
   (`deficiencyZero_iff_deficiencySubspace_eq_bot`). See
   `CRNT/Deficiency/KernelDimension.lean`.
3. **Weakly reversible ⟹ `ker A_k` contains a positive vector** *(complete)* — the
   kinetic matrix `A_k` is a graph Laplacian: its columns sum to zero
   (`kineticMap_sum_eq_zero`) and reactions stay within linkage classes
   (`linked_of_reaction`). For a weakly reversible
   network each linkage class is strongly connected, so `A_k` restricted to it is an
   irreducible Metzler matrix whose kernel is one-dimensional and strictly positive.
   This is Perron–Frobenius, and the abstract theorem is now **proved**, sorry-free, in
   `CRNT.LinearAlgebra.PerronFrobenius` (Mathlib has no Brouwer, Perron–Frobenius, or
   Matrix-Tree theorem, so it is built from primitives):

   * **Existence** (`exists_nonneg_mulVec_fixed_of_colStochastic`): a column-stochastic
     nonnegative matrix has a nonnegative, nonzero fixed vector. Proved by the
     Cesàro/Markov–Kakutani argument — the affine map `x ↦ P x` preserves the compact
     convex simplex, orbit time-averages stay in it, and a convergent subsequence's limit
     is forced to be a fixed point. No Brouwer.
   * **Positivity** (`pos_of_nonneg_mulVec_fixed_of_stronglyConnected`): strong
     connectivity of the support digraph upgrades that fixed vector to strictly positive.
     Purely combinatorial.
   * **Combined** (`exists_pos_mulVec_fixed_of_stronglyConnected`): a strongly connected
     column-stochastic nonnegative matrix has a strictly positive fixed vector.

   **CRN reduction (done).**
   `CRNT.PositiveKernel.weaklyReversible_exists_positive_kernelVector` completes the
   milestone: rescale `A_k` to the column-stochastic `P = 1 + d⁻¹ A_k`, which is block-
   diagonal across linkage classes, so the strengthened existence
   (`exists_nonneg_mulVec_fixed_invariant`) keeps each class's uniform mass positive;
   weak reversibility (`WeaklyReversible.reaches_of_linked`) makes each class strongly
   connected, and positivity spreads across the whole kernel vector. See
   `CRNT/Theorems/DeficiencyZero/PositiveKernel.lean`.
4. **Birch's theorem** *(complete)* — relative to a positive reference `x*`, every
   positive stoichiometric compatibility class `c + S` contains a **unique** point with
   `S`-orthogonal log-ratio: the complex-balanced equilibrium of that class
   (`CRNT.birch`, in `CRNT/Theorems/DeficiencyZero/BirchExistence.lean`).

   * **Uniqueness** (`birch_uniqueness`, `CRNT/Theorems/DeficiencyZero/Birch.lean`): an
     elementary argument from the strict monotonicity of `Real.log` and orthogonality.
   * **Existence** (`birch_existence`) minimizes the **dual objective**
     `birchDual x* c w = ∑ᵢ (x*ᵢ exp(wᵢ) − cᵢ wᵢ)` over `Sᗮ`; the minimizer `ŵ` yields
     `x = x* ⊙ exp(ŵ)`. Its analytic chain:
     - the **Fenchel–Young inequality** `birchDualTerm_ge` (convex conjugate, dual to
       Gibbs), hence `birchDual` is **bounded below** (`birchDual_ge`);
     - **coercivity** `birchDual_coercive`: bounded sublevel sets (lower bound from
       `x*ᵢ exp wᵢ ≥ 0`, upper bound from `birchDualTerm_ge` with the *halved* coefficient
       `x*ᵢ/2` plus `Real.add_one_le_exp`);
     - the **minimizer over `Sᗮ`** `birchDual_exists_isMinOn` (continuity + coercivity +
       compactness);
     - **first-order optimality** `birchDual_firstOrder`: the line `t ↦ birchDual (ŵ + t v)`
       has a min at `0`, so `IsLocalMin.hasDerivAt_eq_zero` gives
       `∑ᵢ (x*ᵢ exp(ŵᵢ) − cᵢ) vᵢ = 0` for `v ∈ Sᗮ`, i.e. `x − c ∈ (Sᗮ)ᗮ`;
     - the **double dot-product orthogonal complement** `orthSum_orthSum` (`(Sᗮ)ᗮ = S`,
       `CRNT/LinearAlgebra/OrthogonalComplement.lean`, by transporting Mathlib's
       `Submodule.orthogonal_orthogonal` across `ι → ℝ ≃ EuclideanSpace ℝ ι`), placing
       `x − c ∈ S`.
5. **Horn–Jackson Lyapunov function** *(function + positive-definiteness done; dissipation
   open)* — the Lyapunov function `relEntropy` and its positive-definiteness about a
   reference equilibrium are proved in `CRNT/Theorems/DeficiencyZero/Lyapunov.lean`
   (Gibbs' inequality). Local asymptotic stability further requires the dissipation
   inequality `d/dt relEntropy(x(t)) ≤ 0` along mass-action trajectories and a LaSalle
   argument (deferrable).
6. **Assembly** — discharge
   `SatisfiesDeficiencyZeroHypotheses → DeficiencyZeroConclusion` in
   `CRNT/Theorems/DeficiencyZero/`.

Steps 3 and 4 are the deep ones, both now proved by building the Mathlib-adjacent
machinery they need (a Perron–Frobenius existence/positivity argument, and the Birch
existence/uniqueness result via dual-objective minimization). What remains for the
headline theorem is step 6, the assembly.

## Verified Boolean decision procedures

Provide computable companions to the propositional graph predicates, related by
equivalence theorems:

- `reachableBool : Network S → Complex S → Complex S → Bool` with
  `reachableBool_iff : reachableBool N c d = true ↔ N.Reaches c d`;
- `weaklyReversibleBool` with `weaklyReversibleBool_iff`.

The natural implementation is a verified finite-reachability closure over the
network's complex carrier (a fixed-point iteration bounded by the complex count, with a
stabilization proof). This makes `decide` close reachability goals directly and lets
`numLinkageClasses` be computed rather than only proved per example.

## Exact rank certificates

Define the stoichiometric matrix over `ℤ`/`ℚ` and check externally supplied row-
reduction certificates, yielding exact rational rank for `stoichRank` without the
noncomputable `Module.finrank`.

## The `crnt_check` tactic

A tactic that discharges the common certificate goals (complex equality, membership in
the complex set, finite reachability, weak reversibility, small deficiency
computations), so generated files need only write `by crnt_check`.

## Deficiency-zero theorem

Prove `∀ N, N.SatisfiesDeficiencyZeroHypotheses → N.DeficiencyZeroConclusion`. This is
substantial algebra; the statement interface in
`CRNT/Theorems/DeficiencyZero/Statement.lean` is already in place.

## Further theory

Deficiency-one theory and multistationarity criteria; absolute concentration robustness
(Shinar–Feinberg); detailed balance; stochastic CRN (CTMC) semantics; and SBML/SBOL
codegen bridges as separate external tools.

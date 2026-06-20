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
4. **Birch's theorem** — existence and uniqueness of the complex-balanced equilibrium in
   each positive stoichiometric compatibility class (the toric / convex-geometry core).
5. **Horn–Jackson Lyapunov function** — local asymptotic stability (deferrable).
6. **Assembly** — discharge
   `SatisfiesDeficiencyZeroHypotheses → DeficiencyZeroConclusion` in
   `CRNT/Theorems/DeficiencyZero/`.

Steps 3 and 4 are the deep ones and likely require building Mathlib-adjacent machinery
(the Markov-chain tree theorem and a Birch/toric uniqueness result).

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

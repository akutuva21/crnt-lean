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
5. **Horn–Jackson Lyapunov function & stability** *(Lyapunov function, dissipation, and
   descent done; full asymptotic stability open)* — the Lyapunov function `relEntropy` and
   its positive-definiteness about a reference equilibrium are proved in
   `CRNT/Theorems/DeficiencyZero/Lyapunov.lean` (Gibbs' inequality). Beyond that:

   * the **dissipation inequality** `dissipation_nonpos`
     (`CRNT/Theorems/DeficiencyZero/Dissipation.lean`): the directional derivative
     `∑_s (log x_s − log x*_s) f(x)_s ≤ 0`, with vanishing exactly at complex-balanced
     points (`complexBalanced_of_dissipation_eq_zero`) — `relEntropy` is a strict Lyapunov
     function. Proof termwise over reactions via the Gibbs inequality `a(log b − log a) ≤ b − a`;
   * the **Lyapunov chain rule** `relEntropy_hasDerivAt` and **descent**
     `relEntropy_antitone_along_solution` (`CRNT/Theorems/DeficiencyZero/Stability.lean`):
     `relEntropy` is nonincreasing along every positive mass-action solution;
   * the abstract **LaSalle invariance principle** `Flow.laSalle`
     (`CRNT/Dynamics/LaSalle.lean`): for a forward semiflow (`Flow ℝ≥0`), a continuous
     Lyapunov function with precompact orbit is constant on the ω-limit set — general
     dynamical-systems content, written for upstreaming.

   The **ODE foundations** are in `CRNT/Dynamics/MassActionField.lean`:

   * `massActionVectorField_contDiff`: the field `f` is `C^∞` (it is a polynomial map) — the
     regularity hypothesis of the existence theory;
   * `massActionVectorField_nonneg_of_zero`: on a boundary face `{x_s = 0}` of the orthant,
     `f_s ≥ 0` (every reaction decreasing `x_s` consumes `x_s`) — the algebraic core of
     forward-invariance of the positive orthant;
   * `exists_local_solution`: local existence of solutions from every start (Picard–Lindelöf
     via the smoothness).

   Toward the forward semiflow, `CRNT/Dynamics/FlowConstruction.lean` collects the general
   (CRN-free, upstream-targeted) lemmas, and the previously-missing analytic pieces are now
   proved:

   * **continuous dependence and uniqueness** — two global solutions of an autonomous
     Lipschitz ODE diverge at most exponentially (`ODE.dist_le_of_isIntegralCurve`, from
     Grönwall) and so a solution is determined on `[0, ∞)` by its initial value
     (`ODE.eqOn_Ici_of_isIntegralCurve`);
   * **global existence** (`ODE.exists_isIntegralCurve`) — a *bounded* Lipschitz autonomous
     field has a global integral curve through every point. Because the field is bounded the
     Picard–Lindelöf ball radius is unrestricted, giving a solution on `[-T, T]` for every
     `T` (no continuation-limit argument); the pieces are glued by uniqueness. This is the
     step the Mathlib ODE library otherwise lacks;
   * **the forward semiflow** (`ODE.exists_flow`) — a bounded Lipschitz autonomous field
     generates a `Flow ℝ≥0 E` whose orbits are its solutions (semigroup from uniqueness,
     joint continuity from continuous dependence via a local squeeze). The general
     flow-construction-with-continuous-dependence is thus complete.

   What remains is the mass-action *application*. The three analytic inputs are proved
   (`CRNT/Theorems/DeficiencyZero/Confinement.lean`):

   * **coercivity** `relEntropy_coord_le`: on the nonnegative orthant a sublevel set
     `{relEntropy x* · ≤ C}` is bounded in each coordinate (each per-coordinate term grows
     superlinearly);
   * **positivity** `pos_of_forward_deriv_ge`: a differentiable `y` with `0 < y 0` and
     `y' ≥ −L·y` (where `y > 0`) stays positive on `[0,∞)` — the first-crossing argument
     that keeps a confined trajectory off the boundary (so `relEntropy` stays differentiable
     and the dissipation descent is valid). For each species `f_s(x) ≥ −L·x_s` on a bounded
     region, supplying the hypothesis;
   * **cutoff** `exists_cutoff`: clamping each coordinate to `[-B,B]` (`clampBox`, a
     `1`-Lipschitz retraction onto the box) and precomposing the field gives a globally
     bounded, globally Lipschitz field agreeing with `f` on the box — the field
     `ODE.exists_flow` applies to. (This is the bounded-Lipschitz route, simpler than a
     smooth product-bump and free of the smooth-norm/inner-product issues.)

   Remaining — the **final assembly** on top of the proved pieces:

   * apply `ODE.exists_flow` to the cutoff field to get a `Flow ℝ≥0`; choose `B` past the
     coercivity bound of `{relEntropy x* · ≤ relEntropy x* x₀}` so the box interior contains
     that sublevel set;
   * **confinement** — the orbit of `x₀` stays in the compact set
     `K = {x.Positive ∧ relEntropy x* x ≤ relEntropy x* x₀}`: a coupled maximal-interval
     argument joining `pos_of_forward_deriv_ge` (positivity, where the cutoff equals `f`)
     and the descent + `relEntropy_coord_le` (box-confinement), each needing the other on
     `[0,T*)` and closed by continuity at `T*`;
   * **compatibility** — the orbit stays in `x₀`'s positive class (velocity `f(x) ∈ S`, so
     the displacement lies in the stoichiometric subspace);
   * **invocation** — `Flow.laSalle` (continuous `relEntropy`, precompact orbit, descent)
     gives `relEntropy` constant on `ω(x₀)`; invariance + chain rule ⟹ dissipation `= 0`
     there ⟹ `complexBalanced_of_dissipation_eq_zero` ⟹ each `ω`-point is complex-balanced
     in `x₀`'s class ⟹ by `deficiencyZeroTheorem` uniqueness equals `x*`, so
     `ω(x₀) = {x*}`.
6. **Assembly** *(complete)* — `SatisfiesDeficiencyZeroHypotheses →
   DeficiencyZeroConclusion` is discharged as `deficiencyZeroTheorem`. The toric structure
   of complex-balanced equilibria is in `CRNT/Theorems/DeficiencyZero/Toric.lean`:

   * the **monomial vector scales toricly** about a positive reference,
     `Ψ(x)_c = Ψ(x*)_c · exp(⟨c, log(x/x*)⟩)` (`complexMonomialVector_eq_mul_exp`,
     `log_complexMonomialVector`), and orthogonality to the stoichiometric subspace means
     `⟨tgt r, log(x/x*)⟩ = ⟨src r, log(x/x*)⟩` per reaction (`pairing_eq_of_orthogonal`);
   * the **toric inclusion** `complexBalanced_of_logRatio_orthogonal`: relative to a
     complex-balanced reference `x*`, any positive `x` with `log(x/x*) ⊥ S` is
     complex-balanced — proved termwise (each reaction contributing to `(A_k Ψ x)_c` is
     incident to `c`, so the common factor `exp(⟨c, log(x/x*)⟩)` pulls out of
     `A_k Ψ x* = 0`);
   * hence, **given one complex-balanced equilibrium**, every positive compatibility class
     contains one (`exists_isComplexBalanced_in_positiveClass`), by Birch existence + the
     toric inclusion.

   The **converse toric inclusion** is now also proved
   (`logRatio_orthogonal_of_complexBalanced`): for a weakly reversible network, two positive
   complex-balanced concentrations have `S`-orthogonal log-ratio. Its engine is
   **Perron–Frobenius uniqueness** (`mulVec_fixed_unique_of_stronglyConnected`, in
   `CRNT/LinearAlgebra/PerronFrobenius.lean`): on a strongly connected nonnegative matrix a
   positive fixed vector is unique up to scaling (a min-ratio argument feeding the localized
   positivity-spreading lemma `pos_of_supportReaches_pos_on`). Applied per linkage class,
   `Ψ x` and `Ψ x*` are proportional on each class, so the ratio is constant along every
   reaction. This yields **per-class uniqueness of the complex-balanced equilibrium**
   (`isComplexBalanced_unique_in_positiveClass`), via `birch_uniqueness`.

   The last gap — **existence of a first complex-balanced equilibrium** — is now also
   proved (`exists_isComplexBalanced`, in `CRNT/Theorems/DeficiencyZero/Existence.lean`),
   and this is where `δ = 0` is consumed. Weak reversibility gives a strictly positive
   kernel vector `b` of `A_k`; realizing some positive kernel vector as a monomial vector
   `Ψ x` requires the reaction-edge differences `log b(target) − log b(source)` to be of
   the form `⟨reaction vector, p⟩`. Those differences lie in the row space of the incidence
   matrix `∂ᵀ`, and **deficiency zero makes the stoichiometric and incidence row spaces
   coincide** (`range_stoichTranspose_eq`: `Im(stoichᵀ) ⊆ Im(∂ᵀ)` always, with equal
   dimensions `s = n − ℓ` exactly when `δ = 0`), so the system is solvable; `x = exp(p)` is
   then complex-balanced (`kineticMap_scale_eq_zero`).

   Combining existence (`exists_isComplexBalanced` + `exists_isComplexBalanced_in_positiveClass`)
   with uniqueness (`isComplexBalanced_unique_in_positiveClass`) discharges
   `DeficiencyZeroConclusion`: **the Feinberg–Horn–Jackson deficiency-zero theorem**
   `deficiencyZeroTheorem` is proved.

Steps 3 and 4 were the deep ones, proved by building the Mathlib-adjacent machinery they
need (a Perron–Frobenius existence/positivity/uniqueness argument, and the Birch
existence/uniqueness result via dual-objective minimization). With step 6 complete, the
**headline theorem `deficiencyZeroTheorem` is proved**; the items below are independent
extensions.

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

## Further theory

Deficiency-one theory and multistationarity criteria; absolute concentration robustness
(Shinar–Feinberg); detailed balance; stochastic CRN (CTMC) semantics; and SBML/SBOL
codegen bridges as separate external tools.

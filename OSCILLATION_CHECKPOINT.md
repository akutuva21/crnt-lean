# Oscillation formalization checkpoint — 2026-09-17

This checkpoint contains the in-progress expansion of `crnt-lean` toward proof-carrying global oscillation analysis for finite CRNs.

## Implemented in this checkpoint

- Unified periodic-orbit and oscillatory-capacity API.
- Proof-carrying fixed-parameter and structural oscillation certificates.
- Global exclusion from weakly reversible deficiency-zero CRNT.
- Global exclusion for stoichiometric rank <= 1, with the geometric argument generalized to admissible locally Lipschitz kinetics where appropriate.
- Generic exclusion lemmas from strict Lyapunov/monotone observables, convergence to a point, and equilibrium hitting plus ODE uniqueness.
- Poincare return-map bridge to exact periodic trajectories.
- Rank-two stoichiometric-coordinate reduction and planar lifting back to CRNs.
- Child selections, unstable structural cores, feedback classification, and reaction-restriction infrastructure.
- Corrected Vassena matrix vocabulary and steady-flux/core-matrix representation.
- Exact mass-action factorization `J = B(v) diag(1/x)` and realizability of positive diagonal scalings as steady-state Jacobians.
- Smooth globally positive continuation paths for Vassena/global-Hopf work.
- Floquet/monodromy interfaces, return-map contraction/stability machinery, and parameterized return-map IFT persistence.
- Exact inheritance under zero-vector/self-reaction enlargement.
- Dependent-reaction perturbation algebra and smooth epsilon-family setup.
- Planar omega-limit preprocessing, return-interval fixed-point closure, and Bendixson-Dulac local calculus/zero-flux layer.
- Global-attraction target separated from mere periodic-orbit existence.
- Analyzer contract v16, regression examples, docs, and static validation script.

## Remaining mathematical kernels

- Full Poincare-Bendixson recurrent-transversal construction/classification.
- Jordan/Green theorem needed to close Bendixson-Dulac globally.
- Global-Hopf/Fiedler continuation theorem connecting the Vassena path to periodic-orbit existence.
- Floquet-nondegeneracy to smooth parameterized Poincare-return hypotheses in full generality.
- Continuous-time interpolation from section attraction to orbital attraction.
- General Banaji-style periodic-orbit inheritance under nontrivial network enlargements.

## Validation status

`scripts/check_oscillation_static.py` passes at this checkpoint. The environment used to create this archive did not have a usable Lean 4.31/Lake toolchain and could not fetch one from GitHub, so the new Lean code has **not** yet received a full `lake build` elaboration pass. Any elaboration errors discovered on a real Lean 4.31 + pinned Mathlib environment should be fixed directly; do not replace them with axioms, `sorry`, or `admit`.

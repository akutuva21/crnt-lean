import CRNT.Multistationarity.ReducedSRGraph
import CRNT.Multistationarity.JacobianDeterminantSign
import CRNT.Multistationarity.PMatrix

/-!
# General-chart injectivity from consistently signed reduced-Jacobian covers

The reduced Jacobian `reducedJacobian κ x₀ y` is an honest `r × r` matrix (`r = stoichRank`),
the matrix of the full mass-action Jacobian restricted to its invariant stoichiometric subspace
`S(N)` in the chosen chart. Its top determinant is the chart-independent invariant
`det(M|_{S(N)})`, but its *proper* principal minors are basis-dependent: a proper principal
submatrix of `P · M · B` is `M|_{S(N)}` compressed onto a coordinate subspace of the chart, which
moves with the chart. The reduced P-matrix property is therefore not a consequence of the full
Jacobian being a P-matrix and must be phrased on the reduced covers themselves.

Reading the reduced Jacobian as any other square matrix, the abstract cover-sign machinery of
`JacobianDeterminantSign` applies to it and to each of its principal submatrices. Each principal
submatrix `(reducedJacobian κ x₀ y).submatrix incl incl` (`incl : ↥s → Fin r` the coercion) carries
its own cycle-cover decomposition `det = ∑ σ, coverTerm σ` over permutations of the restricted
chart-index set. The chart-level consistent-sign condition `ReducedConsistentSRSign` asks that, at
the chart coordinate `y`, every such cover term of every principal submatrix is nonnegative and the
diagonal cover term of every principal submatrix is strictly positive. Under it
`det_pos_of_coverTerm_nonneg` makes every reduced principal minor positive, i.e.
`IsPMatrix (reducedJacobian κ x₀ y)` — with no coordinate-selection hypothesis on the chart.

Chaining through `massActionInjectiveOnClass_of_jacobian_pmatrix`, a `ReducedConsistentSRSign`
condition holding throughout the chart box yields an `hsub`-free injectivity verdict
`massActionInjectiveOnClass_of_reducedConsistentSRSign`: the general-chart Craciun–Feinberg
monostationarity conclusion, stated on the reduced-cover sign hypothesis directly.

The remaining rung is the network-structure bridge: relating `ReducedConsistentSRSign` (a condition
on the reduced-Jacobian cover signs in the chart) back to the network's species–reaction graph, so
it is checkable from the network rather than the chart. That bridge is not built here; the chart-level
verdict is complete and `hsub`-free.

This is the reduced-coordinate species–reaction-graph injectivity route of Craciun and Feinberg
("Multiple equilibria in complex chemical reaction networks: II. The species–reaction graph"), whose
injectivity conclusion feeds the global-univalence theorem of Gale and Nikaido ("The Jacobian matrix
and global univalence of mappings").

* `ReducedConsistentSRSign` — the chart-level consistent-sign condition on the reduced-Jacobian
  covers: every principal-submatrix cover term nonnegative, every principal-submatrix diagonal cover
  term positive.
* `isPMatrix_reducedJacobian_of_reducedConsistentSRSign` — the condition makes the reduced Jacobian a
  P-matrix in the chart.
* `massActionInjectiveOnClass_of_reducedConsistentSRSign` — an `hsub`-free general-chart injectivity
  verdict from the condition holding throughout the chart box.
* `subsingleton_steadyState_of_reducedConsistentSRSign` — the corresponding monostationarity
  conclusion.

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Multistationarity.ReducedSRGraph`, `CRNT.Multistationarity.JacobianDeterminantSign`,
`CRNT.Multistationarity.PMatrix`.
-/

namespace CRNT

namespace Network

open scoped BigOperators Matrix
open Equiv Finset

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The chart-level consistent reduced-cover sign condition.** Reading the reduced Jacobian
`reducedJacobian κ x₀ y` as a plain `r × r` matrix (`r = stoichRank`), this asks that at the chart
coordinate `y` the covers of every principal submatrix share one sign: for every subset `s` of the
chart indices, every cycle-cover term `coverTerm (reducedJacobian.submatrix incl incl) σ` is
nonnegative, and the diagonal cover term of that principal submatrix is strictly positive.

This is the reduced-coordinate analogue of the consistent signed species–reaction cover of Craciun
and Feinberg; it is phrased on the reduced Jacobian's own covers, not on the full SR-graph, because
the proper reduced minors are basis-dependent and so the reduced P-matrix property does not follow
from the full Jacobian being a P-matrix. -/
def ReducedConsistentSRSign (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (y : Fin N.stoichRank → ℝ) : Prop :=
  ∀ s : Finset (Fin N.stoichRank),
    (∀ σ : Perm s,
        0 ≤ coverTerm ((N.reducedJacobian κ x₀ y).submatrix
          (fun i : s => (i : Fin N.stoichRank)) (fun i : s => (i : Fin N.stoichRank))) σ) ∧
      0 < coverTerm ((N.reducedJacobian κ x₀ y).submatrix
        (fun i : s => (i : Fin N.stoichRank)) (fun i : s => (i : Fin N.stoichRank)))
        (1 : Perm s)

/-- **The consistent reduced-cover sign condition makes the reduced Jacobian a P-matrix.** For each
subset `s` of chart indices the principal submatrix of `reducedJacobian κ x₀ y` has nonnegative
cover terms and a strictly positive diagonal cover term, so `det_pos_of_coverTerm_nonneg` makes its
determinant positive; every principal minor is positive, hence the reduced Jacobian is a P-matrix.
There is no coordinate-selection hypothesis on the chart: the condition is read off the reduced
Jacobian's own covers. -/
theorem isPMatrix_reducedJacobian_of_reducedConsistentSRSign (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (y : Fin N.stoichRank → ℝ)
    (h : N.ReducedConsistentSRSign κ x₀ y) :
    (N.reducedJacobian κ x₀ y).IsPMatrix := by
  intro s
  obtain ⟨hnonneg, hdiag⟩ := h s
  exact det_pos_of_coverTerm_nonneg _ hnonneg hdiag

/-- **`hsub`-free general-chart injectivity from a consistent reduced-cover sign condition.** Suppose
the chart coordinates of every point of the positive compatibility class of `x₀` lie in a box
`Icc lo hi`, and the consistent reduced-cover sign condition holds at every coordinate of that box.
Then the reduced Jacobian is a P-matrix throughout the box, and the box Gale–Nikaido chain — pulled
back through the affine chart by `massActionInjectiveOnClass_of_jacobian_pmatrix` — makes mass-action
kinetics injective on the class. The verdict carries no coordinate-selection hypothesis on the chart:
the sign condition is phrased on the reduced covers in the working chart. -/
theorem massActionInjectiveOnClass_of_reducedConsistentSRSign (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) {lo hi : Fin N.stoichRank → ℝ}
    (hbox : ∀ x ∈ N.positiveCompatibilityClass x₀, N.chartCoord x₀ x ∈ Set.Icc lo hi)
    (hsign : ∀ y ∈ Set.Icc lo hi, N.ReducedConsistentSRSign κ x₀ y) :
    (N.massActionKinetics κ).InjectiveOnClass x₀ :=
  N.massActionInjectiveOnClass_of_jacobian_pmatrix κ x₀ hbox
    (fun y hy => N.isPMatrix_reducedJacobian_of_reducedConsistentSRSign κ x₀ y (hsign y hy))

/-- **Monostationarity from a consistent reduced-cover sign condition.** Under the hypotheses of
`massActionInjectiveOnClass_of_reducedConsistentSRSign`, the positive compatibility class of `x₀`
carries at most one positive mass-action steady state. This is the `hsub`-free general-chart
Craciun–Feinberg monostationarity conclusion. -/
theorem subsingleton_steadyState_of_reducedConsistentSRSign (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) {lo hi : Fin N.stoichRank → ℝ}
    (hbox : ∀ x ∈ N.positiveCompatibilityClass x₀, N.chartCoord x₀ x ∈ Set.Icc lo hi)
    (hsign : ∀ y ∈ Set.Icc lo hi, N.ReducedConsistentSRSign κ x₀ y)
    {x y : Concentration S}
    (hx : x ∈ N.positiveCompatibilityClass x₀) (hy : y ∈ N.positiveCompatibilityClass x₀)
    (hsx : N.IsMassActionSteadyState κ x) (hsy : N.IsMassActionSteadyState κ y) : x = y :=
  N.subsingleton_steadyState_of_jacobian_pmatrix κ x₀ hbox
    (fun y hy => N.isPMatrix_reducedJacobian_of_reducedConsistentSRSign κ x₀ y (hsign y hy))
    hx hy hsx hsy

end Network

end CRNT

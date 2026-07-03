import CRNT.Multistationarity.ReducedCoverSign
import CRNT.Multistationarity.ReducedSRGraph

/-!
# A network-checkable bridge to the consistent reduced-cover sign condition

The general-chart injectivity verdict `massActionInjectiveOnClass_of_reducedConsistentSRSign`
of `ReducedCoverSign` runs off `ReducedConsistentSRSign`, a sign condition on the cycle covers of
the principal submatrices of the reduced Jacobian `reducedJacobian κ x₀ y`. That predicate is
phrased on the reduced Jacobian read as an abstract `r × r` matrix (`r = stoichRank`); to use it the
caller must already have the reduced matrix in hand. This module re-expresses the very same condition
on the network's own data, so the verdict becomes checkable from the network.

The reduced Jacobian is the oblique compression `reducedJacobian κ x₀ y = P · M · B`
(`reducedJacobian_eq_mul`) of the full mass-action Jacobian
`M = massActionJacobian κ (affineChart x₀ y)` through the chart matrix `B = stoichChartMatrix` and
its dual projection `P = stoichProjMatrix`. Each principal submatrix of the reduced Jacobian is
therefore the corresponding principal submatrix of `P · M · B`, and each of its cycle-cover terms is
a `coverTerm` of that chart-transported full-Jacobian compression. The condition is genuinely
**chart-anchored** — it depends on the chosen basis `B` through `P · M · B` — because the proper
reduced minors are basis-dependent, exactly as recorded in `ReducedSRGraph`: the reduced P-matrix
property is not a consequence of `M` being a P-matrix and so cannot be phrased on the full
species–reaction graph alone.

* `ReducedJacobianCompressionSRSign` — the chart-anchored network condition: at the chart coordinate
  `y`, every cycle-cover term of every principal submatrix of the chart-transported full Jacobian
  `P · M · B` is nonnegative, and the diagonal cover term of every principal submatrix is strictly
  positive. This reads off the network data `κ`, `x₀`, the chart `B`/`P`, and the full mass-action
  Jacobian `M`, with no reference to the abstract reduced matrix.
* `reducedConsistentSRSign_of_compressionSRSign` — the condition implies `ReducedConsistentSRSign`,
  since `reducedJacobian κ x₀ y` *is* `P · M · B`.
* `massActionInjectiveOnClass_of_compressionSRSign` — composing with
  `massActionInjectiveOnClass_of_reducedConsistentSRSign`, the chart-anchored network condition
  holding throughout the chart box yields the `hsub`-free general-chart Craciun–Feinberg injectivity
  verdict, now stated on network-checkable data.
* `subsingleton_steadyState_of_compressionSRSign` — the corresponding monostationarity conclusion.

A fully chart-free condition phrased on the network's signed species–reaction graph alone is not
available for the proper reduced minors: the magnitude/sign split
`coverProductSingle_eq_magnitude_mul_sign` of `JacobianCycleSign` factors a cover term of the *full*
Jacobian `M` over the full species set into a nonnegative rate-and-gradient magnitude times a product
of signed SR-incidence signs, but a proper principal minor of `P · M · B` mixes the full-Jacobian
entries through the chart `B`/`P` and is not a single such SR-cover; its sign is basis-dependent. The
chart-anchored form here is the appropriate network-checkable bridge.

This is the reduced-coordinate species–reaction-graph injectivity route of Craciun and Feinberg
("Multiple equilibria in complex chemical reaction networks: II. The species–reaction graph"), whose
injectivity conclusion feeds the global-univalence theorem of Gale and Nikaido ("The Jacobian matrix
and global univalence of mappings").

Depends on:
`CRNT.Multistationarity.ReducedCoverSign`, `CRNT.Multistationarity.ReducedSRGraph`.
-/

namespace CRNT

namespace Network

open scoped BigOperators Matrix
open Equiv Finset

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The chart-anchored network compression-cover sign condition.** Reading the chart-transported
full mass-action Jacobian `P · M · B` (with `M = massActionJacobian κ (affineChart x₀ y)`,
`B = stoichChartMatrix`, `P = stoichProjMatrix`) as a plain `r × r` matrix, this asks that at the
chart coordinate `y` the covers of every principal submatrix share one sign: for every subset `s` of
the chart indices, every cycle-cover term of the principal submatrix is nonnegative, and the diagonal
cover term of that principal submatrix is strictly positive.

This is the network-data presentation of `ReducedConsistentSRSign`: it is read off `κ`, `x₀`, the
full Jacobian `M`, and the chart `B`/`P`, never the abstract reduced matrix. It is chart-anchored —
it depends on the chosen basis `B` — because the proper reduced minors are genuinely
basis-dependent. -/
def ReducedJacobianCompressionSRSign (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (y : Fin N.stoichRank → ℝ) : Prop :=
  ∀ s : Finset (Fin N.stoichRank),
    (∀ σ : Perm s,
        0 ≤ coverTerm ((N.stoichProjMatrix * N.massActionJacobian κ (N.affineChart x₀ y)
            * N.stoichChartMatrix).submatrix
          (fun i : s => (i : Fin N.stoichRank)) (fun i : s => (i : Fin N.stoichRank))) σ) ∧
      0 < coverTerm ((N.stoichProjMatrix * N.massActionJacobian κ (N.affineChart x₀ y)
          * N.stoichChartMatrix).submatrix
        (fun i : s => (i : Fin N.stoichRank)) (fun i : s => (i : Fin N.stoichRank)))
        (1 : Perm s)

/-- **The compression-cover sign condition is the consistent reduced-cover sign condition.** The
reduced Jacobian is the oblique compression `reducedJacobian κ x₀ y = P · M · B`
(`reducedJacobian_eq_mul`), so its principal submatrices are exactly the principal submatrices of
`P · M · B`. The two sign conditions therefore coincide term by term, and the network-data condition
implies `ReducedConsistentSRSign`. -/
theorem reducedConsistentSRSign_of_compressionSRSign (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (y : Fin N.stoichRank → ℝ)
    (h : N.ReducedJacobianCompressionSRSign κ x₀ y) :
    N.ReducedConsistentSRSign κ x₀ y := by
  intro s
  rw [reducedJacobian_eq_mul]
  exact h s

/-- **`hsub`-free general-chart injectivity from the chart-anchored network condition.** Suppose the
chart coordinates of every point of the positive compatibility class of `x₀` lie in a box `Icc lo hi`,
and the compression-cover sign condition holds at every coordinate of that box. Then, since the
condition coincides with `ReducedConsistentSRSign`, the reduced Jacobian is a P-matrix throughout the
box and the box Gale–Nikaido chain makes mass-action kinetics injective on the class. The verdict is
now stated on network-checkable data — the full Jacobian `M` transported through the chart `B`/`P` —
and carries no coordinate-selection hypothesis on the chart. -/
theorem massActionInjectiveOnClass_of_compressionSRSign (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) {lo hi : Fin N.stoichRank → ℝ}
    (hbox : ∀ x ∈ N.positiveCompatibilityClass x₀, N.chartCoord x₀ x ∈ Set.Icc lo hi)
    (hsign : ∀ y ∈ Set.Icc lo hi, N.ReducedJacobianCompressionSRSign κ x₀ y) :
    (N.massActionKinetics κ).InjectiveOnClass x₀ :=
  N.massActionInjectiveOnClass_of_reducedConsistentSRSign κ x₀ hbox
    (fun y hy => N.reducedConsistentSRSign_of_compressionSRSign κ x₀ y (hsign y hy))

/-- **Monostationarity from the chart-anchored network condition.** Under the hypotheses of
`massActionInjectiveOnClass_of_compressionSRSign`, the positive compatibility class of `x₀` carries
at most one positive mass-action steady state: the `hsub`-free general-chart Craciun–Feinberg
monostationarity conclusion, now phrased on network-checkable data. -/
theorem subsingleton_steadyState_of_compressionSRSign (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) {lo hi : Fin N.stoichRank → ℝ}
    (hbox : ∀ x ∈ N.positiveCompatibilityClass x₀, N.chartCoord x₀ x ∈ Set.Icc lo hi)
    (hsign : ∀ y ∈ Set.Icc lo hi, N.ReducedJacobianCompressionSRSign κ x₀ y)
    {x y : Concentration S}
    (hx : x ∈ N.positiveCompatibilityClass x₀) (hy : y ∈ N.positiveCompatibilityClass x₀)
    (hsx : N.IsMassActionSteadyState κ x) (hsy : N.IsMassActionSteadyState κ y) : x = y :=
  N.subsingleton_steadyState_of_reducedConsistentSRSign κ x₀ hbox
    (fun y hy => N.reducedConsistentSRSign_of_compressionSRSign κ x₀ y (hsign y hy))
    hx hy hsx hsy

end Network

end CRNT

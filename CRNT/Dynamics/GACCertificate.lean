import CRNT.Dynamics.GACSeparatingWitness

/-!
# A checkable certificate for the global attractor conclusion

The global attractor conjecture for weakly reversible complex-balanced networks is reduced, in
`gac_of_separatingConfinement`, to a single geometric predicate: that the genuine mass-action orbit
through the start is confined to a bounded region holding a fixed positive distance above every
coordinate facet (`Network.SeparatingConfinement`). This module packages that predicate as a
per-network certificate with a soundness theorem and constructors from the proven
classes, so the conclusion becomes a checkable property of one bundled datum rather than a theorem
to be reproved network by network.

`Network.GACCertificate N κ x₀` carries exactly the separating-confinement datum. Its soundness
theorem `Network.gac_of_gacCertificate` discharges the global attractor conclusion — the genuine
semiflow's ω-limit set through `x₀` is `{x*}` — for any network supplying the certificate together
with the standing data (weak reversibility, a positive complex-balanced reference, a positive start
in its class). Soundness routes through `gac_of_separatingConfinement`, so the certificate inherits
the full reduction with no additional content.

The certificate is non-vacuous: it is constructible on every class for which separating confinement
is already established. `Network.gacCertificate_of_hasNoCriticalSiphon` builds it on the
no-critical-siphon class (a decidable structural condition, Anderson–Craciun–Kurtz,
_Product-form stationary distributions for deficiency zero chemical reaction networks_), and
`Network.gacCertificate_of_local` builds it in the near-equilibrium regime, where the relative
entropy of the start lies below every reference coordinate.

For the curved case of Craciun, _Toric differential inclusions and a proof of the global attractor
conjecture_, the certificate's region datum is exactly the zero-separating surface that is not
otherwise constructed here. The certificate does not solve that case; it isolates it as the single
field that remains to be filled. The framework makes the global attractor conclusion **checkable**
per network — supply the separating region and soundness delivers the conclusion — not solved in
general.

## Contents

* `Network.GACCertificate N κ x₀` — a structure bundling the separating-confinement datum
  sufficient for the global attractor conclusion at `x₀`.

* `Network.gac_of_gacCertificate` — soundness: the certificate, with the standing data, implies the
  genuine semiflow's ω-limit set through `x₀` is `{x*}`.

* `Network.gacCertificate_of_hasNoCriticalSiphon` and `Network.gacCertificate_of_local` —
  constructors exhibiting the certificate on the no-critical-siphon class and near equilibrium.

* `Network.persistentFrom_of_gacCertificate` and `Network.gacCertificate_of_persistentFrom` — the
  certificate is interchangeable with the persistence certificate `Network.PersistentFrom` (the
  reverse for a positive start), so the verifiable target and the single-linkage persistence input
  carry the same content.

Depends on: `CRNT.Dynamics.GACSeparatingWitness`.
-/

open scoped BigOperators NNReal Topology
open Filter

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **A checkable certificate for the global attractor conclusion.** The certificate carries the
separating-confinement datum (`Network.SeparatingConfinement`): a bounded region holding the genuine
mass-action orbit through `x₀` a fixed positive distance above every coordinate facet. This is the
single predicate to which `gac_of_separatingConfinement` reduces the global attractor conjecture for
weakly reversible complex-balanced networks; bundling it as a structure gives the verifiable-reward
loop one type to target, with the open curved case reduced to supplying this one field. -/
structure GACCertificate (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) : Prop where
  /-- The separating-confinement datum: a bounded forward-invariant region for the genuine orbit
  through `x₀`, bounded a fixed positive distance off every facet. -/
  separatingConfinement : N.SeparatingConfinement κ x₀

/-- **Soundness of the certificate.** For a weakly reversible network with a positive
complex-balanced reference `x*` and a positive start `x₀` in its class, a `GACCertificate` implies
the global attractor conclusion: the genuine mass-action semiflow's ω-limit set through `x₀` is
`{x*}`. The proof routes the certificate's separating-confinement datum through
`gac_of_separatingConfinement`, so the certificate carries the full reduction and no extra content.
-/
theorem gac_of_gacCertificate
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar)
    (cert : N.GACCertificate κ x₀) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} :=
  N.gac_of_separatingConfinement hwr κ hxs hcb hx0 hx0compat cert.separatingConfinement

/-- **The certificate on the no-critical-siphon class.** For a weakly reversible network with no
critical siphon, a positive complex-balanced reference `x*`, and a positive start `x₀` in its class,
the `GACCertificate` is constructible: `separatingConfinement_of_hasNoCriticalSiphon` builds the
required region. The no-critical-siphon condition is a decidable structural precondition, so this
constructor exhibits the certificate as non-vacuous on a fully recognizable class. -/
theorem gacCertificate_of_hasNoCriticalSiphon
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants) (hncs : N.HasNoCriticalSiphon)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar) :
    N.GACCertificate κ x₀ :=
  ⟨N.separatingConfinement_of_hasNoCriticalSiphon hwr κ hncs hxs hcb hx0 hx0compat⟩

/-- **The certificate near equilibrium.** When the relative entropy of the start lies strictly below
every reference coordinate (`hloc : ∀ s, relEntropy x* x₀ < x*_s`), the `GACCertificate` is
constructible: `separatingConfinement_of_local` exhibits the relative-entropy sublevel set through
`x₀` as the required confining region. This constructor exhibits the certificate as non-vacuous in
the near-equilibrium regime under an explicit, checkable closeness hypothesis. -/
theorem gacCertificate_of_local
    (N : Network S) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hloc : ∀ s, relEntropy xstar x₀ < xstar s) :
    N.GACCertificate κ x₀ :=
  ⟨N.separatingConfinement_of_local κ hxs hcb hx0 hloc⟩

/-- **The certificate gives the persistence certificate.** A `GACCertificate` yields
`Network.PersistentFrom`, the absorbing-set input consumed by `gac_of_persistent` and the
single-linkage development, via `persistentFrom_of_separatingConfinement`. -/
theorem persistentFrom_of_gacCertificate
    (N : Network S) (κ : N.RateConstants) {x₀ : Concentration S} (cert : N.GACCertificate κ x₀) :
    N.PersistentFrom κ x₀ :=
  N.persistentFrom_of_separatingConfinement κ cert.separatingConfinement

/-- **The persistence certificate gives the certificate, for a positive start.** A
`Network.PersistentFrom` datum — a compact positive absorbing set — yields a `GACCertificate` via
`separatingConfinement_of_persistentFrom`. With `persistentFrom_of_gacCertificate` the two are
interchangeable for a positive start, so the verifiable target and the single-linkage persistence
input carry the same content. -/
theorem gacCertificate_of_persistentFrom
    (N : Network S) (κ : N.RateConstants) {x₀ : Concentration S} (hx0 : x₀.Positive)
    (hpf : N.PersistentFrom κ x₀) :
    N.GACCertificate κ x₀ :=
  ⟨N.separatingConfinement_of_persistentFrom κ hx0 hpf⟩

end Network

end CRNT

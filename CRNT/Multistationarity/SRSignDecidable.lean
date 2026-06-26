import CRNT.Multistationarity.SRInjectivityClass

/-!
# A decidable certificate for the consistent signed SR-cover condition

The species–reaction graph injectivity verdict
(`massActionInjectiveOnClass_of_consistentSRSign`) rests on a sign hypothesis `hweight`: over
every restricted species set, every reaction-choice cover carries a nonnegative signed-incidence
weight `(coverCoeff σ) · ∏ a, signedEdge (σ a) (ρ a)`. As stated that hypothesis lives over the
reals — `signedEdge` is the `SignType` sign of a real reaction-vector coordinate, so the weight is
a real number and its sign cannot be settled by computation.

This module makes the condition computable. The signed incidence of `(s, r)` is the comparison of
two natural-number complex coordinates `(reaction r).source s` and `(reaction r).target s`, so it
is decided by `intSignedEdge`, a `SignType`-valued `if`-cascade that agrees with `signedEdge`
(`intSignedEdge_eq`). The cover weight is then a product of `SignType` values scaled by the
cycle-cover unit `coverCoeff σ : ℤˣ`, both cast to `ℤ`, where the order is decidable. The
resulting predicate `ConsistentSRSign` quantifies over the finite domain
`Finset S × Perm s × (s → N.R)` and carries a `Decidable` instance, so a concrete network settles
it by `decide`. Its real-cast image is exactly the verdict's `hweight`
(`hweight_of_consistentSRSign`), whence `massActionInjectiveOnClass_of_consistentSRSign_decide`
and `subsingleton_steadyState_of_consistentSRSign_decide` take the decidable certificate in place
of `hweight`: a network whose chart, box, and diagonal hypotheses are supplied discharges
mass-action injectivity — and monostationarity — on the positive compatibility class by a kernel
sign computation.

This is the computable face of the Craciun–Feinberg signed species–reaction graph injectivity
criterion ("Multiple equilibria in complex chemical reaction networks: I. The injectivity
property" and "II. The species–reaction graph").

* `intSignedEdge` — the computable `SignType` incidence sign, comparing the natural source and
  target multiplicities of the species in the reaction.
* `ConsistentSRSign` — the decidable consistent-signed-SR-cover predicate over the finite cover
  domain, with its `Decidable` instance.
* `hweight_of_consistentSRSign` — the certificate's real-cast image is the verdict's weight
  hypothesis.
* `massActionInjectiveOnClass_of_consistentSRSign_decide` /
  `subsingleton_steadyState_of_consistentSRSign_decide` — the verdict and its monostationarity
  payoff with the sign hypothesis replaced by the `decide`-friendly certificate.

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Multistationarity.SRInjectivityClass`.
-/

namespace CRNT

namespace Network

open scoped BigOperators
open Equiv Finset

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The **computable signed incidence** of species `s` in reaction `r`: the `SignType` sign of the
net stoichiometric change, decided by comparing the natural source and target multiplicities
`(reaction r).source s` and `(reaction r).target s`. It is the computable companion of
`signedEdge`, whose real reaction-vector sign it reproduces (`intSignedEdge_eq`). -/
def intSignedEdge (N : Network S) (s : S) (r : N.R) : SignType :=
  if (N.reaction r).source s < (N.reaction r).target s then 1
  else if (N.reaction r).target s < (N.reaction r).source s then -1
  else 0

/-- The computable incidence sign agrees with `signedEdge`: the natural-multiplicity comparison
reproduces the `SignType` sign of the real reaction-vector coordinate. -/
theorem intSignedEdge_eq (N : Network S) (s : S) (r : N.R) :
    N.intSignedEdge s r = N.signedEdge s r := by
  rw [signedEdge, reactionVector_apply, intSignedEdge]
  rcases lt_trichotomy ((N.reaction r).source s) ((N.reaction r).target s) with h | h | h
  · rw [if_pos h, eq_comm,
      sign_pos (by
        have : ((N.reaction r).source s : ℝ) < (N.reaction r).target s := by exact_mod_cast h
        linarith)]
  · rw [h, if_neg (lt_irrefl _), if_neg (lt_irrefl _)]; simp
  · rw [if_neg (by omega), if_pos h, eq_comm,
      sign_neg (by
        have : ((N.reaction r).target s : ℝ) < (N.reaction r).source s := by exact_mod_cast h
        linarith)]

/-- **The decidable consistent-signed-SR-cover predicate.** Over every restricted species set `s`,
every reaction-choice cover `(σ, ρ)` carries a nonnegative signed-incidence weight
`(coverCoeff σ) · ∏ a, intSignedEdge (σ a) (ρ a)`, read in `ℤ` where the order is decidable. The
quantifiers range over the finite domain `Finset S × Perm s × (s → N.R)`, so the predicate is
decidable; its real-cast image is the verdict's weight hypothesis (`hweight_of_consistentSRSign`). -/
def ConsistentSRSign (N : Network S) : Prop :=
  ∀ (s : Finset S) (σ : Perm s) (ρ : s → N.R),
    (0 : ℤ) ≤ (coverCoeff σ : ℤ) *
      ((∏ a : s, N.intSignedEdge ((σ a : S)) (ρ a) : SignType) : ℤ)

instance (N : Network S) : Decidable N.ConsistentSRSign := by
  unfold ConsistentSRSign; infer_instance

/-- The certificate's real-cast image is exactly the weight hypothesis the species–reaction graph
injectivity verdict consumes: nonnegativity of `(coverCoeff σ) · ∏ a, signedEdge (σ a) (ρ a)` over
every restricted cover. The `ℤ`-valued inequality transports to `ℝ` by the order-reflecting cast,
after rewriting `intSignedEdge` to `signedEdge`. -/
theorem hweight_of_consistentSRSign (N : Network S) (h : N.ConsistentSRSign) :
    ∀ (s : Finset S) (σ : Perm s) (ρ : s → N.R),
      0 ≤ ((coverCoeff σ : ℤ) : ℝ) *
        ((∏ a : s, N.signedEdge ((σ a : S)) (ρ a) : SignType) : ℝ) := by
  intro s σ ρ
  have key := h s σ ρ
  simp_rw [intSignedEdge_eq] at key
  have hcast : ((0 : ℤ) : ℝ) ≤
      (((coverCoeff σ : ℤ) *
        ((∏ a : s, N.signedEdge ((σ a : S)) (ρ a) : SignType) : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast key
  push_cast at hcast
  exact hcast

/-- **Mass-action injectivity on a compatibility class from a decidable signed SR-cover
certificate.** This is `massActionInjectiveOnClass_of_consistentSRSign` with the real weight
hypothesis replaced by the decidable `ConsistentSRSign` certificate: a concrete network discharges
the sign condition by `decide` and, given the chart box, positivity, positive-diagonal, and
coordinate-selection hypotheses, the mass-action kinetics is injective on the positive
compatibility class. -/
theorem massActionInjectiveOnClass_of_consistentSRSign_decide (N : Network S)
    (κ : N.RateConstants) (x₀ : Concentration S) {lo hi : Fin N.stoichRank → ℝ}
    {f : Fin N.stoichRank → S} (hf : Function.Injective f)
    (hbox : ∀ x ∈ N.positiveCompatibilityClass x₀, N.chartCoord x₀ x ∈ Set.Icc lo hi)
    (hpos : ∀ y ∈ Set.Icc lo hi, Concentration.Positive (N.affineChart x₀ y))
    (hsign : N.ConsistentSRSign)
    (hdiag : ∀ y ∈ Set.Icc lo hi, ∀ i : S,
      0 < (N.massActionJacobian κ (N.affineChart x₀ y)) i i)
    (hsub : ∀ y ∈ Set.Icc lo hi, N.reducedJacobian κ x₀ y
      = (N.massActionJacobian κ (N.affineChart x₀ y)).submatrix f f) :
    (N.massActionKinetics κ).InjectiveOnClass x₀ :=
  N.massActionInjectiveOnClass_of_consistentSRSign κ x₀ hf hbox hpos
    (fun _ _ => N.hweight_of_consistentSRSign hsign) hdiag hsub

/-- **Monostationarity from a decidable signed SR-cover certificate.** Under the hypotheses of
`massActionInjectiveOnClass_of_consistentSRSign_decide`, the positive compatibility class of `x₀`
carries at most one positive mass-action steady state. The Craciun–Feinberg injectivity verdict in
its monostationarity form, with the sign condition supplied by `decide`. -/
theorem subsingleton_steadyState_of_consistentSRSign_decide (N : Network S)
    (κ : N.RateConstants) (x₀ : Concentration S) {lo hi : Fin N.stoichRank → ℝ}
    {f : Fin N.stoichRank → S} (hf : Function.Injective f)
    (hbox : ∀ x ∈ N.positiveCompatibilityClass x₀, N.chartCoord x₀ x ∈ Set.Icc lo hi)
    (hpos : ∀ y ∈ Set.Icc lo hi, Concentration.Positive (N.affineChart x₀ y))
    (hsign : N.ConsistentSRSign)
    (hdiag : ∀ y ∈ Set.Icc lo hi, ∀ i : S,
      0 < (N.massActionJacobian κ (N.affineChart x₀ y)) i i)
    (hsub : ∀ y ∈ Set.Icc lo hi, N.reducedJacobian κ x₀ y
      = (N.massActionJacobian κ (N.affineChart x₀ y)).submatrix f f)
    {x y : Concentration S}
    (hx : x ∈ N.positiveCompatibilityClass x₀) (hy : y ∈ N.positiveCompatibilityClass x₀)
    (hsx : N.IsMassActionSteadyState κ x) (hsy : N.IsMassActionSteadyState κ y) : x = y :=
  N.subsingleton_steadyState_of_consistentSRSign κ x₀ hf hbox hpos
    (fun _ _ => N.hweight_of_consistentSRSign hsign) hdiag hsub hx hy hsx hsy

end Network

end CRNT

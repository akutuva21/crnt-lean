import CRNT.Design.ACR
import CRNT.Theorems.DeficiencyOne.Uniqueness
import CRNT.Deficiency.ComplexBalancedRatio
import CRNT.Deficiency.LogMonomialRatio
import CRNT.Deficiency.DeficiencyOneStructure

/-!
# Toward unconditional absolute concentration robustness

The Shinar–Feinberg ACR theorem is packaged in `CRNT.Design.ACR` as a reduction of `HasACR`
to a single named input `ShinarFeinbergHypotheses.PinnedRatio`: the monomial ratio of the two
non-terminal complexes is pinned to one constant across all positive steady states. This module
assembles the deficiency-one machinery that bears directly on that input.

The keystone is `logMonomialRatio_eqOn_linkageClass`: the per-complex log-monomial ratio `Φ` is
constant on *every* linkage class of a deficiency-one network, unifying the deficiency-zero and
deficiency-one class constancy lemmas into one statement valid for an arbitrary class. From it the
*same-class* fragment of the pinned ratio is derived by exponentiation: two complexes in a common
linkage class have a pinned monomial ratio across two positive steady states sharing a rate
constant.

The remaining content of the Shinar–Feinberg theorem — the cross-class equality `Φ(c) = Φ(d)`
relating the two a-priori-independent per-class constants of complexes in *distinct* linkage
classes — is isolated as the named predicate `CrossClassRatioPinned`. The honest reduction
`HasACR.of_crossClassRatioGap` shows that this single cross-class equality, together with a witness
positive steady state, is exactly what remains to upgrade the reduction to an unconditional ACR
theorem. The cross-class equality is consumed as input here; deriving it from non-terminality and
the deficiency-one cut structure is the outstanding mathematical step.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Design.ACR`,
`CRNT.Theorems.DeficiencyOne.Uniqueness`, `CRNT.Deficiency.ComplexBalancedRatio`,
`CRNT.Deficiency.LogMonomialRatio`, `CRNT.Deficiency.DeficiencyOneStructure`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The log-monomial ratio is constant on every linkage class.** For a deficiency-one network
meeting Feinberg's hypotheses, two positive mass-action steady states have equal log-monomial ratio
`Φ` at any two complexes of one linkage class `q`, whatever the deficiency of that class. This is
the keystone unifying the deficiency-zero and deficiency-one class-constancy lemmas: each class has
deficiency `0` or `1`, and in either case `Φ` is constant on it. -/
theorem logMonomialRatio_eqOn_linkageClass (N : Network S) (h : N.DeficiencyOneHypotheses)
    (hδ : N.DeficiencyOne) (κ : RateConstants N) {x y : Concentration S}
    (hxpos : x.Positive) (hypos : y.Positive)
    (hxss : N.IsMassActionSteadyState κ x) (hyss : N.IsMassActionSteadyState κ y)
    {q : Quotient N.linkedSetoid} :
    ∀ c d, N.classOf c = q → N.classOf d = q →
      N.logMonomialRatio x y c = N.logMonomialRatio x y d := by
  intro c d hc hd
  rcases N.linkageDeficiency_eq_zero_or_one h.conditions q with hz | ho
  · exact N.logMonomialRatio_const_of_deficiencyZeroClass h κ hxpos hypos hxss hyss hz hc hd
  · exact N.logMonomialRatio_eqOn_deficientClass h hδ κ hxpos hypos hxss hyss ho c d hc hd

/-- **Same-class pinned ratio.** Two complexes `c`, `d` of one linkage class `q` have a pinned
monomial ratio across two positive mass-action steady states `x`, `y` sharing a rate constant:
`Ψ(x)_c · Ψ(y)_d = Ψ(x)_d · Ψ(y)_c`. This is the exponentiated form of the keystone constancy of
`Φ` on `q`. -/
theorem monomialRatio_pinned_of_sameClass (N : Network S) (h : N.DeficiencyOneHypotheses)
    (hδ : N.DeficiencyOne) (κ : RateConstants N) {x y : Concentration S}
    (hxpos : x.Positive) (hypos : y.Positive)
    (hxss : N.IsMassActionSteadyState κ x) (hyss : N.IsMassActionSteadyState κ y)
    {q : Quotient N.linkedSetoid} {c d : N.ComplexIdx}
    (hc : N.classOf c = q) (hd : N.classOf d = q) :
    c.val.massActionMonomial x * d.val.massActionMonomial y
      = d.val.massActionMonomial x * c.val.massActionMonomial y := by
  have hΦ : N.logMonomialRatio x y c = N.logMonomialRatio x y d :=
    N.logMonomialRatio_eqOn_linkageClass h hδ κ hxpos hypos hxss hyss c d hc hd
  -- Positivity of the four monomials.
  have hxc : (0 : ℝ) < c.val.massActionMonomial x := Complex.massActionMonomial_pos hxpos c.val
  have hyc : (0 : ℝ) < c.val.massActionMonomial y := Complex.massActionMonomial_pos hypos c.val
  have hxd : (0 : ℝ) < d.val.massActionMonomial x := Complex.massActionMonomial_pos hxpos d.val
  have hyd : (0 : ℝ) < d.val.massActionMonomial y := Complex.massActionMonomial_pos hypos d.val
  -- Unfold `Φ` and rearrange to a sum of logs.
  simp only [logMonomialRatio, complexMonomialVector_apply] at hΦ
  have hlog : Real.log (c.val.massActionMonomial x) + Real.log (d.val.massActionMonomial y)
      = Real.log (d.val.massActionMonomial x) + Real.log (c.val.massActionMonomial y) := by
    linarith [hΦ]
  -- Combine logs and exponentiate.
  rw [← Real.log_mul hxc.ne' hyd.ne', ← Real.log_mul hxd.ne' hyc.ne'] at hlog
  have := congrArg Real.exp hlog
  rwa [Real.exp_log (mul_pos hxc hyd), Real.exp_log (mul_pos hxd hyc)] at this

/-- **The cross-class content of Shinar–Feinberg, isolated.** For the two non-terminal complexes
`c`, `d` of the structural hypotheses — which lie in *distinct* linkage classes — the log-monomial
ratio `Φ` takes equal values, for any single rate constant and any two positive mass-action steady
states. This equates the two a-priori-independent per-class constants of `Φ`; it is the sole
ingredient beyond same-class constancy needed for unconditional ACR, and it has no derivation in
the present development. -/
def ShinarFeinbergHypotheses.CrossClassRatioPinned {N : Network S} {s : S}
    (H : N.ShinarFeinbergHypotheses s) : Prop :=
  ∀ (κ : RateConstants N) (x y : Concentration S),
    x.Positive → N.IsMassActionSteadyState κ x →
    y.Positive → N.IsMassActionSteadyState κ y →
    N.logMonomialRatio x y ⟨H.c, H.hc⟩ = N.logMonomialRatio x y ⟨H.d, H.hd⟩

/-- **Cross-class `Φ`-equality yields the pinned monomial ratio.** Given the cross-class equality
of `Φ` at the two non-terminal complexes, for a single rate constant the monomial ratio of `c` and
`d` is pinned: `Φ(c) = Φ(d)` exponentiates to `c.mono x · d.mono y = c.mono y · d.mono x`, the
shape ACR's `pin_of_pinned_ratio` consumes. -/
theorem monomial_cross_of_crossClassRatioPinned {N : Network S} {s : S}
    (H : N.ShinarFeinbergHypotheses s) (hcc : H.CrossClassRatioPinned)
    (κ : RateConstants N) {x y : Concentration S}
    (hxpos : x.Positive) (hxss : N.IsMassActionSteadyState κ x)
    (hypos : y.Positive) (hyss : N.IsMassActionSteadyState κ y) :
    H.c.massActionMonomial x * H.d.massActionMonomial y
      = H.c.massActionMonomial y * H.d.massActionMonomial x := by
  have hΦ : N.logMonomialRatio x y ⟨H.c, H.hc⟩ = N.logMonomialRatio x y ⟨H.d, H.hd⟩ :=
    hcc κ x y hxpos hxss hypos hyss
  have hxc : (0 : ℝ) < H.c.massActionMonomial x := Complex.massActionMonomial_pos hxpos H.c
  have hyc : (0 : ℝ) < H.c.massActionMonomial y := Complex.massActionMonomial_pos hypos H.c
  have hxd : (0 : ℝ) < H.d.massActionMonomial x := Complex.massActionMonomial_pos hxpos H.d
  have hyd : (0 : ℝ) < H.d.massActionMonomial y := Complex.massActionMonomial_pos hypos H.d
  simp only [logMonomialRatio, complexMonomialVector_apply] at hΦ
  have hlog : Real.log (H.c.massActionMonomial x) + Real.log (H.d.massActionMonomial y)
      = Real.log (H.c.massActionMonomial y) + Real.log (H.d.massActionMonomial x) := by
    linarith [hΦ]
  rw [← Real.log_mul hxc.ne' hyd.ne', ← Real.log_mul hyc.ne' hxd.ne'] at hlog
  have := congrArg Real.exp hlog
  rwa [Real.exp_log (mul_pos hxc hyd), Real.exp_log (mul_pos hyc hxd)] at this

/-- **ACR from the cross-class ratio gap.** Restating `HasACR.of_pinnedRatio` factored through the
isolated cross-class equality: given the Shinar–Feinberg hypotheses, the cross-class `Φ`-equality
input `CrossClassRatioPinned`, and a witness positive steady state, the network has ACR in `s`. The
single fixed rate constant of the witness fixes the common value; the cross-class equality pins the
monomial ratio at that constant; the ACR pinning lever then propagates the species-`s` value to
every positive steady state of *that* rate constant. -/
theorem HasACR.of_crossClassRatioGap {N : Network S} {s : S}
    (H : N.ShinarFeinbergHypotheses s) (hcc : H.CrossClassRatioPinned)
    {κ₀ : RateConstants N} {x₀ : Concentration S}
    (hx₀pos : x₀.Positive) (hx₀ss : N.IsMassActionSteadyState κ₀ x₀) :
    ∃ v : ℝ, ∀ (x : Concentration S),
      x.Positive → N.IsMassActionSteadyState κ₀ x → x s = v := by
  refine ⟨x₀ s, fun x hxpos hxss => ?_⟩
  have hratio : H.c.massActionMonomial x * H.d.massActionMonomial x₀
      = H.c.massActionMonomial x₀ * H.d.massActionMonomial x :=
    N.monomial_cross_of_crossClassRatioPinned H hcc κ₀ hxpos hxss hx₀pos hx₀ss
  exact pin_of_pinned_ratio hxpos hx₀pos H.c H.d s H.differOnlyAt H.differAt hratio

import CRNT.Equilibria.SteadyState
import CRNT.Deficiency.DeficiencyOneHypotheses
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Absolute concentration robustness

A network has *absolute concentration robustness* (ACR) in a species `s` when the
steady-state concentration of `s` is the same value `v` at every positive mass-action
steady state, for every choice of rate constants. This module formalizes the ACR
predicate, the Shinar–Feinberg structural hypotheses under which ACR is expected, the
algebraic lever turning a pinned monomial ratio of two complexes into a pinned value of
`x s`, and a packaging theorem deriving `HasACR` from the pinning supplied as an
explicit input.

The Shinar–Feinberg theorem identifies ACR with a deficiency-one network possessing two
non-terminal complexes that lie in distinct linkage classes and differ in exactly one
species. The canonical instance is the EnvZ/OmpR two-component signalling network, which
is ACR in its response regulator. The single genuinely deficiency-one ingredient — that
the monomial ratio of the two non-terminal complexes is *pinned* to one constant across
all positive steady states — is isolated here as the named predicate `PinnedRatio`. It
follows from the deficiency-one characterization of the positive steady-state set, whose
proof is not yet available in this development; `PinnedRatio` is therefore consumed as a
hypothesis rather than discharged. Everything else — the cross-multiplied monomial
identity, the pinning lever, and the reduction of `HasACR` to `PinnedRatio` — is proved.

This module is **stable**. Depends on: `CRNT.Equilibria.SteadyState`,
`CRNT.Deficiency.DeficiencyOneHypotheses`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A network **has absolute concentration robustness** in species `s` when there is a
single value `v` taken by `x s` at every positive mass-action steady state `x`, for every
choice of rate constants. -/
def HasACR (N : Network S) (s : S) : Prop :=
  ∃ v : ℝ, ∀ (κ : RateConstants N) (x : Concentration S),
    x.Positive → N.IsMassActionSteadyState κ x → x s = v

/-- The **Shinar–Feinberg structural hypotheses** for ACR in species `s`: a
deficiency-one network with two non-terminal complexes `c` and `d` lying in distinct
linkage classes and differing in exactly the single species `s`. -/
structure ShinarFeinbergHypotheses (N : Network S) (s : S) where
  /-- The first non-terminal complex. -/
  c : Complex S
  /-- The second non-terminal complex. -/
  d : Complex S
  /-- `c` is a complex of the network. -/
  hc : c ∈ N.complexes
  /-- `d` is a complex of the network. -/
  hd : d ∈ N.complexes
  /-- `c` is not terminal. -/
  nonTerminalC : ¬ N.IsTerminalSLC c
  /-- `d` is not terminal. -/
  nonTerminalD : ¬ N.IsTerminalSLC d
  /-- `c` and `d` lie in distinct linkage classes. -/
  diffClass : N.classOf ⟨c, hc⟩ ≠ N.classOf ⟨d, hd⟩
  /-- `c` and `d` agree away from `s`. -/
  differOnlyAt : ∀ t, t ≠ s → c t = d t
  /-- `c` and `d` differ at `s`. -/
  differAt : c s ≠ d s
  /-- The network satisfies the deficiency-one hypotheses. -/
  defOne : N.DeficiencyOneHypotheses

/-- **Cross-multiplied monomial identity.** When `c` and `d` agree away from `s`, the
monomial of `d` times `(x s) ^ (c s)` equals the monomial of `c` times `(x s) ^ (d s)`:
the factors at every species `t ≠ s` are shared, and the `s`-factors recombine. -/
theorem monomial_cross_of_differ (c d : Complex S) (s : S)
    (hcd : ∀ t, t ≠ s → c t = d t) (x : Concentration S) :
    d.massActionMonomial x * (x s) ^ (c s) = c.massActionMonomial x * (x s) ^ (d s) := by
  classical
  have hmem : s ∈ (Finset.univ : Finset S) := Finset.mem_univ s
  -- Split each monomial into the `s`-factor times the product over the other species.
  have hc : c.massActionMonomial x
      = (x s) ^ (c s) * ∏ t ∈ Finset.univ.erase s, (x t) ^ (c t) :=
    (Finset.mul_prod_erase (Finset.univ) (fun t => (x t) ^ (c t)) hmem).symm
  have hd : d.massActionMonomial x
      = (x s) ^ (d s) * ∏ t ∈ Finset.univ.erase s, (x t) ^ (d t) :=
    (Finset.mul_prod_erase (Finset.univ) (fun t => (x t) ^ (d t)) hmem).symm
  -- The products over the other species coincide because `c` and `d` agree there.
  have hprod : (∏ t ∈ Finset.univ.erase s, (x t) ^ (c t))
      = ∏ t ∈ Finset.univ.erase s, (x t) ^ (d t) :=
    Finset.prod_congr rfl fun t ht => by
      rw [hcd t (Finset.ne_of_mem_erase ht)]
  rw [hc, hd, hprod]
  ring

/-- **Pinning lever, ordered helper.** With `d s < c s`, a pinned monomial ratio of `c`
and `d` across two positive concentrations forces `x s = y s`. -/
theorem pin_xs_of_lt {x y : Concentration S} (hx : x.Positive) (hy : y.Positive)
    (c d : Complex S) (s : S) (hcd : ∀ t, t ≠ s → c t = d t) (hlt : d s < c s)
    (hpin : c.massActionMonomial x * d.massActionMonomial y
      = c.massActionMonomial y * d.massActionMonomial x) :
    x s = y s := by
  set a := c s
  set b := d s
  have hxs : 0 < x s := hx s
  have hys : 0 < y s := hy s
  have hcx : 0 < c.massActionMonomial x := Complex.massActionMonomial_pos hx c
  have hdx : 0 < d.massActionMonomial x := Complex.massActionMonomial_pos hx d
  have hcy : 0 < c.massActionMonomial y := Complex.massActionMonomial_pos hy c
  have hdy : 0 < d.massActionMonomial y := Complex.massActionMonomial_pos hy d
  -- The cross identities at `x` and at `y`.
  have hX : d.massActionMonomial x * (x s) ^ a = c.massActionMonomial x * (x s) ^ b :=
    monomial_cross_of_differ c d s hcd x
  have hY : d.massActionMonomial y * (y s) ^ a = c.massActionMonomial y * (y s) ^ b :=
    monomial_cross_of_differ c d s hcd y
  -- Let `e = a - b > 0`; then `(·)^a = (·)^b * (·)^e`.
  obtain ⟨e, he, hepos⟩ : ∃ e, a = b + e ∧ e ≠ 0 :=
    ⟨a - b, by omega, by omega⟩
  have hpowx : (x s) ^ a = (x s) ^ b * (x s) ^ e := by rw [he, pow_add]
  have hpowy : (y s) ^ a = (y s) ^ b * (y s) ^ e := by rw [he, pow_add]
  -- Cancel the common `(·)^b` factor to express `c.mono = d.mono * (·)^e`.
  have hbx : 0 < (x s) ^ b := pow_pos hxs b
  have hby : 0 < (y s) ^ b := pow_pos hys b
  have hCX : c.massActionMonomial x = d.massActionMonomial x * (x s) ^ e := by
    have := hX
    rw [hpowx] at this
    have h2 : c.massActionMonomial x * (x s) ^ b
        = (d.massActionMonomial x * (x s) ^ e) * (x s) ^ b := by
      ring_nf; ring_nf at this; linarith [this]
    exact (mul_right_cancel₀ (ne_of_gt hbx) h2)
  have hCY : c.massActionMonomial y = d.massActionMonomial y * (y s) ^ e := by
    have := hY
    rw [hpowy] at this
    have h2 : c.massActionMonomial y * (y s) ^ b
        = (d.massActionMonomial y * (y s) ^ e) * (y s) ^ b := by
      ring_nf; ring_nf at this; linarith [this]
    exact (mul_right_cancel₀ (ne_of_gt hby) h2)
  -- Substitute into the pinning hypothesis and cancel `d.mono x * d.mono y`.
  rw [hCX, hCY] at hpin
  have key : (x s) ^ e = (y s) ^ e := by
    have hprod : 0 < d.massActionMonomial x * d.massActionMonomial y := mul_pos hdx hdy
    have heq : (d.massActionMonomial x * d.massActionMonomial y) * (x s) ^ e
        = (d.massActionMonomial x * d.massActionMonomial y) * (y s) ^ e := by
      ring_nf; ring_nf at hpin; linarith [hpin]
    exact mul_left_cancel₀ (ne_of_gt hprod) heq
  exact (pow_left_inj₀ hxs.le hys.le hepos).mp key

/-- **Pinning lever.** A pinned monomial ratio of two complexes `c` and `d` that differ
only at `s` forces the species-`s` concentrations to coincide. This is the algebraic
mechanism turning a pinned ratio into ACR. -/
theorem pin_of_pinned_ratio {x y : Concentration S} (hx : x.Positive) (hy : y.Positive)
    (c d : Complex S) (s : S) (hcd : ∀ t, t ≠ s → c t = d t) (hne : c s ≠ d s)
    (hpin : c.massActionMonomial x * d.massActionMonomial y
      = c.massActionMonomial y * d.massActionMonomial x) :
    x s = y s := by
  rcases lt_or_gt_of_ne hne with h | h
  · -- `c s < d s`: swap the roles of `c` and `d`.
    have hcd' : ∀ t, t ≠ s → d t = c t := fun t ht => (hcd t ht).symm
    have hpin' : d.massActionMonomial x * c.massActionMonomial y
        = d.massActionMonomial y * c.massActionMonomial x := by linarith [hpin]
    exact pin_xs_of_lt hx hy d c s hcd' h hpin'
  · exact pin_xs_of_lt hx hy c d s hcd h hpin

/-- The deficiency-one content of the Shinar–Feinberg theorem, isolated as a named
predicate: across every pair of positive mass-action steady states (for any rate
constants), the monomials of the two non-terminal complexes have a **pinned ratio**. -/
def ShinarFeinbergHypotheses.PinnedRatio {N : Network S} {s : S}
    (H : N.ShinarFeinbergHypotheses s) : Prop :=
  ∀ (κ₁ κ₂ : RateConstants N) (x y : Concentration S),
    x.Positive → N.IsMassActionSteadyState κ₁ x →
    y.Positive → N.IsMassActionSteadyState κ₂ y →
    H.c.massActionMonomial x * H.d.massActionMonomial y
      = H.c.massActionMonomial y * H.d.massActionMonomial x

/-- **ACR from a pinned ratio.** Given the Shinar–Feinberg hypotheses, the pinned-ratio
input, and a witness positive steady state to fix the value, the network has ACR in `s`.
The pinning lever propagates the common species-`s` value to every positive steady
state. -/
theorem HasACR.of_pinnedRatio {N : Network S} {s : S}
    (H : N.ShinarFeinbergHypotheses s) (hpin : H.PinnedRatio)
    (hne : ∃ (κ : RateConstants N) (x : Concentration S),
      x.Positive ∧ N.IsMassActionSteadyState κ x) :
    N.HasACR s := by
  obtain ⟨κ₀, x₀, hx₀pos, hx₀ss⟩ := hne
  refine ⟨x₀ s, fun κ x hxpos hxss => ?_⟩
  have hratio := hpin κ κ₀ x x₀ hxpos hxss hx₀pos hx₀ss
  exact pin_of_pinned_ratio hxpos hx₀pos H.c H.d s H.differOnlyAt H.differAt hratio

/-- A two-species toy exercising the lever directly: species `Bool`, with `c = X + Y`
(`c false = 1`, `c true = 1`) and `d = 2X + Y` (`d false = 2`, `d true = 1`), differing
only at `s = false`. The cross identity reads `d.mono x * (x false)^1 = c.mono x *
(x false)^2`. -/
example (x : Concentration Bool) :
    let c : Complex Bool := fun b => if b then 1 else 1
    let d : Complex Bool := fun b => if b then 1 else 2
    d.massActionMonomial x * (x false) ^ (c false)
      = c.massActionMonomial x * (x false) ^ (d false) :=
  monomial_cross_of_differ (S := Bool)
    (fun b => if b then 1 else 1) (fun b => if b then 1 else 2) false
    (fun t ht => by cases t <;> simp_all) x

end Network

end CRNT

import CRNT.Multistationarity.Capacity
import CRNT.Deficiency.Signature

/-!
# Deficiency One Algorithm, forward direction: the log-ratio signature

The forward direction of the Deficiency One Algorithm's correctness — `HasMultistationarityCapacity
→ DOAAffirmsCapacity` — begins by encoding two witnessing steady states `c, c*` as the log-ratio
`μ = ln c* − ln c`. This module formalizes that **entry step**: from two *distinct positive*
stoichiometrically compatible concentrations, the log-ratio is nonzero and sign-compatible with the
stoichiometric subspace.

* `signCompatible_logRatio` — for distinct positive compatible `x, y`, the vector
  `μ = ln y − ln x` is nonzero (log is injective on the positives) and sign-compatible with the
  stoichiometric subspace, witnessed by `y − x ∈ stoichSubspace` whose sign pattern matches `μ`'s
  (`logRatio_sameSign`).
* `exists_signCompatible_of_hasMultistationarityCapacity` — hence multistationarity capacity yields
  a nonzero sign-compatible `μ`.

This is the first step of the forward direction. Bridging from "a nonzero sign-compatible `μ`" to a
full **signature** — that `μ` solves some shelf partition's constraint system (`DOAAffirmsCapacity`)
— is the deficiency-one structural analysis (Feinberg 1995) and is not carried out here.

Depends on: `CRNT.Multistationarity.Capacity`,
`CRNT.Deficiency.Signature`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The log-ratio of two distinct positive compatible concentrations is a nonzero, sign-compatible
vector.** `μ = ln y − ln x` is nonzero because `log` is injective on the positive reals, and
sign-compatible because `y − x` lies in the stoichiometric subspace and shares `μ`'s coordinatewise
sign pattern. -/
theorem signCompatible_logRatio (N : Network S) {x y : Concentration S}
    (hx : x.Positive) (hy : y.Positive) (hcompat : N.StoichCompatible x y) (hxy : x ≠ y) :
    (fun s => Real.log (y s) - Real.log (x s)) ≠ 0 ∧
      N.SignCompatibleWithStoich (fun s => Real.log (y s) - Real.log (x s)) := by
  refine ⟨?_, ⟨y - x, hcompat, logRatio_sameSign hy hx⟩⟩
  obtain ⟨s, hs⟩ := Function.ne_iff.mp hxy
  rw [Function.ne_iff]
  refine ⟨s, ?_⟩
  rw [Pi.zero_apply]
  intro hlog
  have heqlog : Real.log (y s) = Real.log (x s) := sub_eq_zero.mp hlog
  have hyx : y s = x s := by
    have h2 := congrArg Real.exp heqlog
    rwa [Real.exp_log (hy s), Real.exp_log (hx s)] at h2
  exact hs hyx.symm

/-- **Multistationarity capacity yields a nonzero sign-compatible vector** — the log-ratio of the two
witnessing steady states. The first step of the Deficiency One Algorithm's forward direction. -/
theorem exists_signCompatible_of_hasMultistationarityCapacity (N : Network S)
    (h : N.HasMultistationarityCapacity) :
    ∃ μ : S → ℝ, μ ≠ 0 ∧ N.SignCompatibleWithStoich μ := by
  obtain ⟨κ, x₀, x, y, hxmem, hymem, _, _, hxy⟩ := h
  have hcompat : N.StoichCompatible x y := hxmem.1.symm.trans hymem.1
  obtain ⟨hne, hsc⟩ := N.signCompatible_logRatio hxmem.2 hymem.2 hcompat hxy
  exact ⟨_, hne, hsc⟩

end Network

end CRNT

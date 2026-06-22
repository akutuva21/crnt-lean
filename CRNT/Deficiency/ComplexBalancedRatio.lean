import CRNT.Deficiency.DeficiencyOneLocalize
import CRNT.Deficiency.DeficiencyOneHypotheses
import CRNT.Deficiency.PerClassKernelUnique
import CRNT.Deficiency.Drainage
import CRNT.Deficiency.LogMonomialRatio

/-!
# The log-monomial ratio is constant on deficiency-zero linkage classes

On a linkage class of deficiency zero, the deficiency-one localization makes every
mass-action steady state complex-balanced: the monomial vector `Ψ(x)` restricted to the
class is a kernel vector of the kinetic map `A_k`, strictly positive on the class. Drainage
forces the class to be a single terminal strong linkage class — hence strongly connected —
so the per-class kernel is one-dimensional. Two steady states therefore have proportional
restricted monomial vectors, and the **log-monomial ratio** `Φ(c) = log Ψ(x)_c − log Ψ(y)_c`
is constant across the class.

Combined with the reformulation `logRatio_mem_orthSum_iff`, this discharges the toric
condition on every deficiency-zero class, reducing the log-ratio characterization of
deficiency-one steady states to the single deficient linkage class.

* `reaches_of_complexBalanced_class` — a class complex-balanced at a positive point is
  strongly connected.
* `logMonomialRatio_const_of_deficiencyZeroClass` — `Φ` is constant on a deficiency-zero
  linkage class.

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Deficiency.DeficiencyOneLocalize`, `CRNT.Deficiency.DeficiencyOneHypotheses`,
`CRNT.Deficiency.PerClassKernelUnique`, `CRNT.Deficiency.Drainage`,
`CRNT.Deficiency.LogMonomialRatio`.
-/

namespace CRNT

namespace Network

open scoped Classical BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **A class complex-balanced at a positive point is strongly connected.** If the monomial
vector of a positive `x`, restricted to a class `q`, is a kernel vector of `A_k`, then every
complex of `q` is terminal (drainage); with the one-terminal-SLC condition all complexes of
`q` lie in the single terminal strong linkage class, so any two are mutually reachable. -/
theorem reaches_of_complexBalanced_class (N : Network S)
    (h3 : N.OneTerminalSLCPerLinkageClass) (κ : RateConstants N)
    {x : Concentration S} (hx : x.Positive) {q : Quotient N.linkedSetoid}
    (hbal : N.restrictToClass q (N.kineticMap κ (N.complexMonomialVector x)) = 0)
    {c c' : N.ComplexIdx} (hc : N.classOf c = q) (hc' : N.classOf c' = q) :
    N.Reaches c.val c'.val := by
  set vx := N.restrictToClass q (N.complexMonomialVector x) with hvx
  have hker : N.kineticMap κ vx = 0 := by rw [hvx, kineticMap_restrictToClass]; exact hbal
  have hnn : ∀ d, 0 ≤ vx d := by
    intro d
    by_cases hd : N.classOf d = q
    · rw [hvx, restrictToClass_apply_of_eq _ _ hd]
      exact Complex.massActionMonomial_nonneg hx.nonnegative _
    · rw [hvx, restrictToClass_apply_of_ne _ _ hd]
  have hpos : ∀ {d : N.ComplexIdx}, N.classOf d = q → 0 < vx d := by
    intro d hd
    rw [hvx, restrictToClass_apply_of_eq _ _ hd]
    exact Complex.massActionMonomial_pos hx _
  have htc : N.IsTerminalSLC c.val := N.isTerminalSLC_of_pos_kernel κ hnn hker (hpos hc)
  have htc' : N.IsTerminalSLC c'.val := N.isTerminalSLC_of_pos_kernel κ hnn hker (hpos hc')
  obtain ⟨σ, _, hσuniq⟩ := h3 q
  have e1 : Quotient.mk N.stronglyLinkedSetoid c = σ :=
    hσuniq _ ⟨by rw [strongToLinkage_mk]; exact hc, by rw [isTerminalSLClass_mk]; exact htc⟩
  have e2 : Quotient.mk N.stronglyLinkedSetoid c' = σ :=
    hσuniq _ ⟨by rw [strongToLinkage_mk]; exact hc', by rw [isTerminalSLClass_mk]; exact htc'⟩
  exact (Quotient.exact (e1.trans e2.symm)).1

/-- **The log-monomial ratio is constant across a deficiency-zero linkage class.** For two
positive mass-action steady states `x`, `y`, the per-complex log-ratio `Φ` takes equal values
at any two complexes of a deficiency-zero class: the localization makes both monomial vectors
complex-balanced there, strong connectivity makes the per-class kernel one-dimensional, and
the resulting proportionality `Ψ(y) = t·Ψ(x)` on the class makes `Φ ≡ −log t`. -/
theorem logMonomialRatio_const_of_deficiencyZeroClass (N : Network S)
    (h : N.DeficiencyOneHypotheses) (κ : RateConstants N)
    {x y : Concentration S} (hx : x.Positive) (hy : y.Positive)
    (hxss : N.IsMassActionSteadyState κ x) (hyss : N.IsMassActionSteadyState κ y)
    {q : Quotient N.linkedSetoid} (hq : N.linkageDeficiency q = 0)
    {c c' : N.ComplexIdx} (hc : N.classOf c = q) (hc' : N.classOf c' = q) :
    N.logMonomialRatio x y c = N.logMonomialRatio x y c' := by
  set vx := N.restrictToClass q (N.complexMonomialVector x) with hvx
  set vy := N.restrictToClass q (N.complexMonomialVector y) with hvy
  have hbalx : N.restrictToClass q (N.kineticMap κ (N.complexMonomialVector x)) = 0 :=
    N.restrictToClass_kineticImage_eq_zero h.conditions κ hxss hq
  have hbaly : N.restrictToClass q (N.kineticMap κ (N.complexMonomialVector y)) = 0 :=
    N.restrictToClass_kineticImage_eq_zero h.conditions κ hyss hq
  have hkerx : N.kineticMap κ vx = 0 := by rw [hvx, kineticMap_restrictToClass]; exact hbalx
  have hkery : N.kineticMap κ vy = 0 := by rw [hvy, kineticMap_restrictToClass]; exact hbaly
  have hxoff : ∀ d, N.classOf d ≠ q → vx d = 0 := fun d hd => by
    rw [hvx, restrictToClass_apply_of_ne _ _ hd]
  have hyoff : ∀ d, N.classOf d ≠ q → vy d = 0 := fun d hd => by
    rw [hvy, restrictToClass_apply_of_ne _ _ hd]
  have hxpos : ∀ d, N.classOf d = q → 0 < vx d := fun d hd => by
    rw [hvx, restrictToClass_apply_of_eq _ _ hd]; exact Complex.massActionMonomial_pos hx _
  have hθ : ∀ d d' : N.ComplexIdx, N.classOf d = q → N.classOf d' = q → N.Reaches d.val d'.val :=
    fun d d' hd hd' => N.reaches_of_complexBalanced_class h.oneTerminal κ hx hbalx hd hd'
  obtain ⟨t, ht⟩ := N.perClass_kernel_unique κ q hθ hxpos hxoff hkerx hyoff hkery
  -- `Ψ(y) = t·Ψ(x)` on the class, with `t > 0`.
  have hval : ∀ {d : N.ComplexIdx}, N.classOf d = q →
      N.complexMonomialVector y d = t * N.complexMonomialVector x d := by
    intro d hd
    have h1 : vy d = t * vx d := by have := congrFun ht d; simpa [Pi.smul_apply] using this
    rwa [hvx, hvy, restrictToClass_apply_of_eq _ _ hd, restrictToClass_apply_of_eq _ _ hd] at h1
  have hxc : 0 < N.complexMonomialVector x c := Complex.massActionMonomial_pos hx _
  have hyc : 0 < N.complexMonomialVector y c := Complex.massActionMonomial_pos hy _
  have htpos : 0 < t := by
    by_contra hcon
    rw [not_lt] at hcon
    have : t * N.complexMonomialVector x c ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon hxc.le
    rw [← hval hc] at this
    exact absurd hyc (not_lt.mpr this)
  -- `Φ` is `−log t` on each complex of the class.
  have hphi : ∀ {d : N.ComplexIdx}, N.classOf d = q → N.logMonomialRatio x y d = -Real.log t := by
    intro d hd
    have hdpos : 0 < N.complexMonomialVector x d := Complex.massActionMonomial_pos hx _
    rw [logMonomialRatio, hval hd, Real.log_mul htpos.ne' hdpos.ne']
    ring
  rw [hphi hc, hphi hc']

end Network

end CRNT

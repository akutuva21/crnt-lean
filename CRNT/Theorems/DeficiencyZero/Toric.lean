import CRNT.Dynamics.MassActionAlgebra
import CRNT.Theorems.DeficiencyZero.BirchExistence
import CRNT.Theorems.DeficiencyZero.PositiveKernel
import CRNT.Equilibria.CompatibilityClass
import CRNT.Stoich.Subspace
import CRNT.Graph.LinkageClass

/-!
# The toric structure of complex-balanced equilibria

Complex-balanced equilibria form a log-linear ("toric") set. The key fact proved here is
that, relative to a complex-balanced reference `x*`, any positive concentration whose
log-ratio `log(x/x*)` is orthogonal to the stoichiometric subspace is itself
complex-balanced (`complexBalanced_of_logRatio_orthogonal`).

The argument is termwise and elementary: writing the kinetic matrix as
`A_k v = ∑_r κ_r v_{src r} (1_{tgt r} − 1_{src r})`, the monomial vector scales as
`Ψ(x)_c = Ψ(x*)_c · exp(⟨c, log(x/x*)⟩)`, and orthogonality to the stoichiometric subspace
means `⟨tgt r, log(x/x*)⟩ = ⟨src r, log(x/x*)⟩` for every reaction. Every reaction
contributing to `(A_k Ψ x)_c` is incident to `c`, so its source carries the same exponent
as `c`; that common factor pulls out of the whole sum, turning `A_k Ψ x = 0` into
`exp(⟨c, ·⟩) · A_k Ψ x* = 0`.

Combined with Birch existence, this gives a complex-balanced equilibrium in every positive
compatibility class, *provided one complex-balanced equilibrium already exists*
(`exists_isComplexBalanced_in_positiveClass`). Producing that first equilibrium from weak
reversibility and deficiency zero, and the converse toric inclusion (which needs uniqueness
of the positive kernel of `A_k`), remain.

This module is **stable** and `sorry`-free.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The logarithm of a monomial of a positive concentration is the linear pairing of the
complex with `log x`: `log (Ψ x)_c = ∑ s, c_s · log x_s`. -/
theorem log_complexMonomialVector (N : Network S) {x : Concentration S} (hx : x.Positive)
    (c : N.ComplexIdx) :
    Real.log (N.complexMonomialVector x c) = ∑ s, (c.val s : ℝ) * Real.log (x s) := by
  simp only [complexMonomialVector_apply, Complex.massActionMonomial]
  rw [Real.log_prod fun s _ => pow_ne_zero (c.val s) (hx s).ne']
  exact Finset.sum_congr rfl fun s _ => Real.log_pow _ _

/-- The monomial vector scales toricly about a positive reference:
`Ψ(x)_c = Ψ(x*)_c · exp(∑ s, c_s · (log x_s − log x*_s))`. -/
theorem complexMonomialVector_eq_mul_exp (N : Network S) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (c : N.ComplexIdx) :
    N.complexMonomialVector x c
      = N.complexMonomialVector xstar c
        * Real.exp (∑ s, (c.val s : ℝ) * (Real.log (x s) - Real.log (xstar s))) := by
  have hpx : 0 < N.complexMonomialVector x c := by
    rw [complexMonomialVector_apply]; exact Complex.massActionMonomial_pos hx c.val
  have hpxs : 0 < N.complexMonomialVector xstar c := by
    rw [complexMonomialVector_apply]; exact Complex.massActionMonomial_pos hxs c.val
  have hsplit : (∑ s, (c.val s : ℝ) * (Real.log (x s) - Real.log (xstar s)))
      = Real.log (N.complexMonomialVector x c)
        - Real.log (N.complexMonomialVector xstar c) := by
    rw [log_complexMonomialVector N hx, log_complexMonomialVector N hxs,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hsplit, Real.exp_sub, Real.exp_log hpx, Real.exp_log hpxs, mul_comm,
    div_mul_cancel₀ _ hpxs.ne']

/-- Orthogonality of `μ` to the stoichiometric subspace means the linear pairing
`∑ s, c_s · μ_s` agrees at the source and target of every reaction. -/
theorem pairing_eq_of_orthogonal (N : Network S) {μ : S → ℝ}
    (hμ : μ ∈ orthSum N.stoichSubspace) (r : N.R) :
    (∑ s, ((N.targetIdx r).val s : ℝ) * μ s) = ∑ s, ((N.sourceIdx r).val s : ℝ) * μ s := by
  have h := (mem_orthSum.mp hμ) (N.reactionVector r) (N.reactionVector_mem_stoichSubspace r)
  simp only [reactionVector_apply, mul_sub] at h
  rw [Finset.sum_sub_distrib, sub_eq_zero] at h
  rw [Finset.sum_congr rfl fun s _ => mul_comm ((N.targetIdx r).val s : ℝ) (μ s),
    Finset.sum_congr rfl fun s _ => mul_comm ((N.sourceIdx r).val s : ℝ) (μ s)]
  exact h

/-- **The toric inclusion (existence direction of the Horn–Jackson characterization).**
Relative to a positive complex-balanced reference `x*`, any positive `x` with
`log(x/x*)` orthogonal to the stoichiometric subspace is complex-balanced. -/
theorem complexBalanced_of_logRatio_orthogonal (N : Network S) (κ : RateConstants N)
    {x xstar : Concentration S} (hx : x.Positive) (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (horth : (fun s => Real.log (x s) - Real.log (xstar s)) ∈ orthSum N.stoichSubspace) :
    N.IsComplexBalanced κ x := by
  rw [isComplexBalanced_iff_kineticMap] at hcb ⊢
  funext c
  rw [kineticMap_apply, Pi.zero_apply]
  -- each reaction's contribution scales by the common factor `exp(⟨c, log(x/x*)⟩)`
  have key : ∀ r : N.R,
      κ.k r * N.complexMonomialVector x (N.sourceIdx r) *
          ((if N.targetIdx r = c then (1 : ℝ) else 0) - (if N.sourceIdx r = c then 1 else 0))
        = Real.exp (∑ s, (c.val s : ℝ) * (Real.log (x s) - Real.log (xstar s)))
          * (κ.k r * N.complexMonomialVector xstar (N.sourceIdx r) *
            ((if N.targetIdx r = c then (1 : ℝ) else 0)
              - (if N.sourceIdx r = c then 1 else 0))) := by
    intro r
    rw [complexMonomialVector_eq_mul_exp N hx hxs (N.sourceIdx r)]
    by_cases hI : ((if N.targetIdx r = c then (1 : ℝ) else 0)
        - (if N.sourceIdx r = c then 1 else 0)) = 0
    · rw [hI]; ring
    · have hpair : (∑ s, ((N.sourceIdx r).val s : ℝ) * (Real.log (x s) - Real.log (xstar s)))
          = ∑ s, (c.val s : ℝ) * (Real.log (x s) - Real.log (xstar s)) := by
        rcases eq_or_ne (N.sourceIdx r) c with hsc | hsc
        · rw [hsc]
        · rcases eq_or_ne (N.targetIdx r) c with htc | htc
          · rw [← htc]; exact (pairing_eq_of_orthogonal N horth r).symm
          · exact absurd (by rw [if_neg htc, if_neg hsc]; ring) hI
      rw [hpair]; ring
  rw [Finset.sum_congr rfl fun r _ => key r, ← Finset.mul_sum]
  have hzero : (∑ r : N.R, κ.k r * N.complexMonomialVector xstar (N.sourceIdx r) *
      ((if N.targetIdx r = c then (1 : ℝ) else 0) - (if N.sourceIdx r = c then 1 else 0))) = 0 := by
    have := congrFun hcb c
    rwa [kineticMap_apply, Pi.zero_apply] at this
  rw [hzero, mul_zero]

/-- **A complex-balanced equilibrium exists in every positive compatibility class, given
one complex-balanced reference.** Birch existence places, in the positive class of `x₀`, a
point whose log-ratio against the reference `x*` is orthogonal to the stoichiometric
subspace; the toric inclusion then makes that point complex-balanced. -/
theorem exists_isComplexBalanced_in_positiveClass (N : Network S) (κ : RateConstants N)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) (hx0 : x₀.Positive) :
    ∃ x ∈ N.positiveCompatibilityClass x₀, N.IsComplexBalanced κ x := by
  obtain ⟨x, hxpos, hxc, hxorth⟩ := birch_existence N.stoichSubspace hxs hx0
  refine ⟨x, ⟨hxc, hxpos⟩, ?_⟩
  refine complexBalanced_of_logRatio_orthogonal N κ hxpos hxs hcb ?_
  rw [mem_orthSum]
  exact hxorth

/-- **The converse toric inclusion.** For a weakly reversible network, two positive
complex-balanced concentrations differ by a log-ratio orthogonal to the stoichiometric
subspace: `log(x/x*) ⊥ S`. The crux is *uniqueness* of the positive kernel of `A_k` on
each linkage class — both `Ψ x` and `Ψ x*` are positive fixed vectors of the rescaled
column-stochastic matrix, so on each (strongly connected) class they are proportional, and
the ratio `Ψ(x)_c/Ψ(x*)_c = exp(⟨c, log(x/x*)⟩)` is constant along every reaction. -/
theorem logRatio_orthogonal_of_complexBalanced (N : Network S) (hwr : N.WeaklyReversible)
    (κ : RateConstants N) {x xstar : Concentration S} (hx : x.Positive) (hxs : xstar.Positive)
    (hcbx : N.IsComplexBalanced κ x) (hcbs : N.IsComplexBalanced κ xstar) :
    (fun s => Real.log (x s) - Real.log (xstar s)) ∈ orthSum N.stoichSubspace := by
  classical
  set a := N.complexMonomialVector xstar with ha_def
  set v := N.complexMonomialVector x with hv_def
  have hapos : ∀ c, 0 < a c := fun c => by
    rw [ha_def, complexMonomialVector_apply]; exact Complex.massActionMonomial_pos hxs c.val
  have hafix : (PositiveKernel.smat N κ).mulVec a = a :=
    (PositiveKernel.smat_fix_iff a).mpr ((N.isComplexBalanced_iff_kineticMap κ xstar).mp hcbs)
  have hvfix : (PositiveKernel.smat N κ).mulVec v = v :=
    (PositiveKernel.smat_fix_iff v).mpr ((N.isComplexBalanced_iff_kineticMap κ x).mp hcbx)
  have hratio : ∀ c, v c
      = a c * Real.exp (∑ s, (c.val s : ℝ) * (Real.log (x s) - Real.log (xstar s))) :=
    fun c => by rw [hv_def, ha_def]; exact N.complexMonomialVector_eq_mul_exp hx hxs c
  -- ratio `v/a` is constant on each linkage class (PF kernel uniqueness, per class)
  have hclass_const : ∀ c d : N.ComplexIdx,
      Quotient.mk N.linkedSetoid c = Quotient.mk N.linkedSetoid d → v c * a d = v d * a c := by
    intro c d hcd
    set q := Quotient.mk N.linkedSetoid c with hq
    set T : Finset N.ComplexIdx :=
      Finset.univ.filter (fun e => Quotient.mk N.linkedSetoid e = q) with hTdef
    have hcT : c ∈ T := by rw [hTdef, Finset.mem_filter]; exact ⟨Finset.mem_univ c, hq.symm⟩
    obtain ⟨c₀, hc₀T, hmin⟩ := Finset.exists_min_image T (fun e => v e / a e) ⟨c, hcT⟩
    have hc₀q : Quotient.mk N.linkedSetoid c₀ = q := by
      rw [hTdef, Finset.mem_filter] at hc₀T; exact hc₀T.2
    set t := v c₀ / a c₀ with htdef
    set w := v - t • a with hwdef
    set D : N.ComplexIdx → Prop := fun e => Quotient.mk N.linkedSetoid e = q with hDdef
    have hDfwd : ∀ e, D e → ∀ k, PositiveKernel.smat N κ e k ≠ 0 → D k := by
      intro e hDe k hek
      have hek2 : Quotient.mk N.linkedSetoid e = Quotient.mk N.linkedSetoid k := by
        by_contra hne; exact hek (PositiveKernel.smat_blockdiag hne)
      show Quotient.mk N.linkedSetoid k = q
      rw [← hek2]; exact hDe
    have hwnnD : ∀ e, D e → 0 ≤ w e := by
      intro e hDe
      have heT : e ∈ T := by rw [hTdef, Finset.mem_filter]; exact ⟨Finset.mem_univ e, hDe⟩
      have hle : t ≤ v e / a e := hmin e heT
      rw [le_div_iff₀ (hapos e)] at hle
      simp only [hwdef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; linarith
    have hwfix : (PositiveKernel.smat N κ).mulVec w = w := by
      rw [hwdef, Matrix.mulVec_sub, Matrix.mulVec_smul, hvfix, hafix]
    have hwc0 : w c₀ = 0 := by
      have hcancel : v c₀ / a c₀ * a c₀ = v c₀ := div_mul_cancel₀ (v c₀) (hapos c₀).ne'
      simp only [hwdef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, htdef]
      rw [hcancel, sub_self]
    have hwe0 : ∀ e, D e → w e = 0 := by
      intro e hDe
      by_contra hne
      have hwe : 0 < w e := (hwnnD e hDe).lt_of_ne (Ne.symm hne)
      have hlink : N.Linked e.val c₀.val := Quotient.exact (hDe.trans hc₀q.symm)
      have hsupp : supportReaches (PositiveKernel.smat N κ) c₀ e :=
        PositiveKernel.reaches_supportReaches e.val e.2 (hwr.reaches_of_linked hlink) c₀.2
      have hpos := pos_of_supportReaches_pos_on (PositiveKernel.smat N κ)
        PositiveKernel.smat_nonneg D hDfwd w hwnnD hwfix hc₀q hsupp hwe
      rw [hwc0] at hpos; exact lt_irrefl 0 hpos
    have ec : v c = t * a c := by
      have hc0 : w c = 0 := hwe0 c hq.symm
      simp only [hwdef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hc0
      linarith
    have ed : v d = t * a d := by
      have hd0 : w d = 0 := hwe0 d hcd.symm
      simp only [hwdef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hd0
      linarith
    rw [ec, ed]; ring
  -- assemble orthogonality from per-reaction equality of the pairing
  show (fun s => Real.log (x s) - Real.log (xstar s)) ∈ orthSum N.stoichSubspace
  apply mem_orthSum_span
  rintro g ⟨r, rfl⟩
  have hcd : Quotient.mk N.linkedSetoid (N.sourceIdx r) = Quotient.mk N.linkedSetoid (N.targetIdx r) :=
    Quotient.sound (N.linked_of_reaction r)
  have hcc := hclass_const (N.sourceIdx r) (N.targetIdx r) hcd
  rw [hratio (N.sourceIdx r), hratio (N.targetIdx r)] at hcc
  have hExp : Real.exp (∑ s, ((N.sourceIdx r).val s : ℝ) * (Real.log (x s) - Real.log (xstar s)))
      = Real.exp (∑ s, ((N.targetIdx r).val s : ℝ) * (Real.log (x s) - Real.log (xstar s))) := by
    have h2 : a (N.sourceIdx r) * a (N.targetIdx r)
          * Real.exp (∑ s, ((N.sourceIdx r).val s : ℝ) * (Real.log (x s) - Real.log (xstar s)))
        = a (N.sourceIdx r) * a (N.targetIdx r)
          * Real.exp (∑ s, ((N.targetIdx r).val s : ℝ) * (Real.log (x s) - Real.log (xstar s))) := by
      linear_combination hcc
    exact mul_left_cancel₀ (mul_pos (hapos _) (hapos _)).ne' h2
  have hGeq : (∑ s, ((N.sourceIdx r).val s : ℝ) * (Real.log (x s) - Real.log (xstar s)))
      = ∑ s, ((N.targetIdx r).val s : ℝ) * (Real.log (x s) - Real.log (xstar s)) :=
    Real.exp_eq_exp.mp hExp
  simp only [reactionVector_apply, mul_sub]
  rw [Finset.sum_sub_distrib,
    show (∑ i, (Real.log (x i) - Real.log (xstar i)) * ((N.reaction r).target i : ℝ))
        = ∑ s, ((N.targetIdx r).val s : ℝ) * (Real.log (x s) - Real.log (xstar s)) from
      Finset.sum_congr rfl fun i _ => by simp only [Network.targetIdx]; ring,
    show (∑ i, (Real.log (x i) - Real.log (xstar i)) * ((N.reaction r).source i : ℝ))
        = ∑ s, ((N.sourceIdx r).val s : ℝ) * (Real.log (x s) - Real.log (xstar s)) from
      Finset.sum_congr rfl fun i _ => by simp only [Network.sourceIdx]; ring]
  rw [hGeq, sub_self]

/-- **Uniqueness of the complex-balanced equilibrium in a positive compatibility class**
for a weakly reversible network: two positive complex-balanced concentrations in the same
compatibility class are equal. The converse toric inclusion gives `log(x/y) ⊥ S`, and Birch
uniqueness closes it. -/
theorem isComplexBalanced_unique_in_positiveClass (N : Network S) (hwr : N.WeaklyReversible)
    (κ : RateConstants N) {x₀ x y : Concentration S}
    (hx : x ∈ N.positiveCompatibilityClass x₀) (hy : y ∈ N.positiveCompatibilityClass x₀)
    (hcbx : N.IsComplexBalanced κ x) (hcby : N.IsComplexBalanced κ y) : x = y := by
  obtain ⟨hxc, hxpos⟩ := hx
  obtain ⟨hyc, hypos⟩ := hy
  have horth := N.logRatio_orthogonal_of_complexBalanced hwr κ hxpos hypos hcbx hcby
  have hxy : x - y ∈ N.stoichSubspace := by
    rw [(sub_sub_sub_cancel_right x y x₀).symm]
    exact N.stoichSubspace.sub_mem hxc hyc
  exact birch_uniqueness N.stoichSubspace hxpos hypos hxy fun s hs => (mem_orthSum.mp horth) s hs

end Network

end CRNT

import CRNT.Theorems.DeficiencyOne.ToricReduction
import CRNT.Deficiency.StructuredPreimage
import CRNT.Deficiency.ExcessPositivity
import CRNT.Deficiency.LevelSetSign
import CRNT.Deficiency.SignedDrainage
import CRNT.Deficiency.DeficientClassKernel
import CRNT.Deficiency.TerminalReachable
import CRNT.LinearAlgebra.LogSumInj

/-!
# Deficiency-one uniqueness: pinning the equilibrium parameter

The deficiency-one uniqueness theorem reduces (`deficiencyOneUniqueness_of_deficientClassRatioConst`)
to constancy of the log-monomial ratio `Φ` on the single deficient linkage class `θ`. This module
discharges that obligation by Feinberg's argument, assembled from the bricks built earlier:

* from two positive steady states `x`, `y`, the kinetic images lie on a line `A_k Ψ = c · g`;
* a structured preimage `y*` of the deficiency mode with a zero coordinate is built (`y* = Ψx/c_x −
  t·b`), and the equilibrium parameter is the root of `H(β) = ⟨g, log(β·y* + b)⟩`;
* `H` is injective (`eq_of_shiftedLogSum_eq`) — its level-set sign data comes from the kinetic-map
  flux signs (`sum_kineticMap_superlevel_nonneg`, `sum_kineticMap_closed_nonneg`) and its positive
  lump from net inflow into the zero set (`sum_kineticMap_pos_of_inflow` plus a crossing reaction);
* both steady states are roots of `H`, so they share `β`, forcing `Ψx ∝ Ψy` on `θ` — i.e. `Φ` is
  constant — and the Birch sign argument then gives `x = y`.

* `proportional_of_kineticImage_ne` — for `c_x ≠ 0`, `Ψx ∝ Ψy` on the deficient class.

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Theorems.DeficiencyOne.ToricReduction`, `CRNT.Deficiency.StructuredPreimage`,
`CRNT.Deficiency.ExcessPositivity`, `CRNT.Deficiency.LevelSetSign`,
`CRNT.Deficiency.SignedDrainage`, `CRNT.Deficiency.DeficientClassKernel`,
`CRNT.Deficiency.TerminalReachable`, `CRNT.LinearAlgebra.LogSumInj`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Proportionality of the monomials on the deficient class (the `c_x ≠ 0` core).** For two
positive steady states whose kinetic images lie on the line through the deficiency mode `g`
(supported on `θ`, in `ker Y`), with the `x`-coefficient nonzero, the monomial vectors are
proportional on the deficient class `θ`: `Ψx = K · Ψy` there for some `K > 0`. -/
theorem proportional_of_kineticImage_ne (N : Network S) (κ : RateConstants N)
    {x y : Concentration S} (hxpos : x.Positive) (hypos : y.Positive)
    {θ : Quotient N.linkedSetoid} {c0 : N.ComplexIdx}
    (hc0term : N.IsTerminalSLC c0.val) (hc0θ : N.classOf c0 = θ)
    (hSLθ : ∀ c, N.classOf c = θ → N.IsTerminalSLC c.val → N.StronglyLinked c0.val c.val)
    {g : N.ComplexIdx → ℝ} (hg0 : g ≠ 0)
    (hgY : N.complexMap g = 0) (hgθ : ∀ c, N.classOf c ≠ θ → g c = 0)
    {cx cy : ℝ} (hcx0 : cx ≠ 0)
    (hAx : N.kineticMap κ (N.complexMonomialVector x) = cx • g)
    (hAy : N.kineticMap κ (N.complexMonomialVector y) = cy • g) :
    ∃ K : ℝ, 0 < K ∧
      ∀ c, N.classOf c = θ → N.complexMonomialVector x c = K * N.complexMonomialVector y c := by
  classical
  set Ψx := N.complexMonomialVector x with hΨxdef
  set Ψy := N.complexMonomialVector y with hΨydef
  have hΨxpos : ∀ c, 0 < Ψx c := fun c => Complex.massActionMonomial_pos hxpos c.val
  have hΨypos : ∀ c, 0 < Ψy c := fun c => Complex.massActionMonomial_pos hypos c.val
  -- `StronglyLinked c0` lies inside `θ`.
  have hSLθ' : ∀ c, N.StronglyLinked c0.val c.val → N.classOf c = θ := by
    intro c hsl
    have : N.classOf c0 = N.classOf c := Quotient.sound (Linked.of_reaches hsl.1)
    rw [← this]; exact hc0θ
  -- the terminal-class kernel mode
  obtain ⟨b, hbpos, hboff, hbker⟩ := N.exists_pos_kernelVector_on_terminalSLC κ hc0term
  have hbnn : ∀ c, 0 ≤ b c := by
    intro c
    by_cases hsl : N.StronglyLinked c0.val c.val
    · exact (hbpos c hsl).le
    · rw [hboff c hsl]
  -- the structured preimage `y* = Ψx − t·b`
  obtain ⟨ystar, cm, hAys, hcmsl, hcm0, hynnSL, hyoffSL⟩ :=
    N.exists_zeroCoord_preimage κ b Ψx hbpos hboff hbker
  have hG : N.kineticMap κ ystar = cx • g := by rw [hAys]; exact hAx
  have hGθ : ∀ c, N.classOf c ≠ θ → N.kineticMap κ ystar c = 0 := by
    intro c hc; rw [hG]; simp only [Pi.smul_apply, smul_eq_mul, hgθ c hc, mul_zero]
  -- `y* ≥ 0` everywhere, and `{y* = 0} ⊆ StronglyLinked c0`.
  have hynn : ∀ c, 0 ≤ ystar c := by
    intro c
    by_cases hsl : N.StronglyLinked c0.val c.val
    · exact hynnSL c hsl
    · rw [hyoffSL c hsl]; exact (hΨxpos c).le
  have hUsl : ∀ c, ystar c = 0 → N.StronglyLinked c0.val c.val := by
    intro c hc; by_contra hsl
    rw [hyoffSL c hsl] at hc; exact absurd hc (hΨxpos c).ne'
  -- `b > 0 ↔ StronglyLinked c0`; the set `{b > 0}` is absorbing.
  have hbpos_iff : ∀ c, 0 < b c ↔ N.StronglyLinked c0.val c.val := by
    intro c
    constructor
    · intro h; by_contra hsl; rw [hboff c hsl] at h; exact absurd h (lt_irrefl 0)
    · exact hbpos c
  -- exponent sum is zero
  have hGsum : ∑ c, N.kineticMap κ ystar c = 0 := N.kineticMap_sum_eq_zero κ ystar
  -- the toric orthogonality `⟨g, log Ψ⟩ = 0`
  have hortho : ∀ {z : Concentration S}, z.Positive →
      ∑ c, g c * Real.log (N.complexMonomialVector z c) = 0 := by
    intro z hz
    have : ∀ c, g c * Real.log (N.complexMonomialVector z c)
        = ∑ s, g c * ((c.val s : ℝ) * Real.log (z s)) := by
      intro c
      rw [N.log_complexMonomialVector hz c, Finset.mul_sum]
    simp only [this]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro s _
    have : ∑ c, g c * ((c.val s : ℝ) * Real.log (z s))
        = (∑ c, g c * (c.val s : ℝ)) * Real.log (z s) := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun c _ => by ring
    rw [this]
    have hY : ∑ c, g c * (c.val s : ℝ) = 0 := by
      have := congrFun hgY s
      simpa [N.complexMap_apply] using this
    rw [hY, zero_mul]
  -- t and γ via per-class kernel uniqueness
  have hkeruniq : ∀ w : N.ComplexIdx → ℝ, N.kineticMap κ w = 0 →
      ∃ s : ℝ, ∀ c, N.classOf c = θ → w c = s * b c := by
    intro w hw
    have hvker : N.kineticMap κ (N.restrictToClass θ w) = 0 := by
      rw [N.kineticMap_restrictToClass, hw]
      funext c; by_cases hcq : N.classOf c = θ <;>
        simp [restrictToClass_apply_of_eq, restrictToClass_apply_of_ne, hcq]
    have hvoff : ∀ c, ¬ N.StronglyLinked c0.val c.val → N.restrictToClass θ w c = 0 := by
      intro c hsl
      by_cases hcq : N.classOf c = θ
      · have hcnt : ¬ N.IsTerminalSLC c.val := fun ht => hsl (hSLθ c hcq ht)
        rw [restrictToClass_apply_of_eq _ _ hcq]
        exact N.kineticMap_eq_zero_of_not_terminal κ hw hcnt
      · exact restrictToClass_apply_of_ne _ _ hcq
    obtain ⟨s, hs⟩ := N.terminalSLC_kernel_unique κ hbpos hboff hbker hvoff hvker
    refine ⟨s, fun c hcq => ?_⟩
    have := congrFun hs c
    rwa [restrictToClass_apply_of_eq _ _ hcq, Pi.smul_apply, smul_eq_mul] at this
  -- `Ψx = ystar + t·b` on `θ`
  have hwxker : N.kineticMap κ (Ψx - ystar) = 0 := by
    rw [map_sub, hAys, sub_self]
  obtain ⟨t, ht⟩ := hkeruniq (Ψx - ystar) hwxker
  have htval : ∀ c, N.classOf c = θ → Ψx c = ystar c + t * b c := by
    intro c hcq; have := ht c hcq; simp only [Pi.sub_apply] at this; linarith [this]
  -- `Ψy = (cy/cx)·ystar + γ·b` on `θ`
  have hwyker : N.kineticMap κ (Ψy - (cy / cx) • ystar) = 0 := by
    rw [map_sub, map_smul, hAy, hAys, hAx, smul_smul,
      show cy / cx * cx = cy from div_mul_cancel₀ cy hcx0, sub_self]
  obtain ⟨γ, hγ⟩ := hkeruniq (Ψy - (cy / cx) • ystar) hwyker
  have hγval : ∀ c, N.classOf c = θ → Ψy c = cy / cx * ystar c + γ * b c := by
    intro c hcq; have := hγ c hcq
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this; linarith [this]
  -- `t > 0` and `γ > 0` (evaluate at the zero-coordinate `cm`).
  have hcmθ : N.classOf cm = θ := hSLθ' cm hcmsl
  have hbcm : 0 < b cm := hbpos cm hcmsl
  have htpos : 0 < t := by
    have := htval cm hcmθ
    rw [hcm0, zero_add] at this
    have hx := hΨxpos cm
    nlinarith [this, hx, hbcm]
  have hγpos : 0 < γ := by
    have := hγval cm hcmθ
    rw [hcm0, mul_zero, zero_add] at this
    have hy := hΨypos cm
    nlinarith [this, hy, hbcm]
  -- the two equilibrium parameters
  set βx : ℝ := 1 / t with hβx
  set βy : ℝ := cy / (cx * γ) with hβy
  -- key pointwise identities `β · ystar + b = Ψ / scale`
  have hβxc : ∀ c, N.classOf c = θ → βx * ystar c + b c = Ψx c / t := by
    intro c hcq; rw [htval c hcq, hβx]; field_simp
  have hβyc : ∀ c, N.classOf c = θ → βy * ystar c + b c = Ψy c / γ := by
    intro c hcq; rw [hγval c hcq, hβy]; field_simp
  -- the index sets `s`, `U` over the deficient class
  set sS : Finset N.ComplexIdx := Finset.univ.filter (fun c => N.classOf c = θ ∧ 0 < ystar c)
    with hsS
  set US : Finset N.ComplexIdx := Finset.univ.filter (fun c => N.classOf c = θ ∧ ystar c = 0)
    with hUS
  have hmems : ∀ c, c ∈ sS ↔ N.classOf c = θ ∧ 0 < ystar c := by
    intro c; rw [hsS, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ c, h⟩⟩
  have hmemU : ∀ c, c ∈ US ↔ N.classOf c = θ ∧ ystar c = 0 := by
    intro c; rw [hUS, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ c, h⟩⟩
  have hdisj : Disjoint sS US := by
    rw [Finset.disjoint_left]
    intro c hcs hcU
    exact absurd ((hmemU c).mp hcU).2 ((hmems c).mp hcs).2.ne'
  have hsuU : sS ∪ US = Finset.univ.filter (fun c => N.classOf c = θ) := by
    apply Finset.ext; intro c
    simp only [Finset.mem_union, hmems, hmemU, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hcq; rcases lt_or_eq_of_le (hynn c) with h | h
      · exact Or.inl ⟨hcq, h⟩
      · exact Or.inr ⟨hcq, h.symm⟩
  have hys : ∀ c ∈ sS, 0 < ystar c := fun c hc => ((hmems c).mp hc).2
  have hyU : ∀ c ∈ US, ystar c = 0 := fun c hc => ((hmemU c).mp hc).2
  -- `b > 0` exactly on the zero set within `θ` (the zero coordinates are in the SLC).
  have hUbpos : ∀ c, N.classOf c = θ → ystar c = 0 → 0 < b c :=
    fun c _ hy0 => hbpos c (hUsl c hy0)
  -- there is a complex of `θ` where `y*` is positive (else `g = 0`)
  have hc1 : ∃ c1 : N.ComplexIdx, N.classOf c1 = θ ∧ 0 < ystar c1 := by
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    have hy0 : ∀ c, N.classOf c = θ → ystar c = 0 :=
      fun c hcq => le_antisymm (hcon c hcq) (hynn c)
    apply hg0
    have hcxg : cx • g = N.kineticMap κ (N.restrictToClass θ Ψx) := by
      rw [N.kineticMap_restrictToClass, hAx]
      funext c; by_cases hcq : N.classOf c = θ
      · simp [restrictToClass_apply_of_eq, hcq]
      · rw [restrictToClass_apply_of_ne _ _ hcq, Pi.smul_apply, smul_eq_mul,
          hgθ c hcq, mul_zero]
    have hrΨx : N.restrictToClass θ Ψx = t • b := by
      funext c; by_cases hcq : N.classOf c = θ
      · rw [restrictToClass_apply_of_eq _ _ hcq, htval c hcq, hy0 c hcq, zero_add,
          Pi.smul_apply, smul_eq_mul]
      · rw [restrictToClass_apply_of_ne _ _ hcq, Pi.smul_apply, smul_eq_mul,
          hboff c (fun hsl => hcq (hSLθ' c hsl)), mul_zero]
    rw [hrΨx, map_smul, hbker, smul_zero] at hcxg
    exact (smul_eq_zero.mp hcxg).resolve_left hcx0
  obtain ⟨c1, hc1θ, hc1pos⟩ := hc1
  -- `a₀ > 0`: net inflow into the zero set from a `y*`-positive complex (a crossing reaction)
  have ha0 : 0 < ∑ c ∈ US, N.kineticMap κ ystar c := by
    obtain ⟨d, hreach, hdterm⟩ := N.exists_terminal_reachable c1
    have hdθ : N.classOf d = θ := by
      rw [← hc1θ]; exact (Quotient.sound (Linked.of_reaches hreach)).symm
    have hSLd : N.StronglyLinked c0.val d.val := hSLθ d hdθ hdterm
    have hreachcm : N.Reaches c1.val cm.val := hreach.trans (hSLd.2.trans hcmsl.1)
    obtain ⟨r₀, hns, hnt⟩ :=
      N.exists_crossing_reaction
        (fun c => ∃ h : c ∈ N.complexes, (⟨c, h⟩ : N.ComplexIdx) ∈ US) hreachcm
        (fun ⟨h, hmem⟩ => absurd ((hmemU _).mp hmem).2 hc1pos.ne')
        ⟨cm.property, (hmemU cm).mpr ⟨hcmθ, hcm0⟩⟩
    obtain ⟨ht, htmem⟩ := hnt
    have htgtU : N.targetIdx r₀ ∈ US := htmem
    have hsrcU : N.sourceIdx r₀ ∉ US := fun hmem => hns ⟨(N.sourceIdx r₀).property, hmem⟩
    have hsrcθ : N.classOf (N.sourceIdx r₀) = θ := by
      rw [N.classOf_sourceIdx_eq_targetIdx]; exact ((hmemU _).mp htgtU).1
    have hsrcpos : 0 < ystar (N.sourceIdx r₀) := by
      rcases lt_or_eq_of_le (hynn (N.sourceIdx r₀)) with hp | hp
      · exact hp
      · exact absurd ((hmemU _).mpr ⟨hsrcθ, hp.symm⟩) hsrcU
    exact N.sum_kineticMap_pos_of_inflow κ ystar US hynn hyU hsrcU htgtU hsrcpos
  -- the level set decomposes as a super-level set of `b − v·y*`
  have hcombine : ∀ v : ℝ,
      (∑ c ∈ US, N.kineticMap κ ystar c)
        + (∑ c ∈ sS.filter (fun c => v < b c / ystar c), N.kineticMap κ ystar c)
      = ∑ c ∈ Finset.univ.filter (fun c => v * ystar c < b c), N.kineticMap κ ystar c := by
    intro v
    have hdU : Disjoint (sS.filter (fun c => v < b c / ystar c)) US := by
      rw [Finset.disjoint_left]
      intro c hcs hcU
      have hpos : 0 < ystar c := ((hmems c).mp (Finset.mem_of_mem_filter c hcs)).2
      rw [((hmemU c).mp hcU).2] at hpos; exact lt_irrefl 0 hpos
    rw [add_comm, ← Finset.sum_union hdU]
    apply Finset.sum_subset
    · intro c hc
      rw [Finset.mem_filter]; refine ⟨Finset.mem_univ c, ?_⟩
      rw [Finset.mem_union] at hc
      rcases hc with hc | hc
      · have hyc : 0 < ystar c := ((hmems c).mp (Finset.mem_of_mem_filter c hc)).2
        exact (lt_div_iff₀ hyc).mp (Finset.mem_filter.mp hc).2
      · have hcU := (hmemU c).mp hc
        rw [hcU.2, mul_zero]; exact hUbpos c hcU.1 hcU.2
    · intro c hcuniv hc2
      by_contra hGc
      have hcθ : N.classOf c = θ := by by_contra h; exact hGc (hGθ c h)
      have hlt : v * ystar c < b c := (Finset.mem_filter.mp hcuniv).2
      rw [Finset.mem_union, not_or] at hc2
      rcases lt_or_eq_of_le (hynn c) with hyc | hyc
      · exact hc2.1 (Finset.mem_filter.mpr ⟨(hmems c).mpr ⟨hcθ, hyc⟩,
          (lt_div_iff₀ hyc).mpr hlt⟩)
      · exact hc2.2 ((hmemU c).mpr ⟨hcθ, hyc.symm⟩)
  -- the level-set sign in all three threshold regimes
  have hlevel : ∀ v : ℝ,
      0 ≤ (∑ c ∈ US, N.kineticMap κ ystar c)
        + ∑ c ∈ sS.filter (fun c => v < b c / ystar c), N.kineticMap κ ystar c := by
    intro v
    rw [hcombine v]
    rcases lt_trichotomy v 0 with hv | hv | hv
    · have heq : (∑ c ∈ Finset.univ.filter (fun c => v * ystar c < b c), N.kineticMap κ ystar c)
          = ∑ c, N.kineticMap κ ystar c := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro c _ hc2
        by_contra hGc
        have hcθ : N.classOf c = θ := by by_contra h; exact hGc (hGθ c h)
        refine hc2 (Finset.mem_filter.mpr ⟨Finset.mem_univ c, ?_⟩)
        by_cases hb : 0 < b c
        · nlinarith [mul_nonpos_of_nonpos_of_nonneg hv.le (hynn c)]
        · have hb0 : b c = 0 := le_antisymm (not_lt.mp hb) (hbnn c)
          have hsl : ¬ N.StronglyLinked c0.val c.val := fun h => hb (hbpos c h)
          have hyp : 0 < ystar c := by rw [hyoffSL c hsl]; exact hΨxpos c
          rw [hb0]; nlinarith [hyp]
      rw [heq, hGsum]
    · subst hv
      have hfeq : (Finset.univ.filter (fun c => (0 : ℝ) * ystar c < b c))
          = Finset.univ.filter (fun c => (0 : ℝ) < b c) := by
        apply Finset.filter_congr; intro c _; rw [zero_mul]
      rw [hfeq]
      apply N.sum_kineticMap_closed_nonneg κ ystar _ _ hynn
      intro r hsrc
      rw [Finset.mem_filter] at hsrc ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have hsl : N.StronglyLinked c0.val (N.sourceIdx r).val := (hbpos_iff _).mp hsrc.2
      have hreachtgt : N.Reaches c0.val (N.targetIdx r).val := hsl.1.tail ⟨r, rfl, rfl⟩
      exact (hbpos_iff _).mpr (N.stronglyLinked_of_reaches_of_terminal hc0term hreachtgt)
    · exact N.sum_kineticMap_superlevel_nonneg κ b ystar hv hbker
  -- total exponent sum over the class is zero
  have hsum0 : (∑ c ∈ US, N.kineticMap κ ystar c) + ∑ c ∈ sS, N.kineticMap κ ystar c = 0 := by
    have huniv : (∑ c ∈ sS ∪ US, N.kineticMap κ ystar c) = 0 := by
      rw [hsuU]
      rw [show (∑ c ∈ Finset.univ.filter (fun c => N.classOf c = θ), N.kineticMap κ ystar c)
            = ∑ c, N.kineticMap κ ystar c from
          Finset.sum_subset (Finset.subset_univ _)
            (fun c _ hc => hGθ c (by simpa using hc)), hGsum]
    rw [Finset.sum_union hdisj] at huniv; linarith [huniv]
  -- domain membership for both parameters, from positivity of the monomials
  have hd₁ : ∀ c ∈ sS, - (b c / ystar c) < βx := by
    intro c hc
    have hcq : N.classOf c = θ := ((hmems c).mp hc).1
    have hyc : 0 < ystar c := ((hmems c).mp hc).2
    have hpos : 0 < βx * ystar c + b c := by rw [hβxc c hcq]; exact div_pos (hΨxpos c) htpos
    have key : 0 < βx + b c / ystar c := by
      rw [show βx + b c / ystar c = (βx * ystar c + b c) / ystar c by field_simp]
      exact div_pos hpos hyc
    linarith [key]
  have hd₂ : ∀ c ∈ sS, - (b c / ystar c) < βy := by
    intro c hc
    have hcq : N.classOf c = θ := ((hmems c).mp hc).1
    have hyc : 0 < ystar c := ((hmems c).mp hc).2
    have hpos : 0 < βy * ystar c + b c := by rw [hβyc c hcq]; exact div_pos (hΨypos c) hγpos
    have key : 0 < βy + b c / ystar c := by
      rw [show βy + b c / ystar c = (βy * ystar c + b c) / ystar c by field_simp]
      exact div_pos hpos hyc
    linarith [key]
  -- both parameters are roots of the log-sum `H`
  have hHzero : ∀ (z : Concentration S), z.Positive → ∀ (β rr : ℝ), 0 < rr →
      (∀ c, N.classOf c = θ → β * ystar c + b c = N.complexMonomialVector z c / rr) →
      (∑ c ∈ sS ∪ US, N.kineticMap κ ystar c * Real.log (β * ystar c + b c)) = 0 := by
    intro z hz β rr hrr hβc
    rw [hsuU]
    rw [show (∑ c ∈ Finset.univ.filter (fun c => N.classOf c = θ),
              N.kineticMap κ ystar c * Real.log (β * ystar c + b c))
          = ∑ c, N.kineticMap κ ystar c * Real.log (β * ystar c + b c) from
        Finset.sum_subset (Finset.subset_univ _)
          (fun c _ hc => by rw [hGθ c (by simpa using hc), zero_mul])]
    rw [show (∑ c, N.kineticMap κ ystar c * Real.log (β * ystar c + b c))
          = ∑ c, N.kineticMap κ ystar c
              * (Real.log (N.complexMonomialVector z c) - Real.log rr) from
        Finset.sum_congr rfl fun c _ => by
          by_cases hcq : N.classOf c = θ
          · have hzc : (0 : ℝ) < N.complexMonomialVector z c :=
              Complex.massActionMonomial_pos hz c.val
            rw [hβc c hcq, Real.log_div hzc.ne' hrr.ne']
          · rw [hGθ c hcq, zero_mul, zero_mul]]
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hGsum, zero_mul, sub_zero]
    rw [show (∑ c, N.kineticMap κ ystar c * Real.log (N.complexMonomialVector z c))
          = cx * ∑ c, g c * Real.log (N.complexMonomialVector z c) from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by
          rw [hG]; simp only [Pi.smul_apply, smul_eq_mul]; ring]
    rw [hortho hz, mul_zero]
  have hH : (∑ c ∈ sS ∪ US, N.kineticMap κ ystar c * Real.log (βx * ystar c + b c))
      = ∑ c ∈ sS ∪ US, N.kineticMap κ ystar c * Real.log (βy * ystar c + b c) :=
    (hHzero x hxpos βx t htpos hβxc).trans (hHzero y hypos βy γ hγpos hβyc).symm
  -- the two parameters coincide, forcing proportionality
  have hβeq : βx = βy :=
    eq_of_shiftedLogSum_eq sS US hdisj ystar b (N.kineticMap κ ystar) hys hyU ha0 hsum0
      hlevel hd₁ hd₂ hH
  refine ⟨t / γ, by positivity, fun c hcq => ?_⟩
  have hpr : Ψx c / t = Ψy c / γ := by
    rw [← hβxc c hcq, hβeq, hβyc c hcq]
  have h2 : Ψx c * γ = Ψy c * t := (div_eq_div_iff htpos.ne' hγpos.ne').mp hpr
  rw [div_mul_eq_mul_div, eq_div_iff hγpos.ne']
  linarith [h2]

/-- **The log-monomial ratio is constant on the deficient class.** For a deficiency-one network
meeting the hypotheses, two positive mass-action steady states have equal log-monomial ratio at
any two complexes of the deficient linkage class. -/
theorem logMonomialRatio_eqOn_deficientClass (N : Network S) (h : N.DeficiencyOneHypotheses)
    (hδ : N.DeficiencyOne) (κ : RateConstants N) {x y : Concentration S}
    (hxpos : x.Positive) (hypos : y.Positive)
    (hxss : N.IsMassActionSteadyState κ x) (hyss : N.IsMassActionSteadyState κ y)
    {θ : Quotient N.linkedSetoid} (hθ : N.linkageDeficiency θ = 1) :
    ∀ c d, N.classOf c = θ → N.classOf d = θ →
      N.logMonomialRatio x y c = N.logMonomialRatio x y d := by
  classical
  obtain ⟨q0, hq0δ, hq0eq⟩ :=
    N.deficiencySubspace_eq_linkageDeficiencySubspace_of_deficiencyOne hδ h.conditions
  obtain ⟨q1, _, hq1uniq⟩ := N.existsUnique_deficient_of_deficiencyOne hδ h.conditions
  have hθq0 : θ = q0 := (hq1uniq θ hθ).trans (hq1uniq q0 hq0δ).symm
  subst hθq0
  -- the deficiency mode
  obtain ⟨g, hgmem, hg0, hspan⟩ := N.exists_spanning_deficiencySubspace_of_deficiencyOne hδ
  have hgY : N.complexMap g = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hgmem).1
  have hgθ : ∀ c, N.classOf c ≠ θ → g c = 0 := by
    rw [hq0eq] at hgmem
    have hg' : g ∈ N.deficiencySubspace ⊓ N.supportedOn θ := hgmem
    exact mem_supportedOn.mp (Submodule.mem_inf.mp hg').2
  obtain ⟨cx, hcx⟩ := hspan _ (N.kineticMap_complexMonomial_mem_deficiencySubspace κ hxss)
  obtain ⟨cy, hcy⟩ := hspan _ (N.kineticMap_complexMonomial_mem_deficiencySubspace κ hyss)
  -- terminal representative of the class and the one-terminal facts
  obtain ⟨σ, ⟨hσθ, hσterm⟩, hσuniq⟩ := h.oneTerminal θ
  obtain ⟨c0, hc0σ⟩ := Quotient.exists_rep σ
  have hc0term : N.IsTerminalSLC c0.val := by rw [← isTerminalSLClass_mk, hc0σ]; exact hσterm
  have hc0θ : N.classOf c0 = θ := by
    have hcl : N.classOf c0 = N.strongToLinkage (Quotient.mk N.stronglyLinkedSetoid c0) :=
      (N.strongToLinkage_mk c0).symm
    rw [hcl, hc0σ]; exact hσθ
  have hSLθ : ∀ c, N.classOf c = θ → N.IsTerminalSLC c.val → N.StronglyLinked c0.val c.val := by
    intro c hcθ hcterm
    have e1 : Quotient.mk N.stronglyLinkedSetoid c = σ :=
      hσuniq _ ⟨by rw [strongToLinkage_mk]; exact hcθ, by rw [isTerminalSLClass_mk]; exact hcterm⟩
    exact Quotient.exact (hc0σ.trans e1.symm)
  -- proportionality of the monomials on the class
  have hprop : ∃ K : ℝ, 0 < K ∧
      ∀ c, N.classOf c = θ → N.complexMonomialVector x c = K * N.complexMonomialVector y c := by
    by_cases hcx0 : cx = 0
    · by_cases hcy0 : cy = 0
      · -- both complex-balanced
        obtain ⟨b', hb'pos, hb'ker, hb'uniq⟩ := N.exists_kernel_mode_of_deficiencyOne h κ θ
        have hAx0 : N.kineticMap κ (N.complexMonomialVector x) = 0 := by
          rw [← hcx, hcx0, zero_smul]
        have hAy0 : N.kineticMap κ (N.complexMonomialVector y) = 0 := by
          rw [← hcy, hcy0, zero_smul]
        have hrest : ∀ z : Concentration S, N.kineticMap κ (N.complexMonomialVector z) = 0 →
            N.kineticMap κ (N.restrictToClass θ (N.complexMonomialVector z)) = 0 := by
          intro z hz0
          rw [N.kineticMap_restrictToClass, hz0]
          funext c; by_cases hcq : N.classOf c = θ <;>
            simp [restrictToClass_apply_of_eq, restrictToClass_apply_of_ne, hcq]
        obtain ⟨sx, hsx⟩ := hb'uniq _ (hrest x hAx0)
          (fun c hc => restrictToClass_apply_of_ne _ _ hc)
        obtain ⟨sy, hsy⟩ := hb'uniq _ (hrest y hAy0)
          (fun c hc => restrictToClass_apply_of_ne _ _ hc)
        have hb'c0 : 0 < b' c0 := hb'pos c0 hc0θ hc0term
        have hxc0 : N.complexMonomialVector x c0 = sx * b' c0 := by
          have := congrFun hsx c0
          rwa [restrictToClass_apply_of_eq _ _ hc0θ, Pi.smul_apply, smul_eq_mul] at this
        have hyc0 : N.complexMonomialVector y c0 = sy * b' c0 := by
          have := congrFun hsy c0
          rwa [restrictToClass_apply_of_eq _ _ hc0θ, Pi.smul_apply, smul_eq_mul] at this
        have hxc0pos : 0 < N.complexMonomialVector x c0 :=
          Complex.massActionMonomial_pos hxpos c0.val
        have hyc0pos : 0 < N.complexMonomialVector y c0 :=
          Complex.massActionMonomial_pos hypos c0.val
        have hsxpos : 0 < sx := by nlinarith [hxc0pos, hb'c0, hxc0]
        have hsypos : 0 < sy := by nlinarith [hyc0pos, hb'c0, hyc0]
        refine ⟨sx / sy, div_pos hsxpos hsypos, fun c hcq => ?_⟩
        have ex : N.complexMonomialVector x c = sx * b' c := by
          have := congrFun hsx c
          rwa [restrictToClass_apply_of_eq _ _ hcq, Pi.smul_apply, smul_eq_mul] at this
        have ey : N.complexMonomialVector y c = sy * b' c := by
          have := congrFun hsy c
          rwa [restrictToClass_apply_of_eq _ _ hcq, Pi.smul_apply, smul_eq_mul] at this
        rw [ex, ey]; field_simp
      · -- `c_y ≠ 0`: run the core with the roles swapped
        obtain ⟨K', hK', hP'⟩ := N.proportional_of_kineticImage_ne κ hypos hxpos hc0term hc0θ
          hSLθ hg0 hgY hgθ hcy0 hcy.symm hcx.symm
        refine ⟨1 / K', by positivity, fun c hcq => ?_⟩
        have := hP' c hcq
        rw [this]; field_simp
    · exact N.proportional_of_kineticImage_ne κ hxpos hypos hc0term hc0θ hSLθ hg0 hgY hgθ hcx0
        hcx.symm hcy.symm
  -- constancy of `Φ` follows from proportionality
  obtain ⟨K, hK, hP⟩ := hprop
  have key : ∀ e, N.classOf e = θ → N.logMonomialRatio x y e = Real.log K := by
    intro e he
    have hye : 0 < N.complexMonomialVector y e := Complex.massActionMonomial_pos hypos e.val
    rw [logMonomialRatio, hP e he, Real.log_mul hK.ne' hye.ne']
    ring
  intro c d hc hd; rw [key c hc, key d hd]

/-- **The deficiency-one uniqueness theorem.** A deficiency-one network meeting Feinberg's
structural hypotheses has at most one positive mass-action steady state in each positive
stoichiometric compatibility class, for every choice of rate constants. -/
theorem deficiencyOneUniqueness (N : Network S) (h : N.DeficiencyOneHypotheses)
    (hδ : N.DeficiencyOne) : N.DeficiencyOneUniqueness := by
  refine N.deficiencyOneUniqueness_of_deficientClassRatioConst h ?_
  intro κ x₀ _ x y hxmem hxss hymem hyss r hr
  exact N.logMonomialRatio_eqOn_deficientClass h hδ κ hxmem.2 hymem.2 hxss hyss hr
    (N.targetIdx r) (N.sourceIdx r) (N.classOf_sourceIdx_eq_targetIdx r ▸ rfl)
    (N.classOf_sourceIdx_eq_targetIdx r ▸ rfl)

end Network

end CRNT

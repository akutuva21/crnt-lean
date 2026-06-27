import CRNT.Dynamics.GACSeparatingCapstone
import CRNT.Dynamics.GenuineConfinement
import CRNT.Dynamics.ForwardInvariance
import CRNT.Dynamics.SingleLinkageGAC
import CRNT.Dynamics.GACNoCriticalSiphon

/-!
# A witness for the separating-confinement predicate

`Network.SeparatingConfinement` is the single predicate to which the global attractor conjecture for
weakly reversible complex-balanced networks is reduced (`gac_of_separatingConfinement`). Throughout
the reduction it appears only as a hypothesis. This module constructs it outright in the
near-equilibrium regime, so the predicate is exhibited as realizable rather than merely assumed.

When the relative entropy of the start lies strictly below every reference coordinate
(`hloc : ∀ s, relEntropy x* x₀ < x*_s`), the relative-entropy sublevel set through `x₀` is a compact
region sitting entirely inside the open positive orthant (`relEntropy_sublevel_subset_positive`): a
boundary state would have relative entropy at least `x*_s`. The genuine mass-action orbit through
`x₀` stays in that set — it is positive (`genuineOrbit_pos`) and its relative entropy never rises
(`genuineOrbit_relEntropy_le`). Compactness then converts the orbit's positivity into a uniform
per-coordinate floor, which is exactly the separating-confinement data: a bounded, forward-invariant
region a fixed distance above every facet.

A second reading places the predicate exactly: it is logically equivalent to the persistence
certificate `Network.PersistentFrom` that `gac_of_persistent` and the single-linkage development
consume. A separating region, closed up, is a compact positive absorbing set; a compact positive
absorbing set, with the start adjoined, is a separating region. So `SeparatingConfinement` is neither
weaker nor stronger than persistence — it is the same content in geometric dress.

## Contents

* `Network.separatingConfinement_of_local` — under the local relative-entropy hypothesis, the
  separating-confinement predicate holds at `x₀`.

* `Network.gac_of_local_separatingConfinement` — composing with `gac_of_separatingConfinement`, the
  resulting global attractor conclusion routed through the constructed witness.

* `Network.persistentFrom_of_separatingConfinement` and
  `Network.separatingConfinement_of_persistentFrom` — the two directions identifying
  `SeparatingConfinement` with the persistence certificate `PersistentFrom` (the reverse for a
  positive start).

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.GACSeparatingCapstone`,
`CRNT.Dynamics.GenuineConfinement`, `CRNT.Dynamics.ForwardInvariance`,
`CRNT.Dynamics.SingleLinkageGAC`.
-/

open scoped BigOperators NNReal Topology
open Filter

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The separating-confinement predicate holds near equilibrium.** For a positive complex-balanced
reference `x*` and a positive start `x₀` whose relative entropy lies strictly below every reference
coordinate, the relative-entropy sublevel set through `x₀` is a compact region inside the open
positive orthant that the genuine orbit never leaves; its compactness furnishes a uniform
per-coordinate floor. This is `Network.SeparatingConfinement` at `x₀`. -/
theorem separatingConfinement_of_local (N : Network S) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hloc : ∀ s, relEntropy xstar x₀ < xstar s) :
    N.SeparatingConfinement κ x₀ := by
  set C₀ := relEntropy xstar x₀ with hC₀
  set R : Set (Concentration S) := {y | y.Nonnegative ∧ relEntropy xstar y ≤ C₀} with hR
  have hRcpt : IsCompact R := isCompact_relEntropy_sublevel hxs C₀
  have hRpos : ∀ y ∈ R, y.Positive := fun y hy =>
    relEntropy_sublevel_subset_positive hxs hloc hy.1 hy.2
  have hx0R : x₀ ∈ R := ⟨hx0.nonnegative, le_of_eq hC₀.symm⟩
  have hRne : R.Nonempty := ⟨x₀, hx0R⟩
  -- A strictly positive per-coordinate floor, attained on the compact region.
  have hfloor : ∀ s, ∃ e : ℝ, 0 < e ∧ ∀ y ∈ R, e ≤ y s := by
    intro s
    obtain ⟨p, hpR, hpmin⟩ := hRcpt.exists_isMinOn hRne (continuous_apply s).continuousOn
    exact ⟨p s, hRpos p hpR s, fun y hy => isMinOn_iff.mp hpmin y hy⟩
  choose ε hεpos hεle using hfloor
  refine ⟨R, R, ε, hRcpt, hεpos, subset_refl R, fun y hy s => hεle s y hy, hx0R, ?_⟩
  -- Forward invariance: the genuine orbit through `x₀` is positive with nonincreasing entropy.
  intro Γ hΓ0 hΓd t ht
  have hΓ0pos : (Γ 0).Positive := by rw [hΓ0]; exact hx0
  have hpos := N.genuineOrbit_pos κ hΓ0pos hΓd
  have hle := N.genuineOrbit_relEntropy_le κ hxs hcb hpos hΓd t ht
  rw [hΓ0] at hle
  exact ⟨(hpos t ht).nonnegative, hle.trans_eq hC₀.symm⟩

/-- **Global attractor conclusion near equilibrium, via the constructed witness.** Composing
`separatingConfinement_of_local` with the reduction `gac_of_separatingConfinement`: for a weakly
reversible network with a positive complex-balanced reference `x*` and a positive start `x₀` in its
class whose relative entropy is below every reference coordinate, the genuine semiflow's ω-limit set
through `x₀` is `{x*}`. -/
theorem gac_of_local_separatingConfinement
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar)
    (hloc : ∀ s, relEntropy xstar x₀ < xstar s) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} :=
  N.gac_of_separatingConfinement hwr κ hxs hcb hx0 hx0compat
    (N.separatingConfinement_of_local κ hxs hcb hx0 hloc)

/-- **Separating confinement gives the persistence certificate.** A separating region, being
contained in a per-facet floor, has its closure inside the open positive orthant; that closure is a
compact positive set absorbing the genuine orbit — exactly `Network.PersistentFrom`. -/
theorem persistentFrom_of_separatingConfinement (N : Network S) (κ : N.RateConstants)
    {x₀ : Concentration S} (hsc : N.SeparatingConfinement κ x₀) :
    N.PersistentFrom κ x₀ := by
  obtain ⟨R, B, ε, hBcpt, hεpos, hRB, hfloor, hx0R, hinv⟩ := hsc
  have hFloorClosed : IsClosed {y : Concentration S | ∀ s, ε s ≤ y s} := by
    have hrw : {y : Concentration S | ∀ s, ε s ≤ y s} = ⋂ s, {y | ε s ≤ y s} := by
      ext y; simp [Set.mem_iInter]
    rw [hrw]
    exact isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)
  have hRfloor : R ⊆ {y : Concentration S | ∀ s, ε s ≤ y s} := fun y hy => hfloor y hy
  have hclR : closure R ⊆ {y : Concentration S | ∀ s, ε s ≤ y s} :=
    closure_minimal hRfloor hFloorClosed
  refine ⟨closure R,
    hBcpt.of_isClosed_subset isClosed_closure (closure_minimal hRB hBcpt.isClosed), ?_, ?_⟩
  · intro y hy s
    exact lt_of_lt_of_le (hεpos s) (hclR hy s)
  · intro Γ hΓ0 hΓd t ht
    exact subset_closure (hinv Γ hΓ0 hΓd t ht)

/-- **The persistence certificate gives separating confinement, for a positive start.** A compact
positive absorbing set `K₀`, with the start adjoined, is a bounded forward-invariant region holding a
uniform per-coordinate floor — exactly `Network.SeparatingConfinement`. The floor is attained on the
compact region. -/
theorem separatingConfinement_of_persistentFrom (N : Network S) (κ : N.RateConstants)
    {x₀ : Concentration S} (hx0 : x₀.Positive) (hpf : N.PersistentFrom κ x₀) :
    N.SeparatingConfinement κ x₀ := by
  obtain ⟨K₀, hK₀cpt, hK₀pos, hconf⟩ := hpf
  set R : Set (Concentration S) := insert x₀ K₀ with hR
  have hRcpt : IsCompact R := hK₀cpt.insert x₀
  have hRpos : ∀ y ∈ R, y.Positive := by
    intro y hy
    rcases hy with rfl | hy
    · exact hx0
    · exact hK₀pos y hy
  have hRne : R.Nonempty := ⟨x₀, Set.mem_insert _ _⟩
  have hfloor : ∀ s, ∃ e : ℝ, 0 < e ∧ ∀ y ∈ R, e ≤ y s := by
    intro s
    obtain ⟨p, hpR, hpmin⟩ := hRcpt.exists_isMinOn hRne (continuous_apply s).continuousOn
    exact ⟨p s, hRpos p hpR s, fun y hy => isMinOn_iff.mp hpmin y hy⟩
  choose ε hεpos hεle using hfloor
  refine ⟨R, R, ε, hRcpt, hεpos, subset_refl R, fun y hy s => hεle s y hy,
    Set.mem_insert _ _, ?_⟩
  intro Γ hΓ0 hΓd t ht
  exact Set.mem_insert_of_mem _ (hconf Γ hΓ0 hΓd t ht)

/-- **The no-critical-siphon class produces the persistence certificate.** For a weakly reversible
network with no critical siphon, a positive complex-balanced reference `x*`, and a positive start
`x₀` in its class, the genuine orbit's closure is a compact set inside the open positive orthant that
absorbs every genuine orbit through `x₀` — exactly `Network.PersistentFrom`.

The headline theorem `gac_of_hasNoCriticalSiphon` gives the genuine semiflow with ω-limit `{x*}`. The
orbit lies in a compact relative-entropy sublevel set; its closure splits, at every cut time, into a
compact initial arc and a tail whose closure is the ω-limit set, so every closure point is either an
orbit point or `x*` — strictly positive in both cases. Uniqueness of the genuine orbit inside the
confining box (`genuineOrbit_unique_of_box`) carries the confinement to an arbitrary integral curve.

This is the persistence certificate the no-critical-siphon argument does not otherwise expose. -/
theorem persistentFrom_of_hasNoCriticalSiphon
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants) (hncs : N.HasNoCriticalSiphon)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar) :
    N.PersistentFrom κ x₀ := by
  obtain ⟨ϕ, γ, hγ0, hϕγ, hsol, hω⟩ :=
    N.gac_of_hasNoCriticalSiphon hwr κ hncs hxs hcb hx0 hx0compat
  set C₀ := relEntropy xstar x₀ with hC₀
  set B : ℝ := 1 + |C₀| + ∑ s, Real.exp 2 * xstar s with hBdef
  have hsumnn : 0 ≤ ∑ s, Real.exp 2 * xstar s :=
    Finset.sum_nonneg fun s _ => (mul_pos (Real.exp_pos 2) (hxs s)).le
  have hBnn : 0 ≤ B := by rw [hBdef]; have := abs_nonneg C₀; linarith
  have hBbig : ∀ s, max (Real.exp 2 * xstar s) C₀ < B := by
    intro s
    have hsum : Real.exp 2 * xstar s ≤ ∑ s', Real.exp 2 * xstar s' :=
      Finset.single_le_sum (fun s' _ => (mul_pos (Real.exp_pos 2) (hxs s')).le) (Finset.mem_univ s)
    rw [max_lt_iff, hBdef]
    exact ⟨by linarith [abs_nonneg C₀], by linarith [le_abs_self C₀]⟩
  have hγ0x0 : γ x₀ 0 = x₀ := hγ0 x₀
  have hΓ0pos : (γ x₀ 0).Positive := by rw [hγ0x0]; exact hx0
  have hpos : ∀ t, 0 ≤ t → (γ x₀ t).Positive := N.genuineOrbit_pos κ hΓ0pos hsol
  have hrele : ∀ t, 0 ≤ t → relEntropy xstar (γ x₀ t) ≤ C₀ := by
    intro t ht
    have := N.genuineOrbit_relEntropy_le κ hxs hcb hpos hsol t ht
    rwa [hγ0x0] at this
  -- box bound shared by every genuine orbit through `x₀`
  have hboxOf : ∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
      (∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) →
      ∀ t, 0 ≤ t → ∀ s, |Γ t s| ≤ B := by
    intro Γ hΓ0 hΓd t ht s
    have hΓ0p : (Γ 0).Positive := by rw [hΓ0]; exact hx0
    have hp := N.genuineOrbit_pos κ hΓ0p hΓd t ht
    have hre : relEntropy xstar (Γ t) ≤ C₀ := by
      have := N.genuineOrbit_relEntropy_le κ hxs hcb (N.genuineOrbit_pos κ hΓ0p hΓd) hΓd t ht
      rwa [hΓ0] at this
    rw [abs_le]
    exact ⟨by linarith [hp s], le_of_lt (lt_of_le_of_lt
      (relEntropy_coord_le hxs hp.nonnegative hre s) (hBbig s))⟩
  -- the compact sublevel set and the orbit's closure
  set SC : Set (Concentration S) := {y | y.Nonnegative ∧ relEntropy xstar y ≤ C₀} with hSCdef
  have hSCcpt : IsCompact SC := isCompact_relEntropy_sublevel hxs C₀
  set O : Set (Concentration S) := γ x₀ '' Set.Ici (0 : ℝ) with hOdef
  have hOSC : O ⊆ SC := by
    rintro z ⟨t, ht, rfl⟩
    exact ⟨(hpos t ht).nonnegative, hrele t ht⟩
  have hclOSC : closure O ⊆ SC := (IsClosed.closure_subset_iff hSCcpt.isClosed).mpr hOSC
  have hclOcpt : IsCompact (closure O) := hSCcpt.of_isClosed_subset isClosed_closure hclOSC
  -- closure of the orbit is strictly positive: each point is an orbit point or the equilibrium
  have hclOpos : ∀ p ∈ closure O, p.Positive := by
    intro p hp
    by_cases hpO : p ∈ O
    · obtain ⟨t, ht, rfl⟩ := hpO; exact hpos t ht
    · have htail : ∀ T' : ℝ≥0, p ∈ closure (Set.image2 ϕ (Set.Ici T') {x₀}) := by
        intro T'
        have hT0 : (0 : ℝ) ≤ (T' : ℝ) := T'.coe_nonneg
        have hcontOn : ContinuousOn (γ x₀) (Set.Icc 0 (T' : ℝ)) :=
          fun t ht => (hsol t ht.1).continuousAt.continuousWithinAt
        have hdecomp : O = γ x₀ '' Set.Icc 0 (T' : ℝ) ∪ γ x₀ '' Set.Ici (T' : ℝ) := by
          rw [hOdef, ← Set.image_union, Set.Icc_union_Ici_eq_Ici hT0]
        have hcompactInit : IsCompact (γ x₀ '' Set.Icc 0 (T' : ℝ)) :=
          isCompact_Icc.image_of_continuousOn hcontOn
        have hpInTail : p ∈ closure (γ x₀ '' Set.Ici (T' : ℝ)) := by
          have hpcl : p ∈ closure (γ x₀ '' Set.Icc 0 (T' : ℝ))
              ∪ closure (γ x₀ '' Set.Ici (T' : ℝ)) := by
            rw [← closure_union, ← hdecomp]; exact hp
          rcases hpcl with hpic | hpit
          · rw [hcompactInit.isClosed.closure_eq] at hpic
            exact absurd (Set.image_mono Set.Icc_subset_Ici_self hpic) hpO
          · exact hpit
        have hconv : γ x₀ '' Set.Ici (T' : ℝ) = Set.image2 ϕ (Set.Ici T') {x₀} := by
          rw [Set.image2_singleton_right]
          have hfeq : (fun s : ℝ≥0 => ϕ s x₀) = γ x₀ ∘ NNReal.toReal := by
            funext s; exact hϕγ x₀ s
          rw [hfeq, Set.image_comp, NNReal.image_coe_Ici]
        rwa [hconv] at hpInTail
      have hpω : p ∈ omegaLimit atTop ϕ {x₀} := by
        rw [omegaLimit_def]
        simp only [Set.mem_iInter]
        intro u hu
        obtain ⟨a, ha⟩ := Filter.mem_atTop_sets.mp hu
        exact closure_mono (Set.image2_subset (fun b hb => ha b hb) (subset_refl _)) (htail a)
      rw [hω, Set.mem_singleton_iff] at hpω
      rw [hpω]; exact hxs
  -- assemble the persistence certificate
  refine ⟨closure O, hclOcpt, hclOpos, ?_⟩
  intro Γ hΓ0 hΓd t ht
  have heq : Γ t = γ x₀ t :=
    N.genuineOrbit_unique_of_box κ hBnn hΓd hsol (hboxOf Γ hΓ0 hΓd)
      (hboxOf (γ x₀) hγ0x0 hsol) (by rw [hΓ0, hγ0x0]) t ht
  rw [heq]
  exact subset_closure ⟨t, ht, rfl⟩

/-- **The separating-confinement predicate holds on the no-critical-siphon class.** Combining
`persistentFrom_of_hasNoCriticalSiphon` with the persistence-to-confinement direction: for a weakly
reversible network with no critical siphon, `Network.SeparatingConfinement` holds at every positive
start in a positive complex-balanced class. This is a structural, fully decidable precondition under
which the reduction target is constructed, with the orbit allowed to approach the boundary at finite
times — only its closure is held off every facet. -/
theorem separatingConfinement_of_hasNoCriticalSiphon
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants) (hncs : N.HasNoCriticalSiphon)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar) :
    N.SeparatingConfinement κ x₀ :=
  N.separatingConfinement_of_persistentFrom κ hx0
    (N.persistentFrom_of_hasNoCriticalSiphon hwr κ hncs hxs hcb hx0 hx0compat)

end Network

end CRNT

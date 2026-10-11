import CRNT.Dynamics.HighCodimensionSiphonFace


/-!
# Scratch probe (NOT part of the build): the exact residue after the vertex descent lemma

`lake build` ignores this file.  Everything below is `CRNT/Dynamics/HighCodimensionSiphonFace.lean`
plus the three vertex lemmas landed there in the `VertexDescentProbe` commit.  Its only purpose is
to state, in Lean, exactly what is left of
`Network.exists_positive_omegaPoint_of_highCodimension_siphonFace_nonVertex` once

* `hnoG` is assumed (no positive ω-limit point exists),
* `not_isVertexZeroSet_of_siphonCarried_of_noPositive_omegaPoint` is applied to every carried face,
* `omegaPoint_zeroSet_trichotomy` is split, and
* the two "closed" branches (a strictly smaller carried critical siphon, and the all-vanishing
  branch, which `hface_of_trichotomyThird` collapses to "every ω-point has zero set exactly
  `Pmax`") are chained through the existing siphon machinery.

## What type-checks (all of it, no sorry between these steps)

* branch (I): `exists_cardMinimal_carried_siphon_lt` manufactures a cardinality-minimal carried
  critical siphon `Pm` with `Pm.card < Pmax.card`; `hPmnov : ¬ IsVertexZeroSet Pm` comes in one line
  from the vertex lemma; `Pmax ⊄ Pm` (else `Pmax ⊆ Pm` gives `Pmax.card ≤ Pm.card`) yields an
  ω-zero of `wmax` strictly outside `Pm`, and `exists_omegaPoint_vanishing_across_siphon` then gives
  an ω-point `z` vanishing both inside and outside `Pm`.
* branch (II)+(IV): `hface_of_trichotomyThird` gives `hface`, and `hface_iff_zeroSet_eq` gives
  `hzeroSet`, i.e. every ω-point has zero set exactly `Pmax`.

## The two remaining goals, verbatim

1. **branch (I).**  From `hnoG`, `hPmne`, `hPmcarr`, `hPmmin`,
   `hPmnov : ¬ N.IsVertexZeroSet Pm`, `hstrad`, `hnv`, `hcodim` (and `hmaxExact`, `hzcard`),
   derive `∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive`.

   This is Craciun v3 Theorem B / Anderson's comparable-growth estimate.  It cannot be obtained
   from the vertex technology: the descent iteration of `omegaLimit_positive_of_descend` bottoms out
   at `Pm`, and there minimality already forbids the shrinking disjunct
   (`descendStep_iff_omegaPointPositive_of_cardMinimal`), while `hPmnov` removes the vertex exit.
   The only new information available is `hstrad` (an ω-point straddling `Pm`), and no comparison of
   the zero-set cardinalities of the straddling point with `Pm.card` is derivable statically — see
   `research/DEAD-ENDS.md` A-54…A-64.

2. **branch (II).**  From `hface`, `hzeroSet`, `hPmaxne`, `hcodim : 2 ≤ finrank (stoichSubspace.map
   (projOn Pmax))`, `hnv`, derive a positive ω-point.

   This is the "ω-limit set contained in the relative interior of the `Pmax`-face" case, i.e. the
   claim that no such face can absorb the orbit.  The static hypotheses are all satisfiable there
   (`research/DEAD-ENDS.md` A-46/A-48 machine-check this on
   `CRNT.Examples.CodimTwoFaceModel`), so any proof must consume `hsol` essentially.

Both goals are the open step of the global attractor conjecture; neither is reachable by the
descent/vertex/connectedness machinery present in the tree.
-/


open scoped NNReal Topology
open Filter

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Probe: with `hnoG` assumed, what survives of the trichotomy? -/
theorem probe_residual
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx₀ : x₀.Positive)
    {Pmax : Finset S} (hPmaxne : Pmax.Nonempty)
    {wmax : Concentration S} (hwmax : wmax ∈ omegaLimit atTop ϕ {x₀})
    (hzeroMax : ∀ s, s ∈ Pmax ↔ wmax s = 0)
    (hmaxExact : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (∀ s ∈ Pmax, z s = 0) →
      ∀ s, z s = 0 ↔ s ∈ Pmax)
    (hzcard : ∀ z ∈ omegaLimit atTop ϕ {x₀},
      (Finset.univ.filter (fun s => z s = 0)).card ≤ Pmax.card)
    (hcodim : 2 ≤ Module.finrank ℝ (N.stoichSubspace.map (projOn Pmax)))
    (hcard : 2 ≤ Pmax.card)
    (hrank : N.stoichRank ≠ 1)
    (hnv : ¬ N.IsVertexZeroSet Pmax) :
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive := by
  classical
  by_contra hnoG
  have hnov : ∀ P : Finset S, N.SiphonCarried ϕ x₀ P → ¬ N.IsVertexZeroSet P :=
    fun _ hcarr => N.not_isVertexZeroSet_of_siphonCarried_of_noPositive_omegaPoint κ hxs hcb
      hϕγ hsol hωnn hωaff hx₀ hnoG hcarr
  have hcarrPmax : N.SiphonCarried ϕ x₀ Pmax := ⟨wmax, hwmax, hzeroMax⟩
  have hcritPmax : N.IsCriticalSiphon Pmax :=
    N.isCriticalSiphon_of_siphonCarried κ hϕγ hK hmaps hωnn hgenω hωaff hx₀ hPmaxne hcarrPmax
  rcases N.omegaPoint_zeroSet_trichotomy κ hϕγ hK hmaps hωnn hgenω hωaff hx₀ hmaxExact hzcard with
    h | ⟨Q, hQne, hQcrit, hQlt, hQcarr⟩ | hthird
  · exact hnoG h
  · -- BRANCH (I): a strictly smaller carried critical siphon `Q` exists
    obtain ⟨Pm, hPmcrit, hPmcarr, hPmlt, hPmmin⟩ :=
      N.exists_cardMinimal_carried_siphon_lt ⟨Q, hQcrit, hQcarr, hQlt⟩
    have hPmne : Pm.Nonempty := hPmcrit.1
    have hPmnov : ¬ N.IsVertexZeroSet Pm := hnov Pm hPmcarr
    have hout : ∃ t, t ∉ Pm ∧ wmax t = 0 := by
      by_contra hall
      push Not at hall
      have hsub : Pmax ⊆ Pm := by
        intro s hs
        by_contra hsn
        exact hall s hsn ((hzeroMax s).mp hs)
      have hcard := Finset.card_le_card hsub
      omega
    obtain ⟨t, htn, hwt0⟩ := hout
    have hstrad : ∃ z ∈ omegaLimit atTop ϕ {x₀}, ∃ s ∈ Pm, ∃ t ∉ Pm, z s = 0 ∧ z t = 0 :=
      N.exists_omegaPoint_vanishing_across_siphon κ hϕγ hsol hK hmaps hωnn hnoG hPmne hPmcarr
        ⟨wmax, hwmax, t, htn, hwt0⟩
    -- REMAINING GOAL (branch I): a contradiction out of
    --   hPmnov, hPmmin, hstrad, hnv, hcodim, hPmne, hPmcarr, Pmax, wmax
    sorry
  · -- BRANCH (II)+(IV): every ω-point vanishes on Pmax
    have hface : ∀ z ∈ omegaLimit atTop ϕ {x₀}, ∀ s ∈ Pmax, z s = 0 := by
      refine N.hface_of_trichotomyThird κ hϕγ hsol hK hmaps hmaxExact hwmax hzeroMax ?_
      intro z hz
      rcases hthird z hz with hfilter | htie
      · left
        intro s hs
        have hs' : s ∈ (Finset.univ.filter (fun u => z u = 0)) := by
          rw [hfilter]; exact hs
        simpa using hs'
      · right
        obtain ⟨hA, hB, _⟩ := htie
        obtain ⟨t, htn, hzt0⟩ := hB
        exact ⟨t, htn, hzt0⟩
    have hzeroSet : ∀ z ∈ omegaLimit atTop ϕ {x₀},
        (Finset.univ.filter (fun s => z s = 0)) = Pmax := by
      intro z hz
      exact (hface_iff_zeroSet_eq hmaxExact).mp hface z hz
    -- REMAINING GOAL (branch II): a positive ω-point out of hface, hzeroSet, hcodim, hnv, hPmaxne
    sorry

end Network
end CRNT

import CRNT.Dynamics.EscapeSiphonFace
import CRNT.Dynamics.GACOmegaPositive

/-!
# Siphon-dimension descent to an interior ω-limit point

This module is the scaffold of Anderson's siphon-dimension descent (David F. Anderson, "A proof of
the global attractor conjecture in the single linkage class case"). For a precompact positive
mass-action trajectory the boundary ω-limit points are pinned to critical-siphon faces
(`CriticalSiphonOmega`, `EscapeSiphonFace`); the descent organises those faces by the *cardinality*
of the underlying critical siphon and walks downward until the siphon is gone, at which point the
ω-limit set meets the open positive orthant and `omegaLimit_eq_singleton_of_mem_positive` collapses
it to `{x*}`.

## Carrier of a siphon

`Network.SiphonCarried ϕ x₀ P` records that the species set `P` is the zero set of *some* ω-limit
point of the trajectory through `x₀`. A boundary ω-point supplies such a carrier directly, and the
escape geometry of `exists_escape_forwardLimit_criticalSiphonFace` produces carriers inside the
forward limit of any escaping ω-point (those forward limits are subsets of the ω-limit set). A
nonempty carried set is a critical siphon (`isCriticalSiphon_zeroSet_of_mem_omegaLimit`).

## The descent

The single genuinely analytic ingredient — Anderson's comparable-growth Lyapunov-family estimate,
which forbids the trajectory from cycling among boundary faces and forces each boundary excursion to
strip away at least one species — is isolated as the predicate `Network.ComparableGrowthDescent`. It
asserts exactly one thing: every nonempty carried critical siphon `P` either coexists with a
strictly positive ω-limit point or yields another carried critical siphon `Q` with `Q.card < P.card`.
Nothing about the underlying real-analysis estimate is assumed beyond this strict-decrease step; its
proof needs near-facet influx and Lyapunov-comparison infrastructure that is not developed here.

Given that predicate the descent is finite: a critical siphon is nonempty, so its cardinality is at
least one, and a strictly decreasing chain of cardinalities cannot continue forever. Strong induction
on the cardinality (`omegaLimit_positive_of_comparableGrowthDescent`) therefore terminates in the
strictly positive ω-limit point, which `omegaLimit_eq_singleton_of_mem_positive` turns into the
global attractor conclusion `ω = {x*}` (`omegaLimit_eq_singleton_of_comparableGrowthDescent`).

The Butler–McGehee escape that manufactures the smaller-face carrier in the analytic proof is exposed
separately as `siphonCarried_of_escape`: an ω-limit set not contained in an isolated invariant set
yields an escaping ω-point whose forward limit carries a critical siphon, hence a `SiphonCarried`
witness.

The comparable-growth descent is the sole carried hypothesis.
Depends on: `CRNT.Dynamics.EscapeSiphonFace`, `CRNT.Dynamics.GACOmegaPositive`.
-/

open Filter Topology
open scoped BigOperators NNReal Topology

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **A species set carried as the zero set of an ω-limit point.** `P` is *carried* by the
trajectory through `x₀` when some ω-limit point `w ∈ ω{x₀}` vanishes exactly on `P`. Boundary
ω-points and the forward limits of escaping ω-points both furnish carriers; a nonempty carrier is a
critical siphon. -/
def SiphonCarried (_N : Network S) (ϕ : Flow ℝ≥0 (Concentration S)) (x₀ : Concentration S)
    (P : Finset S) : Prop :=
  ∃ w ∈ omegaLimit atTop ϕ {x₀}, ∀ s, s ∈ P ↔ w s = 0

/-- A nonempty carried species set is a critical siphon. This is
`isCriticalSiphon_zeroSet_of_mem_omegaLimit` read through the carrier: the witness `w` is an ω-limit
point whose zero set is exactly `P`. -/
theorem isCriticalSiphon_of_siphonCarried (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, (y : Concentration S).Nonnegative)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx0pos : x₀.Positive) {P : Finset S} (hPne : P.Nonempty) (hP : N.SiphonCarried ϕ x₀ P) :
    N.IsCriticalSiphon P := by
  obtain ⟨w, hw, hwP⟩ := hP
  exact N.isCriticalSiphon_zeroSet_of_mem_omegaLimit κ hϕγ hK hmaps hωnn hgenω hωaff hx0pos hw
    hwP hPne

/-- **Butler–McGehee escape supplies a carried critical siphon.** If the ω-limit set is not contained
in the isolated invariant set `M` (the maximal invariant subset of its isolating neighborhood
`Nbhd`), `exists_escape_forwardLimit_criticalSiphonFace` produces an escaping ω-point `q` whose
forward limit `ω{q}` is a subset of `ω{x₀}` on which every nonempty zero set is a critical siphon. If
that forward limit holds a boundary point `w` — a coordinate `w s₁ = 0` — its zero set is a nonempty
critical siphon carried by the trajectory through `x₀`. This is the step that, in Anderson's proof,
manufactures the smaller-face carrier the descent consumes. -/
theorem siphonCarried_of_escape (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hKcl : IsClosed K)
    (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, (y : Concentration S).Nonnegative)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx0pos : x₀.Positive) {M Nbhd : Set (Concentration S)}
    (hMisol : maximalInvariantSubset ϕ Nbhd = M) (hMN : M ⊆ Nbhd)
    (hΩM : ¬ omegaLimit atTop ϕ {x₀} ⊆ M)
    -- a boundary point of the escaping forward limit, located by its escaping ω-point
    (hbdry : ∀ q ∈ omegaLimit atTop ϕ {x₀}, q ∉ M →
      ∃ w ∈ omegaLimit atTop ϕ {q}, ∃ s, w s = 0) :
    ∃ P : Finset S, P.Nonempty ∧ N.IsCriticalSiphon P ∧ N.SiphonCarried ϕ x₀ P := by
  classical
  obtain ⟨q, hq, hqM, _hne, _hcpt, _hinv, hsubq, hface⟩ :=
    N.exists_escape_forwardLimit_criticalSiphonFace κ hϕγ hK hKcl hmaps hωnn hgenω hωaff hx0pos
      hMisol hMN hΩM
  obtain ⟨w, hwq, s₁, hs₁⟩ := hbdry q hq hqM
  set P : Finset S := Finset.univ.filter (fun s => w s = 0) with hPdef
  have hwP : ∀ s, s ∈ P ↔ w s = 0 := fun s => by
    rw [hPdef, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ s, h⟩⟩
  have hPne : P.Nonempty := ⟨s₁, (hwP s₁).mpr hs₁⟩
  exact ⟨P, hPne, hface w hwq P hwP hPne, w, hsubq hwq, hwP⟩

/-- **Anderson's comparable-growth descent (carried analytic step).** The sole hypothesis isolating
the genuinely-hard analytic content. It asserts that the trajectory cannot cycle among boundary
faces: every nonempty *carried critical siphon* `P` either coexists with a strictly positive ω-limit
point, or produces a *strictly smaller* carried critical siphon `Q` (with `Q.card < P.card`). In the
analytic proof the strict shrinking is forced by comparing the growth of the relative-entropy
Lyapunov family across an escape from the face `SiphonFace P`; that estimate is the content not
formalised here. The descent walks the strictly decreasing cardinalities down to the empty siphon,
i.e. to the strictly positive ω-limit point. -/
structure ComparableGrowthDescent (N : Network S) (ϕ : Flow ℝ≥0 (Concentration S))
    (x₀ : Concentration S) : Prop where
  /-- Every nonempty carried critical siphon `P` either coexists with a positive ω-limit point or
  yields a carried critical siphon of strictly smaller cardinality. -/
  descend : ∀ P : Finset S, P.Nonempty → N.IsCriticalSiphon P → N.SiphonCarried ϕ x₀ P →
    (∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive) ∨
      (∃ Q : Finset S, Q.Nonempty ∧ N.IsCriticalSiphon Q ∧ Q.card < P.card ∧
        N.SiphonCarried ϕ x₀ Q)

/-- **The descent reaches a positive ω-limit point from any carried critical siphon.** Strong
induction on the siphon cardinality: a carried critical siphon either already exposes a positive
ω-limit point or, by `ComparableGrowthDescent`, hands off a strictly smaller carried critical siphon,
and a chain of strictly decreasing cardinalities terminates. -/
theorem omegaLimit_positive_of_descend (N : Network S)
    {ϕ : Flow ℝ≥0 (Concentration S)} {x₀ : Concentration S}
    (hdesc : N.ComparableGrowthDescent ϕ x₀)
    {P₀ : Finset S} (hP₀ne : P₀.Nonempty) (hP₀crit : N.IsCriticalSiphon P₀)
    (hP₀carr : N.SiphonCarried ϕ x₀ P₀) :
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive := by
  -- strong induction on the cardinality of the carried critical siphon
  suffices h : ∀ n : ℕ, ∀ P : Finset S, P.card = n → P.Nonempty → N.IsCriticalSiphon P →
      N.SiphonCarried ϕ x₀ P → ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive by
    exact h P₀.card P₀ rfl hP₀ne hP₀crit hP₀carr
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P hPcard hPne hPcrit hPcarr
    rcases hdesc.descend P hPne hPcrit hPcarr with hpos | ⟨Q, hQne, hQcrit, hQlt, hQcarr⟩
    · exact hpos
    · exact ih Q.card (hPcard ▸ hQlt) Q rfl hQne hQcrit hQcarr

/-- **A boundary ω-limit point launches the descent.** If some ω-limit point `w` lies on the
boundary — a coordinate `w s₁ = 0` — its zero set is a nonempty critical siphon carried by the
trajectory, so the comparable-growth descent delivers a strictly positive ω-limit point. -/
theorem omegaLimit_positive_of_boundary_point (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, (y : Concentration S).Nonnegative)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx0pos : x₀.Positive) (hdesc : N.ComparableGrowthDescent ϕ x₀)
    {w : Concentration S} (hw : w ∈ omegaLimit atTop ϕ {x₀}) {s₁ : S} (hs₁ : w s₁ = 0) :
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive := by
  classical
  -- the zero set of the boundary ω-point is a nonempty carried critical siphon
  set P : Finset S := Finset.univ.filter (fun s => w s = 0) with hPdef
  have hP : ∀ s, s ∈ P ↔ w s = 0 := fun s => by
    rw [hPdef, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ s, h⟩⟩
  have hPne : P.Nonempty := ⟨s₁, (hP s₁).mpr hs₁⟩
  have hcarr : N.SiphonCarried ϕ x₀ P := ⟨w, hw, hP⟩
  have hcrit : N.IsCriticalSiphon P :=
    N.isCriticalSiphon_of_siphonCarried κ hϕγ hK hmaps hωnn hgenω hωaff hx0pos hPne hcarr
  exact N.omegaLimit_positive_of_descend hdesc hPne hcrit hcarr

/-- **The comparable-growth descent produces a positive ω-limit point.** Either every ω-limit point
is already strictly positive — and the ω-limit set is nonempty for a trajectory absorbed by the
compact closed region `K` — or some ω-limit point sits on the boundary and
`omegaLimit_positive_of_boundary_point` runs the descent to a positive ω-limit point. Either way an
interior ω-limit point exists. -/
theorem omegaLimit_positive_of_comparableGrowthDescent (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hKcl : IsClosed K)
    (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, (y : Concentration S).Nonnegative)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx0pos : x₀.Positive) (hdesc : N.ComparableGrowthDescent ϕ x₀) :
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive := by
  classical
  by_cases hall : ∀ w ∈ omegaLimit atTop ϕ {x₀}, w.Positive
  · -- the ω-limit set of a precompact orbit is nonempty
    have hsubK : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ K := by
      rintro z ⟨t, -, x, hx, rfl⟩; rw [Set.mem_singleton_iff] at hx; subst hx; exact hmaps t
    have habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K :=
      ⟨Set.univ, univ_mem, hKcl.closure_subset_iff.mpr hsubK⟩
    obtain ⟨w, hw⟩ :=
      nonempty_omegaLimit_of_isCompact_absorbing atTop ϕ {x₀} hK habs (Set.singleton_nonempty x₀)
    exact ⟨w, hw, hall w hw⟩
  · -- otherwise some ω-point is on the boundary; launch the descent
    obtain ⟨w, hw, hwnp⟩ : ∃ w ∈ omegaLimit atTop ϕ {x₀}, ¬ w.Positive := by
      by_contra h
      exact hall fun w hw => not_not.mp fun hwp => h ⟨w, hw, hwp⟩
    have hwnn : w.Nonnegative := hωnn w hw
    obtain ⟨s₁, hs₁⟩ : ∃ s, ¬ 0 < w s := not_forall.mp hwnp
    have hs₁0 : w s₁ = 0 := le_antisymm (not_lt.mp hs₁) (hwnn s₁)
    exact N.omegaLimit_positive_of_boundary_point κ hϕγ hK hmaps hωnn hgenω hωaff hx0pos hdesc
      hw hs₁0

/-- **Siphon-dimension descent ⇒ the global attractor conclusion.** Combining the comparable-growth
descent with `omegaLimit_eq_singleton_of_mem_positive`: for a weakly reversible network with a
positive complex-balanced reference `x*` and a positive start `x₀` in its class, the standard LaSalle
data of the mass-action semiflow together with the carried descent hypothesis force the ω-limit set
to be the single equilibrium `{x*}`. The descent supplies the strictly positive ω-limit point; the
relative-entropy Lyapunov stack collapses the whole ω-limit set to `{x*}`.

This is the shape of Anderson's single-linkage-class theorem with the comparable-growth Lyapunov
estimate isolated as `ComparableGrowthDescent`. -/
theorem omegaLimit_eq_singleton_of_comparableGrowthDescent
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0compat : N.StoichCompatible x₀ xstar)
    (hγ0 : ∀ x, γ x 0 = x) (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hKcl : IsClosed K)
    (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    {c : ℝ} (hωc : ∀ z ∈ omegaLimit atTop ϕ {x₀}, relEntropy xstar z = c)
    (hposorbit : ∀ p ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive p →
      ∀ t : ℝ, 0 ≤ t → Concentration.Positive (γ p t))
    (hx0pos : x₀.Positive) (hdesc : N.ComparableGrowthDescent ϕ x₀) :
    omegaLimit atTop ϕ {x₀} = {xstar} :=
  N.omegaLimit_eq_singleton_of_mem_positive hwr κ hxs hcb hx0compat hγ0 hϕγ hgenω hωnn hωaff hωc
    hposorbit
    (N.omegaLimit_positive_of_comparableGrowthDescent κ hϕγ hK hKcl hmaps hωnn hgenω hωaff hx0pos
      hdesc)

end Network

end CRNT

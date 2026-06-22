import CRNT.Kinetics.Generalized
import CRNT.Theorems.DeficiencyZero.BirchExistence

/-!
# Toric steady states and the Müller sign-condition reduction

For a network with generalized mass-action kinetics whose steady-state equations are
*binomial*, the positive steady states are **toric**: relative to a positive reference
`x*`, a positive `x` is a steady state in the stoichiometric class `c + S` exactly when
its log-ratio `log(x/x*)` is orthogonal to the kinetic-order subspace `T`. Equivalently,
the steady states parametrize monomially as `xᵢ = x*ᵢ · exp(ŵᵢ)` with `ŵ ∈ orthSum T`.
This is the log-linear / binomial form taken here as the *definition* of the steady-state
set; deriving binomiality from the network's reaction structure (the toric-ideal step)
needs binomial-ideal machinery beyond this development's scope.

The headline result is Müller et al.'s reduction of **multistationarity to a sign
condition** on the two subspaces. The set of toric steady states in a fixed positive class
is a subsingleton — at most one steady state, i.e. multistationarity is ruled out —
precisely when the stoichiometric subspace `S` and the kinetic orthogonal complement
`orthSum T` are *sign-compatible*: no nonzero `u ∈ S` shares its coordinatewise sign
pattern with any `v ∈ orthSum T`. The converse (constructing two distinct steady states
when sign-compatibility fails) is the degree-theoretic half and lies beyond this scope.

* `ToricSteadyStates S T x* c` — the positive `x` with `x − c ∈ S` and
  `log(x/x*) ∈ orthSum T`: the toric/binomial steady-state set.
* `toric_nonempty_self` — in the single-subspace case `T = S`, the toric set is nonempty
  in every positive class, the concrete monomial parametrization via `birch_existence`.
* `SignIncompatible S T` and `signCompatible_iff_not_signIncompatible` — the sign
  condition `SignCompatible` is exactly the absence of a nonzero shared sign vector,
  i.e. `σ(S) ∩ σ(T) = {0}`.
* `toric_subsingleton_of_signCompatible` — the Müller reduction: sign compatibility of
  `S` against `orthSum T` forces uniqueness of toric steady states in each positive class.
* `toric_subsingleton_self` / `toric_unique_self` — the mass-action corollary at `T = S`
  (uniqueness for all `κ`, recovering classical complex-balanced monostationarity via
  `signCompatible_self`).

This module is **stable** and `sorry`-free. Depends on: `CRNT.Kinetics.Generalized`,
`CRNT.Theorems.DeficiencyZero.BirchExistence`.
-/

namespace CRNT

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The **toric (binomial) steady-state set** relative to a positive reference `x*` and a
positive class representative `c`: the positive points `x` that are stoichiometrically
compatible (`x − c ∈ S`) and whose log-ratio `log(x/x*)` is orthogonal to the
kinetic-order subspace `T`. Under generalized mass-action kinetics with binomial
steady-state equations these are exactly the positive steady states in the class `c + S`,
parametrized monomially as `xᵢ = x*ᵢ · exp(ŵᵢ)` with `ŵ ∈ orthSum T`. -/
def ToricSteadyStates (S T : Submodule ℝ (ι → ℝ)) (xstar c : ι → ℝ) : Set (ι → ℝ) :=
  {x | (∀ i, 0 < x i) ∧ x - c ∈ S ∧
    (fun i => Real.log (x i) - Real.log (xstar i)) ∈ orthSum T}

/-- Membership in the toric steady-state set, unfolded. -/
theorem mem_toricSteadyStates {S T : Submodule ℝ (ι → ℝ)} {xstar c x : ι → ℝ} :
    x ∈ ToricSteadyStates S T xstar c ↔
      (∀ i, 0 < x i) ∧ x - c ∈ S ∧
        (fun i => Real.log (x i) - Real.log (xstar i)) ∈ orthSum T :=
  Iff.rfl

/-- **Monomial parametrization / nonemptiness in the single-subspace case.** When the
kinetic-order subspace coincides with the stoichiometric subspace (`T = S`), every
positive stoichiometric class contains a toric steady state, namely the complex-balanced
equilibrium `x = x* ⊙ exp(ŵ)` produced by Birch existence. This is the concrete
realization of the monomial parametrization in the classical mass-action case. -/
theorem toric_nonempty_self (S : Submodule ℝ (ι → ℝ)) {xstar c : ι → ℝ}
    (hxs : ∀ i, 0 < xstar i) (hc : ∀ i, 0 < c i) :
    (ToricSteadyStates S S xstar c).Nonempty := by
  obtain ⟨x, hxpos, hxc, hxorth⟩ := birch_existence S hxs hc
  exact ⟨x, hxpos, hxc, mem_orthSum.mpr hxorth⟩

/-- The **failure** of the Müller sign condition: there is a nonzero `u ∈ S` that shares
its coordinatewise sign pattern with some `v ∈ T`. This is exactly a nonzero common sign
vector of the two subspaces, `σ(S) ∩ σ(T) ≠ {0}`. -/
def SignIncompatible (S T : Submodule ℝ (ι → ℝ)) : Prop :=
  ∃ u ∈ S, ∃ v ∈ T, SameSign u v ∧ u ≠ 0

/-- The sign condition `SignCompatible S T` is precisely the absence of a nonzero shared
sign vector: `σ(S) ∩ σ(T) = {0}`. This is the constructive restatement of the
Müller–Regensburger condition as the negation of `SignIncompatible`. -/
theorem signCompatible_iff_not_signIncompatible (S T : Submodule ℝ (ι → ℝ)) :
    SignCompatible S T ↔ ¬ SignIncompatible S T := by
  constructor
  · intro hsc ⟨u, hu, v, hv, hsame, hune⟩
    exact hune (hsc u hu v hv hsame)
  · intro hni u hu v hv hsame
    by_contra hune
    exact hni ⟨u, hu, v, hv, hsame, hune⟩

/-- **Müller sign-condition reduction (uniqueness half).** If the stoichiometric subspace
`S` is sign-compatible with the kinetic orthogonal complement `orthSum T`, then the toric
steady-state set in any positive class is a subsingleton: at most one positive steady
state, ruling out multistationarity. Two members lie in the same `S`-coset, so their
difference is in `S`; their log-ratio difference is in `orthSum T`; and the sign condition
through `gen_birch_uniqueness` forces them equal. -/
theorem toric_subsingleton_of_signCompatible {S T : Submodule ℝ (ι → ℝ)}
    (hsc : SignCompatible S (orthSum T)) {xstar c : ι → ℝ}
    {x y : ι → ℝ} (hx : x ∈ ToricSteadyStates S T xstar c)
    (hy : y ∈ ToricSteadyStates S T xstar c) : x = y := by
  obtain ⟨hxpos, hxc, hxorth⟩ := hx
  obtain ⟨hypos, hyc, hyorth⟩ := hy
  -- `x − y ∈ S`, from the two cosets.
  have hxy : x - y ∈ S := by
    rw [show x - y = (x - c) - (y - c) from (sub_sub_sub_cancel_right x y c).symm]
    exact S.sub_mem hxc hyc
  -- `log(x/y) ∈ orthSum T`, by subtracting the two log-ratios in the submodule.
  have horth : (fun i => Real.log (x i) - Real.log (y i)) ∈ orthSum T := by
    have hsub := (orthSum T).sub_mem hxorth hyorth
    have heq : (fun i => Real.log (x i) - Real.log (xstar i))
        - (fun i => Real.log (y i) - Real.log (xstar i))
        = fun i => Real.log (x i) - Real.log (y i) := by
      funext i; simp only [Pi.sub_apply]; ring
    rwa [heq] at hsub
  exact gen_birch_uniqueness S T hsc hxpos hypos hxy horth

/-- **Mass-action corollary (subsingleton).** In the classical single-subspace case
`T = S`, the sign condition holds unconditionally (`signCompatible_self`), so the toric
steady-state set is a subsingleton in every positive class, for every kinetics — the
formal statement of complex-balanced monostationarity. -/
theorem toric_subsingleton_self (S : Submodule ℝ (ι → ℝ)) {xstar c : ι → ℝ}
    {x y : ι → ℝ} (hx : x ∈ ToricSteadyStates S S xstar c)
    (hy : y ∈ ToricSteadyStates S S xstar c) : x = y :=
  toric_subsingleton_of_signCompatible (signCompatible_self S) hx hy

/-- **Mass-action corollary (existence and uniqueness).** Combining
`toric_nonempty_self` and `toric_subsingleton_self`: in the classical case `T = S`, every
positive stoichiometric class contains a unique toric steady state. -/
theorem toric_unique_self (S : Submodule ℝ (ι → ℝ)) {xstar c : ι → ℝ}
    (hxs : ∀ i, 0 < xstar i) (hc : ∀ i, 0 < c i) :
    ∃ x, x ∈ ToricSteadyStates S S xstar c ∧
      ∀ y ∈ ToricSteadyStates S S xstar c, y = x := by
  obtain ⟨x, hx⟩ := toric_nonempty_self S hxs hc
  exact ⟨x, hx, fun y hy => toric_subsingleton_self S hy hx⟩

/-- **The converse is the degree-theoretic half.** When sign-compatibility fails, Müller
et al. construct two distinct toric steady states in some positive class via a
topological-degree argument. That existence direction is not available here (no Brouwer /
topological degree), so only the uniqueness direction of the biconditional is established;
this `example` records the shape of the reduction that is proved. -/
example {S T : Submodule ℝ (ι → ℝ)} (hsc : SignCompatible S (orthSum T))
    (xstar c : ι → ℝ) :
    ∀ x ∈ ToricSteadyStates S T xstar c, ∀ y ∈ ToricSteadyStates S T xstar c, x = y :=
  fun _ hx _ hy => toric_subsingleton_of_signCompatible hsc hx hy

end CRNT

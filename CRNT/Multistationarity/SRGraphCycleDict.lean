import CRNT.Multistationarity.SRGraphCriterion

/-!
# Length/parity half of the permutation-cycle ↔ SR-graph-cycle dictionary

The species–reaction-graph criterion of Craciun and Feinberg ("Multiple equilibria in
complex chemical reaction networks: I. The injectivity property") reads the cycles of a
permutation of the species set as cycles of the species–reaction graph. A permutation
cycle on species visits species `s, σ s, σ² s, …`; the dictionary expands each
species-to-species hop `t ↦ σ t` into a two-edge detour `t → r → σ t` through a
reaction `r` in which both species occur. A perm-cycle of length `k` thus becomes an
SR-graph closed walk of length `2k`.

This module records the **length/parity** half of that dictionary: the construction of
the SR-graph closed walk from the cycle data together with its exact length, and the
matching parity fact for arbitrary SR-graph cycles.

* `srStep` — one species→reaction→species segment of an SR-graph walk, length two.
* `srOrbitWalk` — the `k`-fold alternating walk following the orbit of a permutation
  `σ` from a species `s`, choosing a reaction `ρ t` at each species `t`; it runs from
  `s` to `σ^[k] s`.
* `srOrbitWalk_length` — that walk has length `2k`.
* `srCycleWalk` — the closed walk obtained when the orbit closes (`σ^[k] s = s`).
* `srCycleWalk_length_eq_two_mul` — the closed walk has length `2k`: a perm-cycle of
  length `k` yields an SR-graph cycle of length `2k`.
* `srCycle_length_eq_two_mul` — conversely, every SR-graph cycle has length `2k` for
  some `k` (the bipartite alternation, `srGraph_even_length_of_isCycle`).

The dictionary's **sign** half — matching a perm-cycle's sign to the signed-walk sign
`walkSign` — is not provided here; it requires the labeled/signed SR-graph and the
product structure of a factored Jacobian, which lie outside this module.

This module is **stable** and `sorry`-free. Depends on:
`CRNT.Multistationarity.SRGraphCriterion`.
-/

namespace CRNT

namespace Network

open SimpleGraph Equiv

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **One species→reaction→species segment of an SR-graph walk.** When a reaction `r`
contains both `s` and `s'`, the two incidence edges `s—r` and `r—s'` form a length-two
walk from the species vertex `s` to the species vertex `s'`. -/
def srStep (N : Network S) (s s' : S) (r : N.R)
    (h1 : N.OccursIn s r) (h2 : N.OccursIn s' r) :
    N.srGraph.Walk (Sum.inl s) (Sum.inl s') :=
  Walk.cons (show N.srGraph.Adj (Sum.inl s) (Sum.inr r) from h1)
    (Walk.cons (show N.srGraph.Adj (Sum.inr r) (Sum.inl s') from h2) Walk.nil)

@[simp] theorem srStep_length (N : Network S) (s s' : S) (r : N.R)
    (h1 : N.OccursIn s r) (h2 : N.OccursIn s' r) :
    (N.srStep s s' r h1 h2).length = 2 := rfl

/-- **The `k`-fold orbit walk.** Following the orbit of a permutation `σ` from a species
`s`, with each species-to-species hop `t ↦ σ t` expanded through the reaction `ρ t`
(which contains both `t` and `σ t`, witnessed by `hocc`), gives an SR-graph walk from
`s` to `σ^[k] s`. -/
def srOrbitWalk (N : Network S) (σ : Perm S) (ρ : S → N.R)
    (hocc : ∀ t : S, N.OccursIn t (ρ t) ∧ N.OccursIn (σ t) (ρ t)) (s : S) :
    ∀ k : ℕ, N.srGraph.Walk (Sum.inl s) (Sum.inl (σ^[k] s))
  | 0 => Walk.nil
  | (k + 1) => by
      have h := hocc (σ^[k] s)
      have step : N.srGraph.Walk (Sum.inl (σ^[k] s)) (Sum.inl (σ (σ^[k] s))) :=
        N.srStep (σ^[k] s) (σ (σ^[k] s)) (ρ (σ^[k] s)) h.1 h.2
      have w := N.srOrbitWalk σ ρ hocc s k
      have e : σ (σ^[k] s) = σ^[k + 1] s := by rw [Function.iterate_succ_apply']
      exact w.append (step.copy rfl (by rw [e]))

/-- **The orbit walk has length `2k`:** each of the `k` species hops contributes a
length-two segment. -/
theorem srOrbitWalk_length (N : Network S) (σ : Perm S) (ρ : S → N.R)
    (hocc : ∀ t : S, N.OccursIn t (ρ t) ∧ N.OccursIn (σ t) (ρ t)) (s : S) :
    ∀ k : ℕ, (N.srOrbitWalk σ ρ hocc s k).length = 2 * k
  | 0 => rfl
  | (k + 1) => by
      rw [srOrbitWalk, Walk.length_append, Walk.length_copy,
        srOrbitWalk_length N σ ρ hocc s k]
      have hstep : (N.srStep (σ^[k] s) (σ (σ^[k] s)) (ρ (σ^[k] s))
          (hocc (σ^[k] s)).1 (hocc (σ^[k] s)).2).length = 2 := rfl
      rw [hstep]
      omega

/-- **The closed orbit walk.** When the orbit of `σ` from `s` closes after `k` steps
(`σ^[k] s = s`), the orbit walk is a closed walk at the species vertex `s`. -/
def srCycleWalk (N : Network S) (σ : Perm S) (ρ : S → N.R)
    (hocc : ∀ t : S, N.OccursIn t (ρ t) ∧ N.OccursIn (σ t) (ρ t)) (s : S) (k : ℕ)
    (hk : σ^[k] s = s) :
    N.srGraph.Walk (Sum.inl s) (Sum.inl s) :=
  (N.srOrbitWalk σ ρ hocc s k).copy rfl (by rw [hk])

/-- **A perm-cycle of length `k` yields an SR-graph closed walk of length `2k`.** This
is the constructive (perm-cycle → SR-cycle) length half of the dictionary. -/
theorem srCycleWalk_length_eq_two_mul (N : Network S) (σ : Perm S) (ρ : S → N.R)
    (hocc : ∀ t : S, N.OccursIn t (ρ t) ∧ N.OccursIn (σ t) (ρ t)) (s : S) (k : ℕ)
    (hk : σ^[k] s = s) :
    (N.srCycleWalk σ ρ hocc s k hk).length = 2 * k := by
  rw [srCycleWalk, Walk.length_copy, srOrbitWalk_length]

/-- **Every SR-graph cycle has length `2k` for some `k`:** the converse parity half of
the dictionary. This repackages the bipartite-alternation evenness
(`srGraph_even_length_of_isCycle`) as an explicit factor of two. -/
theorem srCycle_length_eq_two_mul (N : Network S) {u : N.SRVertex S}
    {w : N.srGraph.Walk u u} (hcyc : w.IsCycle) :
    ∃ k : ℕ, w.length = 2 * k := by
  obtain ⟨k, hk⟩ := srGraph_even_length_of_isCycle N hcyc
  exact ⟨k, by omega⟩

end Network

end CRNT

import CRNT.Graph.WeakReversibility

/-!
# A decidable companion for directed reachability

`Reaches` is the reflexive–transitive closure of the one-step relation `DirectlyReacts`
over `Complex S`, an infinite vertex type, so it is not decidable as stated. `ReachesWithin
k` is the *bounded* reachability relation — reachable by a directed path of at most `k`
reactions — phrased so that each step quantifies over the finite reaction index type. It is
therefore decidable, giving a `decide`-checkable companion related to `Reaches` by:

* `reaches_of_reachesWithin` (soundness): a bounded path is a path;
* `reaches_iff_exists_reachesWithin` (completeness): every path has some finite length.

Bounded weak reversibility `WeaklyReversibleWithin k` is then decidable and sound for
`WeaklyReversible`, so a concrete network discharges weak reversibility by exhibiting a
depth and running `decide` rather than building path witnesses by hand.

This module is **stable**. Depends on: `CRNT.Graph.WeakReversibility`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- `ReachesWithin N k c d`: `d` is reachable from `c` by a directed path of at most `k`
reactions. Each step ranges over the finite reaction index type, so the relation is
decidable. -/
def ReachesWithin (N : Network S) : ℕ → Complex S → Complex S → Prop
  | 0,     c, d => c = d
  | k + 1, c, d => c = d ∨ ∃ r : N.R, (N.reaction r).source = c ∧
      N.ReachesWithin k (N.reaction r).target d

theorem reachesWithin_zero (N : Network S) (c d : Complex S) :
    N.ReachesWithin 0 c d ↔ c = d := Iff.rfl

theorem reachesWithin_succ (N : Network S) (k : ℕ) (c d : Complex S) :
    N.ReachesWithin (k + 1) c d ↔
      c = d ∨ ∃ r : N.R, (N.reaction r).source = c ∧ N.ReachesWithin k (N.reaction r).target d :=
  Iff.rfl

/-- Bounded reachability is decidable: the base case is decidable equality and each step is
a finite existential over the reaction index type. -/
instance decidableReachesWithin (N : Network S) :
    ∀ (k : ℕ) (c d : Complex S), Decidable (N.ReachesWithin k c d)
  | 0, c, d => decEq c d
  | k + 1, c, d =>
      letI : ∀ r : N.R, Decidable (N.ReachesWithin k (N.reaction r).target d) :=
        fun r => decidableReachesWithin N k (N.reaction r).target d
      inferInstanceAs (Decidable (c = d ∨ ∃ r : N.R, (N.reaction r).source = c ∧
        N.ReachesWithin k (N.reaction r).target d))

/-- **Soundness.** A bounded path witnesses (unbounded) reachability. -/
theorem reaches_of_reachesWithin (N : Network S) :
    ∀ {k : ℕ} {c d : Complex S}, N.ReachesWithin k c d → N.Reaches c d
  | 0, c, d, h => h ▸ Reaches.refl N c
  | k + 1, c, d, h => by
      rcases h with rfl | ⟨r, hsrc, hrest⟩
      · exact Reaches.refl N c
      · exact (Reaches.single ⟨r, hsrc, rfl⟩).trans
          (reaches_of_reachesWithin N hrest)

/-- **Completeness.** Reachability holds exactly when some bounded path exists. -/
theorem reaches_iff_exists_reachesWithin (N : Network S) (c d : Complex S) :
    N.Reaches c d ↔ ∃ k : ℕ, N.ReachesWithin k c d := by
  constructor
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, rfl⟩
    | head hstep _ ih =>
      obtain ⟨r, hsrc, htgt⟩ := hstep
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, Or.inr ⟨r, hsrc, htgt ▸ hk⟩⟩
  · rintro ⟨k, hk⟩
    exact reaches_of_reachesWithin N hk

/-- `WeaklyReversibleWithin N k`: every reaction's source is reachable from its target by a
directed path of at most `k` reactions. Decidable, and sufficient for weak reversibility. -/
def WeaklyReversibleWithin (N : Network S) (k : ℕ) : Prop :=
  ∀ r : N.R, N.ReachesWithin k (N.reaction r).target (N.reaction r).source

instance (N : Network S) (k : ℕ) : Decidable (N.WeaklyReversibleWithin k) :=
  Fintype.decidableForallFintype

/-- **A network with a uniform return-path bound is weakly reversible.** This is the
`decide`-friendly entry point: exhibit a depth `k` and check `WeaklyReversibleWithin k`. -/
theorem weaklyReversible_of_within (N : Network S) {k : ℕ}
    (h : N.WeaklyReversibleWithin k) : N.WeaklyReversible :=
  fun r => reaches_of_reachesWithin N (h r)

end Network

end CRNT

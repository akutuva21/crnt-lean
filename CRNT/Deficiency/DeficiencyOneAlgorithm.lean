import CRNT.Deficiency.Shelf
import CRNT.Deficiency.DeficiencyOne
import CRNT.Multistationarity.Capacity

/-!
# The Deficiency One Algorithm: capacity ⟺ signature

The Deficiency One Algorithm decides the capacity for multiple steady states of a *regular*
deficiency-one mass-action network by a parameter-independent linear feasibility test: it searches
over the (one or two) confluence-vector directions and the shelf partitions, and reports capacity
exactly when some generated system is a **signature** — has a nonzero solution `μ` sign-compatible
with the stoichiometric subspace (Ji, *Uniqueness of equilibria for complex chemical reaction
networks*, Ohio State University, 2011, §1.6; Feinberg, *Arch. Rational Mech. Anal.* **132** (1995)).

* `DOAAffirmsCapacity` — the search succeeds: some nonzero confluence vector `g` and shelf partition
  `sp` admit a nonzero, sign-compatible `μ` meeting the placement-rule constraints `sp.imposes g μ`.
  (For a regular deficiency-one network the confluence vectors are collinear, so `∃` over nonzero
  `g` ranges over the at-most-two confluence directions.)
* `DeficiencyOneAlgorithmStatement` — the headline correctness proposition: for a regular
  deficiency-one network, `HasMultistationarityCapacity ↔ DOAAffirmsCapacity`. This is **stated as
  the target proposition, not proved** — it is Feinberg's deficiency-one theorem, a substantial
  analytic result outside the scope of this module. It is written as a `def` (a named proposition),
  never asserted as a theorem.
* `stoichSubspace_ne_bot_of_doaAffirmsCapacity` — a genuine consequence of the verdict, proving the
  apparatus is non-vacuous: affirming capacity exhibits a nonzero stoichiometric vector.

Depends on: `CRNT.Deficiency.Shelf`,
`CRNT.Deficiency.DeficiencyOne`, `CRNT.Multistationarity.Capacity`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The Deficiency One Algorithm affirms capacity.** Some nonzero confluence vector `g` and shelf
partition `sp` yield a signature: a nonzero `μ`, sign-compatible with the stoichiometric subspace,
satisfying the placement-rule constraints. -/
def DOAAffirmsCapacity (N : Network S) : Prop :=
  ∃ g : N.ComplexIdx → ℝ, N.IsConfluenceVector g ∧ g ≠ 0 ∧
    ∃ (sp : N.ShelfPartition) (μ : S → ℝ),
      μ ≠ 0 ∧ N.SignCompatibleWithStoich μ ∧ sp.imposes g μ

/-- **The Deficiency One Algorithm correctness statement.** For a regular deficiency-one network,
the capacity for multiple positive steady states is equivalent to the existence of a signature.
This is Feinberg's theorem (1995); it is recorded here as the target proposition and is *not*
proved — neither direction is established. -/
def DeficiencyOneAlgorithmStatement (N : Network S) : Prop :=
  N.RegularNetwork → N.DeficiencyOne →
    (N.HasMultistationarityCapacity ↔ N.DOAAffirmsCapacity)

/-- **Affirming capacity exhibits a nonzero stoichiometric vector**, so the signature apparatus is
non-vacuous: the sign-compatible `μ ≠ 0` is matched by a nonzero element of the stoichiometric
subspace, whence that subspace is nontrivial. -/
theorem stoichSubspace_ne_bot_of_doaAffirmsCapacity (N : Network S)
    (h : N.DOAAffirmsCapacity) : N.stoichSubspace ≠ ⊥ := by
  obtain ⟨g, -, -, sp, μ, hμ0, ⟨w, hwmem, hsame⟩, -⟩ := h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hμ0
  simp only [Pi.zero_apply] at hi
  have hwi : w i ≠ 0 := by
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · exact ne_of_lt ((hsame i).2.mpr hlt)
    · exact ne_of_gt ((hsame i).1.mpr hgt)
  have hw0 : w ≠ 0 := by
    intro hw; rw [hw] at hwi; exact hwi rfl
  exact (Submodule.ne_bot_iff _).mpr ⟨w, hwmem, hw0⟩

end Network

end CRNT

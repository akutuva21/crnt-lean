import CRNT.Deficiency.Shelf
import CRNT.Deficiency.Colinearity
import CRNT.Multistationarity.Capacity

/-!
# The Advanced Deficiency Algorithm: extended system and verdict (§1.7)

The Advanced Deficiency Algorithm generalizes the Deficiency One Algorithm to higher deficiency by
introducing, for each nonzero colinearity class `CCᵢ`, an extra real unknown `Mᵢ` alongside
`μ ∈ ℝ^𝒮`, and shelving the reactions *within* each colinearity class against its `Mᵢ` (Ji,
*Uniqueness of equilibria for complex chemical reaction networks*, Ohio State University, 2011,
§1.7). A reaction `y → y'` of class `CCᵢ` placed on the upper / middle / lower shelf contributes

```text
y · μ > Mᵢ ,    y · μ = Mᵢ ,    y · μ < Mᵢ
```

respectively, where `y` is the reactant complex.

* `ADAData` — the algorithm's discrete choice: the `Mᵢ` values (as a function on reactions that is
  constant on colinearity classes), and a per-reaction shelving;
* `ADAData.imposes` — the shelf-versus-`Mᵢ` constraints on `μ` it generates;
* `ADAAffirmsCapacity` — some `ADAData` admits a nonzero, sign-compatible `μ` meeting the
  constraints;
* `AdvancedDeficiencyAlgorithmStatement` — the correctness proposition for a regular network,
  `HasMultistationarityCapacity ↔ ADAAffirmsCapacity`, stated as a named target (Feinberg/Ji), *not*
  proved;
* `stoichSubspace_ne_bot_of_adaAffirmsCapacity` — non-vacuity: affirming capacity exhibits a nonzero
  stoichiometric vector.

**Faithfulness note.** This module captures the distinctive ADA ingredient — the per-class `Mᵢ`
variables and the shelf-versus-`Mᵢ` constraints. Two further constraint layers of §1.7 are *not*
imposed here and are flagged as the remaining ADA work: the within-class sign comparisons of
`y · μ` versus `y' · μ` driven by the chosen sign of `CCᵢ`, and the coplanar-set `Mᵢ`-orderings (for
a coplanar triplet `cₖwₖ = cᵢwᵢ + cⱼwⱼ`, one of `Mᵢ > Mₖ > Mⱼ`, all-equal, or `Mᵢ < Mₖ < Mⱼ`).
Omitting them only enlarges the set of `ADAData` considered.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Deficiency.Shelf`,
`CRNT.Deficiency.Colinearity`, `CRNT.Multistationarity.Capacity`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-- **The discrete data of an Advanced Deficiency Algorithm run.** The per-colinearity-class values
`Mᵢ`, carried as a function on reactions that is constant on colinearity classes, together with a
shelving of each reaction within its class. -/
structure ADAData (N : Network S) where
  /-- The value `Mᵢ` of the colinearity class of each reaction. -/
  M : N.R → ℝ
  /-- `M` is constant on colinearity classes: colinear reactions share an `Mᵢ`. -/
  M_colinear : ∀ r r' : N.R, N.ColinearReactions r r' → M r = M r'
  /-- The shelf of each reaction within its colinearity class. -/
  shelf : N.R → Shelf

/-- **The shelf-versus-`Mᵢ` constraints** a run imposes on `μ`: for each reaction `r` with reactant
complex `y`, the shelf of `r` orders `y · μ` against `Mᵢ` (upper ⟹ `>`, middle ⟹ `=`,
lower ⟹ `<`). -/
def ADAData.imposes (d : N.ADAData) (μ : S → ℝ) : Prop :=
  ∀ r : N.R,
    (d.shelf r = Shelf.upper → d.M r < complexPairing (N.reaction r).source μ) ∧
      (d.shelf r = Shelf.middle → complexPairing (N.reaction r).source μ = d.M r) ∧
      (d.shelf r = Shelf.lower → complexPairing (N.reaction r).source μ < d.M r)

/-- **The Advanced Deficiency Algorithm affirms capacity.** Some run admits a nonzero `μ`,
sign-compatible with the stoichiometric subspace, meeting the shelf-versus-`Mᵢ` constraints. -/
def ADAAffirmsCapacity (N : Network S) : Prop :=
  ∃ (d : N.ADAData) (μ : S → ℝ),
    μ ≠ 0 ∧ N.SignCompatibleWithStoich μ ∧ d.imposes μ

/-- **The Advanced Deficiency Algorithm correctness statement.** For a regular network, the capacity
for multiple steady states is equivalent to the advanced-deficiency verdict. Recorded as the target
proposition (Feinberg/Ji); it is *not* proved and is written as a `def`, incurring no `sorry`. -/
def AdvancedDeficiencyAlgorithmStatement (N : Network S) : Prop :=
  N.RegularNetwork → (N.HasMultistationarityCapacity ↔ N.ADAAffirmsCapacity)

/-- **Affirming capacity exhibits a nonzero stoichiometric vector**, so the advanced-deficiency
apparatus is non-vacuous. -/
theorem stoichSubspace_ne_bot_of_adaAffirmsCapacity (N : Network S)
    (h : N.ADAAffirmsCapacity) : N.stoichSubspace ≠ ⊥ := by
  obtain ⟨d, μ, hμ0, ⟨w, hwmem, hsame⟩, -⟩ := h
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

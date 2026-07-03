import CRNT.Compose.Interconnect
import CRNT.Kinetics.General

/-!
# Kinetics of an interconnection

A kinetics for each component network induces a kinetics for their interconnection: the
combined rate law dispatches on the sum index `N₁.R ⊕ N₂.R`, applying the first
component's rate to its reactions and the second component's rate to its. Each
admissibility hypothesis of `Kinetics` is checked reaction-by-reaction by case analysis
on the sum index, reducing to the corresponding hypothesis of the component kinetics.

The vector field of the combined kinetics is the sum of the component vector fields. Both
components act on the shared species pool, and the reaction-vector of a summand index is
the component's own reaction vector, so summing the induced field over `N₁.R ⊕ N₂.R`
splits as the sum over `N₁.R` plus the sum over `N₂.R`.

Depends on: `CRNT.Compose.Interconnect`,
`CRNT.Kinetics.General`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S] {N₁ N₂ : Network S}

namespace Kinetics

/-- **The kinetics of an interconnection** induced by a kinetics on each component. The
rate of a reaction `Sum.inl r` is `K₁.rate r` and the rate of `Sum.inr r` is `K₂.rate r`,
acting on the shared species concentration. The admissibility hypotheses are inherited
componentwise. -/
def sum (K₁ : Kinetics N₁) (K₂ : Kinetics N₂) : Kinetics (N₁.interconnect N₂) where
  rate := Sum.elim K₁.rate K₂.rate
  rate_nonneg := by
    rintro (r | r) x hx
    · exact K₁.rate_nonneg r hx
    · exact K₂.rate_nonneg r hx
  rate_vanishing := by
    rintro (r | r) x s hsrc hs
    · exact K₁.rate_vanishing r hsrc hs
    · exact K₂.rate_vanishing r hsrc hs
  rate_supportDep := by
    rintro (r | r) x y hxy
    · exact K₁.rate_supportDep r hxy
    · exact K₂.rate_supportDep r hxy
  rate_mono := by
    rintro (r | r)
    · exact K₁.rate_mono r
    · exact K₂.rate_mono r

@[simp] theorem sum_rate_inl (K₁ : Kinetics N₁) (K₂ : Kinetics N₂) (r : N₁.R) :
    (K₁.sum K₂).rate (Sum.inl r) = K₁.rate r := rfl

@[simp] theorem sum_rate_inr (K₁ : Kinetics N₁) (K₂ : Kinetics N₂) (r : N₂.R) :
    (K₁.sum K₂).rate (Sum.inr r) = K₂.rate r := rfl

/-- **The vector field of an interconnection is the sum of the component vector fields.**
Both components act on the shared species pool, so the induced field of the combined
kinetics at each species splits as the contribution of `N₁`'s reactions plus that of
`N₂`'s. -/
theorem sum_vectorField (K₁ : Kinetics N₁) (K₂ : Kinetics N₂) :
    (K₁.sum K₂).vectorField = fun x => K₁.vectorField x + K₂.vectorField x := by
  funext x s
  rw [vectorField_apply, Pi.add_apply, vectorField_apply, vectorField_apply]
  have hsplit :
      (∑ r : N₁.R ⊕ N₂.R,
          (K₁.sum K₂).rate r x * (N₁.interconnect N₂).reactionVector r s)
        = (∑ r : N₁.R, K₁.rate r x * N₁.reactionVector r s)
            + ∑ r : N₂.R, K₂.rate r x * N₂.reactionVector r s := by
    rw [← Fintype.sum_sumElim
      (fun r : N₁.R => K₁.rate r x * N₁.reactionVector r s)
      (fun r : N₂.R => K₂.rate r x * N₂.reactionVector r s)]
    refine Finset.sum_congr rfl ?_
    rintro (r | r) _ <;> rfl
  exact hsplit

end Kinetics

end Network

end CRNT

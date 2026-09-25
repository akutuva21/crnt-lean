import CRNT.Multistationarity.TrueSRSpeciesPath
import CRNT.Multistationarity.TrueSRGlueCPairs

/-!
# c-pairs of a species-to-species glue

`ssGlueCycle P Q h` is literally a `glueCycle`, obtained by moving `P`'s last edge onto `Q` so
that two species-to-species paths become two species-to-reaction ones.  So the bookkeeping of
`TrueSRGlueCPairs.lean` applies — but it applies in *shifted* coordinates, and the shift is the
whole point of this file.

For the species-to-reaction glue the identity reads `c(P') + seam + c(Q')`, with a genuine seam
term at the shared end reaction.  For the species-to-species glue that seam term is **not** an
extra degree of freedom: the shared end reaction of the reduced pair is the reaction of `P`'s last
edge, so the seam compares `P`'s two edges at its own last reaction — it *is* the c-pair
indicator of `P` there.  Every reaction vertex of `P ∪ Q` has both of its cycle edges drawn from a
single one of the two paths, because the two shared vertices are species and a c-pair lives only
at a reaction.  Hence

  `numCPairs (P ∪ Q) = c(P) + c(Q)`  with no seam term,

the opposite parity behaviour from `TrueSRParityLemma.three_glued_parity`.  The three pointwise
lemmas below are that statement position by position; `ssCPairAt_of_isCPair` packages them.

Consequence for the `hSR.2` route.  For a species-to-species chord `P` and the two species-arcs
`Q₁`, `Q₂` of a cycle `C`, the three pairwise glues satisfy, modulo 2,

  `numCPairs (P ∪ Q₁) + numCPairs (P ∪ Q₂) ≡ numCPairs (Q₁ ∪ Q₂) = numCPairs C`,

so `C.Even` forces `P ∪ Q₁` and `P ∪ Q₂` to have the *same* parity.  They are therefore both
even or both odd, and every pair among the three cycles meets in a species-to-species path
(`C ∩ (P ∪ Qₘ) = Qₘ`, and `(P ∪ Q₁) ∩ (P ∪ Q₂) = P`), so `SToRIntersection` is never available.
That is why a species-to-species chord is invisible to `TrueSRStrongCriterion`.
-/

namespace CRNT.Network.TrueSRSSPath

open CRNT.Network.TrueSRPath

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {i j : ℕ}
  (P : N.TrueSRSSPath (2 * j + 2)) (Q : N.TrueSRSSPath (2 * i + 2))
  (h : SSGluable P Q)

/-- The c-pair indicator at the `r`-th reaction of a species-to-species path. -/
def ssCPairAt {j : ℕ} (P : N.TrueSRSSPath (2 * j + 2)) (r : Fin (j + 1)) : Prop :=
  (P.edge ⟨2 * r.1, by have := r.isLt; omega⟩).endpoint
    = (P.edge ⟨2 * r.1 + 1, by have := r.isLt; omega⟩).endpoint

/-- Below the seam the condition is intrinsic to `P`. -/
theorem ssGlueCycle_isCPair_below (t : Fin (i + 1 + j + 1)) (ht : t.1 < j) :
    (ssGlueCycle P Q h).isCPair t ↔ ssCPairAt P ⟨t.1, by omega⟩ := by
  have htl := t.isLt
  rw [ssGlueCycle_eq,
    glueCycle_isCPair_below P.toPath (partner P Q h) (gluable_of_ssGluable P Q h) (by omega) t ht]
  rw [toPath_edge, toPath_edge]
  rfl

/-- At the seam the condition is still intrinsic to `P`: it compares `P`'s two edges at `P`'s own
last reaction, because the reduction to `glueCycle` moved `P`'s last edge onto `Q`. -/
theorem ssGlueCycle_isCPair_seam (hj : j < i + 1 + j + 1) :
    (ssGlueCycle P Q h).isCPair ⟨j, hj⟩ ↔ ssCPairAt P ⟨j, by omega⟩ := by
  rw [ssGlueCycle_eq,
    glueCycle_isCPair_seam (i := i + 1) (j := j) P.toPath (partner P Q h)
      (gluable_of_ssGluable P Q h) (by omega) (by omega)]
  rw [toPath_edge, partner,
    extend_edge_last Q P.lastEdge (extend_hes P Q h) (extend_hnew P Q h) (extend_hedge P Q h)
      ⟨2 * (i + 1), by omega⟩ (by show ¬ (2 * (i + 1) < 2 * i + 2); omega),
    lastEdge]
  constructor
  · intro hx
    exact hx.trans (congrArg _ (congrArg P.edge (Fin.ext (by show 2 * j + 2 - 1 = 2 * j + 1; omega))))
  · intro hx
    exact hx.trans (congrArg _ (congrArg P.edge (Fin.ext (by show 2 * j + 1 = 2 * j + 2 - 1; omega))))

/-- Above the seam the condition is intrinsic to `Q`, at the reversed index. -/
theorem ssGlueCycle_isCPair_above (t : Fin (i + 1 + j + 1)) (ht : j < t.1) :
    (ssGlueCycle P Q h).isCPair t ↔ ssCPairAt Q ⟨i + j + 1 - t.1, by have := t.isLt; omega⟩ := by
  have htl := t.isLt
  have hb2 : 2 * (i + 1) + 2 * j - 2 * t.1 < 2 * i + 2 := by omega
  have hb1 : 2 * (i + 1) + 2 * j - 2 * t.1 + 1 < 2 * i + 2 := by omega
  rw [ssGlueCycle_eq,
    glueCycle_isCPair_above P.toPath (partner P Q h) (gluable_of_ssGluable P Q h) (by omega) t ht]
  rw [partner,
    extend_edge_lt Q P.lastEdge (extend_hes P Q h) (extend_hnew P Q h) (extend_hedge P Q h)
      ⟨2 * (i + 1) + 2 * j - 2 * t.1 + 1, by omega⟩ hb1,
    extend_edge_lt Q P.lastEdge (extend_hes P Q h) (extend_hnew P Q h) (extend_hedge P Q h)
      ⟨2 * (i + 1) + 2 * j - 2 * t.1, by omega⟩ hb2]
  unfold ssCPairAt
  rw [show (⟨2 * (i + 1) + 2 * j - 2 * t.1, by omega⟩ : Fin (2 * i + 2))
      = ⟨2 * (i + j + 1 - t.1), by omega⟩ from
        Fin.ext (by show 2 * (i + 1) + 2 * j - 2 * t.1 = 2 * (i + j + 1 - t.1); omega),
    show (⟨2 * (i + 1) + 2 * j - 2 * t.1 + 1, by omega⟩ : Fin (2 * i + 2))
      = ⟨2 * (i + j + 1 - t.1) + 1, by omega⟩ from
        Fin.ext (by show 2 * (i + 1) + 2 * j - 2 * t.1 + 1 = 2 * (i + j + 1 - t.1) + 1; omega)]
  exact ⟨Eq.symm, Eq.symm⟩


/-! ### The count identity and its parity consequence -/

/-- The number of c-pairs of a species-to-species path. -/
noncomputable def ssNumCPairs {j : ℕ} (P : N.TrueSRSSPath (2 * j + 2)) : ℕ := by
  classical
  exact (Finset.univ.filter (ssCPairAt P)).card

/-- **The species-to-species glue count has no seam term.** -/
theorem ssGlueCycle_numCPairs :
    (ssGlueCycle P Q h).numCPairs = ssNumCPairs P + ssNumCPairs Q := by
  classical
  unfold TrueSRCycle.numCPairs ssNumCPairs
  have hsplit : (Finset.univ.filter (ssGlueCycle P Q h).isCPair).card
      = ((Finset.univ.filter (ssGlueCycle P Q h).isCPair).filter
            (fun t : Fin (i + 1 + j + 1) => t.1 ≤ j)).card
        + ((Finset.univ.filter (ssGlueCycle P Q h).isCPair).filter
            (fun t : Fin (i + 1 + j + 1) => ¬ t.1 ≤ j)).card :=
    (Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (ssGlueCycle P Q h).isCPair)
      (fun t : Fin (i + 1 + j + 1) => t.1 ≤ j)).symm
  rw [hsplit]
  congr 1
  · -- below and at the seam: the low block matches `P`
    refine Finset.card_bij
      (fun t _ => (⟨min t.1 j, by omega⟩ : Fin (j + 1))) ?_ ?_ ?_
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      obtain ⟨hcp, hle⟩ := ht
      rcases Nat.lt_or_ge t.1 j with hlt | hge
      · rw [show (⟨min t.1 j, by omega⟩ : Fin (j + 1)) = ⟨t.1, by omega⟩ from
          Fin.ext (by show min t.1 j = t.1; omega)]
        exact (ssGlueCycle_isCPair_below P Q h t hlt).mp hcp
      · have heq : t.1 = j := by omega
        rw [show (⟨min t.1 j, by omega⟩ : Fin (j + 1)) = ⟨j, by omega⟩ from
          Fin.ext (by show min t.1 j = j; omega)]
        rw [show t = (⟨j, by omega⟩ : Fin (i + 1 + j + 1)) from Fin.ext heq] at hcp
        exact (ssGlueCycle_isCPair_seam P Q h (by omega)).mp hcp
    · intro a ha b hb hab
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      have hv : min a.1 j = min b.1 j := congrArg Fin.val hab
      refine Fin.ext ?_
      show a.1 = b.1
      omega
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      have hrlt := r.isLt
      refine ⟨⟨r.1, by omega⟩, ⟨?_, by show r.1 ≤ j; omega⟩, ?_⟩
      · rcases Nat.lt_or_ge r.1 j with hlt | hge
        · refine (ssGlueCycle_isCPair_below P Q h ⟨r.1, by omega⟩ hlt).mpr ?_
          rw [show (⟨(⟨r.1, by omega⟩ : Fin (i + 1 + j + 1)).1, by omega⟩ : Fin (j + 1)) = r from
            Fin.ext (by show r.1 = r.1; rfl)]
          exact hr
        · have heq : r.1 = j := by omega
          rw [show (⟨r.1, by omega⟩ : Fin (i + 1 + j + 1))
              = (⟨j, by omega⟩ : Fin (i + 1 + j + 1)) from Fin.ext (by show r.1 = j; omega)]
          refine (ssGlueCycle_isCPair_seam P Q h (by omega)).mpr ?_
          rw [show (⟨j, by omega⟩ : Fin (j + 1)) = r from Fin.ext (by show j = r.1; omega)]
          exact hr
      · exact Fin.ext (by show min r.1 j = r.1; omega)
  · -- above the seam: the high block matches `Q`, at the reversed index
    refine Finset.card_bij
      (fun t _ => (⟨min (i + j + 1 - t.1) i, by omega⟩ : Fin (i + 1))) ?_ ?_ ?_
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      obtain ⟨hcp, hgt⟩ := ht
      have htl := t.isLt
      rw [show (⟨min (i + j + 1 - t.1) i, by omega⟩ : Fin (i + 1))
          = ⟨i + j + 1 - t.1, by omega⟩ from
        Fin.ext (by show min (i + j + 1 - t.1) i = i + j + 1 - t.1; omega)]
      exact (ssGlueCycle_isCPair_above P Q h t (by omega)).mp hcp
    · intro a ha b hb hab
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      have hal := a.isLt
      have hbl := b.isLt
      have hv : min (i + j + 1 - a.1) i = min (i + j + 1 - b.1) i := congrArg Fin.val hab
      refine Fin.ext ?_
      show a.1 = b.1
      omega
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      have hrlt := r.isLt
      have hb : i + j + 1 - r.1 < i + 1 + j + 1 := by omega
      have hb2 : i + j + 1 - (i + j + 1 - r.1) < i + 1 := by omega
      refine ⟨⟨i + j + 1 - r.1, hb⟩, ⟨?_, by show ¬ i + j + 1 - r.1 ≤ j; omega⟩, ?_⟩
      · refine (ssGlueCycle_isCPair_above P Q h ⟨i + j + 1 - r.1, hb⟩
          (by show j < i + j + 1 - r.1; omega)).mpr ?_
        rw [show (⟨i + j + 1 - (⟨i + j + 1 - r.1, hb⟩ : Fin (i + 1 + j + 1)).1, hb2⟩
            : Fin (i + 1)) = r from
          Fin.ext (by show i + j + 1 - (i + j + 1 - r.1) = r.1; omega)]
        exact hr
      · exact Fin.ext (by
          show min (i + j + 1 - (i + j + 1 - r.1)) i = r.1
          omega)

/-- **The parity obstruction.**  Two species-to-species glues sharing the chord `P` always have
the *same* parity, as soon as the two partners' c-pair counts do — which is exactly what
`C.Even` supplies when the partners are the two species-arcs of `C`.

So the `hSR.2` route is unavailable for a species-to-species chord: the two candidate cycles are
either both even or both odd, and every pair among them and `C` meets in a species-to-species
path. -/
theorem ssGlueCycle_even_iff_even {i₁ i₂ j : ℕ}
    (P : N.TrueSRSSPath (2 * j + 2))
    (Q₁ : N.TrueSRSSPath (2 * i₁ + 2)) (Q₂ : N.TrueSRSSPath (2 * i₂ + 2))
    (h₁ : SSGluable P Q₁) (h₂ : SSGluable P Q₂)
    (hQ : (ssNumCPairs Q₁ + ssNumCPairs Q₂) % 2 = 0) :
    (ssGlueCycle P Q₁ h₁).Even ↔ (ssGlueCycle P Q₂ h₂).Even := by
  unfold TrueSRCycle.Even
  rw [Nat.even_iff, Nat.even_iff, ssGlueCycle_numCPairs P Q₁ h₁, ssGlueCycle_numCPairs P Q₂ h₂]
  omega

end CRNT.Network.TrueSRSSPath

import CRNT.Deficiency.CutPair
import CRNT.Deficiency.ClassConservation

/-!
# Confluence vectors and the cut-pair functional

A **confluence vector** `g` is a vector on complexes lying in the image of the incidence map
(the cut space `Im ∂`); equivalently, a real combination of the incidence columns
`e_{target r} − e_{source r}`. Such a vector sums to zero over every linkage class
(`sum_restrictToClass_eq_zero_of_mem_range_incidenceMap`).

For a cut pair `(y, y')`, deleting the bridge edge `s(y, y')` from `linkageGraph` splits the
linkage class into the component `W(y)` of `y` and the component `W(y')` of `y'`. The Deficiency
One Algorithm reads off the sign of the **cut-pair functional**

```text
[g, y→y', y] := ∑_{p ∈ W(y)} g p,
```

which is antisymmetric, `[g, y→y', y] = − [g, y'→y, y']` (Ji, *Uniqueness of equilibria for complex
chemical reaction networks*, Ohio State University, 2011, §1.6).

* `IsConfluenceVector` — membership in `Im ∂`;
* `cutComponent y y'` (`W(y)`) and `cutSum g y y'` (`[g, y→y', y]`);
* `self_mem_cutComponent`, `cutComponent_subset_linkageClass`, `disjoint_cutComponent`;
* `cutSum_eq_neg_sum_sdiff` — the antisymmetry against the linkage-class complement, from zero sum
  over the class;
* `cutSum_antisymm` — the full antisymmetry `[g, y→y', y] = − [g, y'→y, y']`, using that the two cut
  components partition the linkage class.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Deficiency.CutPair`,
`CRNT.Deficiency.ClassConservation`.
-/

namespace CRNT

namespace Network

open scoped Classical BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Confluence vector.** A vector on complexes in the image of the incidence map (the cut space).
Confluence vectors sum to zero over each linkage class. -/
def IsConfluenceVector (N : Network S) (g : N.ComplexIdx → ℝ) : Prop :=
  g ∈ LinearMap.range N.incidenceMap

/-- **The cut component `W(y)`**: the complexes reachable from `y` once the bridge edge `s(y, y')`
is deleted from the linkage graph. -/
noncomputable def cutComponent (N : Network S) (y y' : N.ComplexIdx) : Finset N.ComplexIdx :=
  Finset.univ.filter (fun v => (N.linkageGraph.deleteEdges {s(y, y')}).Reachable y v)

/-- **The cut-pair functional `[g, y→y', y] = ∑_{p ∈ W(y)} g p`.** -/
noncomputable def cutSum (N : Network S) (g : N.ComplexIdx → ℝ) (y y' : N.ComplexIdx) : ℝ :=
  ∑ p ∈ N.cutComponent y y', g p

/-- The linkage class of `y`, as a `Finset` of complexes. -/
noncomputable def linkageClassFinset (N : Network S) (y : N.ComplexIdx) : Finset N.ComplexIdx :=
  Finset.univ.filter (fun c => N.classOf c = N.classOf y)

theorem mem_cutComponent {N : Network S} {y y' v : N.ComplexIdx} :
    v ∈ N.cutComponent y y' ↔ (N.linkageGraph.deleteEdges {s(y, y')}).Reachable y v := by
  simp [cutComponent]

theorem self_mem_cutComponent (N : Network S) (y y' : N.ComplexIdx) :
    y ∈ N.cutComponent y y' :=
  mem_cutComponent.mpr (SimpleGraph.Reachable.refl _)

/-- Deleting `s(y', y)` and deleting `s(y, y')` give the same graph. -/
theorem deleteEdges_swap (N : Network S) (y y' : N.ComplexIdx) :
    N.linkageGraph.deleteEdges {s(y', y)} = N.linkageGraph.deleteEdges {s(y, y')} := by
  have : ({s(y', y)} : Set (Sym2 N.ComplexIdx)) = {s(y, y')} := by rw [Sym2.eq_swap]
  rw [this]

theorem classOf_eq_iff_linked {N : Network S} {c d : N.ComplexIdx} :
    N.classOf c = N.classOf d ↔ N.Linked c.val d.val :=
  Quotient.eq

/-- A cut component sits inside the linkage class of its base point. -/
theorem cutComponent_subset_linkageClass (N : Network S) (y y' : N.ComplexIdx) :
    N.cutComponent y y' ⊆ N.linkageClassFinset y := by
  intro v hv
  rw [mem_cutComponent] at hv
  have hreach : N.linkageGraph.Reachable y v := hv.mono (N.linkageGraph.deleteEdges_le _)
  have hlink : N.Linked y.val v.val := (linked_iff_reachable N y v).mpr hreach
  rw [linkageClassFinset, Finset.mem_filter]
  exact ⟨Finset.mem_univ v, classOf_eq_iff_linked.mpr hlink.symm⟩

/-- **A confluence vector sums to zero over a linkage class.** -/
theorem sum_linkageClass_eq_zero (N : Network S) {g : N.ComplexIdx → ℝ}
    (hg : N.IsConfluenceVector g) (y : N.ComplexIdx) :
    ∑ p ∈ N.linkageClassFinset y, g p = 0 := by
  have h := N.sum_restrictToClass_eq_zero_of_mem_range_incidenceMap hg (N.classOf y)
  rw [← h]
  rw [linkageClassFinset, Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [restrictToClass]

/-- **The cut-pair functional equals minus the confluence sum over the linkage-class complement.**
This is the antisymmetry expressed against the complement `L ∖ W(y)`, obtained purely from the
zero sum over the class. Identifying `L ∖ W(y)` with `W(y')` is `cutSum_antisymm`. -/
theorem cutSum_eq_neg_sum_sdiff (N : Network S) {g : N.ComplexIdx → ℝ}
    (hg : N.IsConfluenceVector g) (y y' : N.ComplexIdx) :
    N.cutSum g y y' = - ∑ p ∈ (N.linkageClassFinset y \ N.cutComponent y y'), g p := by
  have hsub := N.cutComponent_subset_linkageClass y y'
  have hsplit : ∑ p ∈ (N.linkageClassFinset y \ N.cutComponent y y'), g p
      + ∑ p ∈ N.cutComponent y y', g p = ∑ p ∈ N.linkageClassFinset y, g p :=
    Finset.sum_sdiff hsub
  have hz := N.sum_linkageClass_eq_zero hg y
  rw [hz] at hsplit
  rw [cutSum]
  linarith

/-- **The cut components are disjoint.** A common vertex would be reachable from both `y` and `y'`
in the deleted graph, hence link `y` to `y'` there, contradicting the cut. -/
theorem disjoint_cutComponent (N : Network S) {y y' : N.ComplexIdx} (h : N.CutPair y y') :
    Disjoint (N.cutComponent y y') (N.cutComponent y' y) := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  rw [mem_cutComponent] at hv
  rw [mem_cutComponent, deleteEdges_swap] at hv'
  exact h.2 (hv.trans hv'.symm)

/-- **Deleting the bridge merges nothing beyond the two endpoint components.** Anything reachable
from `y` in the full linkage graph is, after deleting `s(y, y')`, reachable from `y` or from `y'`:
the only crossing the deleted edge can enable lands you on the `y'` side. -/
theorem reachable_full_imp_cut (N : Network S) (y y' : N.ComplexIdx) {v : N.ComplexIdx}
    (h : N.linkageGraph.Reachable y v) :
    (N.linkageGraph.deleteEdges {s(y, y')}).Reachable y v ∨
      (N.linkageGraph.deleteEdges {s(y, y')}).Reachable y' v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inl (SimpleGraph.Reachable.refl _)
  | @tail w v hyw hwv ih =>
    by_cases he : s(w, v) = s(y, y')
    · rw [Sym2.eq_iff] at he
      rcases he with ⟨hw, hv⟩ | ⟨hw, hv⟩
      · subst hw; subst hv; exact Or.inr (SimpleGraph.Reachable.refl _)
      · subst hw; subst hv; exact Or.inl (SimpleGraph.Reachable.refl _)
    · have hG'adj : (N.linkageGraph.deleteEdges {s(y, y')}).Adj w v := by
        rw [SimpleGraph.deleteEdges_adj]
        exact ⟨hwv, by simpa using he⟩
      rcases ih with hl | hr
      · exact Or.inl (hl.trans hG'adj.reachable)
      · exact Or.inr (hr.trans hG'adj.reachable)

/-- **The two cut components partition the linkage class:** `L ∖ W(y) = W(y')`. -/
theorem sdiff_cutComponent_eq (N : Network S) {y y' : N.ComplexIdx} (h : N.CutPair y y') :
    N.linkageClassFinset y \ N.cutComponent y y' = N.cutComponent y' y := by
  have hcls : N.classOf y = N.classOf y' :=
    classOf_eq_iff_linked.mpr ((linked_iff_reachable N y y').mpr h.1.reachable)
  have hLeq : N.linkageClassFinset y = N.linkageClassFinset y' := by
    rw [linkageClassFinset, linkageClassFinset, hcls]
  apply Finset.ext
  intro v
  rw [Finset.mem_sdiff]
  constructor
  · rintro ⟨hvL, hvC⟩
    rw [linkageClassFinset, Finset.mem_filter] at hvL
    have hreach : N.linkageGraph.Reachable y v :=
      (linked_iff_reachable N y v).mp (classOf_eq_iff_linked.mp hvL.2).symm
    rcases N.reachable_full_imp_cut y y' hreach with hl | hr
    · exact absurd (mem_cutComponent.mpr hl) hvC
    · rw [mem_cutComponent, deleteEdges_swap]; exact hr
  · intro hv
    refine ⟨?_, ?_⟩
    · rw [hLeq]; exact N.cutComponent_subset_linkageClass y' y hv
    · exact Finset.disjoint_right.mp (N.disjoint_cutComponent h) hv

/-- **Antisymmetry of the cut-pair functional:** `[g, y→y', y] = − [g, y'→y, y']`. The two cut
components partition the linkage class, over which a confluence vector sums to zero. -/
theorem cutSum_antisymm (N : Network S) {g : N.ComplexIdx → ℝ} (hg : N.IsConfluenceVector g)
    {y y' : N.ComplexIdx} (h : N.CutPair y y') :
    N.cutSum g y y' = - N.cutSum g y' y := by
  rw [N.cutSum_eq_neg_sum_sdiff hg y y', N.sdiff_cutComponent_eq h, cutSum]

end Network

end CRNT

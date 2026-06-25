import CRNT.Analysis.SpernerNParity
import CRNT.Analysis.SpernerNIncidence

/-!
# Door facets and the boundary face

A *door* facet of a Kuhn cell carries exactly the low colors `{0, …, n-1}` (`lowColors n`), so it
omits the top color `Fin.last n`. If such a facet lies entirely on a coordinate face `{x_j = 0}`,
that face must be the one opposite the top color, i.e. `j = Fin.last n`: on any other face `x_j = 0`
(with `j < n`) the Sperner `proper` condition forbids color `j`, yet a door facet must realize every
low color including `j`. These are the structural facts feeding the boundary reduction of the
dimension induction for the n-dimensional Sperner lemma.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Analysis.SpernerNParity`,
`CRNT.Analysis.SpernerNIncidence`.
-/

namespace CRNT.Analysis.SpernerN

open Finset

variable {n N : ℕ}

/-- A door facet omits the top color `Fin.last n` (it carries only low colors). -/
theorem door_no_last_color (c : Cell n N) (m : Fin (n + 1)) (col : SpernerColoring n N)
    (hdoor : (facetVerts c m).image col.color = lowColors n) :
    ∀ p ∈ facetVerts c m, col.color p ≠ Fin.last n := by
  intro p hp hcol
  have hmem : Fin.last n ∈ (facetVerts c m).image col.color := mem_image.mpr ⟨p, hp, hcol⟩
  rw [hdoor] at hmem
  exact last_not_mem_lowColors hmem

/-- The coloring is injective on a door facet (its `n` vertices realize the `n` distinct low colors). -/
theorem door_injOn (c : Cell n N) (m : Fin (n + 1)) (col : SpernerColoring n N)
    (hdoor : (facetVerts c m).image col.color = lowColors n) :
    Set.InjOn col.color (facetVerts c m) := by
  rw [← Finset.card_image_iff, hdoor, lowColors_card, facetVerts_card]

/-- **A door facet lying on a boundary face lies on the face opposite the top color.** If a door
facet (its colors are exactly `lowColors n`) is contained in the coordinate face `{x_j = 0}`, then
`j = Fin.last n`. -/
theorem door_face_eq_last (c : Cell n N) (m : Fin (n + 1)) (col : SpernerColoring n N)
    (j : Fin (n + 1)) (hdoor : (facetVerts c m).image col.color = lowColors n)
    (hface : ∀ p ∈ facetVerts c m, p.1 j = 0) : j = Fin.last n := by
  by_contra hne
  have hjlt : (j : ℕ) < n := by
    have hlt : (j : ℕ) < n + 1 := j.isLt
    have hne' : (j : ℕ) ≠ n := by
      intro h
      exact hne (by ext; rw [Fin.val_last]; exact h)
    omega
  have hjmem : j ∈ (facetVerts c m).image col.color := by
    rw [hdoor]; exact mem_lowColors.mpr hjlt
  obtain ⟨p, hp, hcol⟩ := mem_image.mp hjmem
  have hpos := col.proper p j hcol
  have hzero := hface p hp
  omega

end CRNT.Analysis.SpernerN

import CRNT.Decision.StrongLinkage
import CRNT.Dynamics.MassActionAlgebra

/-!
# Every complex reaches a terminal strong linkage class

In a finite reaction graph, following directed reactions from any complex eventually lands in
a terminal strong linkage class. Formally, every complex `c` reaches a complex `d` whose strong
linkage class is terminal (`exists_terminal_reachable`).

The witness `d` is a complex reachable from `c` whose forward-reachable set is smallest. If such
a `d` had a reaction leaving its strong linkage class, the target's reachable set would be a
proper subset, contradicting minimality; so the reachable set of `d` is exactly its strong
linkage class, i.e. `d` is terminal.

A consequence: every nonempty reaction-closed set of complexes contains a terminal strong
linkage class (`exists_terminal_mem_of_closed`).

Depends on: `CRNT.Decision.StrongLinkage`,
`CRNT.Dynamics.MassActionAlgebra`.
-/

namespace CRNT

namespace Network

open scoped Classical

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Every complex reaches a terminal strong linkage class.** -/
theorem exists_terminal_reachable (N : Network S) (c : N.ComplexIdx) :
    ∃ d : N.ComplexIdx, N.Reaches c.val d.val ∧ N.IsTerminalSLC d.val := by
  classical
  set R : N.ComplexIdx → Finset N.ComplexIdx :=
    fun d => Finset.univ.filter (fun e => N.Reaches d.val e.val) with hRdef
  have hmemR : ∀ d e : N.ComplexIdx, e ∈ R d ↔ N.Reaches d.val e.val := by
    intro d e; rw [hRdef, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ e, h⟩⟩
  have hcc : c ∈ R c := (hmemR c c).mpr (Reaches.refl N c.val)
  obtain ⟨d₀, hd₀mem, hmin⟩ := Finset.exists_min_image (R c) (fun d => (R d).card) ⟨c, hcc⟩
  have hd₀reach : N.Reaches c.val d₀.val := (hmemR c d₀).mp hd₀mem
  refine ⟨d₀, hd₀reach, ?_⟩
  intro r hsl
  have hd₀tgt : N.Reaches d₀.val (N.reaction r).target := hsl.1.trans (N.reaches_of_reaction r)
  set t := N.targetIdx r with htdef
  have hct : t ∈ R c := (hmemR c t).mpr (hd₀reach.trans hd₀tgt)
  have hsub : R t ⊆ R d₀ := by
    intro e he
    rw [hmemR] at he ⊢
    exact hd₀tgt.trans he
  have hcard : (R d₀).card ≤ (R t).card := hmin t hct
  have heq : R t = R d₀ := Finset.eq_of_subset_of_card_le hsub hcard
  have htd₀ : N.Reaches t.val d₀.val :=
    (hmemR t d₀).mp (heq ▸ (hmemR d₀ d₀).mpr (Reaches.refl N d₀.val))
  exact ⟨hd₀tgt, htd₀⟩

/-- **Every nonempty reaction-closed set of complexes contains a terminal strong linkage
class.** If `D` is closed under reactions and contains some complex, it contains a complex whose
strong linkage class is terminal. -/
theorem exists_terminal_mem_of_closed (N : Network S) {D : N.ComplexIdx → Prop}
    (hclosed : ∀ r : N.R, D (N.sourceIdx r) → D (N.targetIdx r))
    {c0 : N.ComplexIdx} (hc0 : D c0) :
    ∃ d : N.ComplexIdx, D d ∧ N.IsTerminalSLC d.val := by
  have hpreserve : ∀ {x y : Complex S}, N.Reaches x y →
      ∀ (hx : x ∈ N.complexes) (hy : y ∈ N.complexes), D ⟨x, hx⟩ → D ⟨y, hy⟩ := by
    intro x y hxy
    induction hxy with
    | refl => intro _ _ hD; exact hD
    | @tail e f _ hef ih =>
      intro hx hy hD
      obtain ⟨r, hs, ht⟩ := hef
      have he : e ∈ N.complexes := hs ▸ N.source_mem_complexes r
      have hDsrc : D (N.sourceIdx r) := (Subtype.ext hs : N.sourceIdx r = ⟨e, he⟩) ▸ ih hx he hD
      have hDtgt : D (N.targetIdx r) := hclosed r hDsrc
      exact (Subtype.ext ht : N.targetIdx r = ⟨f, hy⟩) ▸ hDtgt
  obtain ⟨d, hreach, hterm⟩ := N.exists_terminal_reachable c0
  exact ⟨d, hpreserve hreach c0.property d.property hc0, hterm⟩

end Network

end CRNT

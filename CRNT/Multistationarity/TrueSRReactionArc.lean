import CRNT.Multistationarity.TrueSRParityRR
import CRNT.Multistationarity.TrueSRCycleSplit

/-!
# Reaction-to-reaction arcs of a cycle

`TrueSRSpeciesPath.lean` builds the **species** flavour of a cycle arc: between species vertex
`0` and species vertex `m`, a cycle is two species-to-species paths (`speciesArc`,
`speciesArcBwd`) with those endpoints and disjoint interiors.  The **reaction** flavour has no
builder on `holes`, and `TrueSRPathRR` — the object Shinar--Feinberg's Lemma A.4 three-path
parity argument consumes, and hence the object
`exists_second_evenCycle_of_offCycle_escape` must produce — cannot be built at all without it.

This file supplies that builder.

## The combinatorial content

A `TrueSRCycle n` alternates

```
  R_i --leftEdge i--> S_i      R_i --rightEdge i--> S_{i+1 mod n}
```

because `leftEdge i` has species `species i` and reaction `reaction i`, while `rightEdge i` has
reaction `reaction i` and species `species ⟨(i+1) % n⟩`.  So the graph is the chain

```
  R_0 — S_1 — R_1 — S_2 — R_2 — … — S_m — R_m
```

and from `R_0` there is exactly **one** simple route to `R_m` going forward: the `2m`-edge walk

```
  rightEdge 0, leftEdge 1, rightEdge 1, leftEdge 2, …, rightEdge (m-1), leftEdge m.
```

The parity is forced: the true-SR graph is bipartite (species against reactions), so *every*
reaction-to-reaction path has even length, and `2m` is even.

`TrueSRPathRR j` records a reaction-to-reaction path of `2 * j + 2` edges as a first edge plus a
`TrueSRPath (2 * j + 1)` tail.  Splitting off `rightEdge 0` gives `j = m - 1`:

* `first = rightEdge 0`, joining `R_0` to `S_1`;
* `tail : TrueSRPath (2 * (m - 1) + 1)`, running `S_1 — R_1 — S_2 — … — S_m — R_m`.

`m > 0` is required (a zero-length reaction arc would be a bare reaction vertex) and `m < n` keeps
every species and reaction index inside the cycle.
-/

namespace CRNT.Network.TrueSRCycle

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {n : ℕ}

/-- Every index used by the reaction arc, of the form `q / 2 + 1` with `q < 2 * m`, stays inside
the cycle. -/
private theorem arcIdx {m : ℕ} (hm : m < n) {q : ℕ} (hq : q < 2 * m) : q / 2 + 1 < n := by
  have hq2 : q / 2 < m := by omega
  omega

/-- The species index one step forward is still inside the cycle. -/
private theorem arcIdxSucc {m : ℕ} (hm : m < n) {q : ℕ} (hq : q < 2 * m) : q / 2 + 2 < n := by
  have hq2 : q / 2 < m := by omega
  omega

section ReactionArc

variable (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m)

/-- Edges of the tail of the reaction arc.  Position `q` is `leftEdge (q / 2 + 1)` when `q` is
even and `rightEdge (q / 2 + 1)` when `q` is odd. -/
private noncomputable def rarcEdge (q : Fin (2 * m - 1)) : N.TrueSREdge :=
  C.leftEdge ⟨q.1 / 2 + 1, arcIdx hm q.isLt⟩

/-- Vertices of the tail of the reaction arc.  Position `p` is the species `S_{p / 2 + 1}` when
`p` is even and the reaction `R_{p / 2 + 1}` when `p` is odd.  So position `0` is `S_1` and
position `2 * m - 1` is `R_m`. -/
private noncomputable def rarcVertex (p : Fin (2 * m)) : N.TrueSRVertex :=
  if h : p.1 % 2 = 0 then Sum.inl (C.species ⟨p.1 / 2 + 1, arcIdx hm p.isLt⟩)
  else Sum.inr ⟨C.reaction ⟨p.1 / 2 + 1, arcIdx hm p.isLt⟩,
    C.reaction_internal ⟨p.1 / 2 + 1, arcIdx hm p.isLt⟩⟩

private theorem rarcVertex_even {p : Fin (2 * m)} (h : p.1 % 2 = 0) :
    rarcVertex C m hm p = Sum.inl (C.species ⟨p.1 / 2 + 1, arcIdx hm p.isLt⟩) :=
  if_pos h

private theorem rarcVertex_odd {p : Fin (2 * m)} (h : p.1 % 2 ≠ 0) :
    rarcVertex C m hm p = Sum.inr ⟨C.reaction ⟨p.1 / 2 + 1, arcIdx hm p.isLt⟩,
      C.reaction_internal ⟨p.1 / 2 + 1, arcIdx hm p.isLt⟩⟩ :=
  if_neg h

/-- **The forward reaction arc of a cycle**, from the reaction vertex `R_0` to the reaction
vertex `R_m`.  This is the reaction-to-reaction counterpart of `speciesArc`: the walk

```
  R_0 —rightEdge 0— S_1 —leftEdge 1— R_1 —rightEdge 1— S_2 — … — S_m —leftEdge m— R_m
```

with its first edge `rightEdge 0` split off into `TrueSRPathRR.first` and the remaining
`2 * m - 1` edges forming `TrueSRPathRR.tail`.  The parameter is `j = m - 1`, so the whole arc
has `2 * (m - 1) + 2 = 2 * m` edges: even, as the bipartition of the true-SR graph forces. -/
noncomputable def reactionArc : N.TrueSRPathRR (m - 1) where
  first := C.rightEdge ⟨0, by omega⟩
  tail := by
    have hn := C.nontrivial
    refine
      { length_pos := by omega
        edge := rarcEdge C m hm
        vertex := rarcVertex C m hm
        connects := by
          intro q
          have hq := q.isLt
          have hcs : (Fin.castSucc q).1 = q.1 := rfl
          have hsu : (q.succ).1 = q.1 + 1 := rfl
          by_cases hpar : q.1 % 2 = 0
          · -- position `q` is `leftEdge (q / 2 + 1)`
            refine Or.inl ⟨?_, ?_⟩
            · rw [rarcVertex_even C m hm (by rw [hcs]; exact hpar), C.left_species]
              exact congrArg Sum.inl (congrArg C.species (Fin.ext (by rw [hcs]; rfl)))
            · rw [rarcVertex_odd C m hm (by rw [hsu]; omega), C.left_reaction]
              exact congrArg Sum.inr (Subtype.ext (congrArg C.reaction
                (Fin.ext (by rw [hsu]; omega))))
          · -- position `q` is `rightEdge (q / 2 + 1)`
            refine Or.inr ⟨?_, ?_⟩
            · rw [rarcVertex_odd C m hm (by rw [hcs]; exact hpar), C.right_reaction]
              exact congrArg Sum.inr (Subtype.ext (congrArg C.reaction
                (Fin.ext (by rw [hcs]; rfl))))
            · rw [rarcVertex_even C m hm (by rw [hsu]; omega), C.right_species]
              refine congrArg Sum.inl (congrArg C.species (Fin.ext ?_))
              show (q.1 / 2 + 1 + 1) % n = q.1 / 2 + 2
              rw [Nat.mod_eq_of_lt (arcIdxSucc hm q.isLt)]
        edge_simple := by
          intro i j hij
          have hi := i.isLt
          have hj := j.isLt
          by_cases hpi : i.1 % 2 = 0 <;> by_cases hpj : j.1 % 2 = 0
          · rw [rarcEdge C m hm, rarcEdge C m hm] at hij
            have h := C.sameIncidence_leftEdge_iff _ _ hij
            have hv := congrArg Fin.val h
            exact Fin.ext (by simp only at hv; omega)
          · rw [rarcEdge C m hm, rarcEdge C m hm] at hij
            exact absurd hij (C.not_sameIncidence_left_right _ _)
          · rw [rarcEdge C m hm, rarcEdge C m hm] at hij
            exact absurd (TrueSREdge.SameIncidence.symm hij) (C.not_sameIncidence_left_right _ _)
          · rw [rarcEdge C m hm, rarcEdge C m hm] at hij
            have h := C.sameIncidence_rightEdge_iff _ _ hij
            have hv := congrArg Fin.val h
            exact Fin.ext (by simp only at hv; omega)
        vertex_simple := by
          intro p p' hpp'
          have hp := p.isLt
          have hp' := p'.isLt
          by_cases hpi : p.1 % 2 = 0 <;> by_cases hpj : p'.1 % 2 = 0
          · rw [rarcVertex_even C m hm hpi, rarcVertex_even C m hm hpj] at hpp'
            have h := C.species_injective (Sum.inl.inj hpp')
            have hv := congrArg Fin.val h
            exact Fin.ext (by simp only at hv; omega)
          · rw [rarcVertex_even C m hm hpi, rarcVertex_odd C m hm hpj] at hpp'
            exact absurd hpp' (by simp)
          · rw [rarcVertex_odd C m hm hpi, rarcVertex_even C m hm hpj] at hpp'
            exact absurd hpp' (by simp)
          · rw [rarcVertex_odd C m hm hpi, rarcVertex_odd C m hm hpj] at hpp'
            have h := C.reaction_injective (congrArg Subtype.val (Sum.inr.inj hpp'))
            have hv := congrArg Fin.val h
            exact Fin.ext (by simp only at hv; omega)
        starts_at_species := by
          refine ⟨C.species ⟨1, by omega⟩, ?_⟩
          rw [rarcVertex_even C m hm (by simp)]
          exact congrArg Sum.inl (congrArg C.species
            (Fin.ext (by show (0 : ℕ) / 2 + 1 = 1; rfl)))
        ends_at_reaction := by
          refine ⟨⟨C.reaction ⟨m, hm⟩, C.reaction_internal ⟨m, hm⟩⟩, ?_⟩
          have hlast : (Fin.last (2 * m - 1)).1 = 2 * m - 1 := rfl
          rw [rarcVertex_odd C m hm (by rw [hlast]; omega)]
          exact congrArg Sum.inr (Subtype.ext (congrArg C.reaction
            (Fin.ext (by show (Fin.last (2 * m - 1)).1 / 2 + 1 = m; omega))))
  first_species := by
    have hn := C.nontrivial
    have hlt : (0 + 1) % n = 1 := Nat.mod_eq_of_lt (by omega)
    rw [C.right_species]
    exact congrArg Sum.inl (congrArg C.species (Fin.ext hlt))
  first_ne_tail_edge := by
    intro i
    have hi := i.isLt
    have hidx : i.1 / 2 + 1 = 0 := by omega
    rw [rarcEdge C m hm, hidx]
    exact C.not_sameIncidence_left_right (C.reaction_injective rfl) ⟨0, by omega⟩
  first_ne_tail_vertex := by
    intro i
    have hi := i.isLt
    by_cases hpi : i.1 % 2 = 0
    · rw [rarcVertex_even C m hm hpi]
      simp
    · rw [rarcVertex_odd C m hm hpi, C.right_reaction]
      intro hcon
      exact absurd hcon (by
        refine C.reaction_injective ?_
        have := congrArg Subtype.val hcon
        omega)

theorem reactionArc_startReaction (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m) :
    (C.reactionArc m hm hmpos).startReaction
      = ⟨C.reaction ⟨0, by omega⟩, (C.reaction_internal ⟨0, by omega⟩).internal⟩ := by
  refine Subtype.ext ?_
  exact (C.reactionArc m hm hmpos).first.reaction

/-- **The arc ends at `R_m`.** -/
theorem reactionArc_endReaction (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m) :
    (C.reactionArc m hm hmpos).endReaction = ⟨C.reaction ⟨m, hm⟩, C.reaction_internal ⟨m, hm⟩⟩ :=
  (C.reactionArc m hm hmpos).tail.ends_at_reaction

/-- **The arc's tail starts at `S_1`.** -/
theorem reactionArc_tail_startSpecies (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m) :
    (C.reactionArc m hm hmpos).tail.startSpecies = C.species ⟨1, by omega⟩ := by
  obtain ⟨x, hx⟩ := (C.reactionArc m hm hmpos).tail.starts_at_species
  rw [hx]
  exact congrArg Sum.inl (congrArg C.species (Fin.ext (by
    show (0 : ℕ) / 2 + 1 = 1; rfl)))

/-- **The arc is even-length, as the bipartition forces.**  `2 * (m - 1) + 2 = 2 * m`. -/
theorem reactionArc_length (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m) :
    2 * (m - 1) + 2 = 2 * m := by omega

end ReactionArc

end CRNT.Network.TrueSRCycle
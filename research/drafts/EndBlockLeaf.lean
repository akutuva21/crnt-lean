import CRNT.Graph.SourceBlocks

/-!
# End-block leaf facts

Derived purely from `CRNT.Graph.SourceBlocks`.  Nothing here assumes block existence,
maximality, or block-trees; every statement is a finite consequence of the definitions of
`IsSeparatingVertexOn`, `ConnectedOn`, `IsNonseparableOn` and `IsEndBlockOn`.

Main exports:

* `isEndBlockOn_iff`, `isEndBlockOn_nonseparable`, `isEndBlockOn_atMostOne_ambient`:
  `IsEndBlockOn` split into its two projections.
* `isNonseparableOn_connected`: nonseparability implies connectedness.
* `AmbientSepOn`, `isEndBlockOn_ambientSep_card_le_one`,
  `isEndBlockOn_ambientSep_dichotomy`, `isEndBlockOn_ambientSep_cases`: the leaf
  dichotomy — `S` contains at most one vertex separating the ambient graph on `T`, so
  either none or exactly one.
* `eq_of_isEndBlockOn_of_isSeparatingVertexOn`,
  `not_isSeparatingVertexOn_ambient_of_isEndBlockOn`: the form §5.5 consumers apply.
* `mem_of_isSeparatingVertexOn`: `IsSeparatingVertexOn E S v → v ∈ S` (holds with no
  extra hypotheses; see the proof).
-/

namespace CRNT

variable {V : Type*}

/-! ### 1. Splitting `IsEndBlockOn` -/

/-- The nonseparability projection of end-blockness. -/
theorem isEndBlockOn_nonseparable {E : V → V → Prop} {T S : Finset V}
    (h : IsEndBlockOn E T S) : IsNonseparableOn E S := h.1

/-- The "at most one ambient separating vertex" projection of end-blockness, phrased as
injectivity on the ambient separating vertices carried by `S`. -/
theorem isEndBlockOn_atMostOne_ambient {E : V → V → Prop} {T S : Finset V}
    (h : IsEndBlockOn E T S) {v1 v2 : V} (hv1 : v1 ∈ S) (hv2 : v2 ∈ S)
    (h1 : IsSeparatingVertexOn E T v1) (h2 : IsSeparatingVertexOn E T v2) : v1 = v2 :=
  h.2 v1 hv1 v2 hv2 h1 h2

/-- `IsEndBlockOn` is exactly the conjunction of its two projections, so consumers may
use either side independently (e.g. take only nonseparability, or only the
at-most-one-separator bound). -/
theorem isEndBlockOn_iff {E : V → V → Prop} {T S : Finset V} :
    IsEndBlockOn E T S ↔
      (IsNonseparableOn E S ∧
        ∀ v1 ∈ S, ∀ v2 ∈ S, IsSeparatingVertexOn E T v1 →
          IsSeparatingVertexOn E T v2 → v1 = v2) :=
  Iff.intro
    (fun h : IsEndBlockOn E T S => h)
    (fun h => And.intro h.1 (fun v1 hv1 v2 hv2 h1 h2 => h.2 v1 hv1 v2 hv2 h1 h2))

/-! ### 2. Nonseparability implies connectedness -/

/-- A nonseparable induced graph is connected. -/
theorem isNonseparableOn_connected {E : V → V → Prop} {S : Finset V}
    (h : IsNonseparableOn E S) : ConnectedOn E S := h.1

/-- The pairwise connectedness consequence, for consumers that need `ExistsWalkOn`
directly under a discharged nonseparability hypothesis. -/
theorem existsWalkOn_of_isNonseparableOn {E : V → V → Prop} {S : Finset V}
    (h : IsNonseparableOn E S) (a b : V) (ha : a ∈ S) (hb : b ∈ S) :
    ExistsWalkOn E S a b :=
  h.1 a ha b hb

/-! ### The ambient separating vertices carried by `S` -/

/-- The vertices of `S` that separate the *ambient* graph on `T`. -/
noncomputable def AmbientSepOn (E : V → V → Prop) (T S : Finset V) : Finset V := by
  classical
  exact S.filter (IsSeparatingVertexOn E T)

@[simp]
theorem mem_ambientSepOn (E : V → V → Prop) (T S : Finset V) (v : V) :
    v ∈ AmbientSepOn E T S ↔ v ∈ S ∧ IsSeparatingVertexOn E T v := by
  classical
  rw [AmbientSepOn, Finset.mem_filter]

theorem ambientSepOn_subset (E : V → V → Prop) (T S : Finset V) :
    AmbientSepOn E T S ⊆ S := by
  classical
  intro v hv
  exact (mem_ambientSepOn E T S v).mp hv |>.1

/-- End-blockness bounds the number of ambient separating vertices carried by `S` by
one. -/
theorem isEndBlockOn_ambientSep_card_le_one {E : V → V → Prop}
    {T S : Finset V} (h : IsEndBlockOn E T S) : (AmbientSepOn E T S).card ≤ 1 := by
  classical
  refine Finset.card_le_one.mpr ?_
  intro v1 hv1 v2 hv2
  rcases (mem_ambientSepOn E T S v1).mp hv1 with ⟨hv1S, hv1sep⟩
  rcases (mem_ambientSepOn E T S v2).mp hv2 with ⟨hv2S, hv2sep⟩
  exact h.2 v1 hv1S v2 hv2S hv1sep hv2sep

/-! ### 3. The leaf dichotomy -/

/-- Either `S` carries no ambient separating vertex, or exactly one. -/
theorem isEndBlockOn_ambientSep_dichotomy {E : V → V → Prop} {T S : Finset V}
    (h : IsEndBlockOn E T S) :
    AmbientSepOn E T S = ∅ ∨ (AmbientSepOn E T S).card = 1 := by
  classical
  have key : ∀ x ∈ AmbientSepOn E T S, ∀ y ∈ AmbientSepOn E T S, x = y := by
    intro x hx y hy
    rcases (mem_ambientSepOn E T S x).mp hx with ⟨hxS, hxsep⟩
    rcases (mem_ambientSepOn E T S y).mp hy with ⟨hyS, hysep⟩
    exact h.2 x hxS y hyS hxsep hysep
  by_cases hne : (AmbientSepOn E T S).Nonempty
  · right
    obtain ⟨v, hv⟩ := hne
    refine Finset.card_eq_one.mpr ⟨v, ?_⟩
    ext w
    rw [Finset.mem_singleton]
    constructor
    · intro hw; exact key w hw v hv
    · intro hw; rw [hw]; exact hv
  · left
    exact Finset.not_nonempty_iff_eq_empty.mp hne

/-- The leaf dichotomy, phrased directly on vertices of `S`: either no vertex of `S`
separates the ambient graph on `T`, or there is a unique such vertex.  No `S.Nonempty`
hypothesis is needed. -/
theorem isEndBlockOn_ambientSep_cases {E : V → V → Prop} {T S : Finset V}
    (h : IsEndBlockOn E T S) :
    (∀ v ∈ S, ¬ IsSeparatingVertexOn E T v) ∨
      ∃ v ∈ S, IsSeparatingVertexOn E T v ∧
        ∀ w ∈ S, IsSeparatingVertexOn E T w → w = v := by
  classical
  rcases isEndBlockOn_ambientSep_dichotomy h with he | hc
  · refine Or.inl ?_
    intro v hv hs
    exact absurd ((mem_ambientSepOn E T S v).mpr ⟨hv, hs⟩) (by rw [he]; simp)
  · refine Or.inr ?_
    obtain ⟨v, hvs⟩ := Finset.card_eq_one.mp hc
    have hvA : v ∈ AmbientSepOn E T S := by
      rw [hvs]
      exact Finset.mem_singleton_self v
    refine ⟨v, (mem_ambientSepOn E T S v).mp hvA |>.1,
      (mem_ambientSepOn E T S v).mp hvA |>.2, ?_⟩
    intro w hw hs
    have hwA : w ∈ AmbientSepOn E T S := (mem_ambientSepOn E T S w).mpr ⟨hw, hs⟩
    rw [hvs] at hwA
    exact Finset.mem_singleton.mp hwA

/-! ### 4. What consumers actually apply -/

/-- Uniqueness of an ambient separating vertex inside an end block. -/
theorem eq_of_isEndBlockOn_of_isSeparatingVertexOn {E : V → V → Prop} {T S : Finset V}
    (h : IsEndBlockOn E T S) {v w : V} (hv : v ∈ S) (hw : w ∈ S)
    (hvw : IsSeparatingVertexOn E T v) (hww : IsSeparatingVertexOn E T w) : v = w :=
  h.2 v hv w hw hvw hww

/-- The pointwise form of `eq_of_isEndBlockOn_of_isSeparatingVertexOn`: once one vertex
`v ∈ S` separates the ambient graph on `T`, no *other* vertex of `S` does. -/
theorem not_isSeparatingVertexOn_ambient_of_isEndBlockOn {E : V → V → Prop}
    {T S : Finset V} (h : IsEndBlockOn E T S) {v w : V} (hv : v ∈ S)
    (hvsep : IsSeparatingVertexOn E T v) (hw : w ∈ S) (hne : w ≠ v) :
    ¬ IsSeparatingVertexOn E T w :=
  fun hws => hne (h.2 v hv w hw hvsep hws).symm

/-- Symmetric packaged form: every ambient separating vertex of an end block is the same
vertex. -/
theorem isSeparatingVertexOn_ambient_unique {E : V → V → Prop} {T S : Finset V}
    (h : IsEndBlockOn E T S) {v : V} (hv : v ∈ S) (hvsep : IsSeparatingVertexOn E T v) :
    ∀ w ∈ S, IsSeparatingVertexOn E T w → w = v :=
  fun w hw hwsep => (h.2 v hv w hw hvsep hwsep).symm

/-- End blocks are in particular connected on `S`. -/
theorem connectedOn_of_isEndBlockOn {E : V → V → Prop} {T S : Finset V}
    (h : IsEndBlockOn E T S) : ConnectedOn E S := h.1.1

/-! ### 5. Separating vertices lie in the set they separate -/

/-- **A separating vertex belongs to the vertex set whose graph it separates.**
No `DecidableEq`, no `Fintype`, and no hypothesis on `S` itself are required.

The walk witness is what forces membership: `IsSeparatingVertexOn E S v` supplies
`a, b ∈ S` and `SeparatesWithin E S v a b`, which in turn supplies a walk `W : a → b`
whose entire support lies in `S`, while the separating clause says *every* such walk
visits `v`.  Applying the separating clause to `W` gives `v ∈ W.support ⊆ S`. -/
theorem mem_of_isSeparatingVertexOn {E : V → V → Prop} {S : Finset V} {v : V}
    (h : IsSeparatingVertexOn E S v) : v ∈ S := by
  obtain ⟨a, haS, b, hbS, hav, hbv, hexW, hsep⟩ := h
  obtain ⟨W, hW⟩ := hexW
  have hvW : v ∈ W.support := hsep W hW
  exact hW v hvW

/-- Specialised to the ambient set of an end block. -/
theorem mem_ambient_of_isSeparatingVertexOn {E : V → V → Prop} {T : Finset V} {v : V}
    (h : IsSeparatingVertexOn E T v) : v ∈ T :=
  mem_of_isSeparatingVertexOn h

/-- Nonseparability says more: no vertex of `S` separates the graph induced on `S`. -/
theorem not_isSeparatingVertexOn_on_of_isNonseparableOn {E : V → V → Prop}
    {S : Finset V} (h : IsNonseparableOn E S) {v : V} (hv : v ∈ S) :
    ¬ IsSeparatingVertexOn E S v :=
  h.2 v hv

end CRNT

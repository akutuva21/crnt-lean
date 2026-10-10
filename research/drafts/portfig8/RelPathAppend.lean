import CRNT.Graph.RelPath

/-!
# Gluing directed paths end to end

`RelPath.concat` grows a path by one fresh vertex; the ear decomposition of Shinar–Feinberg
(Props. A.1 and A.3) needs the other shape. `RelPath.appendPath` glues a path `P` to the
front of a path `Q` when `P` ends where `Q` starts: the result has `k + l` steps, keeping
`P`'s vertices at positions `0..k` and reading `Q`'s tail at positions `k+1..k+l`, so the
shared vertex `P k = Q 0` deliberately appears twice. Every step of the result is a step of
`P` or of `Q`; the junction step is `Q`'s first step after transporting `P`'s last vertex
onto `Q`'s first via `hlast`.

`appendPath_noRepeat` is the fact the cycle-extraction consumer needs: with both pieces
injective and `P`'s last vertex absent from `Q` past position 0, no two *consecutive*
vertices of the glued path coincide.
-/

namespace CRNT

namespace RelPath

/-- Append the vertices of `Q` to `P`, identifying `P`'s last vertex with `Q`'s first
(hypothesis `hlast`).  The result has `k + l` steps; positions `0..k` read `P`, positions
`k+1..k+l` read `Q`'s tail. -/
def appendPath {V : Type*} {E : V → V → Prop} {T : Finset V} {k l : ℕ}
    (P : RelPath E T k) (Q : RelPath E T l)
    (hlast : P.vertex ⟨k, by omega⟩ = Q.vertex ⟨0, by omega⟩) : RelPath E T (k + l) where
  vertex := fun i => if h : i.1 ≤ k then P.vertex ⟨i.1, by omega⟩
    else Q.vertex ⟨i.1 - k, by omega⟩
  mem := by
    intro i
    by_cases h : i.1 ≤ k
    · rw [dif_pos h]; exact P.mem _
    · rw [dif_neg h]; exact Q.mem _
  step := by
    intro i
    have hcs : (Fin.castSucc i).1 = i.1 := rfl
    have hsu : (i.succ).1 = i.1 + 1 := rfl
    by_cases h : i.1 < k
    · -- strictly inside P: both endpoints are original
      have h1 : (if hc : (Fin.castSucc i).1 ≤ k
            then P.vertex ⟨(Fin.castSucc i).1, by omega⟩
            else Q.vertex ⟨(Fin.castSucc i).1 - k, by omega⟩)
          = P.vertex ⟨i.1, by omega⟩ := by
        rw [dif_pos (show (Fin.castSucc i).1 ≤ k by rw [hcs]; omega)]
        rfl
      have h2 : (if hc : (i.succ).1 ≤ k
            then P.vertex ⟨(i.succ).1, by omega⟩
            else Q.vertex ⟨(i.succ).1 - k, by omega⟩)
          = P.vertex ⟨i.1 + 1, by omega⟩ := by
        rw [dif_pos (show (i.succ).1 ≤ k by rw [hsu]; omega)]
        rfl
      show E (if hc : (Fin.castSucc i).1 ≤ k then _ else _)
        (if hc : (i.succ).1 ≤ k then _ else _)
      rw [h1, h2]
      have hst := P.step ⟨i.1, by omega⟩
      have e1 : (Fin.castSucc (⟨i.1, by omega⟩ : Fin k)) = (⟨i.1, by omega⟩ : Fin (k + 1)) :=
        Fin.ext rfl
      have e2 : ((⟨i.1, by omega⟩ : Fin k).succ) = (⟨i.1 + 1, by omega⟩ : Fin (k + 1)) :=
        Fin.ext rfl
      rw [e1, e2] at hst
      exact hst
    · by_cases hb : i.1 = k
      · -- the junction: the step is Q's first step, with P's end re-identified
        have hsum : i.1 + 1 - k = 1 := by omega
        have h1 : (if hc : (Fin.castSucc i).1 ≤ k
              then P.vertex ⟨(Fin.castSucc i).1, by omega⟩
              else Q.vertex ⟨(Fin.castSucc i).1 - k, by omega⟩)
            = P.vertex ⟨k, by omega⟩ := by
          rw [dif_pos (show (Fin.castSucc i).1 ≤ k by rw [hcs]; omega)]
          exact congrArg P.vertex (Fin.ext hb)
        have h2 : (if hc : (i.succ).1 ≤ k
              then P.vertex ⟨(i.succ).1, by omega⟩
              else Q.vertex ⟨(i.succ).1 - k, by omega⟩)
            = Q.vertex ⟨1, by omega⟩ := by
          rw [dif_neg (show ¬ (i.succ).1 ≤ k by rw [hsu]; omega)]
          exact congrArg Q.vertex (Fin.ext hsum)
        show E (if hc : (Fin.castSucc i).1 ≤ k then _ else _)
          (if hc : (i.succ).1 ≤ k then _ else _)
        rw [h1, h2, hlast]
        exact Q.step ⟨0, by omega⟩
      · -- strictly inside Q: both endpoints are original
        have hik : k < i.1 := by omega
        have h1 : (if hc : (Fin.castSucc i).1 ≤ k
              then P.vertex ⟨(Fin.castSucc i).1, by omega⟩
              else Q.vertex ⟨(Fin.castSucc i).1 - k, by omega⟩)
            = Q.vertex ⟨i.1 - k, by omega⟩ := by
          rw [dif_neg (show ¬ (Fin.castSucc i).1 ≤ k by rw [hcs]; omega)]
          rfl
        have h2 : (if hc : (i.succ).1 ≤ k
              then P.vertex ⟨(i.succ).1, by omega⟩
              else Q.vertex ⟨(i.succ).1 - k, by omega⟩)
            = Q.vertex ⟨i.1 + 1 - k, by omega⟩ := by
          rw [dif_neg (show ¬ (i.succ).1 ≤ k by rw [hsu]; omega)]
          rfl
        show E (if hc : (Fin.castSucc i).1 ≤ k then _ else _)
          (if hc : (i.succ).1 ≤ k then _ else _)
        rw [h1, h2]
        have hst := Q.step ⟨i.1 - k, by omega⟩
        have e1 : (Fin.castSucc (⟨i.1 - k, by omega⟩ : Fin l))
            = (⟨i.1 - k, by omega⟩ : Fin (l + 1)) := Fin.ext rfl
        have e2 : ((⟨i.1 - k, by omega⟩ : Fin l).succ)
            = (⟨i.1 - k + 1, by omega⟩ : Fin (l + 1)) := Fin.ext rfl
        rw [e1, e2] at hst
        have e3 : (⟨i.1 - k + 1, by omega⟩ : Fin (l + 1)) = ⟨i.1 + 1 - k, by omega⟩ :=
          Fin.ext (by show i.1 - k + 1 = i.1 + 1 - k; omega)
        rw [e3] at hst
        exact hst

/-- The vertex function of `appendPath`: positions up to `k` read `P`, later positions
read `Q` shifted by `k`. -/
@[simp] theorem appendPath_vertex {V : Type*} {E : V → V → Prop} {T : Finset V} {k l : ℕ}
    (P : RelPath E T k) (Q : RelPath E T l)
    (hlast : P.vertex ⟨k, by omega⟩ = Q.vertex ⟨0, by omega⟩) (i : Fin (k + l + 1)) :
    (P.appendPath Q hlast).vertex i =
      if h : i.1 ≤ k then P.vertex ⟨i.1, by omega⟩
      else Q.vertex ⟨i.1 - k, by omega⟩ := rfl

/-- The glued path starts where `P` starts. -/
theorem appendPath_start {V : Type*} {E : V → V → Prop} {T : Finset V} {k l : ℕ}
    (P : RelPath E T k) (Q : RelPath E T l)
    (hlast : P.vertex ⟨k, by omega⟩ = Q.vertex ⟨0, by omega⟩) :
    (P.appendPath Q hlast).vertex ⟨0, by omega⟩ = P.vertex ⟨0, by omega⟩ := by
  rw [appendPath_vertex]
  exact dif_pos (Nat.zero_le k)

/-- The glued path ends where `Q` ends.  When `l = 0` this is exactly `hlast`. -/
theorem appendPath_end {V : Type*} {E : V → V → Prop} {T : Finset V} {k l : ℕ}
    (P : RelPath E T k) (Q : RelPath E T l)
    (hlast : P.vertex ⟨k, by omega⟩ = Q.vertex ⟨0, by omega⟩) :
    (P.appendPath Q hlast).vertex ⟨k + l, by omega⟩ = Q.vertex ⟨l, by omega⟩ := by
  rw [appendPath_vertex]
  by_cases h : k + l ≤ k
  · rw [dif_pos h]
    have hl : l = 0 := by omega
    subst hl
    exact hlast
  · rw [dif_neg h]
    exact congrArg Q.vertex (Fin.ext (by show k + l - k = l; omega))

/-- If `P` and `Q` each list their vertices without repetition and `P`'s last vertex does
not recur on `Q` past its first position, then no two consecutive vertices of the glued
path coincide. -/
theorem appendPath_noRepeat {V : Type*} {E : V → V → Prop} {T : Finset V} {k l : ℕ}
    (P : RelPath E T k) (Q : RelPath E T l)
    (hlast : P.vertex ⟨k, by omega⟩ = Q.vertex ⟨0, by omega⟩)
    (hinjP : Function.Injective P.vertex) (hinjQ : Function.Injective Q.vertex)
    (hsep : ∀ j : Fin (l + 1), 0 < j.1 → P.vertex ⟨k, by omega⟩ ≠ Q.vertex j) :
    ∀ i : Fin (k + l),
      (P.appendPath Q hlast).vertex (Fin.castSucc i) ≠
        (P.appendPath Q hlast).vertex i.succ := by
  intro i hcon
  have hcs : (Fin.castSucc i).1 = i.1 := rfl
  have hsu : (i.succ).1 = i.1 + 1 := rfl
  rw [appendPath_vertex, appendPath_vertex] at hcon
  by_cases h : i.1 + 1 ≤ k
  · -- both endpoints lie strictly inside P
    rw [dif_pos (show (Fin.castSucc i).1 ≤ k by rw [hcs]; omega),
      dif_pos (show (i.succ).1 ≤ k by rw [hsu]; omega)] at hcon
    have heq : (⟨(Fin.castSucc i).1, by rw [hcs]; omega⟩ : Fin (k + 1)) =
      ⟨(i.succ).1, by rw [hsu]; omega⟩ := hinjP hcon
    have hvals : i.1 = i.1 + 1 := congrArg Fin.val heq
    omega
  · by_cases hle : i.1 ≤ k
    · -- the junction: P's last vertex is Q's first
      have hk : i.1 = k := by omega
      have hsum : i.1 + 1 - k = 1 := by omega
      rw [dif_pos (show (Fin.castSucc i).1 ≤ k by rw [hcs]; omega),
        dif_neg (show ¬ (i.succ).1 ≤ k by rw [hsu]; omega)] at hcon
      rw [show (⟨(Fin.castSucc i).1, by rw [hcs]; omega⟩ : Fin (k + 1)) = ⟨k, by omega⟩ from
        Fin.ext hk] at hcon
      rw [show (⟨(i.succ).1 - k, by omega⟩ : Fin (l + 1)) = ⟨1, by omega⟩ from
        Fin.ext hsum] at hcon
      exact absurd hcon (hsep ⟨1, by omega⟩ (by show 0 < 1; omega))
    · -- both endpoints lie in Q past the junction
      rw [dif_neg (show ¬ (Fin.castSucc i).1 ≤ k by rw [hcs]; omega),
        dif_neg (show ¬ (i.succ).1 ≤ k by rw [hsu]; omega)] at hcon
      have heq : (⟨(Fin.castSucc i).1 - k, by omega⟩ : Fin (l + 1)) =
        ⟨(i.succ).1 - k, by omega⟩ := hinjQ hcon
      have hvals : i.1 - k = i.1 + 1 - k := congrArg Fin.val heq
      omega

end RelPath

end CRNT

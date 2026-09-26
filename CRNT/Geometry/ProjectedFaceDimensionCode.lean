import Mathlib.Data.Fin.Basic

/-!
# Binary codes for dimensions along a projection chain

Section 7.2 of Craciun's construction assigns a bit to each one-coordinate projection: the bit is
`1` exactly when that projection lowers the face dimension by one. This file isolates the finite
combinatorics of that encoding. A `FaceProjectionDimensionProfile` records the dimensions along the
projection chain and the required zero-or-one step bound; its code has one bit per projection, and
the number of `1` bits recovers the final face dimension.

The geometric proof that a given chain of faces supplies such a profile is a separate obligation.
-/

namespace CRNT
namespace ZeroSeparatingInduction

/-- The binary letter for the projection step from `Fin (n + 1)` coordinates to `Fin n`
coordinates. It is `true` exactly when the dimension increases by one in the reverse direction,
equivalently when the projection drops dimension by one. -/
def faceProjectionDimensionLetter {n : ℕ} (dimension : Fin (n + 1) → ℕ) (j : Fin n) : Bool :=
  decide (dimension j.succ = dimension j.castSucc + 1)

/-- The binary word of successive dimension changes, in coordinate order. -/
def faceProjectionDimensionWord : (n : ℕ) → (Fin (n + 1) → ℕ) → List Bool
  | 0, _ => []
  | n + 1, dimension =>
      faceProjectionDimensionWord n (fun j => dimension j.castSucc) ++
        [faceProjectionDimensionLetter dimension (Fin.last n)]

/-- Count the `true` letters in a dimension code. -/
def faceProjectionDimensionWordWeight : List Bool → ℕ
  | [] => 0
  | true :: word => faceProjectionDimensionWordWeight word + 1
  | false :: word => faceProjectionDimensionWordWeight word

@[simp]
theorem faceProjectionDimensionWordWeight_append_singleton (word : List Bool) (bit : Bool) :
    faceProjectionDimensionWordWeight (word ++ [bit]) =
      faceProjectionDimensionWordWeight word + (if bit then 1 else 0) := by
  induction word with
  | nil => cases bit <;> rfl
  | cons head tail ih =>
      cases head
      · simp only [List.cons_append, faceProjectionDimensionWordWeight]
        exact ih
      · simp only [List.cons_append, faceProjectionDimensionWordWeight]
        rw [ih]
        omega

/-- A profile of the dimensions of one face under successive coordinate projections. The
`dimension_zero` field records that the terminal projection lands in a point, and `step` expresses
the fact that deleting one coordinate either preserves dimension or lowers it by one. -/
structure FaceProjectionDimensionProfile (n : ℕ) where
  dimension : Fin (n + 1) → ℕ
  dimension_zero : dimension 0 = 0
  step : ∀ j : Fin n,
    dimension j.castSucc ≤ dimension j.succ ∧
      dimension j.succ ≤ dimension j.castSucc + 1

/-- The face word has one letter for each projection. -/
theorem faceProjectionDimensionWord_length {n : ℕ}
    (dimension : Fin (n + 1) → ℕ) :
    (faceProjectionDimensionWord n dimension).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [faceProjectionDimensionWord, ih]

/-- The number of `1` bits in the projection word is the dimension of the original face. -/
theorem FaceProjectionDimensionProfile.dimension_eq_wordWeight {n : ℕ}
    (profile : FaceProjectionDimensionProfile n) :
    profile.dimension (Fin.last n) =
      faceProjectionDimensionWordWeight
        (faceProjectionDimensionWord n profile.dimension) := by
  induction n with
  | zero =>
      simp [faceProjectionDimensionWord, faceProjectionDimensionWordWeight,
        profile.dimension_zero]
  | succ n ih =>
      let initial : FaceProjectionDimensionProfile n :=
        { dimension := fun j => profile.dimension j.castSucc
          dimension_zero := by simpa using profile.dimension_zero
          step := by
            intro j
            simpa using profile.step j.castSucc }
      have hprefix := ih initial
      have hprefix' :
          profile.dimension (Fin.castSucc (Fin.last n)) =
            faceProjectionDimensionWordWeight
              (faceProjectionDimensionWord n
                (fun j => profile.dimension j.castSucc)) := by
        simpa [initial] using hprefix
      let prev := profile.dimension (Fin.castSucc (Fin.last n))
      let next := profile.dimension (Fin.last (n + 1))
      let bit := decide (next = prev + 1)
      have hstepCases : next = prev ∨ next = prev + 1 := by
        rcases profile.step (Fin.last n) with ⟨hlo, hhi⟩
        have hlo' : prev ≤ next := by
          simpa [prev, next, Fin.succ_last] using hlo
        have hhi' : next ≤ prev + 1 := by
          simpa [prev, next, Fin.succ_last] using hhi
        omega
      have hnext : next = prev + (if bit then 1 else 0) := by
        rcases hstepCases with hEq | hSucc
        · simp [bit, hEq]
        · simp [bit, hSucc]
      have hword :
          faceProjectionDimensionWord (n + 1) profile.dimension =
            faceProjectionDimensionWord n (fun j => profile.dimension j.castSucc) ++ [bit] := by
        simp [faceProjectionDimensionWord, faceProjectionDimensionLetter, bit, prev, next]
      rw [hword, faceProjectionDimensionWordWeight_append_singleton, ← hprefix']
      simpa [next, prev] using hnext

end ZeroSeparatingInduction
end CRNT

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

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

/-- Projection from an `(n + 1)`-coordinate space to its first `n` coordinates. -/
def forgetLastCoordinate (n : ℕ) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun x i := x i.castSucc
  map_add' x y := by funext i; rfl
  map_smul' c x := by funext i; rfl

/-- The coordinate projection is onto: append zero to any target tuple. -/
theorem forgetLastCoordinate_surjective (n : ℕ) :
    Function.Surjective (forgetLastCoordinate n) := by
  intro x
  refine ⟨Fin.snoc x 0, ?_⟩
  funext i
  simp [forgetLastCoordinate]

/-- The affine map underlying `forgetLastCoordinate`. -/
def forgetLastAffine (n : ℕ) :
    (Fin (n + 1) → ℝ) →ᵃ[ℝ] (Fin n → ℝ) :=
  AffineMap.mk' (forgetLastCoordinate n) (forgetLastCoordinate n) 0 (by
    intro x
    funext i
    simp [forgetLastCoordinate])

/-- The section of the homogenizing hyperplane `x₀ = 1`, identified with the affine space of the
remaining coordinates. -/
def homogeneousLift (n : ℕ) (x : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.cons 1 x

/-- The affine chart embedding is injective. -/
theorem homogeneousLift_injective (n : ℕ) : Function.Injective (homogeneousLift n) := by
  intro x y h
  funext i
  have hi := congrFun h i.succ
  simpa [homogeneousLift] using hi

/-- Coordinate projection commutes with taking the normalized section of a projected cone. -/
theorem forgetLastCoordinate_homogeneousLift (n : ℕ) (x : Fin (n + 1) → ℝ) :
    forgetLastCoordinate (n + 1) (homogeneousLift (n + 1) x) =
      homogeneousLift n (forgetLastCoordinate n x) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [forgetLastCoordinate, homogeneousLift]
  ·
    have hi : (j.succ).castSucc = (j.castSucc).succ := by
      apply Fin.ext
      simp
    simp [forgetLastCoordinate, homogeneousLift, hi]

/-- The affine face cut out of a cone by the homogenizing hyperplane `x₀ = 1`. -/
def normalizedConeSection {n : ℕ} (C : Set (Fin (n + 1) → ℝ)) : Set (Fin n → ℝ) :=
  {x | homogeneousLift n x ∈ C}

/-- Slicing a cone by `x₀ = 1` commutes with deleting the last coordinate. -/
theorem forgetLastAffine_image_normalizedConeSection (n : ℕ)
    (C : Set (Fin (n + 2) → ℝ)) :
    forgetLastAffine n '' normalizedConeSection (n := n + 1) C =
      normalizedConeSection (n := n) (forgetLastCoordinate (n + 1) '' C) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyC : homogeneousLift (n + 1) y ∈ C := hy
    change homogeneousLift n (forgetLastCoordinate n y) ∈
      forgetLastCoordinate (n + 1) '' C
    rw [← forgetLastCoordinate_homogeneousLift]
    exact Set.mem_image_of_mem (forgetLastCoordinate (n + 1)) hyC
  · intro hx
    change homogeneousLift n x ∈ forgetLastCoordinate (n + 1) '' C at hx
    rcases (Set.mem_image (forgetLastCoordinate (n + 1)) C
      (homogeneousLift n x)).mp hx with ⟨z, hz, hzx⟩
    let y : Fin (n + 1) → ℝ := fun i => z i.succ
    have hz0 : z 0 = 1 := by
      have hzero := congrFun hzx 0
      simpa [forgetLastCoordinate, homogeneousLift] using hzero
    have hyz : homogeneousLift (n + 1) y = z := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [homogeneousLift, y, hz0]
      ·
        rfl
    have hyC : homogeneousLift (n + 1) y ∈ C := by
      rw [hyz]
      exact hz
    have hcoords : forgetLastCoordinate n y = x := by
      apply homogeneousLift_injective n
      calc
        homogeneousLift n (forgetLastCoordinate n y) =
            forgetLastCoordinate (n + 1) (homogeneousLift (n + 1) y) :=
              (forgetLastCoordinate_homogeneousLift n y).symm
        _ = forgetLastCoordinate (n + 1) z := by rw [hyz]
        _ = homogeneousLift n x := hzx
    refine ⟨y, hyC, ?_⟩
    simpa [forgetLastAffine] using hcoords

/-- Dropping one coordinate lowers the dimension of any finite-dimensional subspace by at most
one. The kernel of the restricted projection embeds into the one-dimensional kernel of the ambient
coordinate projection. -/
theorem finrank_map_forgetLastCoordinate_bounds (n : ℕ)
    (U : Submodule ℝ (Fin (n + 1) → ℝ)) :
    Module.finrank ℝ (U.map (forgetLastCoordinate n)) ≤ Module.finrank ℝ U ∧
      Module.finrank ℝ U ≤ Module.finrank ℝ (U.map (forgetLastCoordinate n)) + 1 := by
  constructor
  · exact Submodule.finrank_map_le (forgetLastCoordinate n) U
  · let f := forgetLastCoordinate n
    let g := f.domRestrict U
    have hRank :
        Module.finrank ℝ (U.map f) + Module.finrank ℝ (LinearMap.ker g) =
          Module.finrank ℝ U := by
      have hRank' := LinearMap.finrank_range_add_finrank_ker (f.domRestrict U)
      rw [LinearMap.range_domRestrict] at hRank'
      simpa [g] using hRank'
    have hMapKer : (LinearMap.ker g).map U.subtype ≤ LinearMap.ker f := by
      intro x hx
      rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
      apply LinearMap.mem_ker.mpr
      have hy' : g y = 0 := hy
      simpa [g, f, LinearMap.domRestrict] using hy'
    have hKer : Module.finrank ℝ (LinearMap.ker g) ≤ 1 := by
      calc
        Module.finrank ℝ (LinearMap.ker g) =
            Module.finrank ℝ ((LinearMap.ker g).map U.subtype) := by
              symm
              exact Submodule.finrank_map_subtype_eq U (LinearMap.ker g)
        _ ≤ Module.finrank ℝ (LinearMap.ker f) := Submodule.finrank_mono hMapKer
        _ = 1 := by
          have hRange : Module.finrank ℝ (LinearMap.range f) = n := by
            rw [LinearMap.range_eq_top.mpr (forgetLastCoordinate_surjective n)]
            simp
          have hDomain : Module.finrank ℝ (Fin (n + 1) → ℝ) = n + 1 := by
            simp
          have hRank' := LinearMap.finrank_range_add_finrank_ker f
          rw [hRange, hDomain] at hRank'
          omega
    have hRankFinal :
        Module.finrank ℝ (U.map (forgetLastCoordinate n)) +
          Module.finrank ℝ
            (LinearMap.ker ((forgetLastCoordinate n).domRestrict U)) =
          Module.finrank ℝ U := by
      simpa [f, g] using hRank
    have hKerFinal :
        Module.finrank ℝ
          (LinearMap.ker ((forgetLastCoordinate n).domRestrict U)) ≤ 1 := by
      simpa [f, g] using hKer
    omega

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

/-- A chain of direction spaces for the affine hulls of successively projected faces. For a
projected subdivision face chain, these spaces are the directions of its affine hulls, and each
stage projects onto the preceding stage. -/
structure CoordinateProjectionSubspaceChain (n : ℕ) where
  subspace : (j : Fin (n + 1)) → Submodule ℝ (Fin j.val → ℝ)
  projectedSubspace : ∀ j : Fin n,
    (subspace j.succ).map (forgetLastCoordinate j.val) = subspace j.castSucc

/-- A chain of nonempty affine faces, each the coordinate projection of the next face. -/
structure CoordinateProjectedFaceChain (n : ℕ) where
  face : (j : Fin (n + 1)) → Set (Fin j.val → ℝ)
  face_nonempty : ∀ j, (face j).Nonempty
  projectedFace : ∀ j : Fin n,
    forgetLastAffine j.val '' face j.succ = face j.castSucc

/-- A chain of cones in homogeneous coordinate spaces, where each cone projects onto the
preceding cone and each normalized section is nonempty. -/
structure CoordinateProjectedConeChain (n : ℕ) where
  cone : (j : Fin (n + 1)) → Set (Fin (j.val + 1) → ℝ)
  projectedCone : ∀ j : Fin n,
    forgetLastCoordinate (j.val + 1) '' cone j.succ = cone j.castSucc
  section_nonempty : ∀ j, (normalizedConeSection (cone j)).Nonempty

/-- Normalized sections of an exactly projected cone chain form a projected affine-face chain. -/
def CoordinateProjectedConeChain.toFaceChain {n : ℕ}
    (chain : CoordinateProjectedConeChain n) : CoordinateProjectedFaceChain n := by
  refine ⟨fun j => normalizedConeSection (chain.cone j), chain.section_nonempty, ?_⟩
  intro j
  have h := forgetLastAffine_image_normalizedConeSection j.val (chain.cone j.succ)
  rw [chain.projectedCone j] at h
  exact h

/-- The finranks along a coordinate-projection subspace chain form a valid face-dimension profile.
The coordinate projection rank bound proves each dimension step is zero or one. -/
noncomputable def CoordinateProjectionSubspaceChain.dimensionProfile {n : ℕ}
    (chain : CoordinateProjectionSubspaceChain n) : FaceProjectionDimensionProfile n := by
  refine ⟨fun j => Module.finrank ℝ (chain.subspace j), ?_, ?_⟩
  · have hle := Submodule.finrank_le (chain.subspace (0 : Fin (n + 1)))
    change Module.finrank ℝ (chain.subspace (0 : Fin (n + 1))) ≤
      Module.finrank ℝ (Fin 0 → ℝ) at hle
    have hdim : Module.finrank ℝ (Fin 0 → ℝ) = 0 := by simp
    rw [hdim] at hle
    omega
  · intro j
    have hstep :=
      finrank_map_forgetLastCoordinate_bounds j.val (chain.subspace j.succ)
    rw [chain.projectedSubspace j] at hstep
    exact hstep

/-- Taking affine-hull directions sends an exactly projected face chain to a
`CoordinateProjectionSubspaceChain`. -/
noncomputable def CoordinateProjectedFaceChain.toDirectionSubspaceChain {n : ℕ}
    (chain : CoordinateProjectedFaceChain n) : CoordinateProjectionSubspaceChain n := by
  refine ⟨fun j => (affineSpan ℝ (chain.face j)).direction, ?_⟩
  intro j
  have hface :
      (affineSpan ℝ (chain.face j.succ)).map (forgetLastAffine j.val) =
        affineSpan ℝ (chain.face j.castSucc) := by
    rw [AffineSubspace.map_span, chain.projectedFace j]
  have hdirection := congrArg AffineSubspace.direction hface
  simpa [AffineSubspace.map_direction, forgetLastAffine] using hdirection

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

/-- For a coordinate-projected subspace chain, the binary word of dimension drops has one `1` for
each dimension gained from the zero-dimensional base. -/
theorem CoordinateProjectionSubspaceChain.dimension_eq_wordWeight {n : ℕ}
    (chain : CoordinateProjectionSubspaceChain n) :
    Module.finrank ℝ (chain.subspace (Fin.last n)) =
      faceProjectionDimensionWordWeight
        (faceProjectionDimensionWord n (fun j => Module.finrank ℝ (chain.subspace j))) := by
  exact chain.dimensionProfile.dimension_eq_wordWeight

/-- The dimension word of an exactly projected affine-face chain records its affine-hull
dimensions, with one `1` for every dimension gained above the point projection. -/
theorem CoordinateProjectedFaceChain.dimension_eq_wordWeight {n : ℕ}
    (chain : CoordinateProjectedFaceChain n) :
    Module.finrank ℝ ((affineSpan ℝ (chain.face (Fin.last n))).direction) =
      faceProjectionDimensionWordWeight
        (faceProjectionDimensionWord n
          (fun j => Module.finrank ℝ ((affineSpan ℝ (chain.face j)).direction))) := by
  exact chain.toDirectionSubspaceChain.dimension_eq_wordWeight

/-- The dimension code of a normalized cone chain counts the affine-hull dimension of its final
section. -/
theorem CoordinateProjectedConeChain.dimension_eq_wordWeight {n : ℕ}
    (chain : CoordinateProjectedConeChain n) :
    Module.finrank ℝ
        ((affineSpan ℝ (normalizedConeSection (chain.cone (Fin.last n)))).direction) =
      faceProjectionDimensionWordWeight
        (faceProjectionDimensionWord n
          (fun j => Module.finrank ℝ
            ((affineSpan ℝ (normalizedConeSection (chain.cone j))).direction))) := by
  exact chain.toFaceChain.dimension_eq_wordWeight

end ZeroSeparatingInduction
end CRNT

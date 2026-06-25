import CRNT.Deficiency.Colinearity

/-!
# Colinearity classes as a quotient (Advanced Deficiency Algorithm)

The Advanced Deficiency Algorithm groups reactions into **colinearity classes** — maximal sets of
reactions whose reaction vectors lie on a common line through the origin (Ji, *Uniqueness of
equilibria for complex chemical reaction networks*, Ohio State University, 2011).

Among reactions with nonzero reaction vector, colinearity is reflexive, symmetric, and transitive,
so it is a genuine equivalence relation. This module packages it as a `Setoid` on the subtype of
nonzero reactions and defines the colinearity classes as the corresponding `Quotient`, replacing
the ad-hoc "constant on the relation" side condition with an honest quotient.

A colinearity class carries no intrinsic orientation: collinear vectors may point in opposite
directions. The orientation `sign` of a class is the choice between the two half-lines. The scalar
`a` relating two collinear nonzero vectors `v, w` (with `w = a • v`) is nonzero, and the dichotomy
`0 < a ∨ a < 0` records which half-line `w` lies on relative to `v`.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Deficiency.Colinearity`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A **nonzero reaction** of `N`: a reaction whose reaction vector is nonzero. The colinearity
relation is an equivalence relation precisely on these reactions. -/
def NonzeroReaction (N : Network S) : Type := {r : N.R // N.reactionVector r ≠ 0}

namespace NonzeroReaction

/-- The underlying reaction index. -/
def val {N : Network S} (r : N.NonzeroReaction) : N.R := r.1

/-- The reaction vector of a nonzero reaction is nonzero. -/
theorem reactionVector_ne_zero {N : Network S} (r : N.NonzeroReaction) :
    N.reactionVector r.val ≠ 0 := r.2

/-- Colinearity is reflexive on nonzero reactions. -/
theorem colinear_refl {N : Network S} (r : N.NonzeroReaction) :
    N.ColinearReactions r.val r.val := ColinearReactions.refl _

/-- Colinearity is symmetric on nonzero reactions: the second reaction's vector is nonzero by
construction, so `ColinearReactions.symm` applies. -/
theorem colinear_symm {N : Network S} {r r' : N.NonzeroReaction}
    (h : N.ColinearReactions r.val r'.val) : N.ColinearReactions r'.val r.val :=
  ColinearReactions.symm r'.reactionVector_ne_zero h

/-- Colinearity is transitive on nonzero reactions. -/
theorem colinear_trans {N : Network S} {r r' r'' : N.NonzeroReaction}
    (h₁ : N.ColinearReactions r.val r'.val) (h₂ : N.ColinearReactions r'.val r''.val) :
    N.ColinearReactions r.val r''.val := ColinearReactions.trans h₁ h₂

end NonzeroReaction

/-- The colinearity **equivalence relation** on the nonzero reactions of `N`, packaged as a
`Setoid`. Two nonzero reactions are related when their reaction vectors are collinear. -/
def colinearitySetoid (N : Network S) : Setoid N.NonzeroReaction where
  r r r' := N.ColinearReactions r.val r'.val
  iseqv :=
    { refl := fun r => NonzeroReaction.colinear_refl r
      symm := fun h => NonzeroReaction.colinear_symm h
      trans := fun h₁ h₂ => NonzeroReaction.colinear_trans h₁ h₂ }

/-- The **colinearity classes** of `N`: the quotient of the nonzero reactions by colinearity. Each
class is a maximal collinear set of nonzero reaction vectors. -/
def colinearityClasses (N : Network S) : Type :=
  Quotient N.colinearitySetoid

/-- The colinearity class of a nonzero reaction. -/
def colinearityClass (N : Network S) (r : N.NonzeroReaction) : N.colinearityClasses :=
  Quotient.mk N.colinearitySetoid r

/-- Two nonzero reactions have the same colinearity class iff their reaction vectors are collinear.
This is the quotient form of the relation. -/
theorem colinearityClass_eq {N : Network S} {r r' : N.NonzeroReaction} :
    N.colinearityClass r = N.colinearityClass r' ↔ N.ColinearReactions r.val r'.val :=
  Quotient.eq

end Network

/-!
## Orientation of a colinearity class

Within a class, collinear nonzero vectors are related by a nonzero scalar, and the sign of that
scalar splits the line through the origin into two half-lines — the two orientations of the class.
-/

variable {S : Type}

/-- The scalar relating two collinear nonzero vectors is **nonzero**. If `w = a • v` with `w ≠ 0`,
then `a ≠ 0` (and `v ≠ 0`). -/
theorem ColinearVec.scalar_ne_zero {v w : S → ℝ} (hw : w ≠ 0) {a : ℝ} (ha : w = a • v) :
    a ≠ 0 := by
  rintro rfl
  rw [zero_smul] at ha
  exact hw ha

/-- **Orientation dichotomy.** The scalar `a` relating two collinear nonzero vectors (`w = a • v`,
`w ≠ 0`) is either strictly positive or strictly negative; that is, `w` lies on one of the two
half-lines determined by `v`. -/
theorem ColinearVec.orientation_dichotomy {v w : S → ℝ} (hw : w ≠ 0) {a : ℝ} (ha : w = a • v) :
    0 < a ∨ a < 0 :=
  (lt_or_gt_of_ne (ColinearVec.scalar_ne_zero hw ha)).symm

end CRNT

import CRNT.Stoich.Subspace

/-!
# Colinearity classes of reactions (Advanced Deficiency Algorithm, §1.7)

The Advanced Deficiency Algorithm refines the Deficiency One Algorithm by grouping the reactions
into **colinearity classes** — maximal sets of reactions whose reaction vectors are collinear (lie
on a common line through the origin) — and running a DOA-like construction inside each, coordinated
across classes by the coplanarity relations (Ji, *Uniqueness of equilibria for complex chemical
reaction networks*, Ohio State University, 2011, §1.7).

Collinearity of vectors `v, w` is recorded as `w` being a scalar multiple of `v`:

* `ColinearVec v w` — `∃ a, w = a • v`. Reflexive and transitive unconditionally; symmetric once the
  target vector is nonzero (so it is an equivalence relation among nonzero vectors, the regime of the
  algorithm's *nonzero* colinearity classes).
* `Network.ColinearReactions r r'` — the reaction vectors are collinear; reflexive, transitive, and
  symmetric on reactions with nonzero reaction vector.

A colinearity class carries no intrinsic orientation: collinear vectors may point oppositely, so the
algorithm's *sign* of a class is a chosen orientation, handled in the extended-system enumeration
rather than here.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Stoich.Subspace`.
-/

namespace CRNT

variable {S : Type}

/-- **Collinearity of vectors:** `w` is a scalar multiple of `v`. On nonzero vectors this is the
equivalence relation "lie on a common line through the origin". -/
def ColinearVec (v w : S → ℝ) : Prop := ∃ a : ℝ, w = a • v

/-- Collinearity is reflexive. -/
@[refl] theorem ColinearVec.refl (v : S → ℝ) : ColinearVec v v := ⟨1, (one_smul ℝ v).symm⟩

/-- Collinearity is transitive. -/
theorem ColinearVec.trans {u v w : S → ℝ} (h₁ : ColinearVec u v) (h₂ : ColinearVec v w) :
    ColinearVec u w := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  exact ⟨b * a, by rw [hb, ha, smul_smul]⟩

/-- Collinearity is symmetric once the target vector is nonzero (forcing a nonzero, invertible
scalar). -/
theorem ColinearVec.symm {v w : S → ℝ} (hw : w ≠ 0) (h : ColinearVec v w) : ColinearVec w v := by
  obtain ⟨a, ha⟩ := h
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact hw ha
  exact ⟨a⁻¹, by rw [ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]⟩

namespace Network

variable [DecidableEq S] [Fintype S]

/-- **Two reactions are colinear** when their reaction vectors lie on a common line through the
origin. -/
def ColinearReactions (N : Network S) (r r' : N.R) : Prop :=
  ColinearVec (N.reactionVector r) (N.reactionVector r')

@[refl] theorem ColinearReactions.refl {N : Network S} (r : N.R) : N.ColinearReactions r r :=
  ColinearVec.refl _

/-- Colinearity of reactions is transitive. -/
theorem ColinearReactions.trans {N : Network S} {r r' r'' : N.R}
    (h₁ : N.ColinearReactions r r') (h₂ : N.ColinearReactions r' r'') :
    N.ColinearReactions r r'' :=
  ColinearVec.trans h₁ h₂

/-- Colinearity of reactions is symmetric when the second reaction's vector is nonzero. -/
theorem ColinearReactions.symm {N : Network S} {r r' : N.R}
    (hr' : N.reactionVector r' ≠ 0) (h : N.ColinearReactions r r') : N.ColinearReactions r' r :=
  ColinearVec.symm hr' h

end Network

end CRNT

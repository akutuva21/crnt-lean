import CRNT.Dynamics.SiphonConservation
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Farkas duality for critical-siphon feasibility

The obstruction inside `Network.IsCriticalSiphon` is the *absence* of a positive conservation
law supported exactly on the siphon `P`: a nonnegative species vector `v`, strictly positive
precisely on `P`, orthogonal to every reaction vector. The nonnegativity and orthogonality
clauses alone cut out a convex set — the *conservation cone* — and the existence of a feasible
point in it is the linear-feasibility question whose dual is governed by Farkas' lemma.

`Network.conservationCone` is the closed convex cone in `EuclideanSpace ℝ S` of vectors that are
nonnegative coordinatewise and orthogonal to the stoichiometric subspace. It is a `ProperCone`,
so Mathlib's geometric Farkas' lemma (`ProperCone.hyperplane_separation'`) applies verbatim:

* `mem_conservationCone_iff_farkas` — a vector lies in the conservation cone iff every dual
  direction nonnegative on the cone is nonnegative on it (the double-dual characterization).
* `notMem_conservationCone_iff_farkas` — the strict Farkas alternative: a vector misses the cone
  iff a separating direction is nonnegative on the cone yet strictly negative on the vector.

The bridge `toEuclid_mem_conservationCone` identifies cone membership of the Euclidean image of a
species vector `v : S → ℝ` with the nonnegativity-plus-conservation clauses appearing in
`IsCriticalSiphon`, using `Network.conservationLaw_iff_mem_orthSum`. With it,
`isCriticalSiphon_iff_no_supported_cone_vector` restates `IsCriticalSiphon` so its analytic
obstruction reads as the nonexistence of a conservation-cone vector with support exactly `P` —
the form on which the Farkas characterization acts.

Deciding `IsCriticalSiphon` for a concrete network needs a computable feasibility test for the
existence of such a real vector, i.e. a rational linear-programming reduction certifying the
Farkas alternative; Mathlib v4.31 carries the geometric Farkas duality used here but not that
constructive reduction, so no `Decidable` instance is provided.

The conservation-law feasibility characterization of (non)critical siphons is from
Angeli, De Leenheer, and Sontag, *A Petri net approach to the study of persistence in chemical
reaction networks*; the duality is Farkas' lemma.

This module is **stable** and `sorry`-free. Depends on: `CRNT.Dynamics.SiphonConservation`,
`Mathlib.Analysis.Convex.Cone.InnerDual`,
`Mathlib.Analysis.InnerProductSpace.Projection.Submodule`.
-/

open scoped RealInnerProductSpace BigOperators

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

set_option maxHeartbeats 1000000 in
/-- The **conservation cone** of a network: the closed convex cone in `EuclideanSpace ℝ S` of
species vectors that are nonnegative in every coordinate and orthogonal to the stoichiometric
subspace (the span of the reaction vectors). It is the intersection of the nonnegative orthant
with the orthogonal complement of the stoichiometric subspace, so it is a `ProperCone`. -/
noncomputable def conservationCone (N : Network S) : ProperCone ℝ (EuclideanSpace ℝ S) where
  toSubmodule :=
    { carrier := {v | (∀ s, 0 ≤ v s) ∧ v ∈ (N.stoichSubspace.map toEuclid.toLinearMap)ᗮ}
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        exact ⟨by intro s; simpa using add_nonneg (ha1 s) (hb1 s), Submodule.add_mem _ ha2 hb2⟩
      zero_mem' := ⟨by intro s; simp, Submodule.zero_mem _⟩
      smul_mem' := by
        rintro c a ⟨ha1, ha2⟩
        exact ⟨by intro s; rw [PiLp.smul_apply]; exact mul_nonneg c.2 (ha1 s),
          Submodule.smul_mem _ _ ha2⟩ }
  isClosed' := by
    show IsClosed {v : EuclideanSpace ℝ S |
      (∀ s, 0 ≤ v s) ∧ v ∈ (N.stoichSubspace.map toEuclid.toLinearMap)ᗮ}
    have heq : {v : EuclideanSpace ℝ S |
          (∀ s, 0 ≤ v s) ∧ v ∈ (N.stoichSubspace.map toEuclid.toLinearMap)ᗮ}
        = (⋂ s, {v : EuclideanSpace ℝ S | 0 ≤ v s})
            ∩ ((N.stoichSubspace.map toEuclid.toLinearMap)ᗮ : Set _) := by
      ext v; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, SetLike.mem_coe]
    rw [heq]
    exact (isClosed_iInter fun s => isClosed_le continuous_const
      (PiLp.continuous_apply 2 (fun _ => ℝ) s)).inter (Submodule.isClosed_orthogonal _)

@[simp] theorem mem_conservationCone (N : Network S) (v : EuclideanSpace ℝ S) :
    v ∈ N.conservationCone ↔
      (∀ s, 0 ≤ v s) ∧ v ∈ (N.stoichSubspace.map toEuclid.toLinearMap)ᗮ := Iff.rfl

/-- **Conservation-cone membership equals the `IsCriticalSiphon` analytic clauses.** The Euclidean
image of a species vector `v : S → ℝ` lies in the conservation cone iff `v` is nonnegative and is
a conservation law — orthogonal to every reaction vector — exactly the nonnegativity and
orthogonality clauses inside `IsCriticalSiphon`. -/
theorem toEuclid_mem_conservationCone (N : Network S) (v : S → ℝ) :
    toEuclid v ∈ N.conservationCone ↔
      (∀ s, 0 ≤ v s) ∧ (∀ r : N.R, ∑ s, v s * N.reactionVector r s = 0) := by
  rw [mem_conservationCone]
  refine and_congr ?_ ?_
  · simp only [toEuclid_apply]
  · rw [N.conservationLaw_iff_mem_orthSum, orthSum_eq]; rfl

/-- **Farkas duality for the conservation cone (double-dual form).** A species vector lies in the
conservation cone iff every direction that is nonnegative on the whole cone is also nonnegative on
the vector. This is the closed-cone double-dual characterization, an instance of Farkas' lemma via
`ProperCone.hyperplane_separation'`. -/
theorem mem_conservationCone_iff_farkas (N : Network S) (b : EuclideanSpace ℝ S) :
    b ∈ N.conservationCone ↔
      ∀ y : EuclideanSpace ℝ S, (∀ x ∈ N.conservationCone, 0 ≤ ⟪x, y⟫) → 0 ≤ ⟪b, y⟫ := by
  constructor
  · intro hb y hy; exact hy b hb
  · intro h
    by_contra hb
    obtain ⟨y, hyC, hyb⟩ := N.conservationCone.hyperplane_separation' hb
    exact absurd (h y hyC) (not_le.mpr hyb)

/-- **Farkas alternative for the conservation cone (separating form).** A species vector misses the
conservation cone iff there is a separating direction nonnegative on the entire cone yet strictly
negative on the vector. This is the geometric Farkas' lemma `ProperCone.hyperplane_separation'`
read off for this cone. -/
theorem notMem_conservationCone_iff_farkas (N : Network S) (b : EuclideanSpace ℝ S) :
    b ∉ N.conservationCone ↔
      ∃ y : EuclideanSpace ℝ S, (∀ x ∈ N.conservationCone, 0 ≤ ⟪x, y⟫) ∧ ⟪b, y⟫ < 0 := by
  constructor
  · intro hb; exact N.conservationCone.hyperplane_separation' hb
  · rintro ⟨y, hyC, hyb⟩ hb; exact absurd (hyC b hb) (not_le.mpr hyb)

/-- **Critical siphon as conservation-cone infeasibility.** A nonempty siphon `P` is critical iff
no conservation-cone vector has support exactly `P`: there is no `v : S → ℝ` strictly positive
precisely on `P` whose Euclidean image lies in the conservation cone. This rewrites the analytic
obstruction in `IsCriticalSiphon` as a sign-restricted feasibility question over the conservation
cone, the object on which the Farkas characterizations act. -/
theorem isCriticalSiphon_iff_no_supported_cone_vector (N : Network S) (P : Finset S) :
    N.IsCriticalSiphon P ↔
      P.Nonempty ∧ N.IsSiphon P ∧
        ¬ ∃ v : S → ℝ, (∀ s, 0 < v s ↔ s ∈ P) ∧ toEuclid v ∈ N.conservationCone := by
  unfold IsCriticalSiphon
  refine and_congr_right (fun _ => and_congr_right (fun _ => not_congr ?_))
  constructor
  · rintro ⟨v, hnn, hsupp, hcons⟩
    exact ⟨v, hsupp, (N.toEuclid_mem_conservationCone v).mpr ⟨hnn, hcons⟩⟩
  · rintro ⟨v, hsupp, hmem⟩
    obtain ⟨hnn, hcons⟩ := (N.toEuclid_mem_conservationCone v).mp hmem
    exact ⟨v, hnn, hsupp, hcons⟩

end Network

end CRNT

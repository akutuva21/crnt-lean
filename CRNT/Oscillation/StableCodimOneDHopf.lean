import CRNT.Oscillation.FisherFullerScaling
import CRNT.Oscillation.HurwitzBordering
import CRNT.Oscillation.DHopf

/-!
# Stable-codimension-one class-II cores give D-Hopf witnesses

The second branch in the 2026 class-II definition does not require a separate spectral theorem.
If an unstable negative-feedback core has a Hurwitz principal block of codimension one, keep that
block at unit column scaling and make the one missing column sufficiently small.  The Fisher--Fuller
bordering lemma makes the full matrix Hurwitz.  At the identity scaling the original matrix still
has a strict right-half-plane eigenvalue.  The negative-feedback determinant sign gives
nonsingularity.
-/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The stable codimension-one branch directly gives a strong D-Hopf witness on the full matrix. -/
theorem strongDHopf_of_stableCodimOne
    {M : Matrix n n ℝ}
    (hneg : M.IsUnstableNegativeFeedback)
    (hcodim : M.HasStableCodimOnePrincipalSubmatrix) :
    StrongDHopfWitness M := by
  classical
  obtain ⟨I, hIcard, hIstab⟩ := hcodim
  let dI : I → ℝ := fun _ => 1
  have hdI : ∀ i, 0 < dI i := fun _ => zero_lt_one
  have hIstab' : IsHurwitzReal (M.principalSubmatrix I * Matrix.diagonal dI) := by
    have hdiag : Matrix.diagonal dI = (1 : Matrix I I ℝ) := by
      ext i j
      simp [dI, Matrix.diagonal_apply]
    simpa [hdiag] using hIstab
  have hIdet : principalDet M I ≠ 0 := by
    intro hzero
    have hsubdet : (M.principalSubmatrix I).det = 0 := by
      simpa [principalDet, principalSubmatrix] using hzero
    exact hIstab.det_ne_zero hsubdet
  have hIsign : 0 < (-1 : ℝ) ^ I.card * principalDet M I := by
    have hsubsign : 0 < (-1 : ℝ) ^ Fintype.card I * (M.principalSubmatrix I).det :=
      IsHurwitzReal.signed_det_pos hIstab
    simpa [Fintype.card_coe, principalDet, principalSubmatrix] using hsubsign
  have hfullsign : 0 < (-1 : ℝ) ^ Fintype.card n * M.det := hneg.2
  obtain ⟨eps, heps, hstable⟩ := exists_small_extension_hurwitz
    M I hIcard dI hdI hIstab' hIsign hfullsign
  refine
    { nonsingular := hneg.2.det_ne_zero
      stableDiagonal := extendCodimOneScaling I dI eps
      stablePositive := extendCodimOneScaling_pos hdI heps
      unstableDiagonal := fun _ => 1
      unstablePositive := fun _ => zero_lt_one
      stable := hstable
      unstable := ?_ }
  have hdiag : Matrix.diagonal (fun _ : n => (1 : ℝ)) = (1 : Matrix n n ℝ) := by
    ext i j
    simp [Matrix.diagonal_apply]
  simpa [hdiag] using hneg.1.1

/-- The formerly isolated stable-codimension-one class-II target is now a theorem. -/
theorem stableCodimOneClassIIImpliesStrongDHopfBlock :
    StableCodimOneClassIIImpliesStrongDHopfBlockTarget := by
  intro m _ _ M hneg hcodim
  refine ⟨Finset.univ, ?_⟩
  have hfull : M.principalSubmatrix (Finset.univ : Finset m) = M := by
    ext i j
    rfl
  rw [hfull]
  exact ⟨strongDHopf_of_stableCodimOne hneg hcodim⟩

end Matrix

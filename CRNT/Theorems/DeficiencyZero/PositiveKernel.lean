import CRNT.Dynamics.MassActionAlgebra
import CRNT.Graph.LinkageClass
import CRNT.LinearAlgebra.PerronFrobenius

/-!
# A weakly reversible network has a strictly positive kernel vector of its kinetic matrix

The abstract Perron–Frobenius theorem lives in `CRNT.LinearAlgebra.PerronFrobenius`. Here
we apply it to chemical reaction networks: rescale the kinetic matrix `A_k` to a column-
stochastic matrix `P = 1 + d⁻¹ A_k`, observe that `P` is block-diagonal across linkage
classes (so each class retains its uniform mass), and that weak reversibility makes each
class strongly connected. Perron–Frobenius then gives a fixed vector positive on every
class, i.e. a strictly positive kernel vector of `A_k`
(`weaklyReversible_exists_positive_kernelVector`).

The helper matrices `kmat`/`smat` live in the
`CRNT.PositiveKernel` namespace to avoid polluting the root.
-/

namespace CRNT

open scoped BigOperators

namespace PositiveKernel

variable {S : Type} [DecidableEq S] [Fintype S]

section
variable (N : Network S) (κ : Network.RateConstants N)

/-- Rescaling constant, strictly larger than every complex's total outflow. -/
noncomputable def dscale : ℝ := 1 + ∑ r, κ.k r

/-- The kinetic matrix `A_k`: `kmat c c'` is the coefficient of the `c'`-coordinate in
`(kineticMap κ ·) c`. -/
noncomputable def kmat : Matrix N.ComplexIdx N.ComplexIdx ℝ := fun c c' =>
  ∑ r, if N.sourceIdx r = c' then
    κ.k r * ((if N.targetIdx r = c then 1 else 0) - (if c' = c then 1 else 0)) else 0

/-- The rescaled column-stochastic matrix `P = 1 + d⁻¹ A_k`. -/
noncomputable def smat : Matrix N.ComplexIdx N.ComplexIdx ℝ :=
  1 + (dscale N κ)⁻¹ • kmat N κ

variable {N κ}

theorem dscale_pos : 0 < dscale N κ := by
  have : 0 ≤ ∑ r, κ.k r := Finset.sum_nonneg fun r _ => (κ.positive r).le
  unfold dscale; linarith

theorem sum_k_lt_dscale : ∑ r, κ.k r < dscale N κ := by unfold dscale; linarith

/-- The kinetic matrix realizes the kinetic map: `A_k.mulVec b = kineticMap κ b`. -/
theorem kmat_mulVec (b : N.ComplexIdx → ℝ) : (kmat N κ).mulVec b = N.kineticMap κ b := by
  funext c
  rw [Network.kineticMap_apply]
  show ∑ c', kmat N κ c c' * b c' = _
  simp only [kmat, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_eq_single (N.sourceIdx r)]
  · rw [if_pos rfl]; ring
  · intro c'' _ hne; rw [if_neg fun h => hne h.symm, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Column sums of the kinetic matrix vanish (it is a graph Laplacian). -/
theorem kmat_colsum (c' : N.ComplexIdx) : ∑ c, kmat N κ c c' = 0 := by
  have key : ∀ c, kmat N κ c c' = (kmat N κ).mulVec (Pi.single c' (1:ℝ)) c := by
    intro c
    show kmat N κ c c' = ∑ c'', kmat N κ c c'' * (Pi.single c' (1:ℝ) : N.ComplexIdx → ℝ) c''
    rw [Finset.sum_eq_single c']
    · rw [Pi.single_eq_same, mul_one]
    · intro c'' _ hne; rw [Pi.single_eq_of_ne hne, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [key]
  rw [kmat_mulVec]
  exact N.kineticMap_sum_eq_zero κ (Pi.single c' (1:ℝ))

/-- Off-diagonal entries of the kinetic matrix are nonnegative. -/
theorem kmat_offdiag_nonneg {c c' : N.ComplexIdx} (h : c ≠ c') : 0 ≤ kmat N κ c c' := by
  refine Finset.sum_nonneg fun r _ => ?_
  by_cases hsrc : N.sourceIdx r = c'
  · rw [if_pos hsrc, if_neg (Ne.symm h), sub_zero]
    exact mul_nonneg (κ.positive r).le (by positivity)
  · rw [if_neg hsrc]

/-- The kinetic matrix is block-diagonal across linkage classes. -/
theorem kmat_blockdiag {c c' : N.ComplexIdx}
    (h : Quotient.mk N.linkedSetoid c ≠ Quotient.mk N.linkedSetoid c') :
    kmat N κ c c' = 0 := by
  refine Finset.sum_eq_zero fun r _ => ?_
  by_cases hsrc : N.sourceIdx r = c'
  · have hcc' : c' ≠ c := by
      rintro rfl; exact h rfl
    rw [if_pos hsrc, if_neg hcc', sub_zero]
    by_cases htgt : N.targetIdx r = c
    · exfalso
      -- reaction r: source = c'.val, target = c.val, so c' and c are linked
      have hlink : N.Linked c'.val c.val := by
        have : N.DirectlyReacts c'.val c.val :=
          ⟨r, congrArg Subtype.val hsrc, congrArg Subtype.val htgt⟩
        exact Relation.ReflTransGen.single (Or.inl this)
      exact h (Quotient.sound hlink).symm
    · rw [if_neg htgt, mul_zero]
  · rw [if_neg hsrc]

/-- The diagonal of the kinetic matrix is bounded below by minus the total rate. -/
theorem kmat_diag_lb (c : N.ComplexIdx) : -(∑ r, κ.k r) ≤ kmat N κ c c := by
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun r _ => ?_
  by_cases hsrc : N.sourceIdx r = c
  · rw [if_pos hsrc, if_pos rfl]
    by_cases htgt : N.targetIdx r = c
    · rw [if_pos htgt]; have := κ.positive r; nlinarith [κ.positive r]
    · rw [if_neg htgt]; nlinarith [κ.positive r]
  · rw [if_neg hsrc]; have := κ.positive r; linarith

theorem smat_apply (c c' : N.ComplexIdx) :
    smat N κ c c' = (if c = c' then 1 else 0) + (dscale N κ)⁻¹ * kmat N κ c c' := by
  simp [smat, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]

/-- The diagonal of the rescaled matrix is strictly positive. -/
theorem smat_diag_pos (c : N.ComplexIdx) : 0 < smat N κ c c := by
  rw [smat_apply, if_pos rfl]
  have hlb := kmat_diag_lb (κ := κ) c
  have hinv : (0 : ℝ) < (dscale N κ)⁻¹ := inv_pos.mpr dscale_pos
  have hmul : (dscale N κ)⁻¹ * dscale N κ = 1 := inv_mul_cancel₀ dscale_pos.ne'
  nlinarith [mul_le_mul_of_nonneg_left hlb hinv.le,
    mul_lt_mul_of_pos_left (sum_k_lt_dscale (N := N) (κ := κ)) hinv, hmul]

theorem smat_nonneg (c c' : N.ComplexIdx) : 0 ≤ smat N κ c c' := by
  by_cases hcc : c = c'
  · subst hcc; exact (smat_diag_pos c).le
  · rw [smat_apply, if_neg hcc, zero_add]
    exact mul_nonneg (inv_nonneg.mpr dscale_pos.le) (kmat_offdiag_nonneg hcc)

theorem smat_colsum (c' : N.ComplexIdx) : ∑ c, smat N κ c c' = 1 := by
  simp_rw [smat_apply]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, kmat_colsum, mul_zero, add_zero]
  simp [Finset.sum_ite_eq']

theorem smat_mulVec (b : N.ComplexIdx → ℝ) :
    (smat N κ).mulVec b = b + (dscale N κ)⁻¹ • N.kineticMap κ b := by
  rw [smat, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, kmat_mulVec]

theorem smat_fix_iff (b : N.ComplexIdx → ℝ) :
    (smat N κ).mulVec b = b ↔ N.kineticMap κ b = 0 := by
  rw [smat_mulVec]
  constructor
  · intro h
    have h2 : (dscale N κ)⁻¹ • N.kineticMap κ b = 0 :=
      add_left_cancel (a := b) (by rw [h, add_zero])
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 (inv_ne_zero dscale_pos.ne')
    · exact h3
  · intro h; rw [h, smul_zero, add_zero]

theorem smat_blockdiag {c c' : N.ComplexIdx}
    (h : Quotient.mk N.linkedSetoid c ≠ Quotient.mk N.linkedSetoid c') :
    smat N κ c c' = 0 := by
  rw [smat_apply, kmat_blockdiag h, mul_zero, add_zero, if_neg (fun hcc => h (by rw [hcc]))]

/-- A reaction `b' → b` makes the rescaled matrix entry `smat b b'` nonzero, hence a
support edge from `b` to `b'`. -/
theorem smat_ne_zero_of_reaction {b b' : N.ComplexIdx} (r : N.R)
    (hs : N.sourceIdx r = b') (ht : N.targetIdx r = b) : smat N κ b b' ≠ 0 := by
  by_cases hbb : b = b'
  · subst hbb; exact (smat_diag_pos b).ne'
  · rw [smat_apply, if_neg hbb, zero_add]
    have hk : 0 < kmat N κ b b' := by
      refine Finset.sum_pos' (fun r' _ => ?_) ⟨r, Finset.mem_univ r, ?_⟩
      · by_cases hsrc : N.sourceIdx r' = b'
        · rw [if_pos hsrc, if_neg (Ne.symm hbb), sub_zero]
          exact mul_nonneg (κ.positive r').le (by positivity)
        · rw [if_neg hsrc]
      · rw [if_pos hs, if_neg (Ne.symm hbb), sub_zero, if_pos ht]
        simpa using κ.positive r
    exact (mul_pos (inv_pos.mpr dscale_pos) hk).ne'

/-- Lifting a directed reaction path to a support path of the rescaled matrix (in the
reverse direction). -/
theorem reaches_supportReaches (a : Complex S) (ha : a ∈ N.complexes) :
    ∀ {b : Complex S}, N.Reaches a b → ∀ (hb : b ∈ N.complexes),
      supportReaches (smat N κ) ⟨b, hb⟩ ⟨a, ha⟩ := by
  intro b hab
  induction hab with
  | refl => intro _; exact Relation.ReflTransGen.refl
  | @tail e f _ hef ih =>
    intro hf
    obtain ⟨r, hsr, htr⟩ := hef
    have he : e ∈ N.complexes := hsr ▸ N.source_mem_complexes r
    exact Relation.ReflTransGen.head
      (smat_ne_zero_of_reaction (b := ⟨f, hf⟩) (b' := ⟨e, he⟩) r (Subtype.ext hsr)
        (Subtype.ext htr)) (ih he)

end

/-- **Milestone 3, complete.** For a weakly reversible mass-action network, the kinetic
matrix `A_k` has a strictly positive kernel vector. -/
theorem weaklyReversible_exists_positive_kernelVector (N : Network S)
    (hwr : N.WeaklyReversible) (κ : Network.RateConstants N) :
    ∃ b : N.ComplexIdx → ℝ, (∀ c, 0 < b c) ∧ N.kineticMap κ b = 0 := by
  classical
  rcases isEmpty_or_nonempty N.ComplexIdx with hempty | hne
  · exact ⟨fun _ => 1, fun c => (hempty.false c).elim, funext fun c => (hempty.false c).elim⟩
  obtain ⟨b, hbnn, hbfix, hbinv⟩ :=
    exists_nonneg_mulVec_fixed_invariant (smat N κ) smat_nonneg smat_colsum
  refine ⟨b, ?_, (smat_fix_iff b).mp hbfix⟩
  intro c
  set q := Quotient.mk N.linkedSetoid c with hq
  set T : Finset N.ComplexIdx :=
    Finset.univ.filter (fun c'' => Quotient.mk N.linkedSetoid c'' = q) with hT
  have hcT : c ∈ T := by rw [hT, Finset.mem_filter]; exact ⟨Finset.mem_univ c, hq.symm⟩
  -- the class `T` is invariant under `smat`, so it keeps its uniform mass.
  have hTinv : ∀ v, ∑ i ∈ T, (smat N κ).mulVec v i = ∑ i ∈ T, v i := by
    intro v
    have hcol0 : ∀ c', ∑ i ∈ T, kmat N κ i c' = 0 := by
      intro c'
      by_cases hc' : Quotient.mk N.linkedSetoid c' = q
      · rw [← kmat_colsum c']
        refine Finset.sum_subset (Finset.subset_univ T) fun i _ hi => ?_
        rw [hT, Finset.mem_filter, not_and] at hi
        exact kmat_blockdiag fun he => hi (Finset.mem_univ i) (he.trans hc')
      · refine Finset.sum_eq_zero fun i hi => ?_
        rw [hT, Finset.mem_filter] at hi
        exact kmat_blockdiag fun he => hc' (he ▸ hi.2)
    have hzero : ∑ i ∈ T, N.kineticMap κ v i = 0 := by
      have hki : ∀ i, N.kineticMap κ v i = ∑ c', kmat N κ i c' * v c' := by
        intro i; rw [← kmat_mulVec]; rfl
      simp_rw [hki]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hcol0, zero_mul]
      simp
    simp_rw [smat_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hzero, mul_zero, add_zero]
  have hmass := hbinv T hTinv
  have hmasspos : 0 < ∑ i ∈ T, b i := by
    rw [hmass]
    exact mul_pos (by exact_mod_cast Finset.card_pos.mpr ⟨c, hcT⟩)
      (inv_pos.mpr (by exact_mod_cast Fintype.card_pos))
  obtain ⟨c'', hc''T, hc''pos⟩ :=
    Finset.exists_lt_of_sum_lt (s := T) (f := fun _ => (0 : ℝ)) (g := b)
      (by rw [Finset.sum_const_zero]; exact hmasspos)
  -- `c''` is in `c`'s class, so `c` reaches it; positivity spreads.
  have hqc'' : Quotient.mk N.linkedSetoid c'' = q := by
    rw [hT, Finset.mem_filter] at hc''T; exact hc''T.2
  have hlink : N.Linked c''.val c.val := Quotient.exact (hqc''.trans hq.symm)
  have hsupp : supportReaches (smat N κ) c c'' :=
    reaches_supportReaches c''.val c''.2 (hwr.reaches_of_linked hlink) c.2
  exact pos_of_supportReaches_pos (smat N κ) smat_nonneg b hbnn hbfix hsupp hc''pos

end PositiveKernel

end CRNT

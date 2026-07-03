import CRNT.Multistationarity.GaleNikaido
import CRNT.Multistationarity.PMatrixSchur
import CRNT.Multistationarity.PMatrixSignature
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Gale–Nikaido on a box: the reduced-map Jacobian is the Schur complement

The inductive core of the degree-free Gale–Nikaido theorem. Fixing the last coordinate by an implicit
solve `φ` of `F_last = c`, the reduced map `G x̂ = (F₁, …, Fₙ)(x̂, φ x̂)` on the lower-dimensional box
has, by the chain rule and implicit differentiation, Jacobian equal to the **Schur complement**
(`Matrix.schurLast`) of the full Jacobian — which is again a P-matrix, driving the dimension
induction.

The only Mathlib gap is the derivative of the `Fin.snoc` embedding `y ↦ Fin.snoc y (φ y)`, supplied
here as `hasFDerivAt_snoc`.

Depends on: `CRNT.Multistationarity.GaleNikaido`,
`CRNT.Multistationarity.PMatrixSchur`, `CRNT.Multistationarity.PMatrixSignature`.
-/

namespace CRNT

open scoped BigOperators Matrix

/-- **The derivative of the `Fin.snoc` embedding.** The map `y ↦ Fin.snoc y (φ y)` from
`Fin n → ℝ` to `Fin (n+1) → ℝ` has derivative `Δ ↦ Fin.snoc Δ (Dφ Δ)`, assembled coordinatewise:
the `castSucc` components are projections, the last component is `φ`. -/
theorem hasFDerivAt_snoc {n : ℕ} {φ : (Fin n → ℝ) → ℝ} {Dφ : (Fin n → ℝ) →L[ℝ] ℝ}
    {x : Fin n → ℝ} (hφ : HasFDerivAt φ Dφ x) :
    HasFDerivAt (fun y => (Fin.snoc y (φ y) : Fin (n + 1) → ℝ))
      (ContinuousLinearMap.pi (Fin.lastCases Dφ (fun j => ContinuousLinearMap.proj j))) x := by
  rw [hasFDerivAt_pi']
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · -- last component is `φ`
    simp only [ContinuousLinearMap.proj_pi, Fin.lastCases_last]
    have hfun : (fun y => (Fin.snoc y (φ y) : Fin (n + 1) → ℝ) (Fin.last n)) = φ := by
      funext y; rw [Fin.snoc_last]
    rw [hfun]; exact hφ
  · -- `castSucc j` component is the `j`-projection
    simp only [ContinuousLinearMap.proj_pi, Fin.lastCases_castSucc]
    have hfun : (fun y => (Fin.snoc y (φ y) : Fin (n + 1) → ℝ) j.castSucc) = (fun y => y j) := by
      funext y; rw [Fin.snoc_castSucc]
    rw [hfun]; exact hasFDerivAt_apply j x

/-- The derivative of the lower-dimensional **reduced map** `G y = (F (Fin.snoc y (φ y)))` with the
last coordinate dropped: by the chain rule it is `dropLast ∘ L ∘ snocDeriv`, where `snocDeriv` is the
embedding derivative (`hasFDerivAt_snoc`) and `dropLast` drops the last coordinate. -/
theorem hasFDerivAt_reduced {n : ℕ} {F : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)}
    {φ : (Fin n → ℝ) → ℝ} {Dφ : (Fin n → ℝ) →L[ℝ] ℝ} {x : Fin n → ℝ}
    {L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)}
    (hF : HasFDerivAt F L (Fin.snoc x (φ x))) (hφ : HasFDerivAt φ Dφ x) :
    HasFDerivAt (fun y => fun i : Fin n => F (Fin.snoc y (φ y)) i.castSucc)
      ((ContinuousLinearMap.pi (fun i : Fin n =>
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) i.castSucc)).comp
        (L.comp (ContinuousLinearMap.pi
          (Fin.lastCases Dφ (fun j => ContinuousLinearMap.proj j))))) x := by
  have hFcomp : HasFDerivAt (fun y => F (Fin.snoc y (φ y)))
      (L.comp (ContinuousLinearMap.pi
        (Fin.lastCases Dφ (fun j => ContinuousLinearMap.proj j)))) x :=
    hF.comp x (hasFDerivAt_snoc hφ)
  exact (ContinuousLinearMap.pi (fun i : Fin n =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) i.castSucc)).hasFDerivAt.comp
    x hFcomp

/-- **Rung 4: the reduced-map Jacobian is the Schur complement.** Under the implicit-differentiation
relation `himp` (the derivative of the last-coordinate constraint `F_last = c`), the matrix of the
reduced map's derivative `dropLast ∘ L ∘ snocDeriv` is exactly the Schur complement `schurLast` of the
full Jacobian `jacobianMatrix L`. Combined with `Matrix.IsPMatrix.schurLast`, the reduced Jacobian is
a P-matrix — the dimension-drop step of the inductive Gale–Nikaido theorem. -/
theorem jacobianMatrix_reduced_eq_schurLast {n : ℕ} {Dφ : (Fin n → ℝ) →L[ℝ] ℝ}
    {L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)}
    (himp : ∀ Δ : Fin n → ℝ, Dφ Δ = -(jacobianMatrix L (Fin.last n) (Fin.last n))⁻¹ *
        ∑ j, jacobianMatrix L (Fin.last n) j.castSucc * Δ j) :
    jacobianMatrix ((ContinuousLinearMap.pi (fun i : Fin n =>
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) i.castSucc)).comp
      (L.comp (ContinuousLinearMap.pi
        (Fin.lastCases Dφ (fun j => ContinuousLinearMap.proj j)))))
      = Matrix.schurLast (jacobianMatrix L) := by
  set M := jacobianMatrix L with hMdef
  set DG := (ContinuousLinearMap.pi (fun i : Fin n =>
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) i.castSucc)).comp
    (L.comp (ContinuousLinearMap.pi
      (Fin.lastCases Dφ (fun j => ContinuousLinearMap.proj j)))) with hDGdef
  have hsd : ∀ Δ : Fin n → ℝ,
      (ContinuousLinearMap.pi (Fin.lastCases Dφ (fun j => ContinuousLinearMap.proj j))) Δ
        = (Fin.snoc Δ (Dφ Δ) : Fin (n + 1) → ℝ) := by
    intro Δ; funext k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simp [ContinuousLinearMap.pi_apply, Fin.lastCases_last, Fin.snoc_last]
    · simp [ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply,
        Fin.lastCases_castSucc, Fin.snoc_castSucc]
  have hact : ∀ Δ : Fin n → ℝ, DG Δ = (Matrix.schurLast M) *ᵥ Δ := by
    intro Δ
    funext i
    have e1 : DG Δ i
        = (∑ j, M i.castSucc j.castSucc * Δ j) + M i.castSucc (Fin.last n) * Dφ Δ := by
      simp only [hDGdef, ContinuousLinearMap.comp_apply]
      rw [hsd Δ]
      simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]
      rw [← jacobianMatrix_mulVec, ← hMdef]
      simp only [Matrix.mulVec, dotProduct]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [e1, himp Δ]
    have hRHS : ((Matrix.schurLast M) *ᵥ Δ) i
        = ∑ j, (M i.castSucc j.castSucc
            - M i.castSucc (Fin.last n) * (M (Fin.last n) (Fin.last n))⁻¹
              * M (Fin.last n) j.castSucc) * Δ j := by
      simp only [Matrix.mulVec, dotProduct, Matrix.schurLast]
    rw [hRHS]
    have hsecond : M i.castSucc (Fin.last n)
          * (-(M (Fin.last n) (Fin.last n))⁻¹ * ∑ j, M (Fin.last n) j.castSucc * Δ j)
        = ∑ j, -(M i.castSucc (Fin.last n) * (M (Fin.last n) (Fin.last n))⁻¹
            * M (Fin.last n) j.castSucc) * Δ j := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hsecond, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  apply Matrix.ext
  intro i j
  have h := congrFun (hact (Pi.single j 1)) i
  rw [← jacobianMatrix_mulVec DG (Pi.single j 1)] at h
  simpa [Matrix.mulVec_single] using h

/-- The reduced map's Jacobian is a **P-matrix**: it equals the Schur complement of the full
P-matrix Jacobian (`jacobianMatrix_reduced_eq_schurLast`), which is a P-matrix
(`Matrix.IsPMatrix.schurLast`). This is the inductive hypothesis-feeder of the Gale–Nikaido
dimension induction. -/
theorem reduced_isPMatrix {n : ℕ} {Dφ : (Fin n → ℝ) →L[ℝ] ℝ}
    {L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)}
    (hP : (jacobianMatrix L).IsPMatrix)
    (himp : ∀ Δ : Fin n → ℝ, Dφ Δ = -(jacobianMatrix L (Fin.last n) (Fin.last n))⁻¹ *
        ∑ j, jacobianMatrix L (Fin.last n) j.castSucc * Δ j) :
    (jacobianMatrix ((ContinuousLinearMap.pi (fun i : Fin n =>
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) i.castSucc)).comp
      (L.comp (ContinuousLinearMap.pi
        (Fin.lastCases Dφ (fun j => ContinuousLinearMap.proj j)))))).IsPMatrix := by
  rw [jacobianMatrix_reduced_eq_schurLast himp]
  exact hP.schurLast

/-- **The one-variable `Fin.snoc` derivative.** Moving only the last coordinate, `t ↦ Fin.snoc x̂ t`
has derivative the basis vector `Pi.single (Fin.last n) 1`. -/
theorem hasDerivAt_snocLast {n : ℕ} (x : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (fun t => (Fin.snoc x t : Fin (n + 1) → ℝ)) (Pi.single (Fin.last n) 1) s := by
  rw [hasDerivAt_pi]
  intro k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simp only [Fin.snoc_last, Pi.single_eq_same]
    exact hasDerivAt_id s
  · simp only [Fin.snoc_castSucc, Pi.single_eq_of_ne (Fin.castSucc_lt_last j).ne]
    exact hasDerivAt_const s (x j)

/-- **The last coordinate is solved uniquely.** Holding the first `n` coordinates fixed at `x`, the
map `s ↦ F (Fin.snoc x s) (Fin.last n)` is injective on the box's last interval: its derivative is the
diagonal Jacobian entry `M (last) (last) > 0` (`IsPMatrix.diag_pos`), so it is strictly monotone. -/
theorem injOn_lastCoord {n : ℕ}
    {F : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)}
    {F' : (Fin (n + 1) → ℝ) → ((Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))}
    {x : Fin n → ℝ} {a b : Fin (n + 1) → ℝ}
    (hF : ∀ z ∈ Set.Icc a b, HasFDerivAt F (F' z) z)
    (hP : ∀ z ∈ Set.Icc a b, (jacobianMatrix (F' z)).IsPMatrix)
    (hmem : ∀ s ∈ Set.Icc (a (Fin.last n)) (b (Fin.last n)),
        (Fin.snoc x s : Fin (n + 1) → ℝ) ∈ Set.Icc a b) :
    Set.InjOn (fun s => F (Fin.snoc x s) (Fin.last n))
      (Set.Icc (a (Fin.last n)) (b (Fin.last n))) := by
  have hderiv : ∀ s ∈ Set.Icc (a (Fin.last n)) (b (Fin.last n)),
      HasDerivAt (fun t => F (Fin.snoc x t) (Fin.last n))
        (jacobianMatrix (F' (Fin.snoc x s)) (Fin.last n) (Fin.last n)) s := by
    intro s hs
    have h1 : HasDerivAt (fun t => F (Fin.snoc x t))
        (F' (Fin.snoc x s) (Pi.single (Fin.last n) 1)) s :=
      (hF _ (hmem s hs)).comp_hasDerivAt s (hasDerivAt_snocLast x s)
    have h2 := hasDerivAt_pi.mp h1 (Fin.last n)
    have hval : (F' (Fin.snoc x s) (Pi.single (Fin.last n) 1)) (Fin.last n)
        = jacobianMatrix (F' (Fin.snoc x s)) (Fin.last n) (Fin.last n) := by
      rw [← jacobianMatrix_mulVec]
      simp [Matrix.mulVec_single]
    rwa [hval] at h2
  apply StrictMonoOn.injOn
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · intro s hs
    exact (hderiv s hs).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Icc, Set.mem_Ioo] at hs
    have hsIcc : s ∈ Set.Icc (a (Fin.last n)) (b (Fin.last n)) :=
      ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    rw [(hderiv s hsIcc).deriv]
    exact (hP _ (hmem s hsIcc)).diag_pos (Fin.last n)

/-- The fiber over a projected point stays in the box: if `p ∈ Icc a b`, then `Fin.snoc (Fin.init p) s`
is in the box for any last coordinate `s` in the last interval. -/
theorem snoc_init_mem {n : ℕ} {a b p : Fin (n + 1) → ℝ} (hp : p ∈ Set.Icc a b)
    {s : ℝ} (hs : s ∈ Set.Icc (a (Fin.last n)) (b (Fin.last n))) :
    (Fin.snoc (Fin.init p) s : Fin (n + 1) → ℝ) ∈ Set.Icc a b := by
  rw [Set.mem_Icc] at hp hs ⊢
  refine ⟨fun k => ?_, fun k => ?_⟩
  · refine Fin.lastCases ?_ (fun j => ?_) k
    · rw [Fin.snoc_last]; exact hs.1
    · rw [Fin.snoc_castSucc, Fin.init_def]; exact hp.1 j.castSucc
  · refine Fin.lastCases ?_ (fun j => ?_) k
    · rw [Fin.snoc_last]; exact hs.2
    · rw [Fin.snoc_castSucc, Fin.init_def]; exact hp.2 j.castSucc

/-- **The Gale–Nikaido dimension-reduction step.** Two points of the box with equal image under `F`
are equal, provided the lower-dimensional **reduced map** `x̂ ↦ (F (Fin.snoc x̂ (φ x̂)))∘castSucc` (with
`φ` a section of the last-coordinate equation through both points) is injective on the projected box.
The last coordinate is pinned by `injOn_lastCoord` (uniqueness of the solve), and the first `n` by the
reduced map's injectivity. -/
theorem eq_of_reduced {n : ℕ}
    {F : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)}
    {F' : (Fin (n + 1) → ℝ) → ((Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))}
    {a b : Fin (n + 1) → ℝ}
    (hF : ∀ z ∈ Set.Icc a b, HasFDerivAt F (F' z) z)
    (hP : ∀ z ∈ Set.Icc a b, (jacobianMatrix (F' z)).IsPMatrix)
    {p q : Fin (n + 1) → ℝ} (hp : p ∈ Set.Icc a b) (hq : q ∈ Set.Icc a b)
    (hFpq : F p = F q)
    {φ : (Fin n → ℝ) → ℝ}
    (hφp : φ (Fin.init p) ∈ Set.Icc (a (Fin.last n)) (b (Fin.last n)))
    (hφq : φ (Fin.init q) ∈ Set.Icc (a (Fin.last n)) (b (Fin.last n)))
    (hsolp : F (Fin.snoc (Fin.init p) (φ (Fin.init p))) (Fin.last n) = F p (Fin.last n))
    (hsolq : F (Fin.snoc (Fin.init q) (φ (Fin.init q))) (Fin.last n) = F q (Fin.last n))
    (hGinj : Set.InjOn (fun x => fun i : Fin n => F (Fin.snoc x (φ x)) i.castSucc)
      (Set.Icc (Fin.init a) (Fin.init b))) :
    p = q := by
  -- The last coordinate of each point is the solve value `φ` at its projection.
  have hlast : ∀ {r : Fin (n + 1) → ℝ}, r ∈ Set.Icc a b →
      φ (Fin.init r) ∈ Set.Icc (a (Fin.last n)) (b (Fin.last n)) →
      F (Fin.snoc (Fin.init r) (φ (Fin.init r))) (Fin.last n) = F r (Fin.last n) →
      r (Fin.last n) = φ (Fin.init r) := by
    intro r hr hφr hsolr
    have hinj := injOn_lastCoord (F := F) (F' := F') (x := Fin.init r) hF hP
      (fun s hs => snoc_init_mem hr hs)
    have hrlast : r (Fin.last n) ∈ Set.Icc (a (Fin.last n)) (b (Fin.last n)) := by
      rw [Set.mem_Icc] at hr ⊢; exact ⟨hr.1 (Fin.last n), hr.2 (Fin.last n)⟩
    apply hinj hrlast hφr
    simp only [Fin.snoc_init_self]
    exact hsolr.symm
  have hpl := hlast hp hφp hsolp
  have hql := hlast hq hφq hsolq
  -- The projected points coincide, by injectivity of the reduced map.
  have hinitp : Fin.init p ∈ Set.Icc (Fin.init a) (Fin.init b) := by
    rw [Set.mem_Icc] at hp ⊢
    exact ⟨fun j => hp.1 j.castSucc, fun j => hp.2 j.castSucc⟩
  have hinitq : Fin.init q ∈ Set.Icc (Fin.init a) (Fin.init b) := by
    rw [Set.mem_Icc] at hq ⊢
    exact ⟨fun j => hq.1 j.castSucc, fun j => hq.2 j.castSucc⟩
  have hredeq : (fun i : Fin n => F (Fin.snoc (Fin.init p) (φ (Fin.init p))) i.castSucc)
      = (fun i : Fin n => F (Fin.snoc (Fin.init q) (φ (Fin.init q))) i.castSucc) := by
    funext i
    rw [← hpl, ← hql, Fin.snoc_init_self, Fin.snoc_init_self, hFpq]
  have hinit : Fin.init p = Fin.init q := hGinj hinitp hinitq hredeq
  -- Reassemble both points from their (equal) projections and last coordinates.
  calc p = Fin.snoc (Fin.init p) (p (Fin.last n)) := (Fin.snoc_init_self p).symm
    _ = Fin.snoc (Fin.init q) (q (Fin.last n)) := by rw [hinit, hpl, hql, hinit]
    _ = q := Fin.snoc_init_self q

/-- **Gale–Nikaido on a box (conditional on the last-coordinate sections).** A `C¹` map with a
P-matrix Jacobian everywhere on a box is injective, **provided** that for each colliding pair `p, q`
(`F p = F q`) there is a section `φ` of the last-coordinate equation through both projected points,
along which the reduced map is injective. The section + reduced-injectivity hypothesis is exactly what
the dimension induction supplies (`reduced_isPMatrix` shows the reduced map is again a P-matrix map)
together with the in-box solvability of the last coordinate — the latter being the ingredient that, in
full generality, requires either a coercivity hypothesis or topological degree. -/
theorem injOn_of_pmatrix_fderiv_of_sections {n : ℕ}
    {F : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)}
    {F' : (Fin (n + 1) → ℝ) → ((Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))}
    {a b : Fin (n + 1) → ℝ}
    (hF : ∀ z ∈ Set.Icc a b, HasFDerivAt F (F' z) z)
    (hP : ∀ z ∈ Set.Icc a b, (jacobianMatrix (F' z)).IsPMatrix)
    (hsec : ∀ p ∈ Set.Icc a b, ∀ q ∈ Set.Icc a b, F p = F q →
      ∃ φ : (Fin n → ℝ) → ℝ,
        φ (Fin.init p) ∈ Set.Icc (a (Fin.last n)) (b (Fin.last n)) ∧
        φ (Fin.init q) ∈ Set.Icc (a (Fin.last n)) (b (Fin.last n)) ∧
        F (Fin.snoc (Fin.init p) (φ (Fin.init p))) (Fin.last n) = F p (Fin.last n) ∧
        F (Fin.snoc (Fin.init q) (φ (Fin.init q))) (Fin.last n) = F q (Fin.last n) ∧
        Set.InjOn (fun x => fun i : Fin n => F (Fin.snoc x (φ x)) i.castSucc)
          (Set.Icc (Fin.init a) (Fin.init b))) :
    Set.InjOn F (Set.Icc a b) := by
  intro p hp q hq hFpq
  obtain ⟨φ, hφp, hφq, hsolp, hsolq, hGinj⟩ := hsec p hp q hq hFpq
  exact eq_of_reduced hF hP hp hq hFpq hφp hφq hsolp hsolq hGinj

end CRNT

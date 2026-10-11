import CRNT.Stochastic.DetailedBalance

/-!
# Finite-region Dirichlet forms for reversible stochastic reaction networks

On a finite set of count states closed under enabled firings, microscopic detailed balance
makes the product-Poisson weighted backward generator symmetric. Its negative quadratic form
is the sum of squared observable increments over reaction channels. Reaction indices are
retained throughout, so parallel channels and paired self-loops are counted with their actual
multiplicities.

The finite-region hypothesis keeps every reindexing finite. This module proves a generator
identity; it does not assert process-level recurrence or convergence.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A count region is fire-closed when each enabled jump starting in the region stays in it.
Since disabled reactions have zero propensity and `fireCount` leaves their source unchanged,
the definition is stated for all reaction channels. -/
def FireClosed (N : Network S) (T : Set (S → ℕ)) : Prop :=
  ∀ n, n ∈ T → ∀ r : N.R, N.fireCount n r ∈ T

/-- A directed enabled reaction channel whose source count lies in `T`. The reaction index is
part of the edge, so distinct parallel channels remain distinct. -/
abbrev EnabledJump (N : Network S) (T : Set (S → ℕ)) :=
  Σ n : ↥T, {r : N.R // N.Enabled n.1 r}

/-- Firing an enabled reaction and then its paired reverse returns to the original count. -/
theorem fireCount_reverse_fireCount (N : Network S) (ρ : ReversiblePairing N)
    {n : S → ℕ} {r : N.R} (hen : N.Enabled n r) :
    N.fireCount (N.fireCount n r) (ρ.rev r) = n := by
  funext s
  have hrev := N.reverse_enabled_after_fire ρ hen
  have hrev' : N.Enabled
      (fun t => n t - (N.reaction r).source t + (N.reaction r).target t)
      (ρ.rev r) := by
    simpa [fireCount, hen] using hrev
  have hsrc : ∀ t, (N.reaction r).source t ≤ n t := hen
  unfold fireCount
  rw [dif_pos hen, dif_pos hrev']
  rw [ρ.source_rev_apply, ρ.target_rev_apply]
  have hs := hsrc s
  omega

/-- The edge involution induced by the reversible pairing. -/
def reverseEnabledJump (N : Network S) (ρ : ReversiblePairing N)
    {T : Set (S → ℕ)} (hT : N.FireClosed T) (e : N.EnabledJump T) :
    N.EnabledJump T :=
  ⟨⟨N.fireCount e.1.1 e.2.1, hT e.1.1 e.1.2 e.2.1⟩,
    ⟨ρ.rev e.2.1, N.reverse_enabled_after_fire ρ e.2.2⟩⟩

theorem reverseEnabledJump_involutive (N : Network S) (ρ : ReversiblePairing N)
    {T : Set (S → ℕ)} (hT : N.FireClosed T) :
    Function.Involutive (N.reverseEnabledJump ρ hT) := by
  intro e
  rcases e with ⟨n, ⟨r, hen⟩⟩
  have hstate : N.fireCount (N.fireCount n.1 r) (ρ.rev r) = n.1 :=
    N.fireCount_reverse_fireCount ρ hen
  apply Sigma.ext
  · apply Subtype.ext
    exact hstate
  · simp only [reverseEnabledJump]
    apply (Subtype.heq_iff_coe_eq (fun q => by rw [hstate])).2
    exact ρ.rev_rev r

/-- The reversal map as an equivalence of enabled reaction channels in a fire-closed region. -/
def reverseEnabledJumpEquiv (N : Network S) (ρ : ReversiblePairing N)
    {T : Set (S → ℕ)} (hT : N.FireClosed T) :
    N.EnabledJump T ≃ N.EnabledJump T :=
  { toFun := N.reverseEnabledJump ρ hT
    invFun := N.reverseEnabledJump ρ hT
    left_inv := N.reverseEnabledJump_involutive ρ hT
    right_inv := N.reverseEnabledJump_involutive ρ hT }

/-- Product-Poisson flux carried by one enabled reaction edge. -/
noncomputable def dirichletEdgeWeight (N : Network S) (κ : RateConstants N)
    (c : Concentration S) {T : Set (S → ℕ)} (e : N.EnabledJump T) : ℝ :=
  productPoissonPMF c e.1.1 * N.stochasticMassActionRate κ e.1.1 e.2.1

/-- Observable increment across an enabled reaction edge. -/
noncomputable def dirichletJumpDelta (N : Network S) {T : Set (S → ℕ)}
    (f : (S → ℕ) → ℝ) (e : N.EnabledJump T) : ℝ :=
  f (N.fireCount e.1.1 e.2.1) - f e.1.1

/-- The product-Poisson flux is unchanged when an enabled edge is reversed under microscopic
detailed balance. -/
theorem dirichletEdgeWeight_reverse (N : Network S) (ρ : ReversiblePairing N)
    (κ : RateConstants N) (c : Concentration S) {T : Set (S → ℕ)}
    (hT : N.FireClosed T) (hdb : N.IsMicroscopicallyDetailedBalanced ρ κ c)
    (e : N.EnabledJump T) :
    N.dirichletEdgeWeight κ c (N.reverseEnabledJump ρ hT e) =
      N.dirichletEdgeWeight κ c e := by
  simpa [dirichletEdgeWeight, reverseEnabledJump] using
    (hdb e.1.1 e.2.1 e.2.2).symm

/-- Reversal negates the observable increment across an enabled edge. -/
theorem dirichletJumpDelta_reverse (N : Network S) (ρ : ReversiblePairing N)
    {T : Set (S → ℕ)} (hT : N.FireClosed T) (f : (S → ℕ) → ℝ)
    (e : N.EnabledJump T) :
    N.dirichletJumpDelta f (N.reverseEnabledJump ρ hT e) =
      -N.dirichletJumpDelta f e := by
  simp [dirichletJumpDelta, reverseEnabledJump,
    N.fireCount_reverse_fireCount ρ e.2.2, sub_eq_add_neg]

/-- Product-Poisson weighted pairing of observables `f` with the stochastic generator applied
to `g`, restricted to a finite region. -/
noncomputable def weightedGeneratorPairing (N : Network S) (κ : RateConstants N)
    (c : Concentration S) {T : Set (S → ℕ)} [Fintype ↥T]
    (f g : (S → ℕ) → ℝ) : ℝ :=
  ∑ n : ↥T, productPoissonPMF c n.1 * f n.1 *
    N.observableGenerator κ g n.1

/-- The bilinear Dirichlet form of the stochastic reaction generator on enabled edges of `T`. -/
noncomputable def dirichletForm (N : Network S)
    (κ : RateConstants N) (c : Concentration S) {T : Set (S → ℕ)} [Fintype ↥T]
    (f g : (S → ℕ) → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ e : N.EnabledJump T,
    N.dirichletEdgeWeight κ c e * N.dirichletJumpDelta f e *
      N.dirichletJumpDelta g e

/-- Expanding the backward generator pairing produces a sum over enabled reaction edges.
Disabled channels disappear because their falling-factorial propensity is zero. -/
theorem weightedGeneratorPairing_eq_enabledJumpSum (N : Network S)
    (κ : RateConstants N) (c : Concentration S) {T : Set (S → ℕ)}
    [Fintype ↥T] (f g : (S → ℕ) → ℝ) :
    N.weightedGeneratorPairing (T := T) κ c f g =
      ∑ e : N.EnabledJump T,
        N.dirichletEdgeWeight κ c e * f e.1.1 *
          N.dirichletJumpDelta g e := by
  classical
  unfold weightedGeneratorPairing
  unfold observableGenerator
  have hrow : ∀ n : ↥T,
      productPoissonPMF c n.1 * f n.1 *
          (∑ r : N.R, N.stochasticMassActionRate κ n.1 r *
            (g (N.fireCount n.1 r) - g n.1)) =
        ∑ r : {r : N.R // N.Enabled n.1 r},
          productPoissonPMF c n.1 * f n.1 *
            (N.stochasticMassActionRate κ n.1 r.1 *
              (g (N.fireCount n.1 r.1) - g n.1)) := by
    intro n
    let p : N.R → Prop := fun r => N.Enabled n.1 r
    let F : N.R → ℝ := fun r => productPoissonPMF c n.1 * f n.1 *
      (N.stochasticMassActionRate κ n.1 r *
        (g (N.fireCount n.1 r) - g n.1))
    have hsplit := Fintype.sum_subtype_add_sum_subtype p F
    have hdisabled :
        (∑ r : {r : N.R // ¬p r}, F r.1) = 0 := by
      apply Finset.sum_eq_zero
      intro r _
      have hr : ¬N.Enabled n.1 r.1 := r.2
      have hz := N.stochasticMassActionRate_eq_zero_of_not_enabled κ n.1 r.1 hr
      simp [F, p, hz]
    rw [Finset.mul_sum]
    change (∑ r : N.R, F r) =
      ∑ r : {r : N.R // N.Enabled n.1 r}, F r.1
    rw [← hsplit, hdisabled, add_zero]
  rw [Fintype.sum_sigma]
  simp only [dirichletEdgeWeight, dirichletJumpDelta]
  calc
    _ = ∑ n : ↥T, ∑ r : {r : N.R // N.Enabled n.1 r},
        productPoissonPMF c n.1 * f n.1 *
          (N.stochasticMassActionRate κ n.1 r.1 *
            (g (N.fireCount n.1 r.1) - g n.1)) := by
      apply Finset.sum_congr rfl
      intro n _
      exact hrow n
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro r _
      ring

/-- **Detailed-balance Dirichlet identity.** On a finite fire-closed count region, microscopic
detailed balance makes the weighted backward generator symmetric and identifies its negative
bilinear pairing with one half of the sum of products of reaction-edge increments. -/
theorem weightedGeneratorPairing_eq_neg_dirichletForm
    (N : Network S) (ρ : ReversiblePairing N) (κ : RateConstants N)
    (c : Concentration S) {T : Set (S → ℕ)} [Fintype ↥T]
    (hT : N.FireClosed T) (hdb : N.IsMicroscopicallyDetailedBalanced ρ κ c)
    (f g : (S → ℕ) → ℝ) :
    N.weightedGeneratorPairing (T := T) κ c f g =
      -N.dirichletForm (T := T) κ c f g := by
  classical
  rw [N.weightedGeneratorPairing_eq_enabledJumpSum κ c f g]
  let eR := N.reverseEnabledJumpEquiv ρ hT
  let A : N.EnabledJump T → ℝ := fun e =>
    N.dirichletEdgeWeight κ c e * f e.1.1 * N.dirichletJumpDelta g e
  let B : N.EnabledJump T → ℝ := fun e =>
    N.dirichletEdgeWeight κ c e * f (N.fireCount e.1.1 e.2.1) *
      N.dirichletJumpDelta g e
  have hswap : (∑ e, B e) = -(∑ e, A e) := by
    calc
      (∑ e, B e) = ∑ e, B (N.reverseEnabledJump ρ hT e) :=
        (eR.sum_comp B).symm
      _ = -(∑ e, A e) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro e _
        simp only [B, A]
        rw [N.dirichletEdgeWeight_reverse ρ κ c hT hdb e,
          N.dirichletJumpDelta_reverse ρ hT g e]
        simp only [reverseEnabledJump]
        rw [N.fireCount_reverse_fireCount ρ e.2.2]
        ring
  have hdelta :
      (∑ e : N.EnabledJump T,
        N.dirichletEdgeWeight κ c e * N.dirichletJumpDelta f e *
          N.dirichletJumpDelta g e) =
        (∑ e, B e) - (∑ e, A e) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    simp only [B, A, dirichletJumpDelta]
    ring
  unfold dirichletForm
  rw [hdelta, hswap]
  ring

/-- Positive reactionwise detailed balance at a deterministic equilibrium therefore gives the
finite-region product-Poisson Dirichlet identity directly. -/
theorem weightedGeneratorPairing_eq_neg_dirichletForm_of_reactionwise
    (N : Network S) (ρ : ReversiblePairing N) (κ : RateConstants N)
    {c : Concentration S} (hc : c.Positive) {T : Set (S → ℕ)} [Fintype ↥T]
    (hT : N.FireClosed T)
    (hdb : N.IsReactionwiseDetailedBalanced ρ κ c)
    (f g : (S → ℕ) → ℝ) :
    N.weightedGeneratorPairing (T := T) κ c f g =
      -N.dirichletForm (T := T) κ c f g := by
  exact N.weightedGeneratorPairing_eq_neg_dirichletForm ρ κ c hT
    (N.microscopicallyDetailedBalanced_of_reactionwise ρ κ hc hdb) f g

/-- The weighted generator is symmetric in the product-Poisson inner product on a finite
fire-closed region with microscopic detailed balance. -/
theorem weightedGeneratorPairing_symm
    (N : Network S) (ρ : ReversiblePairing N) (κ : RateConstants N)
    (c : Concentration S) {T : Set (S → ℕ)} [Fintype ↥T]
    (hT : N.FireClosed T) (hdb : N.IsMicroscopicallyDetailedBalanced ρ κ c)
    (f g : (S → ℕ) → ℝ) :
    N.weightedGeneratorPairing (T := T) κ c f g =
      N.weightedGeneratorPairing (T := T) κ c g f := by
  rw [N.weightedGeneratorPairing_eq_neg_dirichletForm ρ κ c hT hdb f g,
    N.weightedGeneratorPairing_eq_neg_dirichletForm ρ κ c hT hdb g f]
  unfold dirichletForm
  apply congrArg Neg.neg
  apply congrArg (fun x : ℝ => (1 / 2 : ℝ) * x)
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- Nonnegative concentrations make the diagonal Dirichlet energy nonnegative. -/
theorem dirichletForm_nonneg
    (N : Network S) (κ : RateConstants N)
    {c : Concentration S} (hc : c.Nonnegative) {T : Set (S → ℕ)}
    [Fintype ↥T] (f : (S → ℕ) → ℝ) :
    0 ≤ N.dirichletForm (T := T) κ c f f := by
  unfold dirichletForm dirichletEdgeWeight
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun e _ => ?_)
  have hw : 0 ≤ productPoissonPMF c e.1.1 * N.stochasticMassActionRate κ e.1.1 e.2.1 :=
    mul_nonneg (productPoissonPMF_nonneg hc _) (N.stochasticMassActionRate_nonneg κ _ _)
  calc
    productPoissonPMF c e.1.1 * N.stochasticMassActionRate κ e.1.1 e.2.1 *
        N.dirichletJumpDelta f e * N.dirichletJumpDelta f e =
      (productPoissonPMF c e.1.1 * N.stochasticMassActionRate κ e.1.1 e.2.1) *
        (N.dirichletJumpDelta f e) ^ 2 := by ring
    _ ≥ 0 := mul_nonneg hw (sq_nonneg _)

/-- Every conserved linear count observable is a zero-energy mode of the stochastic
Dirichlet form on any finite count region. -/
theorem dirichletForm_linear_eq_zero_of_conserved
    (N : Network S) (κ : RateConstants N)
    (c : Concentration S) {T : Set (S → ℕ)} [Fintype ↥T]
    (w : S → ℝ)
    (hw : ∀ r : N.R, ∑ s : S, w s * N.reactionVector r s = 0) :
    N.dirichletForm (T := T) κ c (linearObservable w) (linearObservable w) = 0 := by
  unfold dirichletForm
  simp only [dirichletJumpDelta]
  have hdelta : ∀ e : N.EnabledJump T,
      linearObservable w (N.fireCount e.1.1 e.2.1) -
          linearObservable w e.1.1 = 0 := by
    intro e
    rw [linearObservable_fireCount_sub (N := N) w e.1.1 e.2.1 e.2.2]
    exact hw e.2.1
  simp [dirichletEdgeWeight, hdelta]

end Network
end CRNT

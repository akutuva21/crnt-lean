import CRNT.Compose.InterconnectMonostationary

/-!
# Stoichiometric independence of an interconnection

Two networks are *stoichiometrically independent* when their stoichiometric subspaces meet
only at the origin. The induced vector field of each component lands in that component's
stoichiometric subspace, so under independence the two contributions to the combined field
live in complementary directions: the combined field can move along `N₁`'s subspace and
along `N₂`'s subspace separately, with no shared direction through which one component
perturbs the other's net dynamics.

Under this hypothesis the equation `f₁(x) + f₂(x) = f₁(y) + f₂(y)` separates: the difference
`f₁(x) − f₁(y)` lies in `N₁`'s subspace and equals `f₂(y) − f₂(x)`, which lies in `N₂`'s
subspace, so it lies in their intersection — the trivial subspace — and is zero. The
component fields therefore agree separately, and injectivity of either component lifts to
the combined kinetics.

This is a purely structural sufficient condition for decoupling. It is *not* the
Del Vecchio–Ninfa–Sontag insulation condition, which concerns retroactivity (the load a
downstream module places on an upstream one through *shared species*) and is a distinct,
stronger requirement not captured by stoichiometric independence alone.

Depends on:
`CRNT.Compose.InterconnectMonostationary`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S] {N₁ N₂ : Network S}

/-- Two networks are **stoichiometrically independent** when their stoichiometric subspaces
are disjoint, i.e. meet only at the origin: no net reaction direction is shared between the
components. -/
def StoichIndependent (N₁ N₂ : Network S) : Prop :=
  Disjoint N₁.stoichSubspace N₂.stoichSubspace

namespace Kinetics

/-- **Field separation under stoichiometric independence.** When the combined fields of two
kinetics agree at `x` and `y` and the networks are stoichiometrically independent, the
component fields agree separately: the shared difference lies in both stoichiometric
subspaces, hence in their trivial intersection. -/
theorem vectorField_separate_of_stoichIndependent
    {K₁ : Kinetics N₁} {K₂ : Kinetics N₂} (hind : N₁.StoichIndependent N₂)
    {x y : Concentration S}
    (heq : K₁.vectorField x + K₂.vectorField x = K₁.vectorField y + K₂.vectorField y) :
    K₁.vectorField x = K₁.vectorField y ∧ K₂.vectorField x = K₂.vectorField y := by
  have h1 : K₁.vectorField x - K₁.vectorField y ∈ N₁.stoichSubspace :=
    N₁.stoichSubspace.sub_mem (K₁.vectorField_mem_stoichSubspace x)
      (K₁.vectorField_mem_stoichSubspace y)
  have hd2 : K₁.vectorField x - K₁.vectorField y = K₂.vectorField y - K₂.vectorField x := by
    rw [sub_eq_sub_iff_add_eq_add, heq, add_comm]
  have h2 : K₁.vectorField x - K₁.vectorField y ∈ N₂.stoichSubspace := by
    rw [hd2]
    exact N₂.stoichSubspace.sub_mem (K₂.vectorField_mem_stoichSubspace y)
      (K₂.vectorField_mem_stoichSubspace x)
  have hzero : K₁.vectorField x - K₁.vectorField y = 0 := by
    have hmem := Submodule.mem_inf.mpr ⟨h1, h2⟩
    rw [hind.eq_bot] at hmem
    exact (Submodule.mem_bot _).mp hmem
  refine ⟨sub_eq_zero.mp hzero, ?_⟩
  have hz2 : K₂.vectorField y - K₂.vectorField x = 0 := by rw [← hd2]; exact hzero
  exact (sub_eq_zero.mp hz2).symm

/-- **Independent interconnection over an injective first component is injective.** When the
networks are stoichiometrically independent and the first component's field separates points
of the interconnection's positive compatibility class of `x₀`, the combined field is
injective on that class: independence makes the combined field separate into its components,
so distinguishing points through the first component alone suffices.

Injectivity of the component is required on the *interconnection's* class rather than the
component's own, because a point of the interconnection's class need not lie in either
component's smaller class. -/
theorem InjectiveOnClass.interconnect_of_stoichIndependent_left
    {K₁ : Kinetics N₁} {K₂ : Kinetics N₂} {x₀ : Concentration S}
    (hind : N₁.StoichIndependent N₂)
    (h₁ : Set.InjOn K₁.vectorField ((N₁.interconnect N₂).positiveCompatibilityClass x₀)) :
    (K₁.sum K₂).InjectiveOnClass x₀ := by
  intro x hx y hy hxy
  rw [sum_vectorField] at hxy
  obtain ⟨he₁, _⟩ := vectorField_separate_of_stoichIndependent hind hxy
  exact h₁ hx hy he₁

/-- **Independent interconnection over an injective second component is injective.** The
symmetric statement: stoichiometric independence plus injectivity of the second component's
field on the interconnection's class lifts to the combined kinetics. -/
theorem InjectiveOnClass.interconnect_of_stoichIndependent_right
    {K₁ : Kinetics N₁} {K₂ : Kinetics N₂} {x₀ : Concentration S}
    (hind : N₁.StoichIndependent N₂)
    (h₂ : Set.InjOn K₂.vectorField ((N₁.interconnect N₂).positiveCompatibilityClass x₀)) :
    (K₁.sum K₂).InjectiveOnClass x₀ := by
  intro x hx y hy hxy
  rw [sum_vectorField] at hxy
  obtain ⟨_, he₂⟩ := vectorField_separate_of_stoichIndependent hind hxy
  exact h₂ hx hy he₂

end Kinetics

end Network

end CRNT

import CRNT.Dynamics.MassActionAlgebra
import CRNT.Decision.StrongLinkage

/-!
# A preimage of the deficiency generator with a zero coordinate

Feinberg's deficiency-one analysis pins the equilibrium parameter using a special preimage `y*`
of the deficiency generator `h = A_k z`: one that is nonnegative, strictly positive off the
terminal strong linkage class, and **zero at some complex of the terminal class**. Such a `y*` is
obtained from any strictly-positive preimage `z` (e.g. `Ψ(x)/c_x` at a steady state) by
subtracting the right multiple of the terminal-class kernel mode `b`:

`y* := z − t·b`, where `t = min_{c ∈ terminal SLC} z_c / b_c`.

Because `b` lies in the kernel of `A_k`, this leaves `A_k y* = A_k z = h` unchanged; because `b`
vanishes off the terminal class, `y*` agrees with `z` there (hence stays positive); and because
`t` is the minimal ratio, `y* ≥ 0` on the terminal class with equality at the arg-min complex —
producing the required zero coordinate.

* `exists_zeroCoord_preimage` — the structured preimage `y*` and its arg-min zero coordinate.

Depends on:
`CRNT.Dynamics.MassActionAlgebra`, `CRNT.Decision.StrongLinkage`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The structured preimage with a zero coordinate.** From the terminal-class kernel mode `b`
(positive on the terminal strong linkage class of `c0`, zero off it, in `ker A_k`) and any vector
`z` (in the intended use `z = Ψ(x)/c_x` is strictly positive on the class), the vector
`y* := z − t·b` with `t` the minimal ratio `z/b` over the class is a preimage `A_k y* = A_k z`,
nonnegative on the class, equal to `z` off the class, and zero at the arg-min complex `cm` of the
class. -/
theorem exists_zeroCoord_preimage (N : Network S) (κ : RateConstants N)
    {c0 : N.ComplexIdx} (b z : N.ComplexIdx → ℝ)
    (hbpos : ∀ c', N.StronglyLinked c0.val c'.val → 0 < b c')
    (hboff : ∀ c', ¬ N.StronglyLinked c0.val c'.val → b c' = 0)
    (hbker : N.kineticMap κ b = 0) :
    ∃ (ystar : N.ComplexIdx → ℝ) (cm : N.ComplexIdx),
      N.kineticMap κ ystar = N.kineticMap κ z ∧
      N.StronglyLinked c0.val cm.val ∧ ystar cm = 0 ∧
      (∀ c', N.StronglyLinked c0.val c'.val → 0 ≤ ystar c') ∧
      (∀ c', ¬ N.StronglyLinked c0.val c'.val → ystar c' = z c') := by
  classical
  set T : Finset N.ComplexIdx := Finset.univ.filter (fun c' => N.StronglyLinked c0.val c'.val)
    with hTdef
  have hmemT : ∀ c', c' ∈ T ↔ N.StronglyLinked c0.val c'.val := by
    intro c'; rw [hTdef, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ c', h⟩⟩
  have hc0T : c0 ∈ T := (hmemT c0).mpr (StronglyLinked.refl N c0.val)
  obtain ⟨cm, hcmT, hmin⟩ := Finset.exists_min_image T (fun c' => z c' / b c') ⟨c0, hc0T⟩
  have hcmsl : N.StronglyLinked c0.val cm.val := (hmemT cm).mp hcmT
  set t := z cm / b cm with ht
  set ystar : N.ComplexIdx → ℝ := fun c' => z c' - t * b c' with hystar
  have hystar_eq : ystar = z - t • b := by
    funext c'; simp [hystar, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨ystar, cm, ?_, hcmsl, ?_, ?_, ?_⟩
  · rw [hystar_eq, map_sub, map_smul, hbker, smul_zero, sub_zero]
  · have hbcm : (0 : ℝ) < b cm := hbpos cm hcmsl
    simp only [hystar, ht]
    rw [div_mul_cancel₀ (z cm) hbcm.ne', sub_self]
  · intro c' hsl
    have hbc' : (0 : ℝ) < b c' := hbpos c' hsl
    have hle : t ≤ z c' / b c' := hmin c' ((hmemT c').mpr hsl)
    have hmul : t * b c' ≤ z c' := (le_div_iff₀ hbc').mp hle
    exact sub_nonneg.mpr hmul
  · intro c' hsl
    show z c' - t * b c' = z c'
    rw [hboff c' hsl, mul_zero, sub_zero]

end Network

end CRNT

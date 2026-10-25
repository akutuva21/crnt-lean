import CRNT.Stochastic.BinaryFlowsEntropy
import CRNT.Theorems.DeficiencyZero.TreeConstantProofComplete

/-!
# A non-vacuous instance of `fullyOpen_ergodic_of_mixed`: `2A ⇄ 2B` with all flows

`CRNT.Stochastic.ACKEntropyObstruction` shows that the *unweighted* entropy is not a Foster
function for `2A ⇄ 2B` with all inflows and outflows (rates `(1, 100, …)`).  The weighted entropy
`U_c` is: the core `2A ⇄ 2B` is complex balanced at `c = (1, √(κ₀/κ₁))` for every choice of rates,
so `fullyOpen_ergodic_of_mixed` (with no small classes, `ι = Empty`) gives ergodicity of
`core.fullyOpen` for **every** rate choice (`core_fullyOpen_ergodic`).

More generally (`fullyOpen_ergodic_of_deficiencyZero`): a binary, weakly reversible network of
deficiency zero, with all inflows and outflows added, is ergodic for every choice of rates.  The
Deficiency Zero Theorem gives a positive complex-balanced `c` for the core rates, and the mixed
theorem applies with no small classes.  Adding the flows raises the deficiency (to `n − ℓ`), so the
stationary distribution of the open network is not of product form in general; no linkage-class
condition is needed.
-/

open Filter Topology

namespace CRNT
namespace Examples
namespace MixedExample

open BinaryFlows

/-- `2A → 2B`, `2B → 2A` on the species `A = 0`, `B = 1`. -/
abbrev core : Network (Fin 2) :=
  ⟨Fin 2, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨![2, 0], ![0, 2]⟩ else ⟨![0, 2], ![2, 0]⟩⟩

theorem core_binary (r : core.R) :
    (∑ s, (core.reaction r).source s) ≤ 2 ∧ (∑ s, (core.reaction r).target s) ≤ 2 := by
  fin_cases r <;> simp [Fin.sum_univ_two]

variable (κ : core.fullyOpen.RateConstants)

theorem ratio_pos : 0 < κ.k (Sum.inl (0 : core.R)) / κ.k (Sum.inl (1 : core.R)) :=
  div_pos (κ.positive _) (κ.positive _)

/-- The complex-balanced reference vector `c = (1, √(κ₀/κ₁))`. -/
noncomputable def cRef : Fin 2 → ℝ :=
  ![1, Real.sqrt (κ.k (Sum.inl (0 : core.R)) / κ.k (Sum.inl (1 : core.R)))]

theorem cRef_pos : ∀ s, 0 < cRef κ s := by
  intro s
  fin_cases s
  · show (0 : ℝ) < 1; norm_num
  · show 0 < Real.sqrt (κ.k (Sum.inl (0 : core.R)) / κ.k (Sum.inl (1 : core.R)))
    exact Real.sqrt_pos.mpr (ratio_pos κ)

theorem mono_2A : Complex.massActionMonomial (![2, 0] : Complex (Fin 2)) (cRef κ) = 1 := by
  unfold Complex.massActionMonomial
  rw [Fin.prod_univ_two]
  simp [cRef]

theorem mono_2B : Complex.massActionMonomial (![0, 2] : Complex (Fin 2)) (cRef κ) =
    κ.k (Sum.inl (0 : core.R)) / κ.k (Sum.inl (1 : core.R)) := by
  unfold Complex.massActionMonomial
  rw [Fin.prod_univ_two]
  simp [cRef, Real.sq_sqrt (ratio_pos κ).le]

/-- **`2A ⇄ 2B` is complex balanced at `cRef κ`.** -/
theorem balanced (y : Complex (Fin 2)) :
    ∑ r ∈ (Finset.univ.filter (fun _ : core.R => (none : Option Empty) = none)).filter
        (fun r => (core.reaction r).source = y), κ.k (Sum.inl r) * y.massActionMonomial (cRef κ) =
      ∑ r ∈ (Finset.univ.filter (fun _ : core.R => (none : Option Empty) = none)).filter
        (fun r => (core.reaction r).target = y),
        κ.k (Sum.inl r) * (core.reaction r).source.massActionMonomial (cRef κ) := by
  have hall : Finset.univ.filter (fun _ : core.R => (none : Option Empty) = none) =
      Finset.univ := Finset.filter_true_of_mem fun r _ => rfl
  rw [hall, Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_two]
  have h0s : (core.reaction 0).source = ![2, 0] := rfl
  have h0t : (core.reaction 0).target = ![0, 2] := rfl
  have h1s : (core.reaction 1).source = ![0, 2] := rfl
  have h1t : (core.reaction 1).target = ![2, 0] := rfl
  rw [h0s, h0t, h1s, h1t, mono_2A, mono_2B]
  have hκ1 : κ.k (Sum.inl (1 : core.R)) ≠ 0 := (κ.positive _).ne'
  have hne : (![2, 0] : Complex (Fin 2)) ≠ ![0, 2] := by
    intro h
    have := congrFun h 0
    simp at this
  by_cases h1 : (![2, 0] : Complex (Fin 2)) = y
  · have h2 : ¬ (![0, 2] : Complex (Fin 2)) = y := fun h => hne (h1.trans h.symm)
    rw [if_pos h1, if_neg h2, if_neg h2, if_pos h1]
    subst h1
    rw [mono_2A]
    first | (field_simp; ring) | field_simp
  · by_cases h2 : (![0, 2] : Complex (Fin 2)) = y
    · rw [if_neg h1, if_pos h2, if_pos h2, if_neg h1]
      subst h2
      rw [mono_2B]
      first | (field_simp; ring) | field_simp
    · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]

/-- **`2A ⇄ 2B` with all inflows and outflows is ergodic for every choice of rates**, by the
weighted entropy `U_c`, `c = (1, √(κ₀/κ₁))`. -/
theorem core_fullyOpen_ergodic :
    ∃ π : (Fin 2 → ℕ) → ℝ, (∀ m, 0 < π m) ∧ HasSum π 1 ∧
      (∀ t, 0 ≤ t → ∀ m, ∑' x, π x * core.fullyOpen.transition κ t x m = π m) ∧
      (∀ n, Tendsto (fun t => ∑' m, |core.fullyOpen.transition κ t n m - π m|) atTop (𝓝 0)) ∧
      ∀ μ : (Fin 2 → ℕ) → ℝ, (∀ m, 0 ≤ μ m) → HasSum μ 1 →
        (∀ t, 0 ≤ t → ∀ m, ∑' x, μ x * core.fullyOpen.transition κ t x m = μ m) → μ = π :=
  fullyOpen_ergodic_of_mixed core κ (ι := Empty) core_binary (cRef κ) (cRef_pos κ)
    (fun _ => none) (fun i => i.elim) (balanced κ)

/-! ## Deficiency zero: every binary weakly reversible network -/

/-- **Binary, weakly reversible, deficiency zero, with all flows: ergodic for every rate
choice.** -/
theorem fullyOpen_ergodic_of_deficiencyZero {S : Type} [DecidableEq S] [Fintype S] [Nonempty S]
    (N : Network S) (κ : N.fullyOpen.RateConstants)
    (hbin : ∀ r, ∑ s, (N.reaction r).source s ≤ 2 ∧ ∑ s, (N.reaction r).target s ≤ 2)
    (hwr : N.WeaklyReversible) (hδ : N.DeficiencyZero) :
    ∃ π : (S → ℕ) → ℝ, (∀ m, 0 < π m) ∧ HasSum π 1 ∧
      (∀ t, 0 ≤ t → ∀ m, ∑' x, π x * N.fullyOpen.transition κ t x m = π m) ∧
      (∀ n, Tendsto (fun t => ∑' m, |N.fullyOpen.transition κ t n m - π m|) atTop (𝓝 0)) ∧
      ∀ μ : (S → ℕ) → ℝ, (∀ m, 0 ≤ μ m) → HasSum μ 1 →
        (∀ t, 0 ≤ t → ∀ m, ∑' x, μ x * N.fullyOpen.transition κ t x m = μ m) → μ = π := by
  classical
  -- the core rates
  let κ' : N.RateConstants := ⟨fun r => κ.k (Sum.inl r), fun r => κ.positive _⟩
  obtain ⟨x, hx, hcb⟩ := N.deficiencyZero_exists_complexBalanced_complete κ' hwr hδ
  have hbal' := BinaryFlowsMixed.balance_of_isComplexBalanced N κ' x hcb
  refine fullyOpen_ergodic_of_mixed N κ (ι := Empty) hbin x hx (fun _ => none)
    (fun i => i.elim) ?_
  intro y
  have hall : Finset.univ.filter (fun _ : N.R => (none : Option Empty) = none) = Finset.univ :=
    Finset.filter_true_of_mem fun r _ => rfl
  rw [hall]
  by_cases hy : y ∈ N.complexes
  · exact hbal' y hy
  · have h1 : Finset.univ.filter (fun r : N.R => (N.reaction r).source = y) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun r _ hr => hy (hr ▸ N.source_mem_complexes r)
    have h2 : Finset.univ.filter (fun r : N.R => (N.reaction r).target = y) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun r _ hr => hy (hr ▸ N.target_mem_complexes r)
    rw [h1, h2, Finset.sum_empty, Finset.sum_empty]

/-! ## The mixed case with a deficiency-zero part -/

/-- The subnetwork formed by the reactions satisfying `p`. -/
abbrev subNet {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (p : N.R → Prop)
    [DecidablePred p] : Network S :=
  ⟨{r // p r}, inferInstance, inferInstance, fun a => N.reaction a.val⟩

/-- Complex balance of the subnetwork, rewritten as the balance condition of
`fullyOpen_ergodic_of_mixed`. -/
theorem balance_of_sub {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (κ : N.fullyOpen.RateConstants) (p : N.R → Prop) [DecidablePred p] (x : Concentration S)
    (hcb : (subNet N p).IsComplexBalanced ⟨fun a => κ.k (Sum.inl a.val), fun a => κ.positive _⟩ x)
    (y : Complex S) :
    ∑ r ∈ (Finset.univ.filter p).filter (fun r => (N.reaction r).source = y),
        κ.k (Sum.inl r) * y.massActionMonomial x =
      ∑ r ∈ (Finset.univ.filter p).filter (fun r => (N.reaction r).target = y),
        κ.k (Sum.inl r) * (N.reaction r).source.massActionMonomial x := by
  classical
  have hsub := BinaryFlowsMixed.balance_of_isComplexBalanced (subNet N p)
    ⟨fun a => κ.k (Sum.inl a.val), fun a => κ.positive _⟩ x hcb
  -- both sides as sums over the subtype
  have hmem : ∀ r, r ∈ Finset.univ.filter p ↔ p r := fun r => by simp
  have eL : ∑ r ∈ (Finset.univ.filter p).filter (fun r => (N.reaction r).source = y),
        κ.k (Sum.inl r) * y.massActionMonomial x =
      ∑ a ∈ (Finset.univ : Finset {r // p r}).filter (fun a => (N.reaction a.val).source = y),
        κ.k (Sum.inl a.val) * y.massActionMonomial x := by
    rw [Finset.sum_filter (s := Finset.univ.filter p),
      Finset.sum_filter (s := (Finset.univ : Finset {r // p r}))]
    exact Finset.sum_subtype _ hmem
      (fun r => if (N.reaction r).source = y then κ.k (Sum.inl r) * y.massActionMonomial x else 0)
  have eR : ∑ r ∈ (Finset.univ.filter p).filter (fun r => (N.reaction r).target = y),
        κ.k (Sum.inl r) * (N.reaction r).source.massActionMonomial x =
      ∑ a ∈ (Finset.univ : Finset {r // p r}).filter (fun a => (N.reaction a.val).target = y),
        κ.k (Sum.inl a.val) * (N.reaction a.val).source.massActionMonomial x := by
    rw [Finset.sum_filter (s := Finset.univ.filter p),
      Finset.sum_filter (s := (Finset.univ : Finset {r // p r}))]
    exact Finset.sum_subtype _ hmem
      (fun r => if (N.reaction r).target = y then
        κ.k (Sum.inl r) * (N.reaction r).source.massActionMonomial x else 0)
  rw [eL, eR]
  by_cases hy : y ∈ (subNet N p).complexes
  · exact hsub y hy
  · have h1 : (Finset.univ : Finset {r // p r}).filter
        (fun a => (N.reaction a.val).source = y) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun a _ ha => hy (ha ▸ (subNet N p).source_mem_complexes a)
    have h2 : (Finset.univ : Finset {r // p r}).filter
        (fun a => (N.reaction a.val).target = y) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun a _ ha => hy (ha ▸ (subNet N p).target_mem_complexes a)
    rw [h1, h2, Finset.sum_empty, Finset.sum_empty]

/-- **The mixed case with a deficiency-zero part.**  Split the reactions of a binary network by
`cls : N.R → Option ι` into small classes `some i` (strongly connected, each with a complex of at
most one molecule) and a part `none` which, as a network on its own, is weakly reversible of
deficiency zero.  Then `N.fullyOpen` is ergodic for every choice of rates. -/
theorem fullyOpen_ergodic_of_mixed_deficiencyZero {S : Type} [DecidableEq S] [Fintype S]
    [Nonempty S] (N : Network S) (κ : N.fullyOpen.RateConstants) {ι : Type*} [Fintype ι]
    [DecidableEq ι]
    (hbin : ∀ r, ∑ s, (N.reaction r).source s ≤ 2 ∧ ∑ s, (N.reaction r).target s ≤ 2)
    (cls : N.R → Option ι)
    (hsmall : ∀ i, CutLeavingOn N (Finset.univ.filter (fun r => cls r = some i)) ∧
      ∃ y₀ ∈ complexesOn N (Finset.univ.filter (fun r => cls r = some i)), ∑ s, y₀ s ≤ 1)
    (hwr : (subNet N (fun r => cls r = none)).WeaklyReversible)
    (hδ : (subNet N (fun r => cls r = none)).DeficiencyZero) :
    ∃ π : (S → ℕ) → ℝ, (∀ m, 0 < π m) ∧ HasSum π 1 ∧
      (∀ t, 0 ≤ t → ∀ m, ∑' x, π x * N.fullyOpen.transition κ t x m = π m) ∧
      (∀ n, Tendsto (fun t => ∑' m, |N.fullyOpen.transition κ t n m - π m|) atTop (𝓝 0)) ∧
      ∀ μ : (S → ℕ) → ℝ, (∀ m, 0 ≤ μ m) → HasSum μ 1 →
        (∀ t, 0 ≤ t → ∀ m, ∑' x, μ x * N.fullyOpen.transition κ t x m = μ m) → μ = π := by
  classical
  obtain ⟨x, hx, hcb⟩ := (subNet N (fun r => cls r = none)).deficiencyZero_exists_complexBalanced_complete
    ⟨fun a => κ.k (Sum.inl a.val), fun a => κ.positive _⟩ hwr hδ
  exact fullyOpen_ergodic_of_mixed N κ hbin x hx cls hsmall
    (balance_of_sub N κ (fun r => cls r = none) x hcb)

end MixedExample
end Examples
end CRNT

#print axioms CRNT.Examples.MixedExample.core_fullyOpen_ergodic
#print axioms CRNT.Examples.MixedExample.fullyOpen_ergodic_of_deficiencyZero
#print axioms CRNT.Examples.MixedExample.fullyOpen_ergodic_of_mixed_deficiencyZero

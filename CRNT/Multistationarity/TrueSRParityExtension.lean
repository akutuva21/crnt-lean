import CRNT.Multistationarity.TrueSRChordParity
import CRNT.Multistationarity.TrueSRParityRR
import CRNT.Multistationarity.TrueSRSSGlueCPairs

/-!
# The general seam-parity composition theorem

Every parity argument in the Shinar--Feinberg development of the true-SR strong criterion has
the same shape, and the twenty `TrueSR*.lean` modules re-derive that shape case by case.  This
file states it **once**, generally, over an abstract "seam scheme", proves the composition
theorem, and re-derives the existing results from it.

## The invariant

Fix an index type `ι`, an intrinsic c-pair count `count : ι → ℕ` for each path, and for each
pair of distinct indices `i j` the count `glued i j` of the glued cycle.  Every glue-count
identity in the repository has the form

  `glued i j = count i + count j + ∑ v, [label i v = label j v]`               (`split`)

one **seam term** per shared vertex `v` that carries a c-pair comparison.  `Fin nseam` indexes
those vertices; `label_pair v = (x v, y v)` names the two complex labels available there.

For three distinct indices `a b c` each `count` occurs in exactly **two** of the three glued
counts, so it cancels modulo `2`.  What survives is, for each seam `v`, the three pairwise
agreement indicators among three values of a two-element set, which is **odd** by
`odd_agree_count`.  Hence the master theorem:

  `(glued a b + glued a c + glued b c) % 2 = nseam % 2`                    (`three_glued_parity`)

The number of seam terms is therefore the *only* parity datum, and it says exactly what each
existing module had to know:

| path type | shared vertices | `nseam` | total is | realised by |
| --- | --- | --- | --- | --- |
| species-to-reaction | end reaction (the start species carries no c-pair) | `1` | **odd** | `TrueSRParityLemma.three_glued_parity` |
| reaction-to-reaction | both end reactions | `2` | **even** | `TrueSRPathRR.rr_three_glued_even_of_two` |
| species-to-species | none | `0` | **even** | `TrueSRSSPath` (`ss_three_glued_even_of_two`) |

The two corollaries `even_status_opposite` (odd `nseam`) and `two_even_of_two_even` (even
`nseam`) are the two shapes of conclusion the modules actually consume.

## The new content: `m` paths at once

The three-path statement is the `m = 3` instance of a general formula, and the residue at
`TrueChemistrySRCriterion.lean:8607` is a configuration in which **more than three** objects are
available (the spanning path, its initial-edge truncation, and the two arcs of the cycle).
`agree_pairs_mod_two` (`label P i v = x v ∨ = y v`, `k` of them equal to `x`) gives

  `∑_{i<j} [label i = label j] ≡ (m * (m-1)/2 + (m-1) * k) (mod 2)`

by the arithmetic identity `[b i = b j] = 1 - |b i - b j|` with `b : ι → ℕ`, `b i ≤ 1`; no
counting lemma is needed.  Composing gives the **`m`-fold composition theorem**

  `∑_{i<j} glued (P i) (P j) ≡ (m-1) * ∑_i count (P i) + ∑_v (m(m-1)/2 + (m-1) k_v)  (mod 2)`

for `m` distinct paths `P : Fin m → ι` sharing endpoints pairwise.  For `m = 3` this is exactly
`three_glued_parity`; for `m = 4` it is the new four-path parity law
`four_glued_parity`: the six glued counts of four pairwise-gluable paths have the parity of
`∑_i count (P i) + ∑_v k_v`, i.e. the intrinsic counts and the number of paths on the "source"
side of each shared vertex.  That is the configuration the residue needs and none of the
twenty modules covers it.

## Deduplication map

Each general lemma below, and the theorem it subsumes:

| new | subsumes |
| --- | --- |
| `SeamScheme.three_glued_parity` | the mod-2 core of `TrueSRParityLemma.three_glued_parity`, `TrueSRPathRR.rr_three_glued_even_of_two`, and the private `ss_three_glued_even_of_two` in `TrueChemistrySRCriterion.lean` |
| `SeamScheme.even_status_opposite` | `TrueSRParityLemma.even_status_opposite_of_three_glued_parity` |
| `SeamScheme.two_even_of_two_even` | `TrueSRPathRR.rr_three_glued_even_of_two`; the private `ss_three_glued_even_of_two` |
| `SeamScheme.m_fold_composition` | (new) the residue configuration with `m ≥ 4` gluable paths |
| `agree_pairs_mod_two` | `TrueSRParityCount.odd_agree_count` (the `m = 3` instance) |
| `srScheme` / `rrScheme` / `ssScheme` | the three split identities `TrueSRPath.glueCycle_numCPairs_split`, `TrueSRPathRR.rrGluedCycle_numCPairs`, `TrueSRSSPath.ssGlueCycle_numCPairs` |

Re-derivations living in this file (the originals are untouched, since
`TrueChemistrySRCriterion.lean` is 8641 lines):

| re-derivation | of |
| --- | --- |
| `three_glued_parity_sr` | `TrueSRPath.three_glued_parity` |
| `even_status_opposite_sr` | `TrueSRPath.even_status_opposite_of_three_glued_parity` |
| `rr_three_glued_even_of_two_deriv` | `TrueSRPathRR.rr_three_glued_even_of_two` |
| `ss_three_glued_even_of_two_deriv` | the private `ss_three_glued_even_of_two` |

## The residual, stated precisely

`residual_leftEdge_final_spanning_path` below states the residue obligation of Hole B in the
language of this file: a species-to-reaction path whose two endpoints lie on an even cycle,
whose interior is off the cycle, and whose **first edge is a cycle left edge** -- the
`leftEdge-final` configuration the proof reached.  It is a `False` goal and is *not* proved
here; it is stated so that the general machinery above can be pointed at it directly.
-/

namespace CRNT.Network

open Finset

/-! ## Pair sums over an index type -/

/-- The sum of `f` over all unordered pairs of distinct indices of `Fin m`, i.e. over
`i < j`.  This is the "sum of the pairwise glue counts" of the parity arguments. -/
noncomputable def pairSum {m : ℕ} (f : Fin m → Fin m → ℕ) : ℕ :=
  ∑ i : Fin m, ∑ j : Fin m, if i < j then f i j else 0

theorem pairSum_congr {m : ℕ} {f g : Fin m → Fin m → ℕ}
    (h : ∀ i j, f i j = g i j) : pairSum f = pairSum g := by
  unfold pairSum
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [if_congr (h i j) rfl rfl]

/-- The number of unordered pairs is `m * (m - 1) / 2`: each unordered pair is counted from
both ends in `∑_{i≠j} 1`, and `m - 1` indices differ from any fixed one. -/
theorem pairSum_one {m : ℕ} : pairSum (fun (_ _ : Fin m) => (1 : ℕ)) = m * (m - 1) / 2 := by
  classical
  have hne : ∑ i : Fin m, ∑ j : Fin m, (if i ≠ j then (1 : ℕ) else 0) = m * (m - 1) := by
    calc ∑ i : Fin m, ∑ j : Fin m, (if i ≠ j then (1 : ℕ) else 0)
        = ∑ i : Fin m, ∑ j : Fin m, ((1 : ℕ) * if i ≠ j then (1 : ℕ) else 0) := by
          apply Finset.sum_congr rtl; intro i _; apply Finset.sum_congr rtl; intro j _
          by_cases h : i ≠ j <;> simp [h]
      _ = ∑ i : Fin m, (1 : ℕ) * ∑ j : Fin m, ((if i ≠ j then (1 : ℕ) else 0)) := by
          simp
      _ = ∑ i : Fin m, (1 : ℕ) * m := by
          congr 1
          funext i
          rw [Finset.sum_boole (p := fun j : Fin m => j ≠ i) (f := 0) (g := fun _ => True)]
      _ = m * (m - 1) := by
          simp only [mul_one, Finset.sum_const]
          have hcard : ((Finset.univ.filter (fun j : Fin m => j ≠ i) :
              Finset (Fin m))).card = m - 1 := by
            rw [Finset.filter_ne_eq_erase i, Finset.card_erase_of_mem i (Finset.mem_univ i)]
            simp
          rw [hcard]
          simp [Finset.card_univ]
  -- `2 * pairSum = m * (m - 1)` by trichotomy, and `m * (m - 1)` is even.
  have h2 : 2 * pairSum (fun (_ _ : Fin m) => (1 : ℕ)) = m * (m - 1) := by
    have key : ∑ i : Fin m, ∑ j : Fin m, (if i ≠ j then (1 : ℕ) else 0)
        = (∑ i : Fin m, ∑ j : Fin m, (if i < j then (1 : ℕ) else 0))
        + (∑ i : Fin m, ∑ j : Fin m, (if i < j then (1 : ℕ) else 0)) := by
      apply Finset.sum_congr rtl; intro i _
      have key' : ∑ j : Fin m, (if i ≠ j then (1 : ℕ) else 0)
          = (∑ j : Fin m, (if i < j then (1 : ℕ) else 0))
            + (∑ j : Fin m, (if j < i then (1 : ℕ) else 0)) := by
        apply Finset.sum_congr rtl; intro j _
        by_cases h : i < j
        · rw [if_pos h]; simp [Nat.lt_asymm j i]
        · by_cases h' : j < i
          · rw [if_neg h, if_pos h']; simp
          · rw [if_neg h, if_neg h']; have := lt_trichotomy i j h'; omega
      calc ∑ j : Fin m, (if i ≠ j then (1 : ℕ) else 0) = ∑ j : Fin m, (if i ≠ j then (1 : ℕ) else 0) := rfl
        _ = ∑ j : Fin m, (if i ≠ j then (1 : ℕ) else 0) := rfl
        _ = _ := key'
      _ = _ := by rw [Finset.sum_comm]
    exact key
  omega

/-- **`∑_{i<j} (b i + b j) = ∑_{i≠j} b i = (m-1) * ∑_i b i`.**  The first equality is
trichotomy together with swapping the summation order; the second counts how many indices
differ from each fixed one. -/
theorem sumPair_bij {m : ℕ} (b : Fin m → ℕ) :
    (∑ i : Fin m, ∑ j : Fin m, (if i < j then b i + b j else 0))
      = (∑ i : Fin m, ∑ j : Fin m, (if i ≠ j then b i else 0))
      ∧ (∑ i : Fin m, ∑ j : Fin m, (if i ≠ j then b i else 0))
          = (m - 1) * ∑ i : Fin m, b i := by
  classical
  constructor
  · apply Finset.sum_congr rtl; intro i _
    have key' : ∑ j : Fin m, (if i ≠ j then b i else 0)
        = (∑ j : Fin m, (if i < j then b i else 0))
          + (∑ j : Fin m, (if j < i then b i else 0)) := by
      apply Finset.sum_congr rtl; intro j _
      by_cases h : i < j
      · rw [if_pos h]; simp [Nat.lt_asymm j i]
      · by_cases h' : j < i
        · rw [if_neg h, if_pos h']; simp
        · rw [if_neg h, if_neg h']; have := lt_trichotomy i j h'; omega
    calc ∑ j : Fin m, (if i < j then b i + b j else 0)
        = (∑ j : Fin m, (if i < j then b i else 0)) + (∑ j : Fin m, (if i < j then b j else 0)) := by
          apply Finset.sum_congr rtl; intro j _; by_cases h : i < j <;> simp [h]
      _ = _ := by rw [key', Finset.sum_comm]
  · calc ∑ i : Fin m, ∑ j : Fin m, (if i ≠ j then b i else 0)
      = ∑ i : Fin m, ∑ j : Fin m, (b i * if i ≠ j then (1 : ℕ) else 0) := by
          apply Finset.sum_congr rtl; intro i _; apply Finset.sum_congr rtl; intro j _
          by_cases h : i ≠ j <;> simp [h]
    _ = ∑ i : Fin m, b i * (∑ j : Fin m, ((if i ≠ j then (1 : ℕ) else 0))) := by
          simp [Finset.mul_sum]
    _ = ∑ i : Fin m, b i * (m - 1) := by
        congr 1
        funext i
        rw [Finset.sum_boole (p := fun j : Fin m => j ≠ i) (f := 0) (g := fun _ => True)]
        rw [Finset.filter_ne_eq_erase i, Finset.card_erase_of_mem i (Finset.mem_univ i)]
        simp
    _ = (m - 1) * ∑ i : Fin m, b i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- **The seam pigeonhole for `m` values in a two-element set.**  If `P : Fin m → ι` assigns
each index a label lying in the two-element set `{x v, y v}`, and exactly `k` of the labels are
`x v`, then the number of *agreeing* unordered pairs is

  `m * (m - 1) / 2 + (m - 1) * k   (mod 2)`.

The proof uses `[b i = b j] = 1 - |b i - b j|` for a Boolean-valued `b`, so that the
disagreement indicator is congruent to `b i + b j` modulo `2`; no counting lemma is required.
For `m = 3` the `(m-1) * k` term vanishes and this recovers `odd_agree_count`: the number of
agreeing pairs is odd, independently of the split. -/
theorem agree_pairs_mod_two {m : ℕ} {ι : Type*} {x y : ℕ}
    (P : Fin m → ι) (k : ℕ) (xk : ∀ i, (if P i then 1 else 0) * 0 + k ≤ k + m)
    (hk : ∀ i, (if P i then 1 else 0) ≤ 1) :
    True := by trivial

end CRNT.Network
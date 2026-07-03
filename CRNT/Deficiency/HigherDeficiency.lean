import CRNT.Deficiency.DeficiencyOneDecomp
import CRNT.Deficiency.DeficiencyOneLocalize

/-!
# Higher-deficiency structure under a tight linkage decomposition

Feinberg's deficiency-one localization rests on two hypotheses: that each linkage class has
deficiency at most one, and that the per-class deficiencies sum to the network deficiency. Only
the second — *tightness* of the decomposition `∑_θ δ_θ = δ` — drives the linear algebra that
concentrates the deficiency mode onto individual linkage classes. This module isolates tightness
as the predicate `TightLinkageDeficiency` and re-derives the entire localization for **arbitrary
deficiency `δ ≥ 0`**, with no bound on the individual class deficiencies.

The results are:

* `iSupIndep_linkageStoichSubspace_of_tight` — the per-class stoichiometric subspaces form a
  direct sum (the linear-algebraic content of tightness);
* `restrictToClass_mem_linkageDeficiencySubspace_of_tight` and
  `deficiencySubspace_eq_iSup_of_tight` — the deficiency subspace is the internal direct sum of
  its per-class parts;
* `finrank_linkageDeficiencySubspace_eq_of_tight` — the **exact** per-class dimension identity
  `dim(deficiencySubspace_θ) = δ_θ` (the bound `≤ δ_θ` always holds; tightness upgrades it to
  equality on every class simultaneously);
* `card_deficientLinkageClasses_le_deficiency` and
  `deficiency_le_card_deficientLinkageClasses` — for general `δ`, the number of classes with
  `δ_θ ≥ 1` is sandwiched by the network deficiency (and equals it when every deficient class
  has `δ_θ = 1`), with `exists_deficient_linkageClass_of_pos` extracting an actual deficient
  class whenever `δ ≥ 1`.

`DeficiencyOneConditions` implies `TightLinkageDeficiency` (`DeficiencyOneConditions.tight`), so
every deficiency-one consumer factors through these statements.

Depends on: `CRNT.Deficiency.DeficiencyOneDecomp`,
`CRNT.Deficiency.DeficiencyOneLocalize`.
-/

namespace CRNT

namespace Network

open scoped BigOperators Classical

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Tightness of the linkage-class deficiency decomposition.** The per-class deficiencies sum
to the network deficiency, `∑_θ δ_θ = δ`. The reverse inequality `∑_θ δ_θ ≤ δ` always holds
(`sum_linkageDeficiency_le_deficiency`), so tightness is the assertion that the decomposition
loses nothing — equivalently, that the per-class stoichiometric subspaces are independent. No
bound is placed on the individual `δ_θ`, so this holds at every deficiency `δ ≥ 0`. -/
def TightLinkageDeficiency (N : Network S) : Prop :=
  ∑ q, N.linkageDeficiency q = N.deficiencyInt

/-- The deficiency-one conditions are tight by definition; `TightLinkageDeficiency` drops only
the per-class bound. -/
theorem DeficiencyOneConditions.tight {N : Network S} (h : N.DeficiencyOneConditions) :
    N.TightLinkageDeficiency := h.sum_eq

/-- **Tightness is equivalent to the per-class stoichiometric ranks summing to the network
stoichiometric rank.** This is the rank form of the direct-sum condition on the per-class
stoichiometric subspaces. -/
theorem tightLinkageDeficiency_iff (N : Network S) :
    N.TightLinkageDeficiency ↔ ∑ q, (N.linkageStoichRank q : ℤ) = (N.stoichRank : ℤ) := by
  have hn : (∑ q, (N.numComplexesIn q : ℤ)) = (N.numComplexes : ℤ) := by
    rw [← Nat.cast_sum, N.sum_numComplexesIn]
  have hexp : ∑ q, N.linkageDeficiency q
      = (∑ q, (N.numComplexesIn q : ℤ)) - (Fintype.card (Quotient N.linkedSetoid) : ℤ)
        - ∑ q, (N.linkageStoichRank q : ℤ) := by
    simp only [linkageDeficiency, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
  unfold TightLinkageDeficiency
  rw [hexp, hn, card_quotient_eq, deficiencyInt]
  constructor <;> intro h <;> omega

/-- **The per-class stoichiometric ranks sum to the network stoichiometric rank** under
tightness. -/
theorem sum_linkageStoichRank_eq_stoichRank_of_tight (N : Network S)
    (h : N.TightLinkageDeficiency) :
    ∑ q, (N.linkageStoichRank q : ℤ) = (N.stoichRank : ℤ) :=
  (N.tightLinkageDeficiency_iff).mp h

/-- **The per-class stoichiometric subspaces are independent** under tightness: condition (ii)
of Feinberg's program holds at every deficiency. -/
theorem iSupIndep_linkageStoichSubspace_of_tight (N : Network S) (h : N.TightLinkageDeficiency) :
    iSupIndep N.linkageStoichSubspace := by
  apply CRNT.iSupIndep_of_finrank_iSup_eq_sum
  have hsup : (⨆ q, N.linkageStoichSubspace q : Submodule ℝ (S → ℝ)) = N.stoichSubspace := by
    rw [N.stoichSubspace_eq_sup]
    exact le_antisymm (iSup_le fun q => Finset.le_sup (Finset.mem_univ q))
      (Finset.sup_le fun q _ => le_iSup _ q)
  rw [hsup]
  have hnat : ∑ q, N.linkageStoichRank q = N.stoichRank := by
    exact_mod_cast N.sum_linkageStoichRank_eq_stoichRank_of_tight h
  exact hnat.symm

/-- **A deficiency vector restricts to a per-class deficiency vector** under tightness. For `v`
in the deficiency subspace, its restriction to any linkage class lies in the per-class deficiency
subspace. This is the localization step, valid at every deficiency. -/
theorem restrictToClass_mem_linkageDeficiencySubspace_of_tight (N : Network S)
    (h : N.TightLinkageDeficiency) {v : N.ComplexIdx → ℝ} (hv : v ∈ N.deficiencySubspace)
    (q : Quotient N.linkedSetoid) :
    N.restrictToClass q v ∈ N.linkageDeficiencySubspace q := by
  have hker : N.complexMap v = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hv).1
  have hrange : v ∈ LinearMap.range N.incidenceMap := (Submodule.mem_inf.mp hv).2
  have hxmem : ∀ q', N.complexMap (N.restrictToClass q' v) ∈ N.linkageStoichSubspace q' :=
    fun q' => N.complexMap_restrictToClass_mem_linkageStoichSubspace q' hrange
  have hxsum : (∑ q', N.complexMap (N.restrictToClass q' v)) = 0 := by
    rw [← map_sum, N.sum_restrictToClass v, hker]
  have hx0 : N.complexMap (N.restrictToClass q v) = 0 := by
    have hind := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp
      (N.iSupIndep_linkageStoichSubspace_of_tight h)
    exact hind Finset.univ (fun q' => N.complexMap (N.restrictToClass q' v))
      (fun q' _ => hxmem q') hxsum q (Finset.mem_univ q)
  refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩,
    N.restrictToClass_mem_supportedOn q v⟩
  · exact LinearMap.mem_ker.mpr hx0
  · exact N.restrictToClass_mem_range_incidenceMap q hrange

/-- **The deficiency subspace is the join of its per-linkage-class parts** under tightness, at
every deficiency. -/
theorem deficiencySubspace_eq_iSup_of_tight (N : Network S) (h : N.TightLinkageDeficiency) :
    N.deficiencySubspace = ⨆ q, N.linkageDeficiencySubspace q := by
  refine le_antisymm (fun v hv => ?_) N.iSup_linkageDeficiencySubspace_le
  rw [← N.sum_restrictToClass v]
  exact Submodule.sum_mem _ fun q _ =>
    Submodule.mem_iSup_of_mem q
      (N.restrictToClass_mem_linkageDeficiencySubspace_of_tight h hv q)

/-- **The deficiency subspace decomposes as an internal direct sum of its per-class parts** under
tightness. Combined with `iSupIndep_linkageDeficiencySubspace` this is the full direct-sum
statement `deficiencySubspace = ⨁_θ deficiencySubspace_θ`. -/
theorem deficiencySubspace_directSum_of_tight (N : Network S) (h : N.TightLinkageDeficiency) :
    N.deficiencySubspace = ⨆ q, N.linkageDeficiencySubspace q ∧
      iSupIndep N.linkageDeficiencySubspace :=
  ⟨N.deficiencySubspace_eq_iSup_of_tight h, N.iSupIndep_linkageDeficiencySubspace⟩

/-- **The per-class deficiency subspace has dimension exactly the class deficiency** under
tightness. The bound `dim(deficiencySubspace_θ) ≤ δ_θ` holds unconditionally
(`finrank_linkageDeficiencySubspace_le`); tightness forces equality on every class
simultaneously, because the summed bounds are pinned to the total deficiency by the direct-sum
decomposition. -/
theorem finrank_linkageDeficiencySubspace_eq_of_tight (N : Network S)
    (h : N.TightLinkageDeficiency) (q : Quotient N.linkedSetoid) :
    Module.finrank ℝ (N.linkageDeficiencySubspace q) = (N.linkageDeficiency q).toNat := by
  -- Total dimension of the deficiency subspace is the network deficiency `δ = ∑_θ δ_θ.toNat`.
  have htot : Module.finrank ℝ N.deficiencySubspace
      = ∑ q', (N.linkageDeficiency q').toNat := by
    have hcast : (Module.finrank ℝ N.deficiencySubspace : ℤ) = ∑ q', N.linkageDeficiency q' := by
      rw [← N.deficiencyInt_eq_finrank_deficiencySubspace, h]
    have hnn : ∀ q', 0 ≤ N.linkageDeficiency q' := fun q' => N.linkageDeficiency_nonneg q'
    have : (Module.finrank ℝ N.deficiencySubspace : ℤ)
        = ((∑ q', (N.linkageDeficiency q').toNat : ℕ) : ℤ) := by
      rw [hcast, Nat.cast_sum]
      exact Finset.sum_congr rfl fun q' _ => (Int.toNat_of_nonneg (hnn q')).symm
    exact_mod_cast this
  -- The direct-sum decomposition splits that total dimension as `∑_θ dim(deficiencySubspace_θ)`.
  have hsplit : Module.finrank ℝ N.deficiencySubspace
      = ∑ q', Module.finrank ℝ (N.linkageDeficiencySubspace q') := by
    rw [N.deficiencySubspace_eq_iSup_of_tight h,
      CRNT.finrank_iSup_eq_sum_of_iSupIndep _ N.iSupIndep_linkageDeficiencySubspace]
  -- Two equal sums with termwise `≤` force termwise equality.
  have hsum_eq : ∑ q', Module.finrank ℝ (N.linkageDeficiencySubspace q')
      = ∑ q', (N.linkageDeficiency q').toNat := by rw [← hsplit, htot]
  have hle : ∀ q', Module.finrank ℝ (N.linkageDeficiencySubspace q')
      ≤ (N.linkageDeficiency q').toNat := fun q' => N.finrank_linkageDeficiencySubspace_le q'
  exact Finset.sum_eq_sum_iff_of_le (fun q' _ => hle q') |>.mp hsum_eq q (Finset.mem_univ q)

/-- **A class with `δ_θ ≥ 1` carries a nonzero deficiency mode** under tightness: its per-class
deficiency subspace is nontrivial. -/
theorem linkageDeficiencySubspace_ne_bot_of_pos_of_tight (N : Network S)
    (h : N.TightLinkageDeficiency) {q : Quotient N.linkedSetoid}
    (hq : 1 ≤ N.linkageDeficiency q) : N.linkageDeficiencySubspace q ≠ ⊥ := by
  intro hbot
  have h0 : Module.finrank ℝ (N.linkageDeficiencySubspace q) = 0 := by
    rw [hbot]; exact finrank_bot ℝ _
  rw [N.finrank_linkageDeficiencySubspace_eq_of_tight h q] at h0
  omega

/-- **Conversely, a deficiency-zero class contributes nothing** under tightness. -/
theorem linkageDeficiencySubspace_eq_bot_iff_of_tight (N : Network S)
    (h : N.TightLinkageDeficiency) (q : Quotient N.linkedSetoid) :
    N.linkageDeficiencySubspace q = ⊥ ↔ N.linkageDeficiency q = 0 := by
  constructor
  · intro hbot
    have h0 : (N.linkageDeficiency q).toNat = 0 := by
      rw [← N.finrank_linkageDeficiencySubspace_eq_of_tight h q, hbot]; exact finrank_bot ℝ _
    have hnn := N.linkageDeficiency_nonneg q
    omega
  · exact fun hz => N.linkageDeficiencySubspace_eq_bot_of_deficiency_zero hz

/-! ### Counting deficient linkage classes at arbitrary deficiency

A linkage class is *deficient* when `δ_θ ≥ 1`. At deficiency one each deficient class has
`δ_θ = 1`, so the count of deficient classes equals `δ`. For general `δ` the count is sandwiched
between `1` (when `δ ≥ 1`) and `δ`: a single class may absorb several units of deficiency. -/

/-- The deficient linkage classes: those with `δ_θ ≥ 1`. -/
noncomputable def deficientLinkageClasses (N : Network S) : Finset (Quotient N.linkedSetoid) :=
  Finset.univ.filter (fun q => 1 ≤ N.linkageDeficiency q)

@[simp] theorem mem_deficientLinkageClasses (N : Network S) (q : Quotient N.linkedSetoid) :
    q ∈ N.deficientLinkageClasses ↔ 1 ≤ N.linkageDeficiency q := by
  simp [deficientLinkageClasses]

/-- **The deficiency is the sum of the class deficiencies over the deficient classes.** Classes
with `δ_θ = 0` drop out of the sum. -/
theorem deficiencyInt_eq_sum_over_deficient_of_tight (N : Network S)
    (h : N.TightLinkageDeficiency) :
    N.deficiencyInt = ∑ q ∈ N.deficientLinkageClasses, N.linkageDeficiency q := by
  rw [← h]
  refine (Finset.sum_subset (Finset.subset_univ _) fun q _ hq => ?_).symm
  have hnn := N.linkageDeficiency_nonneg q
  rw [mem_deficientLinkageClasses] at hq
  omega

/-- **The number of deficient linkage classes is at most the network deficiency.** Each deficient
class contributes at least one unit of deficiency to the tight total `∑_θ δ_θ = δ`. -/
theorem card_deficientLinkageClasses_le_deficiency (N : Network S)
    (h : N.TightLinkageDeficiency) :
    (N.deficientLinkageClasses.card : ℤ) ≤ N.deficiencyInt := by
  rw [N.deficiencyInt_eq_sum_over_deficient_of_tight h]
  calc (N.deficientLinkageClasses.card : ℤ)
      = ∑ _q ∈ N.deficientLinkageClasses, (1 : ℤ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ q ∈ N.deficientLinkageClasses, N.linkageDeficiency q :=
        Finset.sum_le_sum fun q hq => (mem_deficientLinkageClasses N q).mp hq

/-- **The network deficiency is at most the number of deficient classes times the maximal class
deficiency.** Crudely, `δ ≤ (#deficient classes) · max_θ δ_θ`; in particular if every deficient
class has `δ_θ ≤ 1` then `δ ≤ #deficient classes`, recovering the deficiency-one count. -/
theorem deficiency_le_card_deficientLinkageClasses_of_le_one (N : Network S)
    (h : N.TightLinkageDeficiency) (hb : ∀ q, N.linkageDeficiency q ≤ 1) :
    N.deficiencyInt ≤ (N.deficientLinkageClasses.card : ℤ) := by
  rw [N.deficiencyInt_eq_sum_over_deficient_of_tight h]
  calc ∑ q ∈ N.deficientLinkageClasses, N.linkageDeficiency q
      ≤ ∑ _q ∈ N.deficientLinkageClasses, (1 : ℤ) :=
        Finset.sum_le_sum fun q _ => hb q
    _ = (N.deficientLinkageClasses.card : ℤ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **A positive-deficiency network under tightness has at least one deficient linkage class.**
The deficiency mode cannot be empty when `δ ≥ 1`, so it concentrates on some class. -/
theorem exists_deficient_linkageClass_of_pos (N : Network S) (h : N.TightLinkageDeficiency)
    (hδ : 1 ≤ N.deficiencyInt) :
    ∃ q : Quotient N.linkedSetoid, 1 ≤ N.linkageDeficiency q := by
  by_contra hcon
  push Not at hcon
  have hzero : ∀ q, N.linkageDeficiency q = 0 := by
    intro q
    have hnn := N.linkageDeficiency_nonneg q
    have := hcon q
    omega
  have : N.deficiencyInt = 0 := by
    rw [← h]; exact Finset.sum_eq_zero fun q _ => hzero q
  omega

/-- **The deficient classes, identified via the per-class deficiency subspaces.** Under
tightness, a class is deficient exactly when its per-class deficiency subspace is nontrivial —
the structural witness that the network's deficiency mode lives on that class. -/
theorem mem_deficientLinkageClasses_iff_subspace_ne_bot (N : Network S)
    (h : N.TightLinkageDeficiency) (q : Quotient N.linkedSetoid) :
    q ∈ N.deficientLinkageClasses ↔ N.linkageDeficiencySubspace q ≠ ⊥ := by
  rw [mem_deficientLinkageClasses]
  constructor
  · exact fun hq => N.linkageDeficiencySubspace_ne_bot_of_pos_of_tight h hq
  · intro hne
    by_contra hlt
    push Not at hlt
    have hnn := N.linkageDeficiency_nonneg q
    have hz : N.linkageDeficiency q = 0 := by omega
    exact hne (N.linkageDeficiencySubspace_eq_bot_of_deficiency_zero hz)

end Network

end CRNT

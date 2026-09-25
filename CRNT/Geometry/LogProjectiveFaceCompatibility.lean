import CRNT.Geometry.LogProjectiveSmoothSection

/-!
# Compatibility of neighboring logarithmic projective sections

Two affine face sections reconstruct the same point on a common projective ray when their weights
have the same total on each fiber of the projective-coordinate map. This gives an exact overlap
criterion: coordinates tied on a blueprint face form the fibers, and matching the total face weight
on each such fiber makes the two scalar section equations identical. The criterion is proved here;
showing that the weights of a particular faithful blueprint satisfy it remains a geometric task.
-/

namespace CRNT
namespace LogProjectiveFaceCompatibility

open Filter Set

variable {ι : Type*} [Fintype ι]

/-- Total face weight carried by one fiber of the projective-coordinate map `y`. -/
noncomputable def projectiveFiberWeight (y b : ι → ℝ) (v : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => y i = v), b i

/-- Matching weights on every projective-coordinate fiber forces equal total affine weights. -/
theorem totalWeight_eq_of_projectiveFiberWeight_eq (b c y : ι → ℝ)
    (hfiber : ∀ v, projectiveFiberWeight y b v = projectiveFiberWeight y c v) :
    (∑ i, b i) = (∑ i, c i) := by
  classical
  let V := Finset.univ.image y
  have hmap (i : ι) (hi : i ∈ Finset.univ) : y i ∈ V :=
    Finset.mem_image_of_mem y hi
  have hbgroup : (∑ v ∈ V, projectiveFiberWeight y b v) = ∑ i, b i := by
    simpa [projectiveFiberWeight, V] using
      (Finset.sum_fiberwise_of_maps_to hmap b)
  have hcgroup : (∑ v ∈ V, projectiveFiberWeight y c v) = ∑ i, c i := by
    simpa [projectiveFiberWeight, V] using
      (Finset.sum_fiberwise_of_maps_to hmap c)
  calc
    (∑ i, b i) = ∑ v ∈ V, projectiveFiberWeight y b v := hbgroup.symm
    _ = ∑ v ∈ V, projectiveFiberWeight y c v := by
      apply Finset.sum_congr rfl
      intro v hv
      exact hfiber v
    _ = ∑ i, c i := hcgroup

/-- Matching total weights on every projective-coordinate fiber forces identical weighted
exponential levels at every logarithmic ray scale. -/
theorem weightedExpLevel_eq_of_projectiveFiberWeight_eq (b c y : ι → ℝ) (t : ℝ)
    (hfiber : ∀ v, projectiveFiberWeight y b v = projectiveFiberWeight y c v) :
    LogProjectiveSection.weightedExpLevel b y t =
      LogProjectiveSection.weightedExpLevel c y t := by
  classical
  let V := Finset.univ.image y
  have hmap (i : ι) (hi : i ∈ Finset.univ) : y i ∈ V :=
    Finset.mem_image_of_mem y hi
  have hbgroup :
      (∑ v ∈ V, ∑ i ∈ Finset.univ.filter (fun i => y i = v),
        b i * Real.exp (-(t * y i))) = LogProjectiveSection.weightedExpLevel b y t := by
    simpa [LogProjectiveSection.weightedExpLevel, V] using
      (Finset.sum_fiberwise_of_maps_to hmap
        (fun i => b i * Real.exp (-(t * y i))))
  have hcgroup :
      (∑ v ∈ V, ∑ i ∈ Finset.univ.filter (fun i => y i = v),
        c i * Real.exp (-(t * y i))) = LogProjectiveSection.weightedExpLevel c y t := by
    simpa [LogProjectiveSection.weightedExpLevel, V] using
      (Finset.sum_fiberwise_of_maps_to hmap
        (fun i => c i * Real.exp (-(t * y i))))
  have hfiberExpB (v : ℝ) :
      (∑ i ∈ Finset.univ.filter (fun i => y i = v), b i * Real.exp (-(t * y i))) =
        projectiveFiberWeight y b v * Real.exp (-(t * v)) := by
    calc
      (∑ i ∈ Finset.univ.filter (fun i => y i = v),
          b i * Real.exp (-(t * y i))) =
          ∑ i ∈ Finset.univ.filter (fun i => y i = v),
            b i * Real.exp (-(t * v)) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [(Finset.mem_filter.mp hi).2]
      _ = (∑ i ∈ Finset.univ.filter (fun i => y i = v), b i) *
          Real.exp (-(t * v)) := by rw [Finset.sum_mul]
      _ = projectiveFiberWeight y b v * Real.exp (-(t * v)) := rfl
  have hfiberExpC (v : ℝ) :
      (∑ i ∈ Finset.univ.filter (fun i => y i = v), c i * Real.exp (-(t * y i))) =
        projectiveFiberWeight y c v * Real.exp (-(t * v)) := by
    calc
      (∑ i ∈ Finset.univ.filter (fun i => y i = v),
          c i * Real.exp (-(t * y i))) =
          ∑ i ∈ Finset.univ.filter (fun i => y i = v),
            c i * Real.exp (-(t * v)) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [(Finset.mem_filter.mp hi).2]
      _ = (∑ i ∈ Finset.univ.filter (fun i => y i = v), c i) *
          Real.exp (-(t * v)) := by rw [Finset.sum_mul]
      _ = projectiveFiberWeight y c v * Real.exp (-(t * v)) := rfl
  calc
    LogProjectiveSection.weightedExpLevel b y t =
        ∑ v ∈ V, projectiveFiberWeight y b v * Real.exp (-(t * v)) := by
          rw [← hbgroup]
          apply Finset.sum_congr rfl
          intro v hv
          exact hfiberExpB v
    _ = ∑ v ∈ V, projectiveFiberWeight y c v * Real.exp (-(t * v)) := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [hfiber v]
    _ = LogProjectiveSection.weightedExpLevel c y t := by
          rw [← hcgroup]
          apply Finset.sum_congr rfl
          intro v hv
          exact (hfiberExpC v).symm

/-- Fiberwise-compatible affine sections have exactly the same level equation. -/
theorem affineLevel_eq_iff_of_projectiveFiberWeight_eq (b c y : ι → ℝ)
    (a t : ℝ)
    (hfiber : ∀ v, projectiveFiberWeight y b v = projectiveFiberWeight y c v) :
    (LogProjectiveSection.weightedExpLevel b y t = a * (∑ i, b i)) ↔
      (LogProjectiveSection.weightedExpLevel c y t = a * (∑ i, c i)) := by
  rw [weightedExpLevel_eq_of_projectiveFiberWeight_eq b c y t hfiber,
    totalWeight_eq_of_projectiveFiberWeight_eq b c y hfiber]

/-- If neighboring face weights match on every tied-coordinate fiber, then their unique positive
section scales agree exactly. Consequently the two faces reconstruct the same point on every
shared projective ray satisfying the fiber-balance condition. -/
theorem existsUnique_common_sectionScale (b c y : ι → ℝ) {a : ℝ}
    (hb : ∀ i, 0 ≤ b i) (hbsum : 0 < ∑ i, b i)
    (hy : ∀ i, 1 ≤ y i) (ha0 : 0 < a) (ha1 : a < 1)
    (hfiber : ∀ v, projectiveFiberWeight y b v = projectiveFiberWeight y c v) :
    ∃! t : ℝ,
      0 < t ∧
      LogProjectiveSection.weightedExpLevel b y t = a * (∑ i, b i) ∧
      LogProjectiveSection.weightedExpLevel c y t = a * (∑ i, c i) := by
  obtain ⟨t, ht, hunique⟩ :=
    LogProjectiveSection.existsUnique_sectionScale b y hb hbsum hy ha0 ha1
  have hrootC :=
    (affineLevel_eq_iff_of_projectiveFiberWeight_eq b c y a t hfiber).mp ht.2
  refine ⟨t, ⟨ht.1, ht.2, hrootC⟩, ?_⟩
  intro u hu
  exact hunique u ⟨hu.1, hu.2.1⟩

end LogProjectiveFaceCompatibility
end CRNT

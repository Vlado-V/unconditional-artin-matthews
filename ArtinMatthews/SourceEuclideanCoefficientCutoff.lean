module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Geometry.Manifold.PartitionOfUnity


set_option backward.privateInPublic true
@[expose] public section

/-! Smooth cutoffs of actual locally smooth coefficients, with their
values and support retained on the chosen Euclidean neighborhood. -/

namespace ArtinMatthews

open Set Filter
open scoped ContDiff Topology Manifold SchwartzMap

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem sourceSmooth_unit_cutoff_near_point {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) :
    ∃ η : E → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ tsupport η ⊆ U ∧
      (η =ᶠ[𝓝 x] 1) ∧ ∀ y, η y ∈ Icc 0 1 := by
  obtain ⟨K,hK,hxK,hKU⟩ :=
    exists_compact_between (isCompact_singleton (x := x)) hU (singleton_subset_iff.mpr hx)
  obtain ⟨η,hηone,hηout,hηrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (𝓘(ℝ, E)) isClosed_singleton hxK (n := ⊤)
  have hηc : HasCompactSupport (η : E → ℝ) := HasCompactSupport.intro hK hηout
  have hηK : tsupport (η : E → ℝ) ⊆ K :=
    closure_minimal (fun y hy => by
      by_contra h
      exact hy (hηout y h)) hK.isClosed
  exact ⟨η,η.contMDiff.contDiff,hηc,hηK.trans hKU,
    (nhds_le_nhdsSet (mem_singleton x)) hηone,hηrange⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem sourceSmooth_supported_smul {U : Set E} (hU : IsOpen U) (η : E → ℝ) (f : E → F)
    (hη : ContDiff ℝ ∞ η) (hηU : tsupport η ⊆ U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiff ℝ ∞ (fun y => η y • f y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ tsupport η
  · exact hη.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds (hηU hy)))
  · apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E => (0:F)) y).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hy] with z hz
    rw [image_eq_zero_of_notMem_tsupport hz,zero_smul]

end
end ArtinMatthews

module

public import ArtinMatthews.SpectralCoreLocalizationChartCompact
public import ArtinMatthews.SpectralPoincareL2


set_option backward.privateInPublic true
@[expose] public section

/-! A continuous section bounded on the actual high modular tail belongs to
actual translated-region L². The remaining low part is a proved compact set. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups
namespace ArtinMatthews

theorem continuous_memLp_modular_of_tail_bound (F : UpperHalfPlane → ℂ) (hF : Continuous F)
    (r : SL(2,ℤ)) (Y C : ℝ)
    (htail : ∀ z : UpperHalfPlane, z ∈ ModularGroup.fd → Y ≤ z.im → ‖F (r⁻¹ • z)‖ ≤ C) :
    MemLp (fun z : UpperHalfPlane => F (r⁻¹ • z)) 2 (volume.restrict ModularGroup.fd) := by
  let K : Set UpperHalfPlane := {z | (z.re,z.im) ∈ spectralPlaneRectangle (1/2) (1/2) Y}
  have hK : IsCompact K := spectralCoreChart_compact (1/2) (1/2) Y (by norm_num)
  have hf : Continuous (fun z : UpperHalfPlane => F (r⁻¹ • z)) := by
    change Continuous (fun z : UpperHalfPlane => F (Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹ • z))
    exact hF.comp (continuous_const_smul _)
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable (max D C)
  filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
  by_cases hy : Y ≤ z.im
  · exact (htail z hz hy).trans (le_max_right _ _)
  · have hzK : z ∈ K := by
      change (-(1/2:ℝ) ≤ z.re ∧ z.re ≤ 1/2) ∧ 1/2 ≤ z.im ∧ z.im ≤ Y
      refine ⟨abs_le.mp hz.2,?_,(not_le.mp hy).le⟩
      have hsq := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
      nlinarith [z.im_pos]
    exact (hD z hzK).trans (le_max_left _ _)

end ArtinMatthews

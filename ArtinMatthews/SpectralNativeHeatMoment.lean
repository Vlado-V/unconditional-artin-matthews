module

public import ArtinMatthews.SpectralNativeHeatProfile
public import ArtinMatthews.SpectralWeylWeightedMoment


set_option backward.privateInPublic true
@[expose] public section

/-! The direct heat regularity bounds supply the weighted moment and
positive power used in the actual two-profile geometric passage. -/

noncomputable section
open Set MeasureTheory
namespace ArtinMatthews

theorem spectralKLHeatRegularity_measurable (F : ℝ → ℂ) (hF : SpectralKLHeatRegularity F)
    (hzero : ∀ x : ℝ, x ≤ 0 → F x = 0) : Measurable F := by
  have hc := hF.1.continuousOn
  have hz : ContinuousOn F (Ioi (0 : ℝ))ᶜ := by
    apply (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℂ)) (Ioi (0 : ℝ))ᶜ).congr
    intro x hx
    exact hzero x (le_of_not_gt hx)
  have hm := hc.measurable_piecewise hz measurableSet_Ioi
  simpa only [Set.piecewise_same] using hm

theorem spectralKLHeatRegularity_common_bounds (F : ℝ → ℂ) (hF : SpectralKLHeatRegularity F) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, 0 < x → ‖F x‖ ≤ C*x^(3/4 : ℝ)) ∧
      (∀ x : ℝ, 1 ≤ x → ‖F x‖ ≤ C/x^2) := by
  obtain ⟨_,_,⟨C,hC,hsmall⟩,hlarge⟩ := hF
  obtain ⟨D,_,hD⟩ := hlarge 2 (by norm_num)
  refine ⟨max C D,hC.trans (le_max_left _ _),?_,?_⟩
  · intro x hx
    exact (hsmall x hx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx.le _))
  · intro x hx
    exact (hD x hx).trans (div_le_div_of_nonneg_right (le_max_right _ _) (sq_nonneg x))

theorem spectralKLHeatRegularity_five_eighths (F : ℝ → ℂ) (hF : SpectralKLHeatRegularity F)
    (hzero : ∀ x : ℝ, x ≤ 0 → F x = 0) :
    Integrable (fun x : ℝ => x^(-(5/8 : ℝ))*‖F x‖) spectralKLPhysicalMeasure ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x, 0 < x → ‖F x‖ ≤ M*x^(5/8 : ℝ) := by
  obtain ⟨C,hC,hs,hl⟩ := spectralKLHeatRegularity_common_bounds F hF
  have hm := spectralKLHeatRegularity_measurable F hF hzero
  exact ⟨(spectralWeylPhysicalMoment_five_eighths F hm C hC (fun x hx _ => hs x hx) hl).1,
    C,hC,spectralWeylFiveEighths_global_power F C hC (fun x hx _ => hs x hx) hl⟩

end ArtinMatthews

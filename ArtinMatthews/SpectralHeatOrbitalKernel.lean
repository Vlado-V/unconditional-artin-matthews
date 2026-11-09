module

public import ArtinMatthews.SpectralHeatKLAnalysis
public import ArtinMatthews.SpectralNativeHeatMoment
public import ArtinMatthews.SpectralWeylTwoProfileKL


set_option backward.privateInPublic true
@[expose] public section

/-! Literal Gaussian-regularized J/K transforms of the actual
two-height orbital kernel. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff
namespace ArtinMatthews

theorem spectralHeatGaussian_square (R : ℝ) (z : ℂ) :
    spectralKLGaussianData R z*spectralKLGaussianData R z =
      Complex.exp (-2*(z/(R : ℂ))^2) := by
  unfold spectralKLGaussianData
  rw [← Complex.exp_add]
  congr 1
  ring

theorem spectralWeylRegularHeat_same_J {X : ℝ} (hX : 0 < X)
    (T ε : ℝ) (hT : 0 < T) (R : ℝ) (hR : 0 < R)
    (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) (hst : s*t = 1) :
    spectralWeylPhysicalBilinear s t (spectralABLRegularHeatProfile T ε R) (spectralKLHeatProfile R) X =
      ∫ u, spectralWeylJMultiplier u X*spectralABLRegularCorrected T (T^(1-ε)) (u : ℂ)*
        Complex.exp (-2*((u : ℂ)/(R : ℂ))^2) ∂spectralKLSpectralMeasure := by
  let F := spectralKLHeatProfile R
  let G := spectralABLRegularHeatProfile T ε R
  have hF := spectralKLHeatProfile_properties R hR
  have hG := spectralABLRegularHeatProfile_properties T ε R hT hR
  have hzF := spectralKLHeatProfile_nonpositive_zero R
  have hzG := spectralABLRegularHeatProfile_nonpositive_zero T ε R
  have hmF := spectralKLHeatRegularity_measurable F hF hzF
  have hmG := spectralKLHeatRegularity_measurable G hG hzG
  obtain ⟨M,hM,hpower⟩ := (spectralKLHeatRegularity_five_eighths G hG hzG).2
  have hMoment := (spectralKLHeatRegularity_five_eighths F hF hzF).1
  have he := spectralWeylPhysicalBilinear_same_J_two_noncompact zero_lt_one hX
    (by norm_num : (0 : ℝ) < 5/8) (by norm_num : (5/8 : ℝ) ≤ 1) hM
    s t hs ht hst G F hmG hmF hG.1.continuousOn hF.1.continuousOn hG.2.1 hF.2.1 hMoment hpower
  rw [he]
  apply integral_congr_ae
  filter_upwards [spectralABLRegularHeatProfile_completed_analysis T ε R hT hR hG.2.1,
    spectralKLHeatProfile_completed_analysis R hR hF.2.1] with u hGu hFu
  rw [hGu,hFu,spectralKLGaussianWeightedData,spectralKLGaussianData_real_star]
  calc
    _ = spectralWeylJMultiplier u X*spectralABLRegularCorrected T (T^(1-ε)) (u : ℂ)*
        (spectralKLGaussianData R (u : ℂ)*spectralKLGaussianData R (u : ℂ)) := by ring
    _ = _ := by rw [spectralHeatGaussian_square]

theorem spectralWeylRegularHeat_opposite_K {X : ℝ} (hX : 0 < X)
    (T ε : ℝ) (hT : 0 < T) (R : ℝ) (hR : 0 < R)
    (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) (hst : s*t = -1) :
    spectralWeylPhysicalBilinear s t (spectralABLRegularHeatProfile T ε R) (spectralKLHeatProfile R) X =
      ∫ u, spectralWeylKMultiplier u X*spectralABLRegularCorrected T (T^(1-ε)) (u : ℂ)*
        Complex.exp (-2*((u : ℂ)/(R : ℂ))^2) ∂spectralKLSpectralMeasure := by
  let F := spectralKLHeatProfile R
  let G := spectralABLRegularHeatProfile T ε R
  have hF := spectralKLHeatProfile_properties R hR
  have hG := spectralABLRegularHeatProfile_properties T ε R hT hR
  have hzF := spectralKLHeatProfile_nonpositive_zero R
  have hzG := spectralABLRegularHeatProfile_nonpositive_zero T ε R
  have hmF := spectralKLHeatRegularity_measurable F hF hzF
  have hmG := spectralKLHeatRegularity_measurable G hG hzG
  obtain ⟨M,hM,hpower⟩ := (spectralKLHeatRegularity_five_eighths G hG hzG).2
  have hMoment := (spectralKLHeatRegularity_five_eighths F hF hzF).1
  have he := spectralWeylPhysicalBilinear_opposite_K_two_noncompact zero_lt_one hX
    (by norm_num : (0 : ℝ) < 5/8) (by norm_num : (5/8 : ℝ) ≤ 1) hM
    s t hs ht hst G F hmG hmF hG.1.continuousOn hF.1.continuousOn hG.2.1 hF.2.1 hMoment hpower
  rw [he]
  apply integral_congr_ae
  filter_upwards [spectralABLRegularHeatProfile_completed_analysis T ε R hT hR hG.2.1,
    spectralKLHeatProfile_completed_analysis R hR hF.2.1] with u hGu hFu
  rw [hGu,hFu,spectralKLGaussianWeightedData,spectralKLGaussianData_real_star]
  calc
    _ = spectralWeylKMultiplier u X*spectralABLRegularCorrected T (T^(1-ε)) (u : ℂ)*
        (spectralKLGaussianData R (u : ℂ)*spectralKLGaussianData R (u : ℂ)) := by ring
    _ = _ := by rw [spectralHeatGaussian_square]

theorem spectralWeylExceptionalHeat_same_J {X : ℝ} (hX : 0 < X)
    (a : ℝ) (A : ℕ) (hA : 1 ≤ A) (R : ℝ) (hR : 0 < R)
    (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) (hst : s*t = 1) :
    spectralWeylPhysicalBilinear s t (spectralABLExceptionalHeatProfile a A R) (spectralKLHeatProfile R) X =
      ∫ u, spectralWeylJMultiplier u X*spectralABLExceptionalCorrected a A (u : ℂ)*
        Complex.exp (-2*((u : ℂ)/(R : ℂ))^2) ∂spectralKLSpectralMeasure := by
  let F := spectralKLHeatProfile R
  let G := spectralABLExceptionalHeatProfile a A R
  have hF := spectralKLHeatProfile_properties R hR
  have hG := spectralABLExceptionalHeatProfile_properties a A R hA hR
  have hzF := spectralKLHeatProfile_nonpositive_zero R
  have hzG := spectralABLExceptionalHeatProfile_nonpositive_zero a A R
  have hmF := spectralKLHeatRegularity_measurable F hF hzF
  have hmG := spectralKLHeatRegularity_measurable G hG hzG
  obtain ⟨M,hM,hpower⟩ := (spectralKLHeatRegularity_five_eighths G hG hzG).2
  have hMoment := (spectralKLHeatRegularity_five_eighths F hF hzF).1
  have he := spectralWeylPhysicalBilinear_same_J_two_noncompact zero_lt_one hX
    (by norm_num : (0 : ℝ) < 5/8) (by norm_num : (5/8 : ℝ) ≤ 1) hM
    s t hs ht hst G F hmG hmF hG.1.continuousOn hF.1.continuousOn hG.2.1 hF.2.1 hMoment hpower
  rw [he]
  apply integral_congr_ae
  filter_upwards [spectralABLExceptionalHeatProfile_completed_analysis a A R hA hR hG.2.1,
    spectralKLHeatProfile_completed_analysis R hR hF.2.1] with u hGu hFu
  rw [hGu,hFu,spectralKLGaussianWeightedData,spectralKLGaussianData_real_star]
  calc
    _ = spectralWeylJMultiplier u X*spectralABLExceptionalCorrected a A (u : ℂ)*
        (spectralKLGaussianData R (u : ℂ)*spectralKLGaussianData R (u : ℂ)) := by ring
    _ = _ := by rw [spectralHeatGaussian_square]

theorem spectralWeylExceptionalHeat_opposite_K {X : ℝ} (hX : 0 < X)
    (a : ℝ) (A : ℕ) (hA : 1 ≤ A) (R : ℝ) (hR : 0 < R)
    (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) (hst : s*t = -1) :
    spectralWeylPhysicalBilinear s t (spectralABLExceptionalHeatProfile a A R) (spectralKLHeatProfile R) X =
      ∫ u, spectralWeylKMultiplier u X*spectralABLExceptionalCorrected a A (u : ℂ)*
        Complex.exp (-2*((u : ℂ)/(R : ℂ))^2) ∂spectralKLSpectralMeasure := by
  let F := spectralKLHeatProfile R
  let G := spectralABLExceptionalHeatProfile a A R
  have hF := spectralKLHeatProfile_properties R hR
  have hG := spectralABLExceptionalHeatProfile_properties a A R hA hR
  have hzF := spectralKLHeatProfile_nonpositive_zero R
  have hzG := spectralABLExceptionalHeatProfile_nonpositive_zero a A R
  have hmF := spectralKLHeatRegularity_measurable F hF hzF
  have hmG := spectralKLHeatRegularity_measurable G hG hzG
  obtain ⟨M,hM,hpower⟩ := (spectralKLHeatRegularity_five_eighths G hG hzG).2
  have hMoment := (spectralKLHeatRegularity_five_eighths F hF hzF).1
  have he := spectralWeylPhysicalBilinear_opposite_K_two_noncompact zero_lt_one hX
    (by norm_num : (0 : ℝ) < 5/8) (by norm_num : (5/8 : ℝ) ≤ 1) hM
    s t hs ht hst G F hmG hmF hG.1.continuousOn hF.1.continuousOn hG.2.1 hF.2.1 hMoment hpower
  rw [he]
  apply integral_congr_ae
  filter_upwards [spectralABLExceptionalHeatProfile_completed_analysis a A R hA hR hG.2.1,
    spectralKLHeatProfile_completed_analysis R hR hF.2.1] with u hGu hFu
  rw [hGu,hFu,spectralKLGaussianWeightedData,spectralKLGaussianData_real_star]
  calc
    _ = spectralWeylKMultiplier u X*spectralABLExceptionalCorrected a A (u : ℂ)*
        (spectralKLGaussianData R (u : ℂ)*spectralKLGaussianData R (u : ℂ)) := by ring
    _ = _ := by rw [spectralHeatGaussian_square]

end ArtinMatthews

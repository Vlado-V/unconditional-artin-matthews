module

public import ArtinMatthews.SpectralBetaFourierGamma
public import Mathlib.MeasureTheory.Function.L2Space


set_option backward.privateInPublic true
@[expose] public section

/-! Actual L2 membership of the beta log profiles and their Fourier
transforms.  The Barnes pairing itself uses the stronger L1 Fourier input. -/

noncomputable section
open Set MeasureTheory Filter
open scoped FourierTransform

namespace ArtinMatthews

theorem spectralBetaLogProfile_norm_le_one (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) (u : ℝ) :
    ‖spectralBetaLogProfile a b u‖ ≤ 1 := by
  unfold spectralBetaLogProfile
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (Real.sigmoid_pos u),
    Complex.norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr (Real.sigmoid_lt_one u))]
  have h1 := Real.rpow_le_one (Real.sigmoid_nonneg u) (Real.sigmoid_le_one u) ha.le
  have h2 := Real.rpow_le_one (sub_pos.mpr (Real.sigmoid_lt_one u)).le
    (show 1-Real.sigmoid u ≤ 1 by linarith [Real.sigmoid_nonneg u]) hb.le
  have hmul := mul_le_mul_of_nonneg_right h1
    (Real.rpow_nonneg (sub_pos.mpr (Real.sigmoid_lt_one u)).le b.re)
  exact hmul.trans (by simpa only [one_mul] using h2)

theorem spectralBetaLogProfile_memLp_two (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) :
    MemLp (spectralBetaLogProfile a b) 2 volume := by
  have hI := spectralBetaLogProfile_integrable a b ha hb
  apply (memLp_two_iff_integrable_sq_norm hI.aestronglyMeasurable).mpr
  apply hI.norm.mono' ((spectralBetaLogProfile_continuous a b).norm.pow 2).aestronglyMeasurable
  filter_upwards [] with u
  change ‖‖spectralBetaLogProfile a b u‖^2‖ ≤ ‖spectralBetaLogProfile a b u‖
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  simpa only [pow_two,one_mul] using mul_le_mul_of_nonneg_right
    (spectralBetaLogProfile_norm_le_one a b ha hb u) (norm_nonneg (spectralBetaLogProfile a b u))

theorem spectral_fourier_norm_le (f : ℝ → ℂ) (ξ : ℝ) :
    ‖𝓕 f ξ‖ ≤ ∫ u : ℝ, ‖f u‖ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards [] with u
  simp [Complex.norm_exp]

theorem spectralBetaLogProfile_fourier_memLp_two (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) :
    MemLp (𝓕 (spectralBetaLogProfile a b)) 2 volume := by
  have hI := spectralBetaLogProfile_fourier_integrable a b ha hb
  let C := ∫ u : ℝ, ‖spectralBetaLogProfile a b u‖
  have hm := hI.aestronglyMeasurable.norm.mul hI.aestronglyMeasurable.norm
  apply (memLp_two_iff_integrable_sq_norm hI.aestronglyMeasurable).mpr
  apply (hI.norm.const_mul C).mono' (by
    convert hm using 1
    funext ξ
    simp [pow_two])
  filter_upwards [] with ξ
  change ‖‖𝓕 (spectralBetaLogProfile a b) ξ‖^2‖ ≤ C*‖𝓕 (spectralBetaLogProfile a b) ξ‖
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h := spectral_fourier_norm_le (spectralBetaLogProfile a b) ξ
  simpa only [pow_two] using mul_le_mul_of_nonneg_right h (norm_nonneg (𝓕 (spectralBetaLogProfile a b) ξ))

end ArtinMatthews

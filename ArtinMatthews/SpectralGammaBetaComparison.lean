module

public import ArtinMatthews.SpectralGammaVertical
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Complex
noncomputable section

theorem spectral_beta_real_integral (a b : ℝ) :
    Complex.betaIntegral (a : ℂ) (b : ℂ) =
      ((∫ x : ℝ in 0..1, x ^ (a - 1) * (1 - x) ^ (b - 1)) : ℝ) := by
  rw [Complex.betaIntegral, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  dsimp only
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le,
    Complex.ofReal_cpow (sub_nonneg.mpr hx.2.le)]
  push_cast
  rfl

theorem spectral_beta_real_value (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ x : ℝ in 0..1, x ^ (a - 1) * (1 - x) ^ (b - 1)) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  apply Complex.ofReal_injective
  calc
    ((∫ x : ℝ in 0..1, x ^ (a - 1) * (1 - x) ^ (b - 1)) : ℝ) =
        Complex.betaIntegral (a : ℂ) (b : ℂ) := (spectral_beta_real_integral a b).symm
    _ = Complex.Gamma (a : ℂ) * Complex.Gamma (b : ℂ) / Complex.Gamma ((a : ℂ) + (b : ℂ)) :=
      Complex.betaIntegral_eq_Gamma_mul_div _ _ ha hb
    _ = ((Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal]
      push_cast
      rfl

theorem spectral_beta_vertical_norm_le (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ‖Complex.betaIntegral ((a : ℂ) + (t : ℂ) * I) (b : ℂ)‖ ≤
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  unfold Complex.betaIntegral
  calc
    _ ≤ ∫ x : ℝ in 0..1,
        ‖(x : ℂ) ^ (((a : ℂ) + (t : ℂ) * I) - 1) * (1 - (x : ℂ)) ^ ((b : ℂ) - 1)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ = ∫ x : ℝ in 0..1, x ^ (a - 1) * (1 - x) ^ (b - 1) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro x hx
      dsimp only
      have hbase : (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by push_cast; rfl
      rw [norm_mul, hbase, Complex.norm_cpow_eq_rpow_re_of_pos hx.1,
        Complex.norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr hx.2)]
      norm_num [Complex.mul_re]
    _ = _ := spectral_beta_real_value a b ha hb

theorem spectralGamma_vertical_ratio_le (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I) /
      Complex.Gamma (((a + b : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      Real.Gamma a / Real.Gamma (a + b) := by
  let z := (a : ℂ) + (t : ℂ) * I
  let w := ((a + b : ℝ) : ℂ) + (t : ℂ) * I
  have hz : 0 < z.re := by simpa [z, Complex.mul_re] using ha
  have hw : 0 < w.re := by simpa [w, Complex.mul_re] using add_pos ha hb
  have hbg : Complex.Gamma (b : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hb
  have hwg : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hw
  have hsum : z + (b : ℂ) = w := by dsimp [z, w]; push_cast; ring
  have heq : Complex.Gamma z / Complex.Gamma w = Complex.betaIntegral z (b : ℂ) / Complex.Gamma (b : ℂ) := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hz hb, hsum]
    field_simp
  have hGb : 0 < Real.Gamma b := Real.Gamma_pos_of_pos hb
  have hGab : 0 < Real.Gamma (a + b) := Real.Gamma_pos_of_pos (add_pos ha hb)
  change ‖Complex.Gamma z / Complex.Gamma w‖ ≤ _
  rw [heq, norm_div, Complex.Gamma_ofReal, Complex.norm_real, Real.norm_of_nonneg hGb.le]
  calc
    _ ≤ (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)) / Real.Gamma b :=
      div_le_div_of_nonneg_right (spectral_beta_vertical_norm_le a b t ha hb) hGb.le
    _ = _ := by field_simp

end
end ArtinMatthews

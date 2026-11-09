module

public import ArtinMatthews.SpectralGammaHalfLine
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform reciprocal Gamma growth on each vertical line Re(s)>=1/2,
proved by the Beta integral and Euler reflection on the central line. -/
namespace ArtinMatthews

open Complex MeasureTheory Set
noncomputable section

/-- A finite real constant given by the norm of the fixed Beta integrand. -/
def spectralBetaMass (c : ℝ) : ℝ :=
  ∫ x : ℝ in 0..1,
    ‖(x : ℂ)^((1/2 : ℂ)-1) * (1-(x : ℂ))^((c : ℂ)-1)‖

lemma spectralBetaMass_nonneg (c : ℝ) : 0 ≤ spectralBetaMass c := by
  exact intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => norm_nonneg _)

lemma spectral_beta_half_line_bound (c t : ℝ) :
    ‖Complex.betaIntegral (⟨1/2,2*t⟩ : ℂ) (c : ℂ)‖ ≤ spectralBetaMass c := by
  unfold Complex.betaIntegral spectralBetaMass
  apply (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans_eq
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
  dsimp only
  rw [norm_mul,norm_mul]
  congr 1
  rw [Complex.norm_cpow_eq_rpow_re_of_nonneg hx.1 (by norm_num),
    Complex.norm_cpow_eq_rpow_re_of_nonneg hx.1 (by norm_num)]
  norm_num

lemma spectral_inv_gamma_shifted_half_line (c : ℝ) (hc : 0 < c) (t : ℝ) :
    ‖(Complex.Gamma ((⟨1/2,2*t⟩ : ℂ)+(c : ℂ)))⁻¹‖ ≤
      (spectralBetaMass c / ‖Complex.Gamma (c : ℂ)‖)*Real.exp (Real.pi*|t|) := by
  let z : ℂ := ⟨1/2,2*t⟩
  have hz : 0 < z.re := by norm_num [z]
  have hc' : 0 < (c : ℂ).re := hc
  have hzc : 0 < (z+(c : ℂ)).re := by simp only [Complex.add_re,Complex.ofReal_re]; linarith
  have hg₀ := Complex.Gamma_ne_zero_of_re_pos hz
  have hgc := Complex.Gamma_ne_zero_of_re_pos hc'
  have hg₁ := Complex.Gamma_ne_zero_of_re_pos hzc
  have he : (Complex.Gamma (z+(c : ℂ)))⁻¹ =
      (Complex.betaIntegral z (c : ℂ)/Complex.Gamma (c : ℂ)) *
        (Complex.Gamma z)⁻¹ := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div z (c : ℂ) hz hc']
    field_simp
  change ‖(Complex.Gamma (z+(c : ℂ)))⁻¹‖ ≤ _
  rw [he,norm_mul,norm_div]
  apply mul_le_mul
  · exact div_le_div_of_nonneg_right (spectral_beta_half_line_bound c t) (norm_nonneg _)
  · exact spectral_inv_gamma_half_line t
  · exact norm_nonneg _
  · exact div_nonneg (spectralBetaMass_nonneg c) (norm_nonneg _)

theorem spectral_inv_gamma_vertical_bound (c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖(Complex.Gamma (((c+1/2 : ℝ) : ℂ)+2*t*Complex.I))⁻¹‖ ≤
        C*Real.exp (Real.pi*|t|) := by
  by_cases hc₀ : c = 0
  · subst c
    refine ⟨1,by norm_num,?_⟩
    intro t
    have he : (((0+1/2 : ℝ) : ℂ)+2*t*Complex.I) = (⟨1/2,2*t⟩ : ℂ) := by
      apply Complex.ext <;> simp
    simpa only [he,one_mul] using spectral_inv_gamma_half_line t
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc₀)
    let B : ℝ := spectralBetaMass c / ‖Complex.Gamma (c : ℂ)‖
    have hB : 0 ≤ B := div_nonneg (spectralBetaMass_nonneg c) (norm_nonneg _)
    refine ⟨B+1,by positivity,?_⟩
    intro t
    have he : (((c+1/2 : ℝ) : ℂ)+2*t*Complex.I) =
        (⟨1/2,2*t⟩ : ℂ)+(c : ℂ) := by
      apply Complex.ext <;> simp [add_comm]
    rw [he]
    apply (spectral_inv_gamma_shifted_half_line c hcpos t).trans
    change B*_ ≤ (B+1)*_
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

end
end ArtinMatthews

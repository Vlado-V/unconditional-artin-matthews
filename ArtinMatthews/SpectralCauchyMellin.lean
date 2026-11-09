module

public import ArtinMatthews.SpectralBetaLogistic
public import ArtinMatthews.SpectralBesselHyperbolicEvaluation


set_option backward.privateInPublic true
@[expose] public section

/-! Mellin evaluation and absolute integrability of the positive Cauchy kernel. -/

namespace ArtinMatthews

open Set MeasureTheory Filter

noncomputable section

def spectralCauchyMellinKernel (s : ℂ) (y x : ℝ) : ℂ :=
  (x : ℂ) ^ (s - 1) / ((y + x : ℝ) : ℂ)

private theorem betaLogProfile_one_sub (s : ℂ) (u : ℝ) :
    spectralBetaLogProfile s (1 - s) u =
      Complex.exp (s * (u : ℂ)) / (1 + (Real.exp u : ℂ)) := by
  have he := spectralBetaLogProfile_shift (0 : ℂ) 1 s u
  rw [zero_add] at he
  rw [he, spectralBetaLogProfile, Complex.cpow_zero, one_mul, Complex.cpow_one,
    ← Real.sigmoid_neg, Real.sigmoid_def, neg_neg, Complex.ofReal_inv, Complex.ofReal_add,
    Complex.ofReal_one]
  ring

theorem spectralCauchyMellinKernel_jacobian (s : ℂ) {y : ℝ} (hy : 0 < y) (u : ℝ) :
    (y * Real.exp u) • spectralCauchyMellinKernel s y (y * Real.exp u) =
      (y : ℂ) ^ (s - 1) * spectralBetaLogProfile s (1 - s) u := by
  have he : 0 < Real.exp u := Real.exp_pos u
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have heC : (Real.exp u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr he.ne'
  have hden : ((y + y * Real.exp u : ℝ) : ℂ) = (y : ℂ) * (1 + (Real.exp u : ℂ)) := by
    push_cast
    ring
  have hplus : (1 + (Real.exp u : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hpow : (Real.exp u : ℂ) * (Real.exp u : ℂ) ^ (s - 1) = (Real.exp u : ℂ) ^ s := by
    calc
      _ = (Real.exp u : ℂ) ^ (1 : ℂ) * (Real.exp u : ℂ) ^ (s - 1) := by rw [Complex.cpow_one]
      _ = (Real.exp u : ℂ) ^ (1 + (s - 1)) := (Complex.cpow_add _ _ heC).symm
      _ = _ := by congr 1; ring
  have hexp : (Real.exp u : ℂ) ^ s = Complex.exp (s * (u : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero heC, ← Complex.ofReal_log he.le, Real.log_exp, mul_comm]
  rw [spectralCauchyMellinKernel, hden, Complex.real_smul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hy.le he.le, betaLogProfile_one_sub, ← hexp, ← hpow]
  field_simp [hyC, hplus]

theorem spectralCauchyMellinKernel_integrable (s : ℂ) (hs : 0 < s.re) (hsh : s.re < 1)
    {y : ℝ} (hy : 0 < y) :
    IntegrableOn (spectralCauchyMellinKernel s y) (Ioi (0 : ℝ)) := by
  have hb : 0 < (1 - s).re := by simpa only [Complex.sub_re, Complex.one_re, sub_pos] using hsh
  rw [positive_exp_scale_integrable hy]
  simp_rw [spectralCauchyMellinKernel_jacobian s hy]
  exact (spectralBetaLogProfile_integrable s (1 - s) hs hb).const_mul _

theorem spectralCauchyMellinKernel_integral (s : ℂ) (hs : 0 < s.re) (hsh : s.re < 1)
    {y : ℝ} (hy : 0 < y) :
    (∫ x in Ioi (0 : ℝ), spectralCauchyMellinKernel s y x) =
      (y : ℂ) ^ (s - 1) * ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * s)) := by
  have hb : 0 < (1 - s).re := by simpa only [Complex.sub_re, Complex.one_re, sub_pos] using hsh
  rw [positive_exp_scale_integral hy]
  simp_rw [spectralCauchyMellinKernel_jacobian s hy]
  rw [integral_const_mul, spectralBetaLogProfile_integral,
    Complex.betaIntegral_eq_Gamma_mul_div _ _ hs hb, show s + (1 - s) = 1 by ring,
    Complex.Gamma_one, div_one, Complex.Gamma_mul_Gamma_one_sub]

theorem spectralCauchyMellinKernel_norm_integral (s : ℂ) {y : ℝ} (hy : 0 < y) :
    (∫ x in Ioi (0 : ℝ), ‖spectralCauchyMellinKernel s y x‖) =
      ‖(y : ℂ) ^ (s - 1)‖ * ∫ u : ℝ, ‖spectralBetaLogProfile s (1 - s) u‖ := by
  calc
    _ = ∫ u : ℝ, ‖(y * Real.exp u) • spectralCauchyMellinKernel s y (y * Real.exp u)‖ := by
      rw [positive_exp_scale_integral hy]
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hy (Real.exp_pos _)), smul_eq_mul]
    _ = _ := by
      simp_rw [spectralCauchyMellinKernel_jacobian s hy, norm_mul]
      rw [integral_const_mul]

end

end ArtinMatthews

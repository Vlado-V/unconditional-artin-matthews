module

public import ArtinMatthews.SpectralWeberKBasic
public import ArtinMatthews.SpectralInverseSquarePower


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute Mellin/Gaussian Fubini for the actual doubled-order K transform. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

def spectralWeberKMellinKernel (ν s : ℂ) (x p : ℝ) : ℂ :=
  ((p : ℂ)^(s-1)*Complex.exp (-((x^2 : ℝ) : ℂ)*(p : ℂ)))*schlafliBesselK (2*ν) x

theorem spectralWeberKMellinKernel_slice_integrable (ν s : ℂ) (hs : 0 < s.re)
    {x : ℝ} (hx : 0 < x) :
    IntegrableOn (spectralWeberKMellinKernel ν s x) (Ioi (0 : ℝ)) :=
  (spectralLaplaceGamma_integrable s hs (sq_pos_of_pos hx)).mul_const _

theorem spectralWeberKMellinKernel_integral_p (ν s : ℂ) (hs : 0 < s.re)
    {x : ℝ} (hx : 0 < x) :
    (∫ p in Ioi (0 : ℝ), spectralWeberKMellinKernel ν s x p) =
      Complex.Gamma s*((x : ℂ)^(-2*s)*schlafliBesselK (2*ν) x) := by
  unfold spectralWeberKMellinKernel
  rw [integral_mul_const,spectralLaplaceGamma_integral s hs (sq_pos_of_pos hx),
    spectral_inverse_square_cpow hx]
  ring

theorem spectralWeberKMellinKernel_integral_norm (ν s : ℂ) (hs : 0 < s.re)
    {x : ℝ} (hx : 0 < x) :
    (∫ p in Ioi (0 : ℝ), ‖spectralWeberKMellinKernel ν s x p‖) =
      Real.Gamma s.re*(x^(-2*s.re)*‖schlafliBesselK (2*ν) x‖) := by
  have he {p : ℝ} (hp : 0 < p) : ‖spectralWeberKMellinKernel ν s x p‖ =
      (p^(s.re-1)*Real.exp (-(x^2)*p))*‖schlafliBesselK (2*ν) x‖ := by
    unfold spectralWeberKMellinKernel
    rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hp,Complex.norm_exp]
    simp only [Complex.sub_re,Complex.one_re,Complex.mul_re,Complex.neg_re,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  calc
    _ = (∫ p in Ioi (0 : ℝ), p^(s.re-1)*Real.exp (-(x^2)*p))*‖schlafliBesselK (2*ν) x‖ := by
      rw [← integral_mul_const]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro p hp
      exact he hp
    _ = _ := by
      rw [show (∫ p in Ioi (0 : ℝ), p^(s.re-1)*Real.exp (-(x^2)*p)) =
          (1/x^2)^s.re*Real.Gamma s.re by
        simpa only [neg_mul] using Real.integral_rpow_mul_exp_neg_mul_Ioi hs (sq_pos_of_pos hx),
        spectral_inverse_square_rpow hx]
      ring

theorem spectralWeberKMellinKernel_integrable (ν s : ℂ) (hs : 0 < s.re)
    (hstrip : s.re+|ν.re| < 1/2) :
    Integrable (fun z : ℝ × ℝ => spectralWeberKMellinKernel ν s z.1 z.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have horder : |(2*ν).re| < (1-2*s).re := by
    norm_num [Complex.mul_re,abs_mul]
    linarith
  have hm : AEStronglyMeasurable
      (fun z : ℝ × ℝ => spectralWeberKMellinKernel ν s z.1 z.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    unfold spectralWeberKMellinKernel
    apply AEStronglyMeasurable.mul
    · fun_prop
    · have hν : |ν.re| < 1/2 := by linarith
      exact (spectralWeberK_base_integrable hν).aestronglyMeasurable.comp_fst
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact spectralWeberKMellinKernel_slice_integrable ν s hs hx
  · have hi := (schlafliBesselK_mellin_integrable (2*ν) (1-2*s) horder).norm.const_mul (Real.Gamma s.re)
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [spectralWeberKMellinKernel_integral_norm ν s hs hx,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hx]
    congr 2
    norm_num

end ArtinMatthews

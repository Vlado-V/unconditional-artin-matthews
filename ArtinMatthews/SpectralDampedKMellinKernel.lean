module

public import ArtinMatthews.SpectralCoshBeta
public import ArtinMatthews.SpectralLaplaceGamma


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute Laplace/Mellin Fubini for exp(-x) times the actual K kernel.
The natural strip |Re nu|<Re s is proved through the beta log profile. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

def spectralDampedKMellinKernel (ν s : ℂ) (u x : ℝ) : ℂ :=
  Complex.exp (ν*(u : ℂ))*((x : ℂ)^(s-1)*
    Complex.exp (-((1+Real.cosh u : ℝ) : ℂ)*(x : ℂ)))

theorem spectralDampedKMellinKernel_slice_integrable (ν s : ℂ) (hs : 0 < s.re) (u : ℝ) :
    IntegrableOn (spectralDampedKMellinKernel ν s u) (Ioi (0 : ℝ)) :=
  (spectralLaplaceGamma_integrable s hs (by linarith [Real.one_le_cosh u])).const_mul _

theorem spectralDampedKMellinKernel_integral_x (ν s : ℂ) (hs : 0 < s.re) (u : ℝ) :
    (∫ x in Ioi (0 : ℝ), spectralDampedKMellinKernel ν s u x) =
      Complex.Gamma s*spectralCoshBetaProfile s ν u := by
  have hc : 0 < 1+Real.cosh u := by linarith [Real.one_le_cosh u]
  unfold spectralDampedKMellinKernel spectralCoshBetaProfile
  rw [integral_const_mul,spectralLaplaceGamma_integral s hs hc,one_div,
    Complex.inv_cpow_ofReal_nonneg hc.le,← Complex.cpow_neg]
  ring_nf

theorem spectralDampedKMellinKernel_norm (ν s : ℂ) (u : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖spectralDampedKMellinKernel ν s u x‖ =
      Real.exp (ν.re*u)*(x^(s.re-1)*Real.exp (-(1+Real.cosh u)*x)) := by
  unfold spectralDampedKMellinKernel
  rw [norm_mul,norm_mul,Complex.norm_exp,Complex.norm_exp,Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
    Complex.sub_re,Complex.one_re,Complex.neg_re]

theorem spectralDampedKMellinKernel_integral_norm (ν s : ℂ) (hs : 0 < s.re) (u : ℝ) :
    (∫ x in Ioi (0 : ℝ), ‖spectralDampedKMellinKernel ν s u x‖) =
      Real.Gamma s.re*‖spectralCoshBetaProfile s ν u‖ := by
  have hc : 0 < 1+Real.cosh u := by linarith [Real.one_le_cosh u]
  calc
    _ = ∫ x in Ioi (0 : ℝ), Real.exp (ν.re*u)*(x^(s.re-1)*Real.exp (-(1+Real.cosh u)*x)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact spectralDampedKMellinKernel_norm ν s u hx
    _ = Real.exp (ν.re*u)*((1/(1+Real.cosh u))^s.re*Real.Gamma s.re) := by
      rw [integral_const_mul]
      congr 1
      simpa only [neg_mul] using Real.integral_rpow_mul_exp_neg_mul_Ioi hs hc
    _ = _ := by
      unfold spectralCoshBetaProfile
      rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hc,Complex.norm_exp]
      simp only [Complex.neg_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      rw [one_div,← Real.rpow_neg_eq_inv_rpow]
      ring_nf

theorem spectralDampedKMellinKernel_integrable (ν s : ℂ) (hs : |ν.re| < s.re) :
    Integrable (fun p : ℝ × ℝ => spectralDampedKMellinKernel ν s p.1 p.2)
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hs0 : 0 < s.re := (abs_nonneg ν.re).trans_lt hs
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => spectralDampedKMellinKernel ν s p.1 p.2)
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    unfold spectralDampedKMellinKernel
    fun_prop
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Filter.Eventually.of_forall (spectralDampedKMellinKernel_slice_integrable ν s hs0)
  · apply ((spectralCoshBetaProfile_integrable s ν hs).norm.const_mul (Real.Gamma s.re)).congr
    exact Filter.Eventually.of_forall (fun u => (spectralDampedKMellinKernel_integral_norm ν s hs0 u).symm)

theorem spectralDampedKMellinKernel_integral_u (ν s : ℂ) {x : ℝ} (hx : 0 < x) :
    (∫ u : ℝ, spectralDampedKMellinKernel ν s u x) =
      2*((x : ℂ)^(s-1)*Complex.exp (-(x : ℂ))*schlafliBesselK ν x) := by
  have he (u : ℝ) : spectralDampedKMellinKernel ν s u x =
      ((x : ℂ)^(s-1)*Complex.exp (-(x : ℂ)))*spectralKLogKernel ν x u := by
    unfold spectralDampedKMellinKernel spectralKLogKernel
    have harg : -((1+Real.cosh u : ℝ) : ℂ)*(x : ℂ) =
        -(x : ℂ)-(x : ℂ)*(Real.cosh u : ℂ) := by push_cast; ring_nf
    rw [harg]
    calc
      _ = (x : ℂ)^(s-1)*(Complex.exp (ν*(u : ℂ))*
          Complex.exp (-(x : ℂ)-(x : ℂ)*(Real.cosh u : ℂ))) := by ring_nf
      _ = (x : ℂ)^(s-1)*(Complex.exp (-(x : ℂ))*
          Complex.exp (((-x*Real.cosh u : ℝ) : ℂ)+(u : ℂ)*ν)) := by
        congr 1
        rw [← Complex.exp_add,← Complex.exp_add]
        congr 1
        push_cast
        ring_nf
      _ = _ := by ring_nf
  simp_rw [he]
  rw [integral_const_mul,schlafliBesselK_hyperbolic_integral ν hx]
  ring_nf

end ArtinMatthews

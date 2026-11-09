module

public import ArtinMatthews.SpectralKLCoshFourier


set_option backward.privateInPublic true
@[expose] public section

/-! Actual cosh-Fourier inversion, including the literal 2/pi factor and
absolute spectral integrability. This is an analytic identity, not a KL
surjectivity or exponential-span density assumption. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein
open scoped Topology FourierTransform

namespace ArtinMatthews

def spectralKLCoshInverseKernel (x u t : ℝ) : ℂ :=
  Complex.exp (((t*u : ℝ) : ℂ)*Complex.I)*(spectralKLRealKernel t x : ℂ)

theorem spectralKLCoshInverseKernel_integrable {x : ℝ} (hx : 0 < x) (u : ℝ) :
    Integrable (spectralKLCoshInverseKernel x u) := by
  have hK := spectralKLRealKernel_complex_integrable hx
  have hm : AEStronglyMeasurable (spectralKLCoshInverseKernel x u) :=
    (by fun_prop : Continuous (fun t : ℝ => Complex.exp (((t*u : ℝ) : ℂ)*Complex.I))).aestronglyMeasurable.mul
      hK.aestronglyMeasurable
  apply hK.norm.mono' hm
  filter_upwards with t
  simp [spectralKLCoshInverseKernel,Complex.norm_exp]

theorem spectralKLCoshExponential_inverse_full {x : ℝ} (hx : 0 < x) (u : ℝ) :
    (1/Real.pi : ℝ) • (∫ t : ℝ, spectralKLCoshInverseKernel x u t) = spectralKLCoshExponential x u := by
  have hc : Continuous (spectralKLCoshExponential x) := by unfold spectralKLCoshExponential; fun_prop
  have hi := (spectralKLCoshExponential_integrable hx).fourierInv_fourier_eq
    (spectralKLCoshExponential_fourier_integrable hx) (hc.continuousAt (x := u))
  rw [Real.fourierInv_eq_fourier_neg] at hi
  have hphase (ξ : ℝ) :
      Complex.exp (((-2*Real.pi*ξ*(-u) : ℝ) : ℂ)*Complex.I) •
        (2*(spectralKLRealKernel (2*Real.pi*ξ) x : ℂ)) =
      2*spectralKLCoshInverseKernel x u (2*Real.pi*ξ) := by
    rw [show -2*Real.pi*ξ*(-u) = (2*Real.pi*ξ)*u by ring]
    unfold spectralKLCoshInverseKernel
    rw [smul_eq_mul]
    ring
  have heq : 𝓕 (𝓕 (spectralKLCoshExponential x)) (-u) =
      (1/Real.pi : ℝ) • (∫ t : ℝ, spectralKLCoshInverseKernel x u t) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp_rw [spectralKLCoshExponential_fourier hx,hphase]
    rw [integral_const_mul,Measure.integral_comp_mul_left]
    rw [abs_of_pos (inv_pos.mpr (mul_pos two_pos Real.pi_pos)),Complex.real_smul]
    rw [Complex.real_smul]
    push_cast
    field_simp
  exact heq.symm.trans hi

theorem spectralKLCoshInverseKernel_pair (x u t : ℝ) :
    spectralKLCoshInverseKernel x u (-t)+spectralKLCoshInverseKernel x u t =
      2*((spectralKLRealKernel t x : ℂ)*(Real.cos (t*u) : ℂ)) := by
  unfold spectralKLCoshInverseKernel
  rw [spectralKLRealKernel_even]
  have hn : (((-t*u : ℝ) : ℂ)*Complex.I) = -((((t*u : ℝ) : ℂ)*Complex.I)) := by push_cast; ring
  rw [hn,Complex.ofReal_cos]
  have hc := Complex.two_cos (((t*u : ℝ) : ℂ))
  simp only [neg_mul] at hc ⊢
  linear_combination -(spectralKLRealKernel t x : ℂ)*hc

theorem schlafliBesselK_order_cos_integrable {x : ℝ} (hx : 0 < x) (u : ℝ) :
    Integrable (fun t : ℝ => schlafliBesselK ((t : ℂ)*Complex.I) x*(Real.cos (t*u) : ℂ)) := by
  have hK := schlafliBesselK_imaginary_order_integrable hx
  have hm := hK.aestronglyMeasurable.mul
    (by fun_prop : Continuous (fun t : ℝ => (Real.cos (t*u) : ℂ))).aestronglyMeasurable
  apply hK.norm.mono' hm
  filter_upwards with t
  dsimp only [Pi.mul_apply]
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _)

theorem schlafliBesselK_cosh_fourier_inversion {x : ℝ} (hx : 0 < x) (u : ℝ) :
    (2/Real.pi : ℝ) • (∫ t in Ioi (0 : ℝ),
      schlafliBesselK ((t : ℂ)*Complex.I) x*(Real.cos (t*u) : ℂ)) =
      Complex.exp (-(x*Real.cosh u) : ℝ) := by
  have hi := spectralKLCoshExponential_inverse_full hx u
  rw [integral_positive_negative_pair _ (spectralKLCoshInverseKernel_integrable hx u)] at hi
  simp_rw [spectralKLCoshInverseKernel_pair] at hi
  rw [integral_const_mul] at hi
  have heq : (∫ t in Ioi (0 : ℝ),
      (spectralKLRealKernel t x : ℂ)*(Real.cos (t*u) : ℂ)) =
      ∫ t in Ioi (0 : ℝ), schlafliBesselK ((t : ℂ)*Complex.I) x*(Real.cos (t*u) : ℂ) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only
    rw [schlafliBesselK_imaginary_eq_realKernel t hx]
  rw [heq,Complex.real_smul] at hi
  rw [Complex.real_smul]
  calc
    _ = ((1/Real.pi : ℝ) : ℂ)*(2*(∫ t in Ioi (0 : ℝ),
        schlafliBesselK ((t : ℂ)*Complex.I) x*(Real.cos (t*u) : ℂ))) := by push_cast; ring
    _ = _ := hi

theorem schlafliBesselK_cosh_fourier_difference {x : ℝ} (hx : 0 < x) (u v : ℝ) :
    (2/Real.pi : ℝ) • (∫ t in Ioi (0 : ℝ), schlafliBesselK ((t : ℂ)*Complex.I) x*
      ((Real.cos (t*u)-Real.cos (t*v) : ℝ) : ℂ)) =
      Complex.exp (-(x*Real.cosh u) : ℝ)-Complex.exp (-(x*Real.cosh v) : ℝ) := by
  simp only [Complex.ofReal_sub,mul_sub]
  rw [integral_sub (schlafliBesselK_order_cos_integrable hx u).restrict
    (schlafliBesselK_order_cos_integrable hx v).restrict,smul_sub,
    schlafliBesselK_cosh_fourier_inversion hx u,schlafliBesselK_cosh_fourier_inversion hx v]

end ArtinMatthews

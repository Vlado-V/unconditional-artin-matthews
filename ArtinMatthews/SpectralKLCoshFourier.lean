module

public import ArtinMatthews.SpectralKLCoshExponential


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Fourier transform of exp(-x cosh u) is the imaginary-order
K kernel. Its L1 spectral integrability is proved from two L1 derivatives. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein
open scoped Topology FourierTransform

namespace ArtinMatthews

theorem spectralKLRealKernel_even (t x : ℝ) : spectralKLRealKernel (-t) x = spectralKLRealKernel t x := by
  unfold spectralKLRealKernel
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  simp only [neg_mul,Real.cos_neg]

theorem spectralKLCoshExponential_fourier {x : ℝ} (hx : 0 < x) (ξ : ℝ) :
    𝓕 (spectralKLCoshExponential x) ξ = 2*(spectralKLRealKernel (2*Real.pi*ξ) x : ℂ) := by
  let ν : ℂ := ((-(2*Real.pi*ξ : ℝ) : ℝ) : ℂ)*Complex.I
  calc
    _ = ∫ u : ℝ, spectralKLogKernel ν x u := by
      rw [Real.fourier_real_eq_integral_exp_smul]
      apply integral_congr_ae
      filter_upwards with u
      simp only [spectralKLCoshExponential,spectralKLogKernel,smul_eq_mul]
      rw [← Complex.exp_add]
      congr 1
      dsimp [ν]
      push_cast
      ring
    _ = 2*schlafliBesselK ν x := by rw [schlafliBesselK_hyperbolic_integral ν hx]; ring
    _ = _ := by
      rw [schlafliBesselK_imaginary_eq_realKernel (-(2*Real.pi*ξ)) hx,spectralKLRealKernel_even]

theorem spectralKLRealKernel_complex_integrable {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => (spectralKLRealKernel t x : ℂ)) := by
  have hπ : 2*Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hi := ((spectralKLCoshExponential_fourier_integrable hx).comp_mul_left' (inv_ne_zero hπ)).const_mul (1/2 : ℂ)
  apply hi.congr
  filter_upwards with t
  rw [spectralKLCoshExponential_fourier hx]
  have ht : 2*Real.pi*((2*Real.pi)⁻¹*t) = t := by field_simp
  rw [ht]
  ring

theorem spectralKLRealKernel_integrable {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => spectralKLRealKernel t x) :=
  (spectralKLRealKernel_complex_integrable hx).re

theorem schlafliBesselK_imaginary_order_integrable {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => schlafliBesselK ((t : ℂ)*Complex.I) x) := by
  apply (spectralKLRealKernel_complex_integrable hx).congr
  filter_upwards with t
  exact (schlafliBesselK_imaginary_eq_realKernel t hx).symm

end ArtinMatthews

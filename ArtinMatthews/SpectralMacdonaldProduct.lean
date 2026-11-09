module

public import ArtinMatthews.SpectralMacdonaldHeatFubini


set_option backward.privateInPublic true
@[expose] public section

/-! The actual mixed-argument Macdonald product formula, derived from
the cosh convolution and absolutely convergent heat/Fourier Fubini. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein
open scoped Topology FourierTransform

namespace ArtinMatthews

def spectralMacdonaldProductIntegrand (x y t r : ℝ) : ℂ :=
  (r : ℂ)⁻¹*Complex.exp (-(r : ℂ)/2-((x : ℂ)^2+(y : ℂ)^2)/(2*r))*
    schlafliBesselK ((t : ℂ)*Complex.I) (x*y/r)

theorem spectralMacdonald_radius_phase {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (t : ℝ) :
    (∫ w : ℝ, schlafliBesselK 0 (spectralMacdonaldRadius x y w)*
      Complex.exp (((t*w : ℝ) : ℂ)*Complex.I)) =
      2*schlafliBesselK ((t : ℂ)*Complex.I) x*schlafliBesselK ((t : ℂ)*Complex.I) y := by
  have h := spectralMacdonald_radius_fourier hx hy (-t/(2*Real.pi))
  have ht : 2*Real.pi*(-t/(2*Real.pi)) = -t := by field_simp
  rw [ht,spectralKLRealKernel_even,spectralKLRealKernel_even] at h
  rw [schlafliBesselK_imaginary_eq_realKernel t hx,schlafliBesselK_imaginary_eq_realKernel t hy]
  rw [← h,Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with w
  simp only [smul_eq_mul]
  have he : -2*Real.pi*w*(-t/(2*Real.pi)) = t*w := by field_simp
  rw [he]
  ring

theorem spectralMacdonaldHeatFourier_factor {x y r : ℝ} (hx : 0 < x) (hy : 0 < y)
    (_hr : 0 < r) (t w : ℝ) :
    spectralMacdonaldHeatFourier x y t (w,r) =
      ((r : ℂ)⁻¹*Complex.exp (-(r : ℂ)/2-((x : ℂ)^2+(y : ℂ)^2)/(2*r)))*
        spectralKLogKernel ((t : ℂ)*Complex.I) (x*y/r) w := by
  have hs : (spectralMacdonaldRadius x y w : ℂ)^2 =
      (x : ℂ)^2+(y : ℂ)^2+2*(x : ℂ)*(y : ℂ)*(Real.cosh w : ℂ) := by
    exact_mod_cast spectralMacdonaldRadius_sq hx hy w
  unfold spectralMacdonaldHeatFourier spectralMacdonaldHeatKernel spectralKLogKernel
  dsimp only
  conv_lhs => rw [mul_assoc,← Complex.exp_add]
  conv_rhs => rw [mul_assoc,← Complex.exp_add]
  rw [hs]
  congr 2
  push_cast
  field_simp
  ring

theorem spectralMacdonaldHeatFourier_integral_w {x y r : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hr : 0 < r) (t : ℝ) :
    (∫ w : ℝ, spectralMacdonaldHeatFourier x y t (w,r)) =
      2*spectralMacdonaldProductIntegrand x y t r := by
  simp_rw [spectralMacdonaldHeatFourier_factor hx hy hr]
  rw [integral_const_mul]
  unfold spectralMacdonaldProductIntegrand
  rw [schlafliBesselK_hyperbolic_integral _ (div_pos (mul_pos hx hy) hr)]
  ring

theorem spectralMacdonaldProductIntegrand_integrable {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (t : ℝ) :
    IntegrableOn (spectralMacdonaldProductIntegrand x y t) (Ioi (0 : ℝ)) := by
  have hi := (spectralMacdonaldHeatFourier_integrable hx hy t).integral_prod_right
  apply (hi.const_mul (1/2 : ℂ)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [spectralMacdonaldHeatFourier_integral_w hx hy hr]
  ring

theorem schlafliBesselK_imaginary_macdonald_product {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (t : ℝ) :
    (∫ r in Ioi (0 : ℝ), spectralMacdonaldProductIntegrand x y t r) =
      2*schlafliBesselK ((t : ℂ)*Complex.I) x*schlafliBesselK ((t : ℂ)*Complex.I) y := by
  have h := integral_integral_swap (f := fun w r : ℝ => spectralMacdonaldHeatFourier x y t (w,r))
    (spectralMacdonaldHeatFourier_integrable hx hy t)
  have hleft : (∫ w : ℝ, ∫ r in Ioi (0 : ℝ), spectralMacdonaldHeatFourier x y t (w,r)) =
      4*schlafliBesselK ((t : ℂ)*Complex.I) x*schlafliBesselK ((t : ℂ)*Complex.I) y := by
    simp_rw [spectralMacdonaldHeatFourier_integral_r hx hy]
    rw [show (fun w : ℝ => 2*schlafliBesselK 0 (spectralMacdonaldRadius x y w)*
        Complex.exp (((t*w : ℝ) : ℂ)*Complex.I)) =
      (fun w : ℝ => 2*(schlafliBesselK 0 (spectralMacdonaldRadius x y w)*
        Complex.exp (((t*w : ℝ) : ℂ)*Complex.I))) by funext w; ring,
      integral_const_mul,spectralMacdonald_radius_phase hx hy]
    ring
  have hright : (∫ r in Ioi (0 : ℝ), ∫ w : ℝ, spectralMacdonaldHeatFourier x y t (w,r)) =
      2*(∫ r in Ioi (0 : ℝ), spectralMacdonaldProductIntegrand x y t r) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact spectralMacdonaldHeatFourier_integral_w hx hy hr t
  rw [hleft,hright] at h
  linear_combination -h/2

end ArtinMatthews

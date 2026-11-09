module

public import ArtinMatthews.SpectralWeberK


set_option backward.privateInPublic true
@[expose] public section

/-! Real square-root and imaginary-order normalizations of the proved
Gaussian Weber K evaluation. -/

noncomputable section
open Set MeasureTheory
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectral_positive_cpow_neg_half {p : ℝ} (hp : 0 < p) :
    (p : ℂ)^(-(1/2 : ℂ)) = (Real.sqrt p : ℂ)⁻¹ := by
  rw [show (-(1/2 : ℂ)) = ((-(1/2 : ℝ)) : ℂ) by norm_num,
    ← Complex.ofReal_neg,← Complex.ofReal_cpow hp.le,Real.rpow_neg hp.le,← Real.sqrt_eq_rpow,
    Complex.ofReal_inv]

theorem schlafliBesselK_gaussian_weber {ν : ℂ} (hν : |ν.re| < 1/2)
    {p : ℝ} (hp : 0 < p) :
    (∫ x in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(x : ℂ)^2)*schlafliBesselK (2*ν) x) =
      ((Real.sqrt (Real.pi/p) : ℂ)/(4*Complex.cos ((Real.pi : ℂ)*ν)))*
        Complex.exp ((1/(8*p) : ℝ) : ℂ)*schlafliBesselK ν (1/(8*p)) := by
  rw [spectralWeberK_evaluation hν hp,spectral_positive_cpow_neg_half hp,
    show (1/8 : ℝ)/p = 1/(8*p) by simp only [div_eq_mul_inv,mul_inv,one_mul]]
  have hr : (Real.sqrt (Real.pi/p) : ℂ) = (Real.sqrt Real.pi : ℂ)/(Real.sqrt p : ℂ) := by
    rw [Real.sqrt_div Real.pi_pos.le,Complex.ofReal_div]
  rw [hr]
  ring

theorem schlafliBesselK_imaginary_gaussian_weber (r : ℝ) {p : ℝ} (hp : 0 < p) :
    (∫ x in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(x : ℂ)^2)*
      schlafliBesselK (2*((r : ℂ)*Complex.I)) x) =
      ((Real.sqrt (Real.pi/p) : ℂ)/(4*(Real.cosh (Real.pi*r) : ℂ)))*
        Complex.exp ((1/(8*p) : ℝ) : ℂ)*schlafliBesselK ((r : ℂ)*Complex.I) (1/(8*p)) := by
  have hν : |((r : ℂ)*Complex.I).re| < 1/2 := by norm_num
  have hc : Complex.cos ((Real.pi : ℂ)*((r : ℂ)*Complex.I)) =
      (Real.cosh (Real.pi*r) : ℂ) := by
    rw [← mul_assoc,Complex.cos_mul_I,← Complex.ofReal_mul,Complex.ofReal_cosh]
  rw [schlafliBesselK_gaussian_weber hν hp,hc]

end ArtinMatthews

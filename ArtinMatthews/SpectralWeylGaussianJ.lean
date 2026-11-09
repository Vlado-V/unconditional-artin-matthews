module

public import ArtinMatthews.SpectralWeberJ
public import ArtinMatthews.SpectralBesselKIConnection
public import ArtinMatthews.SpectralWeylGaussianKAction


set_option backward.privateInPublic true
@[expose] public section

/-! Actual same-sign J multiplier under Gaussian modulus testing.
The divided multiplier requires sin(pi*nu) != 0; the undivided difference
identity also includes zero order. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralWeberJ_difference {ν : ℂ} (hν : |ν.re| < 1/2)
    {p : ℝ} (hp : 0 < p) :
    (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*
      (Complex.besselJ (2*ν) (X : ℂ)-Complex.besselJ (2*(-ν)) (X : ℂ))) =
      (-(2 : ℂ)/(Real.pi : ℂ))*((Real.sqrt (Real.pi/p) : ℂ)/2)*
        Complex.exp (-((1/(8*p) : ℝ) : ℂ))*Complex.sin ((Real.pi : ℂ)*ν)*
        schlafliBesselK ν (1/(8*p)) := by
  have hpos : -(1/2 : ℝ) < ν.re := by linarith [neg_le_abs ν.re]
  have hneg : -(1/2 : ℝ) < (-ν).re := by simp only [Complex.neg_re]; linarith [le_abs_self ν.re]
  have hv : 0 < 1/(8*p) := one_div_pos.mpr (by positivity)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI := schlafliBesselK_eq_I_difference hν hv
  rw [mul_comm (Real.pi : ℂ) ν] at hI
  have hd : spectralBesselI ν (1/(8*p))-spectralBesselI (-ν) (1/(8*p)) =
      (-(2 : ℂ)/(Real.pi : ℂ))*(Complex.sin ((Real.pi : ℂ)*ν)*schlafliBesselK ν (1/(8*p))) := by
    apply mul_right_cancel₀ hpi
    field_simp [hpi]
    linear_combination 2*hI
  simp_rw [mul_sub]
  rw [integral_sub (spectralWeberJ_integrable ν hpos hp) (spectralWeberJ_integrable (-ν) hneg hp),
    spectralBesselJ_gaussian_weber ν hpos hp,spectralBesselJ_gaussian_weber (-ν) hneg hp]
  calc
    _ = (((Real.sqrt (Real.pi/p) : ℂ)/2)*Complex.exp (-((1/(8*p) : ℝ) : ℂ)))*
        (spectralBesselI ν (1/(8*p))-spectralBesselI (-ν) (1/(8*p))) := by ring
    _ = _ := by rw [hd]; ring

theorem spectralWeylJMultiplier_gaussian_integrable {ν : ℂ} (hν : |ν.re| < 1/2)
    {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun X : ℝ => Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
      ((-(2 : ℂ)*(Real.pi : ℂ)/Complex.sin ((Real.pi : ℂ)*ν))*
        (Complex.besselJ (2*ν) (X : ℂ)-Complex.besselJ (2*(-ν)) (X : ℂ))/(X : ℂ)))
      (Ioi (0 : ℝ)) := by
  have hpos : -(1/2 : ℝ) < ν.re := by linarith [neg_le_abs ν.re]
  have hneg : -(1/2 : ℝ) < (-ν).re := by simp only [Complex.neg_re]; linarith [le_abs_self ν.re]
  have hi := ((spectralWeberJ_integrable ν hpos hp).sub
    (spectralWeberJ_integrable (-ν) hneg hp)).const_mul
      (-(2 : ℂ)*(Real.pi : ℂ)/Complex.sin ((Real.pi : ℂ)*ν))
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
  dsimp only [Pi.sub_apply]
  field_simp [Complex.ofReal_ne_zero.mpr hX.ne']

theorem spectralWeylJMultiplier_gaussian {ν : ℂ} (hν : |ν.re| < 1/2)
    (hsin : Complex.sin ((Real.pi : ℂ)*ν) ≠ 0) {p : ℝ} (hp : 0 < p) :
    (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
      ((-(2 : ℂ)*(Real.pi : ℂ)/Complex.sin ((Real.pi : ℂ)*ν))*
        (Complex.besselJ (2*ν) (X : ℂ)-Complex.besselJ (2*(-ν)) (X : ℂ))/(X : ℂ))) =
      2*(Real.sqrt (Real.pi/p) : ℂ)*Complex.exp (-((1/(8*p) : ℝ) : ℂ))*
        schlafliBesselK ν (1/(8*p)) := by
  have he : (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
      ((-(2 : ℂ)*(Real.pi : ℂ)/Complex.sin ((Real.pi : ℂ)*ν))*
        (Complex.besselJ (2*ν) (X : ℂ)-Complex.besselJ (2*(-ν)) (X : ℂ))/(X : ℂ))) =
      (-(2 : ℂ)*(Real.pi : ℂ)/Complex.sin ((Real.pi : ℂ)*ν))*
        (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*
          (Complex.besselJ (2*ν) (X : ℂ)-Complex.besselJ (2*(-ν)) (X : ℂ))) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro X hX
    dsimp only
    field_simp [Complex.ofReal_ne_zero.mpr hX.ne']
  rw [he,spectralWeberJ_difference hν hp]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi,hsin]

end ArtinMatthews

module

public import ArtinMatthews.SpectralBesselNormalizedOrderBound
public import ArtinMatthews.SpectralWeylGaussianJImaginary


set_option backward.privateInPublic true
@[expose] public section

/-! Actual J/I/K order bounds required for spectral/modulus Fubini.
The common spatial growth is Gaussian and the spectral edge is at most 1/t. -/

noncomputable section
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectral_Gamma_one_neg_imaginary_norm (u : ℝ) :
    ‖Complex.Gamma (1-(u : ℂ)*Complex.I)‖ = ‖Complex.Gamma (1+(u : ℂ)*Complex.I)‖ := by
  have hc : Complex.Gamma (1-(u : ℂ)*Complex.I) =
      star (Complex.Gamma (1+(u : ℂ)*Complex.I)) := by
    change _ = (starRingEnd ℂ) (Complex.Gamma (1+(u : ℂ)*Complex.I))
    rw [← Complex.Gamma_conj]
    congr 1
    simp only [map_add,map_mul,map_one,Complex.conj_ofReal,Complex.conj_I]
    ring
  rw [hc,norm_star]

theorem spectral_besselJ_neg_imaginary_order_bound {t X : ℝ} (ht : 0 < t) (hX : 0 < X) :
    ‖Complex.besselJ (-(((2*t : ℝ) : ℂ)*Complex.I)) (X : ℂ)‖/Real.sinh (Real.pi*t) ≤
      Real.exp (X^2/4)*(1+(Real.sqrt (Real.cosh Real.pi)/Real.pi)/t) := by
  apply spectral_Bessel_sinh_rescale_bound ht (Real.exp_pos _).le
  have h := spectral_besselJ_norm_le_exp_of_re_zero (-(((2*t : ℝ) : ℂ)*Complex.I)) (by simp) hX
  rw [show -(((2*t : ℝ) : ℂ)*Complex.I)+1 = 1-((2*t : ℝ) : ℂ)*Complex.I by ring,
    spectral_Gamma_one_neg_imaginary_norm] at h
  exact h

theorem spectral_besselI_neg_imaginary_order_bound {t X : ℝ} (ht : 0 < t) (hX : 0 < X) :
    ‖spectralBesselI (-(((2*t : ℝ) : ℂ)*Complex.I)) X‖/Real.sinh (Real.pi*t) ≤
      Real.exp (X^2/4)*(1+(Real.sqrt (Real.cosh Real.pi)/Real.pi)/t) := by
  apply spectral_Bessel_sinh_rescale_bound ht (Real.exp_pos _).le
  have h := spectralBesselI_norm_le_exp_of_re_zero (-(((2*t : ℝ) : ℂ)*Complex.I)) (by simp) hX
  rw [show -(((2*t : ℝ) : ℂ)*Complex.I)+1 = 1-((2*t : ℝ) : ℂ)*Complex.I by ring,
    spectral_Gamma_one_neg_imaginary_norm] at h
  exact h

theorem spectral_besselK_imaginary_order_bound {t X : ℝ} (ht : 0 < t) (hX : 0 < X) :
    Real.cosh (Real.pi*t)*‖schlafliBesselK (((2*t : ℝ) : ℂ)*Complex.I) X‖ ≤
      (Real.pi/2)*Real.exp (X^2/4)*(1+(Real.sqrt (Real.cosh Real.pi)/Real.pi)/t) := by
  let ν : ℂ := ((2*t : ℝ) : ℂ)*Complex.I
  let S : ℝ := Real.sinh (Real.pi*t)
  let M : ℝ := Real.exp (X^2/4)*(1+(Real.sqrt (Real.cosh Real.pi)/Real.pi)/t)
  have hS : 0 < S := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht)
  have hν : |ν.re| < 1/2 := by dsimp [ν]; norm_num
  have h := congrArg norm (schlafliBesselK_eq_I_difference hν hX)
  have hsin : ‖Complex.sin ((Real.pi : ℂ)*ν)‖ = Real.sinh (Real.pi*(2*t)) := by
    dsimp [ν]
    rw [spectral_sin_pi_imaginary,norm_mul,Complex.norm_I,one_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos
        (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos (mul_pos two_pos ht)))]
  have hpi : ‖(Real.pi : ℂ)/2‖ = Real.pi/2 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    norm_num
  rw [norm_mul,norm_mul,hsin,hpi] at h
  have hp := spectral_besselI_imaginary_order_bound ht hX
  have hm := spectral_besselI_neg_imaginary_order_bound ht hX
  change ‖spectralBesselI ν X‖/S ≤ M at hp
  change ‖spectralBesselI (-ν) X‖/S ≤ M at hm
  have hp' := (div_le_iff₀ hS).mp hp
  have hm' := (div_le_iff₀ hS).mp hm
  have hsum : ‖spectralBesselI (-ν) X‖+‖spectralBesselI ν X‖ ≤ 2*M*S := by linarith
  have hb : Real.sinh (Real.pi*(2*t))*‖schlafliBesselK ν X‖ ≤ Real.pi*M*S := by
    calc
      _ = (Real.pi/2)*‖spectralBesselI (-ν) X-spectralBesselI ν X‖ := h
      _ ≤ (Real.pi/2)*(‖spectralBesselI (-ν) X‖+‖spectralBesselI ν X‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ Real.pi/2)]
  have hfinal : (2*S)*(Real.cosh (Real.pi*t)*‖schlafliBesselK ν X‖) ≤
      (2*S)*((Real.pi/2)*M) := by
    calc
      _ = Real.sinh (Real.pi*(2*t))*‖schlafliBesselK ν X‖ := by
        rw [show Real.pi*(2*t) = 2*(Real.pi*t) by ring,Real.sinh_two_mul]
        dsimp [S]
        ring
      _ ≤ Real.pi*M*S := hb
      _ = _ := by ring
  have hbound := le_of_mul_le_mul_left hfinal (mul_pos two_pos hS)
  change Real.cosh (Real.pi*t)*‖schlafliBesselK ν X‖ ≤ (Real.pi/2)*Real.exp (X^2/4)*
    (1+(Real.sqrt (Real.cosh Real.pi)/Real.pi)/t)
  simpa only [M,mul_assoc] using hbound

end ArtinMatthews

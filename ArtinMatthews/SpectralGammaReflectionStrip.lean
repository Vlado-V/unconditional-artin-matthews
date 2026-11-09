module

public import ArtinMatthews.SpectralUnitBeta


set_option backward.privateInPublic true
@[expose] public section

/-! Reflection identities on the genuine open strip between consecutive
Gamma poles.  Every denominator is shown nonzero there. -/

noncomputable section

namespace ArtinMatthews

theorem spectral_Gamma_strip_sin_ne_zero (z : ℂ) (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    Complex.sin ((Real.pi : ℂ)*z) ≠ 0 := by
  have hG := Complex.Gamma_ne_zero_of_re_pos hz0
  have hG1 : Complex.Gamma (1-z) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using sub_pos.mpr hz1)
  intro hzero
  have h := Complex.Gamma_mul_Gamma_one_sub z
  rw [hzero,div_zero] at h
  exact mul_ne_zero hG hG1 h

theorem spectral_Gamma_inv_reflection (z : ℂ) (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    (Complex.Gamma (1-z))⁻¹ = Complex.Gamma z*Complex.sin ((Real.pi : ℂ)*z)/(Real.pi : ℂ) := by
  have hG1 : Complex.Gamma (1-z) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using sub_pos.mpr hz1)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := (eq_div_iff (spectral_Gamma_strip_sin_ne_zero z hz0 hz1)).mp
    (Complex.Gamma_mul_Gamma_one_sub z)
  rw [inv_eq_one_div]
  apply (div_eq_div_iff hG1 hpi).mpr
  linear_combination -h

theorem spectral_Gamma_half_cos_reflection (s : ℂ) (hs0 : -(1/2 : ℝ) < s.re)
    (hs1 : s.re < 1/2) :
    Complex.Gamma (1/2-s)*Complex.cos ((Real.pi : ℂ)*s) =
      (Real.pi : ℂ)/Complex.Gamma (s+1/2) := by
  have hz0 : 0 < (s+(1/2 : ℂ)).re := by norm_num; linarith
  have hz1 : (s+(1/2 : ℂ)).re < 1 := by norm_num; linarith
  have hG := Complex.Gamma_ne_zero_of_re_pos hz0
  have h := (eq_div_iff (spectral_Gamma_strip_sin_ne_zero (s+1/2) hz0 hz1)).mp
    (Complex.Gamma_mul_Gamma_one_sub (s+1/2))
  have he : (Real.pi : ℂ)*(s+1/2) = (Real.pi : ℂ)/2+(Real.pi : ℂ)*s := by ring
  rw [he,Complex.sin_add,Complex.sin_pi_div_two,Complex.cos_pi_div_two,
    one_mul,zero_mul,add_zero,show (1 : ℂ)-(s+1/2) = 1/2-s by ring] at h
  apply (eq_div_iff hG).mpr
  linear_combination h

theorem spectral_sin_sum_sub_difference (s ν : ℂ) :
    Complex.sin ((Real.pi : ℂ)*(s+ν))-Complex.sin ((Real.pi : ℂ)*(s-ν)) =
      2*Complex.cos ((Real.pi : ℂ)*s)*Complex.sin ((Real.pi : ℂ)*ν) := by
  rw [mul_add,mul_sub,Complex.sin_add,Complex.sin_sub]
  ring

end ArtinMatthews

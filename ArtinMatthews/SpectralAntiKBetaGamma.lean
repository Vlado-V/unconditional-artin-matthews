module

public import ArtinMatthews.SpectralAntiGammaConstant


set_option backward.privateInPublic true
@[expose] public section

/-! Exact evaluation of the two beta terms in the growing-exponential
K integral.  The cosine of the order is retained in the numerator. -/

noncomputable section

namespace ArtinMatthews

theorem spectralAntiK_beta_gamma (ν s : ℂ)
    (hs : |ν.re| < s.re) (hsh : s.re < 1/2) :
    (1/2 : ℂ)*Complex.Gamma s*(2 : ℂ)^s*
      (Complex.betaIntegral (s-ν) (1-2*s)+Complex.betaIntegral (s+ν) (1-2*s)) =
      (Real.sqrt Real.pi : ℂ)*(2 : ℂ)^(-s)*Complex.Gamma (s+ν)*Complex.Gamma (s-ν)*
        Complex.cos ((Real.pi : ℂ)*ν)/
        (Complex.Gamma (s+1/2)*Complex.cos ((Real.pi : ℂ)*s)) := by
  have hs0 : 0 < s.re := (abs_nonneg ν.re).trans_lt hs
  have ha0 : 0 < (s+ν).re := by simp only [Complex.add_re]; linarith [neg_le_abs ν.re]
  have hb0 : 0 < (s-ν).re := by simp only [Complex.sub_re]; linarith [le_abs_self ν.re]
  have ha1 : (s+ν).re < 1 := by simp only [Complex.add_re]; linarith [le_abs_self ν.re]
  have hb1 : (s-ν).re < 1 := by simp only [Complex.sub_re]; linarith [neg_le_abs ν.re]
  have hc0 : 0 < (1-2*s).re := by norm_num; linarith
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hA := spectral_Gamma_inv_reflection (s+ν) ha0 ha1
  have hB := spectral_Gamma_inv_reflection (s-ν) hb0 hb1
  have hsum : Complex.sin ((Real.pi : ℂ)*(s+ν))+Complex.sin ((Real.pi : ℂ)*(s-ν)) =
      2*Complex.sin ((Real.pi : ℂ)*s)*Complex.cos ((Real.pi : ℂ)*ν) := by
    rw [mul_add,mul_sub,Complex.sin_add,Complex.sin_sub]
    ring_nf
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hb0 hc0,
    Complex.betaIntegral_eq_Gamma_mul_div _ _ ha0 hc0,
    show (s-ν)+(1-2*s) = 1-(s+ν) by ring,
    show (s+ν)+(1-2*s) = 1-(s-ν) by ring]
  simp only [div_eq_mul_inv]
  rw [hA,hB]
  calc
    _ = (Complex.Gamma s*(2 : ℂ)^s*Complex.Gamma (1-2*s)/(2*(Real.pi : ℂ)))*
        Complex.Gamma (s+ν)*Complex.Gamma (s-ν)*
        (Complex.sin ((Real.pi : ℂ)*(s+ν))+Complex.sin ((Real.pi : ℂ)*(s-ν))) := by
      field_simp [hp]
    _ = (Complex.Gamma s*(2 : ℂ)^s*Complex.Gamma (1-2*s)*
          Complex.sin ((Real.pi : ℂ)*s)/(Real.pi : ℂ))*
        Complex.Gamma (s+ν)*Complex.Gamma (s-ν)*Complex.cos ((Real.pi : ℂ)*ν) := by
      rw [hsum]
      ring_nf
    _ = _ := by rw [spectralAntiK_gamma_constant s hs0 hsh]; ring_nf

end ArtinMatthews

module

public import ArtinMatthews.SpectralGammaReflectionStrip


set_option backward.privateInPublic true
@[expose] public section

/-! Exact scalar normalization for the Gaussian K Weber transform. -/

noncomputable section

namespace ArtinMatthews

theorem spectral_cos_pi_ne_zero_middle (ν : ℂ) (hν : |ν.re| < 1/2) :
    Complex.cos ((Real.pi : ℂ)*ν) ≠ 0 := by
  have hlo : -(1/2 : ℝ) < ν.re := by linarith [neg_le_abs ν.re]
  have hhi : ν.re < 1/2 := (le_abs_self ν.re).trans_lt hν
  have hG : Complex.Gamma (ν+1/2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by norm_num; linarith)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := spectral_Gamma_half_cos_reflection ν hlo hhi
  intro hz
  rw [hz,mul_zero] at h
  exact div_ne_zero hpi hG h.symm

theorem spectralWeberK_scalar (ν s : ℂ) (hs : 0 < s.re)
    (hstrip : s.re+|ν.re| < 1/2) :
    ((Real.sqrt Real.pi : ℂ)/(4*Complex.cos ((Real.pi : ℂ)*ν)))*
      (1/8 : ℂ)^(s-1/2)*
      ((Real.sqrt Real.pi : ℂ)*(2 : ℂ)^(-(1/2-s))*Complex.cos ((Real.pi : ℂ)*ν)/
        (Complex.Gamma (1-s)*Complex.cos ((Real.pi : ℂ)*(1/2-s)))) =
      Complex.Gamma s*(2 : ℂ)^(-1-2*s) := by
  have hsh : s.re < 1/2 := by linarith [abs_nonneg ν.re]
  have hν : |ν.re| < 1/2 := by linarith
  have hcos := spectral_cos_pi_ne_zero_middle ν hν
  have hsin := spectral_Gamma_strip_sin_ne_zero s hs (by linarith)
  have hinv := spectral_Gamma_inv_reflection s hs (by linarith)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hroot2 : (Real.sqrt Real.pi : ℂ)^2 = (Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have htrig : Complex.cos ((Real.pi : ℂ)*(1/2-s)) = Complex.sin ((Real.pi : ℂ)*s) := by
    rw [show (Real.pi : ℂ)*(1/2-s) = (Real.pi : ℂ)/2-(Real.pi : ℂ)*s by ring,
      Complex.cos_sub,Complex.cos_pi_div_two,Complex.sin_pi_div_two]
    ring
  have h8 : (1/8 : ℂ)^(s-1/2) = (2 : ℂ)^(-3*(s-1/2)) := by
    rw [show (1/8 : ℂ) = ((8 : ℝ) : ℂ)⁻¹ by norm_num,
      Complex.inv_cpow_ofReal_nonneg (by norm_num),← Complex.cpow_neg]
    norm_num only [Complex.ofReal_ofNat]
    have h := Complex.natCast_cpow_natCast_mul 2 3 (-(s-(1/2 : ℂ)))
    norm_num only [Nat.cast_ofNat,Nat.reducePow] at h
    rw [← h]
    congr 1
    ring
  have hp : (1/4 : ℂ)*(1/8 : ℂ)^(s-1/2)*(2 : ℂ)^(-(1/2-s)) =
      (2 : ℂ)^(-1-2*s) := by
    rw [h8,mul_assoc,← Complex.cpow_add _ _ (by norm_num)]
    rw [show -3*(s-(1/2 : ℂ))+-((1/2 : ℂ)-s) = (1-2*s) by ring]
    have h := Complex.cpow_sub (x := (2 : ℂ)) (1-2*s) 2 (by norm_num)
    rw [Complex.cpow_two] at h
    norm_num at h
    rw [show (-1 : ℂ)-2*s = (1-2*s)-2 by ring,h]
    ring
  calc
    _ = Complex.Gamma s*((1/4 : ℂ)*(1/8 : ℂ)^(s-1/2)*(2 : ℂ)^(-(1/2-s)))*
        ((Real.sqrt Real.pi : ℂ)^2/(Real.pi : ℂ)) := by
      rw [htrig]
      simp only [div_eq_mul_inv,mul_inv,hinv]
      field_simp [hcos,hsin,hpi]
    _ = _ := by rw [hp,hroot2,div_self hpi,mul_one]

end ArtinMatthews

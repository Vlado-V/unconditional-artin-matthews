module

public import ArtinMatthews.SpectralGammaReflectionStrip


set_option backward.privateInPublic true
@[expose] public section

/-! Duplication and reflection supply the exact scalar required by the
growing-exponential K Mellin integral. -/

noncomputable section

namespace ArtinMatthews

theorem spectral_cos_pi_ne_zero_strip (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1/2) :
    Complex.cos ((Real.pi : ℂ)*s) ≠ 0 := by
  have hG : Complex.Gamma (s+1/2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by norm_num; linarith)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := spectral_Gamma_half_cos_reflection s (by linarith) hs1
  intro hz
  rw [hz,mul_zero] at h
  exact div_ne_zero hpi hG h.symm

theorem spectralAntiK_gamma_constant (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1/2) :
    Complex.Gamma s*(2 : ℂ)^s*Complex.Gamma (1-2*s)*
        Complex.sin ((Real.pi : ℂ)*s)/(Real.pi : ℂ) =
      (Real.sqrt Real.pi : ℂ)*(2 : ℂ)^(-s)/
        (Complex.Gamma (s+1/2)*Complex.cos ((Real.pi : ℂ)*s)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hroot : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hroot2 : (Real.sqrt Real.pi : ℂ)^2 = (Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hG : Complex.Gamma (s+1/2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by norm_num; linarith)
  have hcos := spectral_cos_pi_ne_zero_strip s hs0 hs1
  have hpow : (2 : ℂ)^s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num)]
    exact Complex.exp_ne_zero _
  have hdup := Complex.Gamma_mul_Gamma_add_half ((1/2 : ℂ)-s)
  rw [show (1/2 : ℂ)-s+1/2 = 1-s by ring,
    show 2*((1/2 : ℂ)-s) = 1-2*s by ring,
    show (1 : ℂ)-(1-2*s) = 2*s by ring] at hdup
  have href := (eq_div_iff (spectral_Gamma_strip_sin_ne_zero s hs0 (by linarith))).mp
    (Complex.Gamma_mul_Gamma_one_sub s)
  have hhalf := (eq_div_iff hG).mp (spectral_Gamma_half_cos_reflection s (by linarith) hs1)
  have hmain : Complex.Gamma (1-2*s)*(2 : ℂ)^(2*s)*(Real.sqrt Real.pi : ℂ)*
      Complex.Gamma s*Complex.sin ((Real.pi : ℂ)*s)*Complex.Gamma (s+1/2)*
      Complex.cos ((Real.pi : ℂ)*s) = (Real.pi : ℂ)^2 := by
    calc
      _ = (Complex.Gamma ((1/2 : ℂ)-s)*Complex.cos ((Real.pi : ℂ)*s)*Complex.Gamma (s+1/2))*
          (Complex.Gamma s*Complex.Gamma (1-s)*Complex.sin ((Real.pi : ℂ)*s)) := by
        rw [← hdup]
        ring
      _ = _ := by rw [hhalf,href]; ring
  have hp2 : (2 : ℂ)^s*(2 : ℂ)^s = (2 : ℂ)^(2*s) := by
    rw [← Complex.cpow_add _ _ (by norm_num)]
    congr 1
    ring
  have hpc : (2 : ℂ)^(-s)*(2 : ℂ)^s = 1 := by
    rw [← Complex.cpow_add _ _ (by norm_num),neg_add_cancel,Complex.cpow_zero]
  apply (div_eq_div_iff hpi (mul_ne_zero hG hcos)).mpr
  apply mul_right_cancel₀ (mul_ne_zero hpow hroot)
  calc
    _ = Complex.Gamma (1-2*s)*((2 : ℂ)^s*(2 : ℂ)^s)*(Real.sqrt Real.pi : ℂ)*
        Complex.Gamma s*Complex.sin ((Real.pi : ℂ)*s)*Complex.Gamma (s+1/2)*
        Complex.cos ((Real.pi : ℂ)*s) := by ring
    _ = (Real.pi : ℂ)^2 := by rw [hp2,hmain]
    _ = _ := by
      have hr : (Real.sqrt Real.pi : ℂ)*(Real.sqrt Real.pi : ℂ) = (Real.pi : ℂ) := by
        simpa only [pow_two] using hroot2
      calc
        _ = (Real.pi : ℂ)*((Real.sqrt Real.pi : ℂ)*(Real.sqrt Real.pi : ℂ))*
            ((2 : ℂ)^(-s)*(2 : ℂ)^s) := by rw [hr,hpc]; ring
        _ = _ := by ring

end ArtinMatthews

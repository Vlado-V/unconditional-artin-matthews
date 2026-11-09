module

public import ArtinMatthews.SpectralKLPoleFactor


set_option backward.privateInPublic true
@[expose] public section

/-! Exact imaginary-order Gamma normalization for the genuine Bessel
series bounds used in spectral/modulus Fubini. -/

noncomputable section

namespace ArtinMatthews

theorem spectral_Gamma_one_imaginary_product (t : ℝ) (ht : 0 < t) :
    Complex.Gamma (1+(t : ℂ)*Complex.I)*Complex.Gamma (1-(t : ℂ)*Complex.I) =
      ((Real.pi*t/Real.sinh (Real.pi*t) : ℝ) : ℂ) := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hp : (t : ℂ)*Complex.I ≠ 0 := mul_ne_zero ht0 Complex.I_ne_zero
  have hm : -(t : ℂ)*Complex.I ≠ 0 := mul_ne_zero (neg_ne_zero.mpr ht0) Complex.I_ne_zero
  have hs : (Real.sinh (Real.pi*t) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht)).ne'
  rw [show (1 : ℂ)+(t : ℂ)*Complex.I = (t : ℂ)*Complex.I+1 by ring,
    show (1 : ℂ)-(t : ℂ)*Complex.I = -(t : ℂ)*Complex.I+1 by ring,
    Complex.Gamma_add_one _ hp,Complex.Gamma_add_one _ hm]
  have hi : ((t : ℂ)*Complex.I)*(-(t : ℂ)*Complex.I) = (t : ℂ)^2 := by
    ring_nf
    rw [Complex.I_sq]
    ring
  calc
    _ = (((t : ℂ)*Complex.I)*(-(t : ℂ)*Complex.I))*
        (Complex.Gamma ((t : ℂ)*Complex.I)*Complex.Gamma (-(t : ℂ)*Complex.I)) := by ring
    _ = _ := by
      rw [hi,spectral_Gamma_imaginary_product t ht]
      push_cast
      field_simp

theorem spectral_Gamma_one_imaginary_norm_sq (t : ℝ) (ht : 0 < t) :
    ‖Complex.Gamma (1+(t : ℂ)*Complex.I)‖^2 = Real.pi*t/Real.sinh (Real.pi*t) := by
  have hc : Complex.Gamma (1-(t : ℂ)*Complex.I) =
      star (Complex.Gamma (1+(t : ℂ)*Complex.I)) := by
    change _ = (starRingEnd ℂ) (Complex.Gamma (1+(t : ℂ)*Complex.I))
    rw [← Complex.Gamma_conj]
    congr 1
    simp only [map_add,map_mul,map_one,Complex.conj_ofReal,Complex.conj_I]
    ring
  have h := congrArg norm (spectral_Gamma_one_imaginary_product t ht)
  rw [hc,norm_mul,norm_star] at h
  have hpos : 0 < Real.pi*t/Real.sinh (Real.pi*t) :=
    div_pos (mul_pos Real.pi_pos ht) (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht))
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hpos,pow_two] using h

end ArtinMatthews

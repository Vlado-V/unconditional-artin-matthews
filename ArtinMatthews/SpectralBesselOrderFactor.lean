module

public import ArtinMatthews.SpectralGammaImaginaryNorm


set_option backward.privateInPublic true
@[expose] public section

/-! The exact order denominator and a uniform large-order lower bound.
This removes the exponential Gamma/sinh factors from the Bessel majorants. -/

noncomputable section

namespace ArtinMatthews

def spectralBesselOrderDenominator (t : ℝ) : ℝ :=
  ‖Complex.Gamma (1+((2*t : ℝ) : ℂ)*Complex.I)‖*Real.sinh (Real.pi*t)

theorem spectralBesselOrderDenominator_pos {t : ℝ} (ht : 0 < t) :
    0 < spectralBesselOrderDenominator t := by
  apply mul_pos
  · apply norm_pos_iff.mpr
    apply Complex.Gamma_ne_zero_of_re_pos
    norm_num
  · exact Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht)

theorem spectralBesselOrderDenominator_sq {t : ℝ} (ht : 0 < t) :
    (spectralBesselOrderDenominator t)^2 =
      Real.pi*t*Real.sinh (Real.pi*t)/Real.cosh (Real.pi*t) := by
  have hs : Real.sinh (Real.pi*t) ≠ 0 := (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht)).ne'
  have hc : Real.cosh (Real.pi*t) ≠ 0 := by linarith [Real.one_le_cosh (Real.pi*t)]
  unfold spectralBesselOrderDenominator
  rw [mul_pow,spectral_Gamma_one_imaginary_norm_sq (2*t) (by positivity),
    show Real.pi*(2*t) = 2*(Real.pi*t) by ring,Real.sinh_two_mul]
  field_simp

theorem spectral_cosh_le_three_sinh {x : ℝ} (hx : 1 ≤ x) :
    Real.cosh x ≤ 3*Real.sinh x := by
  have he : 0 < Real.exp x := Real.exp_pos _
  have hexp : 3 ≤ (Real.exp x)^2 := by
    have h := Real.add_one_le_exp (2*x)
    rw [show 2*x = x+x by ring,Real.exp_add] at h
    nlinarith
  have hrec : Real.exp x*Real.exp (-x) = 1 := by
    rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
  have hh : 2*Real.exp (-x) ≤ Real.exp x := by
    by_contra hn
    have hlt : Real.exp x < 2*Real.exp (-x) := lt_of_not_ge hn
    have hm := mul_lt_mul_of_pos_right hlt he
    nlinarith
  rw [Real.cosh_eq,Real.sinh_eq]
  linarith

theorem spectralBesselOrderDenominator_ge_one {t : ℝ} (ht : 1 ≤ t) :
    1 ≤ spectralBesselOrderDenominator t := by
  have ht0 : 0 < t := by linarith
  have hd := spectralBesselOrderDenominator_pos ht0
  have hc : 0 < Real.cosh (Real.pi*t) := by linarith [Real.one_le_cosh (Real.pi*t)]
  have hprod : (spectralBesselOrderDenominator t)^2*Real.cosh (Real.pi*t) =
      Real.pi*t*Real.sinh (Real.pi*t) := by
    rw [spectralBesselOrderDenominator_sq ht0]
    field_simp
  have hx : 1 ≤ Real.pi*t := by nlinarith [Real.pi_gt_three]
  have hcs := spectral_cosh_le_three_sinh hx
  have hsq : 1 ≤ (spectralBesselOrderDenominator t)^2 := by
    by_contra hn
    have hn' : (spectralBesselOrderDenominator t)^2 < 1 := lt_of_not_ge hn
    have hspos : 0 < Real.sinh (Real.pi*t) := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht0)
    have hlt := mul_lt_mul_of_pos_right hn' hc
    have hbig : 3 < Real.pi*t := by nlinarith [Real.pi_gt_three]
    have hlt2 := mul_lt_mul_of_pos_right hbig hspos
    linarith
  nlinarith

theorem spectralBesselOrderFactor_large {t : ℝ} (ht : 1 ≤ t) :
    1/spectralBesselOrderDenominator t ≤ 1 := by
  have hd := spectralBesselOrderDenominator_ge_one ht
  exact (div_le_iff₀ (by linarith : 0 < spectralBesselOrderDenominator t)).mpr (by linarith)

end ArtinMatthews

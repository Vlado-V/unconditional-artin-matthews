module

public import ArtinMatthews.SpectralGaussianMellin


set_option backward.privateInPublic true
@[expose] public section

/-! Positive-square power identities used by the Gaussian Mellin kernel. -/

noncomputable section

namespace ArtinMatthews

theorem spectral_inverse_square_cpow {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (1/((x^2 : ℝ) : ℂ))^s = (x : ℂ)^(-2*s) := by
  rw [one_div,Complex.inv_cpow_ofReal_nonneg (sq_nonneg x),← Complex.cpow_neg]
  have hp := Complex.mul_cpow_ofReal_nonneg hx.le hx.le (-s)
  rw [← Complex.ofReal_mul,← pow_two] at hp
  rw [hp,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
  congr 1
  ring

theorem spectral_inverse_square_rpow {x : ℝ} (hx : 0 < x) (s : ℝ) :
    (1/x^2)^s = x^(-2*s) := by
  rw [one_div,← Real.rpow_neg_eq_inv_rpow,← Real.rpow_two,← Real.rpow_mul hx.le]
  congr 1
  ring

end ArtinMatthews

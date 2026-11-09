module

public import ArtinMatthews.SpectralABLWindows


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
noncomputable section

theorem spectral_complex_gaussian_shift_norm (t y m Δ : ℝ) :
    ‖Complex.exp (-((((t : ℂ) + (y : ℂ) * Complex.I - (m : ℂ)) / (Δ : ℂ)) ^ 2))‖ =
      Real.exp ((y / Δ) ^ 2 - ((t - m) / Δ) ^ 2) := by
  have he : ((t : ℂ) + (y : ℂ) * Complex.I - (m : ℂ)) / (Δ : ℂ) =
      (((t - m) / Δ : ℝ) : ℂ) + ((y / Δ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.norm_exp]
  congr 1
  norm_num [pow_two, Complex.mul_re, Complex.mul_im]

theorem spectralABLRegularWindow_strip_bound {T Δ : ℝ} (hT : 0 < T) (hΔ : 0 < Δ)
    (t y : ℝ) (hy : |y| ≤ 1) :
    ‖spectralABLRegularWindow T Δ ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      ((t ^ 2 + 5 / 4) / T ^ 2) * Real.exp (1 / Δ ^ 2) *
        (Real.exp (-(((t - T) / Δ) ^ 2)) + Real.exp (-(((t + T) / Δ) ^ 2))) := by
  let z : ℂ := (t : ℂ) + (y : ℂ) * Complex.I
  have hy2 : y ^ 2 ≤ 1 := by
    rcases abs_le.mp hy with ⟨hl, hr⟩
    nlinarith
  have hzsq : ‖z‖ ^ 2 = t ^ 2 + y ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [z, Complex.normSq_apply, pow_two]
  have hpoly : ‖z ^ 2 + 1 / 4‖ ≤ t ^ 2 + 5 / 4 := by
    calc
      _ ≤ ‖z ^ 2‖ + ‖(1 / 4 : ℂ)‖ := norm_add_le _ _
      _ = t ^ 2 + y ^ 2 + 1 / 4 := by rw [norm_pow, hzsq]; norm_num
      _ ≤ _ := by linarith
  have he (m : ℝ) :
      ‖Complex.exp (-(((z - (m : ℂ)) / (Δ : ℂ)) ^ 2))‖ ≤
        Real.exp (1 / Δ ^ 2) * Real.exp (-(((t - m) / Δ) ^ 2)) := by
    rw [spectral_complex_gaussian_shift_norm t y m Δ, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [div_pow]
    have hsq := div_le_div_of_nonneg_right hy2 (sq_pos_of_pos hΔ).le
    linarith
  have heminus :
      ‖Complex.exp (-(((z + (T : ℂ)) / (Δ : ℂ)) ^ 2))‖ ≤
        Real.exp (1 / Δ ^ 2) * Real.exp (-(((t + T) / Δ) ^ 2)) := by
    simpa only [sub_neg_eq_add, Complex.ofReal_neg] using he (-T)
  have hsum : ‖Complex.exp (-(((z - (T : ℂ)) / (Δ : ℂ)) ^ 2)) +
      Complex.exp (-(((z + (T : ℂ)) / (Δ : ℂ)) ^ 2))‖ ≤
      Real.exp (1 / Δ ^ 2) *
        (Real.exp (-(((t - T) / Δ) ^ 2)) + Real.exp (-(((t + T) / Δ) ^ 2))) :=
    (norm_add_le _ _).trans ((add_le_add (he T) heminus).trans_eq (mul_add _ _ _).symm)
  change ‖(z ^ 2 + 1 / 4) / (T : ℂ) ^ 2 * _‖ ≤ _
  rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hT.le]
  calc
    _ ≤ ((t ^ 2 + 5 / 4) / T ^ 2) * (Real.exp (1 / Δ ^ 2) *
        (Real.exp (-(((t - T) / Δ) ^ 2)) + Real.exp (-(((t + T) / Δ) ^ 2)))) :=
      mul_le_mul (div_le_div_of_nonneg_right hpoly (sq_nonneg T)) hsum (norm_nonneg _) (by positivity)
    _ = _ := by ring

end
end ArtinMatthews

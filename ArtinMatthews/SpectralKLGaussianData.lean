module

public import ArtinMatthews.SpectralGaussianMoments
public import ArtinMatthews.SpectralABLRegularStrip
public import ArtinMatthews.SpectralABLInverseSmooth


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set Complex
open scoped ContDiff
noncomputable section

/-- The direct spectral Gaussian used for the KL approximate unit. -/
def spectralKLGaussianData (R : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-((z / (R : ℂ)) ^ 2))

theorem spectralKLGaussianData_differentiable (R : ℝ) :
    Differentiable ℂ (spectralKLGaussianData R) := by
  unfold spectralKLGaussianData
  fun_prop

theorem spectralKLGaussianData_real_contDiff (R : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => spectralKLGaussianData R (t : ℂ)) :=
  (spectralKLGaussianData_differentiable R).contDiff.restrict_scalars ℝ |>.comp Complex.ofRealCLM.contDiff

theorem spectralKLGaussianData_even (R : ℝ) (z : ℂ) :
    spectralKLGaussianData R (-z) = spectralKLGaussianData R z := by
  simp only [spectralKLGaussianData, neg_div, neg_sq]

theorem spectralKLGaussianData_real (R t : ℝ) :
    spectralKLGaussianData R (t : ℂ) = (Real.exp (-((t / R) ^ 2)) : ℂ) := by
  unfold spectralKLGaussianData
  push_cast
  rfl

theorem spectralKLGaussianData_norm_shift (R t y : ℝ) :
    ‖spectralKLGaussianData R ((t : ℂ) + (y : ℂ) * I)‖ =
      Real.exp ((y / R) ^ 2 - (t / R) ^ 2) := by
  simpa only [spectralKLGaussianData, Complex.ofReal_zero, sub_zero] using
    spectral_complex_gaussian_shift_norm t y 0 R

theorem spectralKLGaussianData_strip_rapid (R : ℝ) (hR : 0 < R)
    (A B : ℝ) (hB : 0 ≤ B) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t y : ℝ, |y| ≤ B →
      (1 + t ^ 2) ^ N * Real.exp (A * |t|) *
        ‖spectralKLGaussianData R ((t : ℂ) + (y : ℂ) * I)‖ ≤ C := by
  let m := A * R ^ 2 / 2
  obtain ⟨C, hC, hbound⟩ := spectralGaussian_shifted_weight_bound m R hR N
  refine ⟨Real.exp ((B / R) ^ 2 + (A * R / 2) ^ 2) * C, by positivity, ?_⟩
  intro t y hy
  have hy2 : y ^ 2 ≤ B ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg y) hB).mpr hy
  have hY : (y / R) ^ 2 ≤ (B / R) ^ 2 := by
    rw [div_pow, div_pow]
    exact div_le_div_of_nonneg_right hy2 (sq_nonneg R)
  have heq : A * |t| - (t / R) ^ 2 =
      (A * R / 2) ^ 2 - ((|t| - m) / R) ^ 2 := by
    dsimp [m]
    field_simp
    nlinarith [sq_abs t]
  have he : A * |t| + ((y / R) ^ 2 - (t / R) ^ 2) ≤
      ((B / R) ^ 2 + (A * R / 2) ^ 2) - ((|t| - m) / R) ^ 2 := by
    linarith
  have hb := hbound |t|
  rw [sq_abs] at hb
  rw [spectralKLGaussianData_norm_shift]
  calc
    _ = (1 + t ^ 2) ^ N * Real.exp (A * |t| + ((y / R) ^ 2 - (t / R) ^ 2)) := by
      rw [mul_assoc, ← Real.exp_add]
    _ ≤ (1 + t ^ 2) ^ N * Real.exp
        (((B / R) ^ 2 + (A * R / 2) ^ 2) - ((|t| - m) / R) ^ 2) := by
      gcongr
    _ = Real.exp ((B / R) ^ 2 + (A * R / 2) ^ 2) *
        ((1 + t ^ 2) ^ N * Real.exp (-((|t| - m) / R) ^ 2)) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)

end
end ArtinMatthews

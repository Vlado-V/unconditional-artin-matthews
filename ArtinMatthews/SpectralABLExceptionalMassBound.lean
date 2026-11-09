module

public import ArtinMatthews.SpectralABLWindowFirstMoments


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set
noncomputable section

theorem spectralABLExceptionalWindowReal_first_moment_bound
    (a : ℝ) {A : ℕ} (hA : 3 ≤ A) {t : ℝ} (ht : 0 ≤ t) :
    t * spectralABLExceptionalWindowReal a A t ≤
      spectralABLExceptionalBound A * (1 + t ^ 2)⁻¹ := by
  let B : ℝ := spectralABLExceptionalBound A
  have hB : 0 ≤ B := by dsimp [B, spectralABLExceptionalBound]; positivity
  let u : ℝ := 1 + t ^ 2
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : 1 ≤ u := by dsimp [u]; nlinarith [sq_nonneg t]
  have htu : t ≤ u := by dsimp [u]; nlinarith [sq_nonneg (t - 1)]
  have hpow : u ^ 2 ≤ u ^ (A - 1) := pow_le_pow_right₀ hu1 (by omega)
  have hdecay := spectralABLExceptionalWindowReal_decay a (show 1 ≤ A by omega) t
  change t * spectralABLExceptionalWindowReal a A t ≤ B * u⁻¹
  calc
    _ ≤ t * (B / u ^ (A - 1)) := mul_le_mul_of_nonneg_left hdecay ht
    _ ≤ t * (B / u ^ 2) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left hB (pow_pos hu _) hpow) ht
    _ = (B / u) * (t / u) := by field_simp
    _ ≤ (B / u) * 1 := mul_le_mul_of_nonneg_left
      ((div_le_one hu).mpr htu) (div_nonneg hB hu.le)
    _ = B * u⁻¹ := by simp [div_eq_mul_inv]

theorem spectralABLExceptionalWindowReal_first_moment_integral_le
    (a : ℝ) {A : ℕ} (hA : 3 ≤ A) :
    (∫ t : ℝ in Ioi 0, t * spectralABLExceptionalWindowReal a A t) ≤
      spectralABLExceptionalBound A * (Real.pi / 2) := by
  have hleft := spectralABLExceptionalWindowReal_first_moment_integrable a hA
  have hright : IntegrableOn
      (fun t : ℝ => spectralABLExceptionalBound A * (1 + t ^ 2)⁻¹) (Ioi 0) :=
    (integrable_inv_one_add_sq.const_mul (spectralABLExceptionalBound A)).integrableOn
  calc
    _ ≤ ∫ t : ℝ in Ioi 0, spectralABLExceptionalBound A * (1 + t ^ 2)⁻¹ := by
      apply integral_mono_ae hleft hright
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact spectralABLExceptionalWindowReal_first_moment_bound a hA ht.le
    _ = spectralABLExceptionalBound A * (Real.pi / 2) := by
      rw [integral_const_mul]
      simp only [integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero]

end
end ArtinMatthews

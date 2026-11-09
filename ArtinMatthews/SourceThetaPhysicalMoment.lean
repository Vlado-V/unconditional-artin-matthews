module

public import ArtinMatthews.SourceThetaAbsoluteSmoothing


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceReflection

open MeasureTheory Set Filter ArtinMatthews.SourcePhysical
noncomputable section

/-- The coefficient in the weighted convolution bound is exactly the
absolute Mellin moment in the physical T coordinate. -/
theorem sourceThetaGaussianLogMoment_eq (C₀ A₀ : ℝ) (r : ℕ) (β : ℝ) :
    sourceThetaGaussianLogMoment C₀ A₀ r β =
      ∫ T in Ioi 0, ‖sourceThetaGaussianKernel C₀ A₀ r T‖ * T ^ (β - 1) := by
  unfold sourceThetaGaussianLogMoment
  rw [← sourceRealExp_image_univ, integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    Real.exp_injective.injOn, Measure.restrict_univ]
  apply integral_congr_ae
  filter_upwards with y
  rw [abs_of_pos (Real.exp_pos _), smul_eq_mul, sourceThetaGaussianKernel, Real.log_exp,
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_left_comm, ← Real.exp_add]
  congr 2
  ring

end
end ArtinMatthews.SourceReflection

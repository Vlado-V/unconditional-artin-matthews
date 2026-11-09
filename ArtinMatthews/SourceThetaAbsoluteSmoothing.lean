module

public import ArtinMatthews.SourceThetaProfileSmoothing


set_option backward.privateInPublic true
@[expose] public section

/-! The absolute smoothing integral with the literal physical dT/T. -/
namespace ArtinMatthews.SourceReflection

open MeasureTheory Set Filter ArtinMatthews.SourcePhysical
noncomputable section

def sourceThetaGaussianProfileAbsIntegrand (C₀ A₀ : ℝ) (r : ℕ) (τ : ℝ)
    (A : ℝ → ℝ) (u T : ℝ) : ℝ :=
  T⁻¹ * (‖sourceThetaGaussianKernel C₀ A₀ r T‖ * A (u * T ^ τ))

def sourceThetaGaussianProfileAbs (C₀ A₀ : ℝ) (r : ℕ) (τ : ℝ) (A : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ T in Ioi 0, sourceThetaGaussianProfileAbsIntegrand C₀ A₀ r τ A u T

private theorem sourceThetaAbsIntegrand_exp (C₀ A₀ : ℝ) (r : ℕ) (τ : ℝ)
    (A : ℝ → ℝ) (x y : ℝ) :
    |Real.exp y| • sourceThetaGaussianProfileAbsIntegrand C₀ A₀ r τ A (Real.exp x) (Real.exp y) =
      ‖sourceThetaGaussianLogKernel C₀ A₀ r y‖ * A (Real.exp (x + τ * y)) := by
  rw [sourceThetaGaussianProfileAbsIntegrand, abs_of_pos (Real.exp_pos _), smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (Real.exp_ne_zero _), one_mul, sourceThetaGaussianKernel, Real.log_exp,
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, Real.exp_add, mul_comm τ y]

theorem sourceThetaGaussianProfileAbs_integrable_iff (C₀ A₀ : ℝ) (r : ℕ) (τ : ℝ)
    (A : ℝ → ℝ) (x : ℝ) :
    IntegrableOn (sourceThetaGaussianProfileAbsIntegrand C₀ A₀ r τ A (Real.exp x)) (Ioi 0) ↔
      Integrable (fun y : ℝ => ‖sourceThetaGaussianLogKernel C₀ A₀ r y‖ * A (Real.exp (x + τ * y))) := by
  rw [← sourceRealExp_image_univ, integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    Real.exp_injective.injOn, integrableOn_univ]
  simp_rw [sourceThetaAbsIntegrand_exp]

theorem sourceThetaGaussianProfileAbs_exp (C₀ A₀ : ℝ) (r : ℕ) (τ : ℝ)
    (A : ℝ → ℝ) (x : ℝ) :
    sourceThetaGaussianProfileAbs C₀ A₀ r τ A (Real.exp x) =
      sourceThetaGaussianLogSmoothAbs C₀ A₀ r τ (fun t => A (Real.exp t)) x := by
  unfold sourceThetaGaussianProfileAbs sourceThetaGaussianLogSmoothAbs
  rw [← sourceRealExp_image_univ, integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    Real.exp_injective.injOn, Measure.restrict_univ]
  simp_rw [sourceThetaAbsIntegrand_exp]

end
end ArtinMatthews.SourceReflection

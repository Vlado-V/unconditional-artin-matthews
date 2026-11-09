module

public import Mathlib.Analysis.MellinInversion


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open MeasureTheory Set
noncomputable section

theorem sourceRealExp_image_univ : Real.exp '' univ = Ioi 0 := by
  ext r
  constructor
  · rintro ⟨t, _, rfl⟩
    exact Real.exp_pos _
  · intro hr
    exact ⟨Real.log r, mem_univ _, Real.exp_log hr⟩

theorem sourceLogMellin_integrand_eq (V : ℝ → ℂ) (s : ℂ) (t : ℝ) :
    |Real.exp t| • ((Real.exp t : ℂ) ^ (s - 1) • V (Real.exp t)) =
      Complex.exp (s * (t : ℂ)) * V (Real.exp t) := by
  rw [abs_of_pos (Real.exp_pos _), Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)), ← Complex.ofReal_log (Real.exp_pos t).le,
    Real.log_exp, smul_eq_mul, RCLike.real_smul_eq_coe_mul]
  change (Real.exp t : ℂ) * (Complex.exp ((t : ℂ) * (s - 1)) * V (Real.exp t)) = _
  rw [← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  ring

theorem sourceMellinConvergent_iff_log (V : ℝ → ℂ) (s : ℂ) :
    MellinConvergent V s ↔
      Integrable (fun t : ℝ => Complex.exp (s * (t : ℂ)) * V (Real.exp t)) := by
  unfold MellinConvergent
  rw [← sourceRealExp_image_univ, integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    Real.exp_injective.injOn, integrableOn_univ]
  simp_rw [sourceLogMellin_integrand_eq]

theorem sourceMellin_eq_log (V : ℝ → ℂ) (s : ℂ) :
    mellin V s = ∫ t : ℝ, Complex.exp (s * (t : ℂ)) * V (Real.exp t) := by
  unfold mellin
  rw [← sourceRealExp_image_univ, integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    Real.exp_injective.injOn, Measure.restrict_univ]
  simp_rw [sourceLogMellin_integrand_eq]

end
end ArtinMatthews.SourcePhysical

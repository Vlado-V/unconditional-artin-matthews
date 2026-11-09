module

public import ArtinMatthews.SourceComplexMellinSchwartz


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory
open scoped SchwartzMap
noncomputable section

def sourceComplexMellinWeight (s z : ℂ) : ℂ :=
  Complex.exp ((2 * s - 2) * (Real.log ‖z‖ : ℂ))

def sourceComplexMellin (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  ∫ z : ℂ, f z * sourceComplexMellinWeight s z ∂sourceComplexTraceMeasure

theorem sourceComplexTraceMeasure_ae_ne_zero : ∀ᵐ z : ℂ ∂sourceComplexTraceMeasure, z ≠ 0 := by
  apply ae_iff.mpr
  simp [sourceComplexTraceMeasure]

theorem sourceComplexMellinWeight_measurable (s : ℂ) :
    Measurable (sourceComplexMellinWeight s) := by
  exact Complex.continuous_exp.measurable.comp
    (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
      (Real.measurable_log.comp continuous_norm.measurable)))

theorem sourceComplexMellinWeight_eq_cpow (s z : ℂ) (hz : z ≠ 0) :
    sourceComplexMellinWeight s z = (‖z‖ : ℂ) ^ (2 * s - 2) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)),
    ← Complex.ofReal_log (norm_nonneg _), sourceComplexMellinWeight, mul_comm]

theorem sourceComplexMellinWeight_norm (s z : ℂ) (hz : z ≠ 0) :
    ‖sourceComplexMellinWeight s z‖ = ‖z‖ ^ (2 * s.re - 2) := by
  rw [sourceComplexMellinWeight_eq_cpow s z hz,
    Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr hz)]
  congr 1
  simp [Complex.mul_re]

theorem sourceComplexMellin_real_eq (f : ℂ → ℂ) (s : ℝ) :
    sourceComplexMellin f (s : ℂ) =
      ∫ z : ℂ, f z * (‖z‖ ^ (2 * s - 2) : ℝ) ∂sourceComplexTraceMeasure := by
  unfold sourceComplexMellin
  apply integral_congr_ae
  filter_upwards [sourceComplexTraceMeasure_ae_ne_zero] with z hz
  rw [sourceComplexMellinWeight_eq_cpow _ _ hz,
    show (2 : ℂ) * (s : ℂ) - 2 = ((2 * s - 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_cpow (norm_nonneg _)]

end
end ArtinMatthews.VaryingKummerAnalytic

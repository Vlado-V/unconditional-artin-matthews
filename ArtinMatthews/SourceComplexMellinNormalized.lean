module

public import ArtinMatthews.SourceComplexMellinWeight


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory
noncomputable section

/-- The exact normalized local norm of a complex place is the squared modulus. -/
theorem sourceComplexMellinWeight_eq_normalized (s z : ℂ) (hz : z ≠ 0) :
    sourceComplexMellinWeight s z = ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s / ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  have h0 : ((‖z‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz))
  unfold sourceComplexMellinWeight
  calc
    _ = Complex.exp (Complex.log ((‖z‖ ^ 2 : ℝ) : ℂ) * s -
        Complex.log ((‖z‖ ^ 2 : ℝ) : ℂ)) := by
      congr 1
      rw [← Complex.ofReal_log (by positivity : 0 ≤ ‖z‖ ^ 2), Real.log_pow]
      push_cast
      ring
    _ = _ := by rw [Complex.exp_sub, Complex.exp_log h0, Complex.cpow_def_of_ne_zero h0]

theorem sourceComplexMellin_eq_normalized (f : ℂ → ℂ) (s : ℂ) :
    sourceComplexMellin f s =
      ∫ z : ℂ, f z * (((‖z‖ ^ 2 : ℝ) : ℂ) ^ s / ((‖z‖ ^ 2 : ℝ) : ℂ))
        ∂sourceComplexTraceMeasure := by
  unfold sourceComplexMellin
  apply integral_congr_ae
  filter_upwards [sourceComplexTraceMeasure_ae_ne_zero] with z hz
  rw [sourceComplexMellinWeight_eq_normalized s z hz]

end
end ArtinMatthews.VaryingKummerAnalytic

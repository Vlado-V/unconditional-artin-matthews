module

public import ArtinMatthews.SourceComplexPolarMeasure
public import ArtinMatthews.SourceCircleHaar


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open MeasureTheory Set
open ArtinMatthews.VaryingKummerAnalytic
open scoped ENNReal Real
noncomputable section

theorem sourceComplexPolar_eq_mul_circle (r θ : ℝ) :
    sourceComplexPolar r θ = (r : ℂ) * (Circle.exp θ : ℂ) := by
  rw [sourceComplexPolar, Circle.coe_exp, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

theorem sourceComplexTraceMultiplicative_lintegral_circle (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z : ℂ, ENNReal.ofReal ((‖z‖ ^ 2)⁻¹) * f z ∂sourceComplexTraceMeasure) =
      ∫⁻ t : ℝ, ∫⁻ θ : Circle, f ((Real.exp (t / 2) : ℂ) * θ) ∂sourceCircleHaar := by
  rw [sourceComplexTraceMultiplicative_lintegral f hf]
  apply lintegral_congr
  intro t
  rw [sourceCircleHaar_lintegral]
  · simp only [sourceComplexPolar_eq_mul_circle]
  · exact hf.comp (measurable_const.mul Circle.measurable_coe)

end
end ArtinMatthews.SourcePhysical

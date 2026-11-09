module

public import ArtinMatthews.SourceTraceFourierDecay
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory
open scoped SchwartzMap FourierTransform
noncomputable section

def sourceComplexTraceDilation : ℂ ≃L[ℝ] ℂ :=
  Complex.conjCLE.trans
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℂ) (Units.mk0 (2 : ℝ) two_ne_zero))

theorem sourceComplexTraceDilation_apply (z : ℂ) :
    sourceComplexTraceDilation z = (2 : ℝ) • star z := rfl

/-- The actual trace transform is a Schwartz map, so its logarithmic
derivatives can use the genuine Schwartz decay bounds. -/
def sourceComplexTraceFourierSchwartz (f : 𝓢(ℂ, ℂ)) : 𝓢(ℂ, ℂ) :=
  (2 : ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ sourceComplexTraceDilation (𝓕 f)

theorem sourceComplexTraceFourierSchwartz_apply (f : 𝓢(ℂ, ℂ)) (z : ℂ) :
    sourceComplexTraceFourierSchwartz f z = sourceComplexTraceFourier f z := by
  change (2 : ℂ) * (𝓕 f : 𝓢(ℂ, ℂ)) (sourceComplexTraceDilation z) = _
  rw [sourceComplexTraceDilation_apply, source_complex_trace_fourier_schwartz_eq]

/-- Radial logarithmic derivative `fderiv ℝ f z z`, as an actual Schwartz map. -/
def sourceComplexEulerSchwartz (f : 𝓢(ℂ, ℂ)) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply (E := ℂ) ℝ ℂ).flip
    (ContinuousLinearMap.id ℝ ℂ).hasTemperateGrowth (SchwartzMap.fderivCLM ℝ ℂ ℂ f)

theorem sourceComplexEulerSchwartz_apply (f : 𝓢(ℂ, ℂ)) (z : ℂ) :
    sourceComplexEulerSchwartz f z = fderiv ℝ f z z := rfl

end
end ArtinMatthews.VaryingKummerAnalytic

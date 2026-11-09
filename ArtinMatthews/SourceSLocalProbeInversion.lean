module

public import ArtinMatthews.SourceSLocalProbeSheetIdentity
public import ArtinMatthews.SourceSLocalSheetMellinInversion
public import ArtinMatthews.SourceSLocalProbeVertical


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (v : InfinitePlace K)
local notation "hv" => (sourceSLocalComplexPlace K hζ v)
local notation "ν" => (sourceSLocalNormalizedSheetMeasure K hζ S v)
local notation "F₀" => (sourceSLocalProbeFourierTensor K hζ S v)

theorem sourceSLocalProbeSheet_eq_verticalIntegral (σ : ℝ) (hσ : 0 < σ) {T : ℝ} (hT : 0 < T) :
    sourceSLocalProbeSheet K hζ S v T =
      (1 / (2 * Real.pi) : ℝ) • ∫ τ : ℝ,
        (T : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I)) *
          sourceSLocalProbeMellin K hζ S v ((σ : ℂ) + (τ : ℂ) * Complex.I) := by
  have : BorelSpace (SWholeUnits K S) := sourceSWholeUnits_product_borel S v
  have : Measure.IsHaarMeasure ν := sourceSLocalNormalizedSheetMeasure_isHaar K hζ S v
  have : SigmaFinite ν := sourceSLocalNormalizedSheetMeasure_sigmaFinite K hζ S v
  have hInt : Integrable (fun x => F₀ x * (sLocalNorm K S x : ℂ) ^ (σ : ℂ))
      (sourceSLocalRadialHaar S hv ν) := by
    rw [← sourceSLocalUnitProductMeasure_eq_radial K hζ S v]
    exact sourceSLocalProbeMellin_integrable K hζ S v (σ : ℂ) (by simpa using hσ)
  have hEq : sourceSLocalRadialMellin S hv ν F₀ = sourceSLocalProbeMellin K hζ S v :=
    funext (sourceSLocalProbeRadialMellin_eq K hζ S v)
  have hVert : Complex.VerticalIntegrable (sourceSLocalRadialMellin S hv ν F₀) σ := by
    rw [hEq]
    exact sourceSLocalProbeMellin_verticalIntegrable K hζ S v σ hσ
  have hV : ContinuousAt (fun t : ℝ => sourceSLocalSheetProfile S ν hζ F₀ (Real.exp t))
      (Real.log T) := (sourceSLocalProbeSheet_logSmooth K hζ S v).continuous.continuousAt
  have h := sourceSLocalSheetProfile_eq_verticalIntegral S hv ν hζ F₀
    (sourceSLocalProbeFourierTensor_measurable K hζ S v) σ hInt hVert hT hV
  rw [hEq] at h
  exact h

end
end ArtinMatthews.SourcePhysical

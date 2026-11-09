module

public import ArtinMatthews.SourceSLocalSheetBorel
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map


set_option backward.privateInPublic true
@[expose] public section

/-! The sheet sends the chosen product Haar measure to the norm-one group
with its exact pushforward normalization. -/

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open scoped NumberField ENNReal ArtinMatthews.SourcePhysical
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (v : InfinitePlace K)
variable [MeasurableSpace (SNormOneOtherUnits S v)] [BorelSpace (SNormOneOtherUnits S v)]

theorem measurable_sourceSheetOtherNorm : Measurable (sourceSheetOtherNorm S v) :=
  (continuous_sourceSheetOtherNorm S v).measurable

theorem measurable_sourceSheetRadius : Measurable (sourceSheetRadius S v) :=
  (continuous_sourceSheetRadius S v).measurable

variable {v}
variable (hv : IsComplex v)

/-- The given sheet measure transported by the exact norm-one coordinates. -/
def sourceSNormOneSheetMeasure (μ : Measure (Circle × SNormOneOtherUnits S v)) :
    Measure (SNormOne K S) :=
  μ.map (sourceSNormOneFromSheet hv S)

theorem sourceSNormOneSheetMeasure_isHaar (μ : Measure (Circle × SNormOneOtherUnits S v))
    [μ.IsHaarMeasure] : (sourceSNormOneSheetMeasure S hv μ).IsHaarMeasure :=
  (sourceSNormOneSheetContinuousMulEquiv hv S).symm.isHaarMeasure_map μ

theorem sourceSNormOneSheetMeasure_prod_isHaar
    (μθ : Measure Circle) (μo : Measure (SNormOneOtherUnits S v))
    [μθ.IsHaarMeasure] [μo.IsHaarMeasure] :
    (sourceSNormOneSheetMeasure S hv (μθ.prod μo)).IsHaarMeasure := by
  let : PolishSpace (SNormOneOtherUnits S v) := sourceSheetOtherUnits_polish S v
  let : LocallyCompactSpace (SNormOneOtherUnits S v) := sourceSheetOtherUnits_locallyCompact S v
  exact sourceSNormOneSheetMeasure_isHaar S hv (μθ.prod μo)

@[simp] theorem sourceSNormOneSheetMeasure_map_toSheet
    (μ : Measure (Circle × SNormOneOtherUnits S v)) :
    (sourceSNormOneSheetMeasure S hv μ).map (sourceSNormOneToSheet hv S) = μ :=
  MeasurableEquiv.map_map_symm (ν := μ) (sourceSNormOneSheetMeasurableEquiv S hv)

theorem sourceSNormOneSheetMeasure_apply (μ : Measure (Circle × SNormOneOtherUnits S v))
    {A : Set (SNormOne K S)} (hA : MeasurableSet A) :
    sourceSNormOneSheetMeasure S hv μ A = μ ((sourceSNormOneFromSheet hv S) ⁻¹' A) :=
  Measure.map_apply (continuous_sourceSNormOneFromSheet hv S).measurable hA

theorem sourceSNormOneSheetMeasure_lintegral (μ : Measure (Circle × SNormOneOtherUnits S v))
    (f : SNormOne K S → ℝ≥0∞) :
    (∫⁻ x, f x ∂sourceSNormOneSheetMeasure S hv μ) =
      ∫⁻ y, f (sourceSNormOneFromSheet hv S y) ∂μ :=
  lintegral_map_equiv f (sourceSNormOneSheetMeasurableEquiv S hv).symm

theorem sourceSNormOneSheetMeasure_integral (μ : Measure (Circle × SNormOneOtherUnits S v))
    (f : SNormOne K S → ℂ) :
    (∫ x, f x ∂sourceSNormOneSheetMeasure S hv μ) =
      ∫ y, f (sourceSNormOneFromSheet hv S y) ∂μ :=
  integral_map_equiv (sourceSNormOneSheetMeasurableEquiv S hv).symm f

end
end ArtinMatthews.SourcePhysical

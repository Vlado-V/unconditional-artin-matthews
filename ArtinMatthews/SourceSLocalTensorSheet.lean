module

public import ArtinMatthews.SourceSLocalRadialSheet
public import ArtinMatthews.SourceSLocalSheetHaar
public import ArtinMatthews.SourceSheetSmooth


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory Set
open scoped NumberField Classical SchwartzMap ContDiff
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable {v : InfinitePlace K} (hv : IsComplex v)

def sourceSLocalChosenTensor (g : 𝓢(ℂ, ℂ)) (G : (SNormOneOtherUnits S v) → ℂ) (x : SWholeUnits K S) : ℂ :=
  g (sourceComplexPlaceUnitsEquiv hv (x.1 v) : ℂ) * G (sourceSheetOther S v x)

variable [MeasurableSpace (SNormOneOtherUnits S v)] [BorelSpace (SNormOneOtherUnits S v)]

/-- The literal physical sheet for the split local tensor, using the original all-place ell_T. -/
def sourceSLocalTensorSheet (μo : Measure (SNormOneOtherUnits S v)) {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (g : 𝓢(ℂ, ℂ)) (G : (SNormOneOtherUnits S v) → ℂ) (T : ℝ) : ℂ :=
  ∫ x : SNormOne K S, sourceSLocalChosenTensor S hv g G
    ((x : SWholeUnits K S) * sLocalPositiveScaling K hζ S T)
      ∂sourceSNormOneSheetMeasure S hv (sourceCircleHaar.prod μo)

theorem sourceSLocalTensorSheet_exp (μo : Measure (SNormOneOtherUnits S v)) [μo.IsHaarMeasure]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (g : 𝓢(ℂ, ℂ)) (G : (SNormOneOtherUnits S v) → ℂ) (t : ℝ) :
    sourceSLocalTensorSheet S hv μo hζ g G (Real.exp t) =
      sourceSheetLogProfile μo (sourceSheetOtherNorm S v) g G t := by
  have : sourceCircleHaar.IsHaarMeasure := sourceCircleHaar_isHaar
  have : (sourceSNormOneSheetMeasure S hv (sourceCircleHaar.prod μo)).IsHaarMeasure :=
    sourceSNormOneSheetMeasure_prod_isHaar S hv sourceCircleHaar μo
  unfold sourceSLocalTensorSheet
  rw [← sourceSLocal_radial_integral_eq_literal S _ hζ hv (sourceSLocalChosenTensor S hv g G),
    sourceSNormOneSheetMeasure_integral]
  unfold sourceSheetLogProfile
  apply integral_congr_ae
  filter_upwards with a
  change sourceSLocalChosenTensor S hv g G (sourceSLocalRadialSheet S hv a t) =
    sourceSheetProfileIntegrand (sourceSheetOtherNorm S v) g G t a
  rw [sourceSLocalChosenTensor, sourceSLocalRadialSheet_chosen, sourceSLocalRadialSheet_other,
    sourceSheetProfileIntegrand]

theorem sourceSLocalTensorSheet_logSmooth (μo : Measure (SNormOneOtherUnits S v)) [μo.IsHaarMeasure] [SFinite μo]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (g : 𝓢(ℂ, ℂ)) (G : (SNormOneOtherUnits S v) → ℂ) (hG : Measurable G)
    (σ : ℝ) (hσ : 0 < σ) (hI : Integrable (fun y => ‖G y‖ * (sourceSheetOtherNorm S v y) ^ σ) μo) :
    ContDiff ℝ ∞ (fun t : ℝ => sourceSLocalTensorSheet S hv μo hζ g G (Real.exp t)) := by
  simp_rw [sourceSLocalTensorSheet_exp]
  exact sourceSheetLogProfile_contDiff μo (sourceSheetOtherNorm S v) (sourceSheetOtherNorm_pos S v)
    (measurable_sourceSheetOtherNorm S v) g G hG σ hσ hI

theorem sourceSLocalTensorSheet_norm_le (μo : Measure (SNormOneOtherUnits S v)) [μo.IsHaarMeasure] [SFinite μo]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (g : 𝓢(ℂ, ℂ)) (G : (SNormOneOtherUnits S v) → ℂ) (hG : Measurable G)
    (σ : ℝ) (hσ : 0 < σ) (hI : Integrable (fun y => ‖G y‖ * (sourceSheetOtherNorm S v y) ^ σ) μo) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T →
      ‖sourceSLocalTensorSheet S hv μo hζ g G T‖ ≤ C * T ^ (-σ) := by
  obtain ⟨C,hC,hb⟩ := (sourceSheetLogProfile_integrable_and_bound μo
    (sourceSheetOtherNorm S v) (sourceSheetOtherNorm_pos S v) (measurable_sourceSheetOtherNorm S v)
    g G hG σ hσ hI).2
  refine ⟨C,hC,fun T hT => ?_⟩
  have h := hb (Real.log T)
  rw [← sourceSLocalTensorSheet_exp S hv μo hζ g G, Real.exp_log hT] at h
  rw [Real.rpow_def_of_pos hT, mul_comm (Real.log T)]
  exact h

end
end ArtinMatthews.SourcePhysical

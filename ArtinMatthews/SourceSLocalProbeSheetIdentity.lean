module

public import ArtinMatthews.SourceSLocalProbeMellin


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField Classical SchwartzMap ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (v : InfinitePlace K)
local notation "hv" => (sourceSLocalComplexPlace K hζ v)
local notation "μo" => (sourceSLocalOtherUnitMeasure K hζ S v)
local notation "ν" => (sourceSLocalNormalizedSheetMeasure K hζ S v)
local notation "F₀" => (sourceSLocalProbeFourierTensor K hζ S v)
local notation "G₀" => (sourceSLocalProbeRetained K hζ S v)

theorem sourceSLocalOtherUnitMeasure_isHaar : Measure.IsHaarMeasure μo :=
  sourceSheetOtherMeasure_isHaar S v (sourceSLocalArchUnitMeasure K hζ) (sourceSLocalFiniteUnitMeasure K S)

theorem sourceSLocalOtherUnitMeasure_sigmaFinite : SigmaFinite μo := by
  unfold sourceSLocalOtherUnitMeasure sourceSheetOtherMeasure
  infer_instance

theorem sourceSLocalNormalizedSheetMeasure_isHaar : Measure.IsHaarMeasure ν := by
  have : BorelSpace (SNormOneOtherUnits S v) := sourceSheetOtherUnits_product_borel S v
  have : Measure.IsHaarMeasure μo := sourceSLocalOtherUnitMeasure_isHaar K hζ S v
  have : sourceCircleHaar.IsHaarMeasure := sourceCircleHaar_isHaar
  exact sourceSNormOneSheetMeasure_prod_isHaar S hv sourceCircleHaar μo

theorem sourceSLocalNormalizedSheetMeasure_sigmaFinite : SigmaFinite ν := by
  have : BorelSpace (SNormOneOtherUnits S v) := sourceSheetOtherUnits_product_borel S v
  have : SigmaFinite μo := sourceSLocalOtherUnitMeasure_sigmaFinite K hζ S v
  let e := (sourceSNormOneSheetContinuousMulEquiv hv S).symm.toHomeomorph.toMeasurableEquiv
  exact e.sigmaFinite_map

theorem sourceSLocalProbeFourierTensor_measurable : Measurable F₀ := by
  have : BorelSpace (SWholeUnits K S) := sourceSWholeUnits_product_borel S v
  have : BorelSpace (SNormOneOtherUnits S v) := sourceSheetOtherUnits_product_borel S v
  have hArch : Measurable (fun x : SWholeUnits K S => sourceProbeArchFactor K hζ v (x.1 v)) :=
    (sourceProbeArchFactor_measurable K hζ v).comp ((measurable_pi_apply v).comp measurable_fst)
  have hOther : Measurable (sourceSheetOther S v) := (continuous_sourceSheetOther S v).measurable
  exact hArch.mul ((sourceSLocalProbeRetained_measurable K hζ S v).comp hOther)

theorem sourceSLocalProbeSheet_logSmooth :
    ContDiff ℝ ∞ (fun t : ℝ => sourceSLocalProbeSheet K hζ S v (Real.exp t)) := by
  have : BorelSpace (SNormOneOtherUnits S v) := sourceSheetOtherUnits_product_borel S v
  have : Measure.IsHaarMeasure μo := sourceSLocalOtherUnitMeasure_isHaar K hζ S v
  have : SigmaFinite μo := sourceSLocalOtherUnitMeasure_sigmaFinite K hζ S v
  exact sourceSLocalTensorSheet_logSmooth S hv μo hζ sourceProbeArchFourier G₀
    (sourceSLocalProbeRetained_measurable K hζ S v) 1 (by norm_num)
    (sourceSLocalProbeRetained_weighted_norm_integrable K hζ S v 1 (by norm_num))

theorem sourceSLocalProbeSheet_norm_le (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T → ‖sourceSLocalProbeSheet K hζ S v T‖ ≤ C * T ^ (-σ) := by
  have : BorelSpace (SNormOneOtherUnits S v) := sourceSheetOtherUnits_product_borel S v
  have : Measure.IsHaarMeasure μo := sourceSLocalOtherUnitMeasure_isHaar K hζ S v
  have : SigmaFinite μo := sourceSLocalOtherUnitMeasure_sigmaFinite K hζ S v
  exact sourceSLocalTensorSheet_norm_le S hv μo hζ sourceProbeArchFourier G₀
    (sourceSLocalProbeRetained_measurable K hζ S v) σ hσ
    (sourceSLocalProbeRetained_weighted_norm_integrable K hζ S v σ hσ)

theorem sourceSLocalProbeRadialMellin_eq (s : ℂ) :
    let : BorelSpace (SWholeUnits K S) := sourceSWholeUnits_product_borel S v
    sourceSLocalRadialMellin S hv ν F₀ s = sourceSLocalProbeMellin K hζ S v s := by
  unfold sourceSLocalRadialMellin sourceSLocalProbeMellin
  rw [← sourceSLocalUnitProductMeasure_eq_radial K hζ S v]
  rfl

theorem sourceSLocalProbeSheet_hasMellin (s : ℂ) (hs : 0 < s.re) :
    HasMellin (sourceSLocalProbeSheet K hζ S v) s (sourceSLocalProbeMellin K hζ S v s) := by
  have : BorelSpace (SWholeUnits K S) := sourceSWholeUnits_product_borel S v
  have : Measure.IsHaarMeasure ν := sourceSLocalNormalizedSheetMeasure_isHaar K hζ S v
  have : SigmaFinite ν := sourceSLocalNormalizedSheetMeasure_sigmaFinite K hζ S v
  have hI : Integrable (fun x => F₀ x * (sLocalNorm K S x : ℂ) ^ s)
      (sourceSLocalRadialHaar S hv ν) := by
    rw [← sourceSLocalUnitProductMeasure_eq_radial K hζ S v]
    exact sourceSLocalProbeMellin_integrable K hζ S v s hs
  rw [← sourceSLocalProbeRadialMellin_eq K hζ S v]
  exact sourceSLocalSheetProfile_hasMellin S hv ν hζ F₀ s hI

end
end ArtinMatthews.SourcePhysical

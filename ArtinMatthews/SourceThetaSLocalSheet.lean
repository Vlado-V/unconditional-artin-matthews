module

public import ArtinMatthews.SourceThetaLogSheet
public import ArtinMatthews.SourceSLocalProbeSheetIdentity


set_option backward.privateInPublic true
@[expose] public section

/-! Literal Haar sheets of the rotated tensors in source03. The
dependent complex log radius is the total log norm minus the
retained log norm. This holds for both the signed and absolute integrals. -/
namespace ArtinMatthews.SourceReflection

open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open ArtinMatthews.SourcePhysical
open scoped NumberField Classical ArtinMatthews.SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (v : InfinitePlace K)

local notation "hv" => sourceSLocalComplexPlace K hζ v
local notation "ν" => sourceSLocalNormalizedSheetMeasure K hζ S v
local notation "μOther" => sourceSLocalOtherUnitMeasure K hζ S v
local notation "N" => sourceSheetOtherNorm S v
local notation "Other" => SNormOneOtherUnits S v

def sourceThetaSLocalTensor (g : Circle → ℝ → ℂ) (G : Other → ℂ) (x : SWholeUnits K S) : ℂ :=
  let z := sourceComplexPlaceUnitsEquiv hv (x.1 v)
  g (sourceComplexUnitAngle z) (sourceComplexUnitLogNorm z) * G (sourceSheetOther S v x)

def sourceThetaSLocalSheet (g : Circle → ℝ → ℂ) (G : Other → ℂ) : ℝ → ℂ :=
  sourceSLocalSheetProfile S ν hζ (sourceThetaSLocalTensor K S hζ v g G)

def sourceThetaSLocalSheetAbs (g : Circle → ℝ → ℂ) (G : Other → ℂ) (T : ℝ) : ℝ :=
  ∫ x : SNormOne K S, ‖sourceThetaSLocalTensor K S hζ v g G
    ((x : SWholeUnits K S) * sLocalPositiveScaling K hζ S T)‖ ∂ν

private theorem sourceThetaSLocalTensor_radial (g : Circle → ℝ → ℂ) (G : Other → ℂ)
    (t : ℝ) (a : Circle × Other) :
    sourceThetaSLocalTensor K S hζ v g G (sourceSLocalRadialSheet S hv a t) =
      sourceThetaLogSheetIntegrand N G g t a := by
  let z := sourceComplexPlaceUnitsEquiv hv ((sourceSLocalRadialSheet S hv a t).1 v)
  have hz : z = sourceComplexRadialUnit (t - Real.log (N a.2)) * Circle.toUnits a.1 := by
    apply Units.ext
    change (sourceComplexPlaceUnitsEquiv hv ((sourceSLocalRadialSheet S hv a t).1 v) : ℂ) = _
    rw [sourceSLocalRadialSheet_chosen, sourceSheetComplexCoordinate]
    rfl
  change g (sourceComplexUnitAngle z) (sourceComplexUnitLogNorm z) *
    G (sourceSheetOther S v (sourceSLocalRadialSheet S hv a t)) = _
  rw [hz, sourceComplexRadialUnit_mul_angle_angle, sourceComplexRadialUnit_mul_angle_logNorm,
    sourceSLocalRadialSheet_other, sourceThetaLogSheetIntegrand]

private theorem sourceThetaSLocalTensor_integral_exp (g : Circle → ℝ → ℂ) (G : Other → ℂ)
    (φ : ℂ → ℂ) (t : ℝ) :
    (∫ x : SNormOne K S, φ (sourceThetaSLocalTensor K S hζ v g G
        ((x : SWholeUnits K S) * sLocalPositiveScaling K hζ S (Real.exp t))) ∂ν) =
      ∫ a, φ (sourceThetaLogSheetIntegrand N G g t a) ∂sourceCircleHaar.prod μOther := by
  have : BorelSpace Other := sourceSheetOtherUnits_product_borel S v
  have : Measure.IsHaarMeasure ν := sourceSLocalNormalizedSheetMeasure_isHaar K hζ S v
  change (∫ x : SNormOne K S, (φ ∘ sourceThetaSLocalTensor K S hζ v g G)
    ((x : SWholeUnits K S) * sLocalPositiveScaling K hζ S (Real.exp t)) ∂ν) = _
  rw [← sourceSLocal_radial_integral_eq_literal S ν hζ hv
      (φ ∘ sourceThetaSLocalTensor K S hζ v g G) t,
    sourceSLocalNormalizedSheetMeasure, sourceSNormOneSheetMeasure_integral]
  apply integral_congr_ae
  filter_upwards with a
  change φ (sourceThetaSLocalTensor K S hζ v g G (sourceSLocalRadialSheet S hv a t)) = _
  rw [sourceThetaSLocalTensor_radial K S hζ v]

theorem sourceThetaSLocalSheet_exp (g : Circle → ℝ → ℂ) (G : Other → ℂ) (t : ℝ) :
    sourceThetaSLocalSheet K S hζ v g G (Real.exp t) = sourceThetaLogSheet μOther N G g t :=
  sourceThetaSLocalTensor_integral_exp K S hζ v g G id t

theorem sourceThetaSLocalSheetAbs_exp (g : Circle → ℝ → ℂ) (G : Other → ℂ) (t : ℝ) :
    sourceThetaSLocalSheetAbs K S hζ v g G (Real.exp t) = sourceThetaLogSheetAbs μOther N G g t := by
  have h := sourceThetaSLocalTensor_integral_exp K S hζ v g G (fun z => (‖z‖ : ℂ)) t
  apply Complex.ofReal_injective
  unfold sourceThetaSLocalSheetAbs sourceThetaLogSheetAbs
  rw [← integral_complex_ofReal, ← integral_complex_ofReal]
  exact h

end
end ArtinMatthews.SourceReflection

module

public import ArtinMatthews.SLocalNormOneUnfold
public import ArtinMatthews.SourceSLocalProbeAbsoluteSheet


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (v : InfinitePlace K)

local notation "ν" => sourceSLocalNormalizedSheetMeasure K hζ S v
local notation "F₀" => sourceSLocalProbeFourierTensor K hζ S v
local notation "Γ" => sNormOneSixthSubgroup K S
local notation "Q" => SNormOneSixthQuotient K S

/-- The quotient measure induced by the exact normalized sheet Haar. -/
def sourceSLocalProbeQuotientMeasure : Measure Q := sNormOneQuotientMeasure K S ν

theorem sourceSLocalProbeQuotientMeasure_finite :
    IsFiniteMeasure (sourceSLocalProbeQuotientMeasure K hζ S v) := by
  let : Measure.IsHaarMeasure ν := sourceSLocalNormalizedSheetMeasure_isHaar K hζ S v
  exact sNormOneQuotientMeasure_finite K S ν

theorem sourceSLocalProbeQuotientMeasure_isHaar :
    (sourceSLocalProbeQuotientMeasure K hζ S v).IsHaarMeasure := by
  let : Measure.IsHaarMeasure ν := sourceSLocalNormalizedSheetMeasure_isHaar K hζ S v
  exact sNormOneQuotientMeasure_isHaar K S ν

def sourceSLocalProbeScaled (u : SWholeUnits K S) (x : SNormOne K S) : ℂ :=
  F₀ ((x : SWholeUnits K S) * u)

/-- One term of the actual periodization by distinct unit sixth powers. -/
def sourceSLocalProbeOrbitTranslate (u : SWholeUnits K S)
    (a : Γ) (x : SNormOne K S) : ℂ :=
  sourceSLocalProbeScaled K hζ S v u (x * a.val)

def sourceSLocalProbeOrbit (u : SWholeUnits K S) : Q → ℂ :=
  sNormOnePeriodize K S (sourceSLocalProbeScaled K hζ S v u)

theorem sourceSLocalProbeOrbitTranslate_measurable (u : SWholeUnits K S) (a : Γ) :
    Measurable (sourceSLocalProbeOrbitTranslate K hζ S v u a) :=
  (sourceSLocalProbeSheetScaled_measurable K hζ S v u).comp
    (continuous_id.mul continuous_const).measurable

theorem sourceSLocalProbeOrbit_measurable (u : SWholeUnits K S) :
    Measurable (sourceSLocalProbeOrbit K hζ S v u) := by
  let : Countable Γ := sNormOneSixthSubgroup_countable K S
  exact quotientPeriodize_measurable Γ _ (sourceSLocalProbeSheetScaled_measurable K hζ S v u)

/-- The literal orbit uses each group element of the sixth-power image once. -/
theorem sourceSLocalProbeOrbit_mk (u : SWholeUnits K S) (x : SNormOne K S) :
    sourceSLocalProbeOrbit K hζ S v u (sNormOneSixthQuotientMap K S x) =
      ∑' a : Γ, sourceSLocalProbeOrbitTranslate K hζ S v u a x := by
  rw [sourceSLocalProbeOrbit, sNormOnePeriodize_mk]
  exact ((Subgroup.equivOp Γ).tsum_eq
    (fun a : (Γ).op => sourceSLocalProbeScaled K hζ S v u (a • x))).symm

theorem sourceSLocalProbeOrbitTranslate_value (u : SWholeUnits K S) (a : Γ) (x : SNormOne K S) :
    sourceSLocalProbeOrbitTranslate K hζ S v u a x =
      F₀ ((x : SWholeUnits K S) * ((a.val : SNormOne K S) : SWholeUnits K S) * u) := rfl

/-- Haar translation absorbs the norm-one part of the physical frequency. -/
theorem sourceSLocalProbeScaled_integral_eq_sheet (u : SWholeUnits K S) :
    (∫ x, sourceSLocalProbeScaled K hζ S v u x ∂ν) =
      sourceSLocalProbeSheet K hζ S v (sLocalNorm K S u) := by
  let : Measure.IsHaarMeasure ν := sourceSLocalNormalizedSheetMeasure_isHaar K hζ S v
  apply sourceSLocal_sameNorm_integral S ν F₀
  rw [sLocalPositiveScaling_norm K hζ S (sLocalNorm_pos K S u)]

/-- One actual sixth-power orbit integrates to the sheet at its exact norm. -/
theorem sourceSLocalProbeOrbit_unfold (u : SWholeUnits K S) :
    Integrable (sourceSLocalProbeOrbit K hζ S v u) (sourceSLocalProbeQuotientMeasure K hζ S v) ∧
    (∫ q, sourceSLocalProbeOrbit K hζ S v u q ∂sourceSLocalProbeQuotientMeasure K hζ S v) =
      sourceSLocalProbeSheet K hζ S v (sLocalNorm K S u) := by
  let : Measure.IsHaarMeasure ν := sourceSLocalNormalizedSheetMeasure_isHaar K hζ S v
  have h := sNormOnePeriodize_unfold K S ν (sourceSLocalProbeScaled K hζ S v u)
    (sourceSLocalProbeSheetScaled_measurable K hζ S v u)
    (sourceSLocalProbeSheetScaled_integrable K hζ S v u)
  exact ⟨h.1, h.2.trans (sourceSLocalProbeScaled_integral_eq_sheet K hζ S v u)⟩

end
end ArtinMatthews.SourcePhysical

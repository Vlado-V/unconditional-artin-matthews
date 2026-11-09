module

public import ArtinMatthews.SourceThetaRotatedSheetBounds


set_option backward.privateInPublic true
@[expose] public section

/-! The absolute mass bound for each rotated tensor on the original
normalized norm-one Haar sheet at an arbitrary scaling element. -/
namespace ArtinMatthews.SourceReflection.SourceThetaRotatedTensor

open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open ArtinMatthews.SourcePhysical
open scoped NumberField ENNReal
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {ζ : K} {hζ : IsPrimitiveRoot ζ 12} {v : InfinitePlace K} {δ : ℝ}
variable (d : SourceThetaRotatedTensor K S hζ v δ)

local notation "hv" => sourceSLocalComplexPlace K hζ v
local notation "ν" => sourceSLocalNormalizedSheetMeasure K hζ S v
local notation "Other" => SNormOneOtherUnits S v
local notation "μo" => sourceSLocalOtherUnitMeasure K hζ S v
local notation "N" => sourceSheetOtherNorm S v
private def tensor (j : ℕ) : SWholeUnits K S → ℂ :=
  sourceThetaSLocalTensor K S hζ v (d.localDeriv j) d.retained

local notation "F" => tensor d

theorem tensor_measurable (j : ℕ) : Measurable (F j) := by
  have : BorelSpace (SWholeUnits K S) := sourceSWholeUnits_product_borel S v
  have : BorelSpace Other := sourceSheetOtherUnits_product_borel S v
  have hz : Measurable (fun x : SWholeUnits K S => sourceComplexPlaceUnitsEquiv hv (x.1 v)) :=
    (sourceComplexPlaceUnitsEquiv hv).continuous.measurable.comp
      ((measurable_pi_apply v).comp measurable_fst)
  exact ((d.local_measurable j).comp
    ((sourceComplexUnitAngle_continuous.measurable.comp hz).prodMk
      (sourceComplexUnitLogNorm_continuous.measurable.comp hz))).mul
    (d.retained_measurable.comp (continuous_sourceSheetOther S v).measurable)

theorem scaled_tensor_measurable (j : ℕ) (u : SWholeUnits K S) :
    Measurable (fun x : SNormOne K S => F j ((x : SWholeUnits K S) * u)) := by
  have : BorelSpace (SWholeUnits K S) := sourceSWholeUnits_product_borel S v
  exact (d.tensor_measurable j).comp (continuous_subtype_val.mul continuous_const).measurable

theorem scaled_tensor_lintegral_enorm_eq (j : ℕ) (u : SWholeUnits K S) :
    (∫⁻ x : SNormOne K S, ‖F j ((x : SWholeUnits K S) * u)‖ₑ ∂ν) =
      ∫⁻ p : Circle × Other,
        ‖sourceThetaLogSheetIntegrand N d.retained (d.localDeriv j)
          (Real.log (sLocalNorm K S u)) p‖ₑ ∂sourceCircleHaar.prod μo := by
  have : BorelSpace Other := sourceSheetOtherUnits_product_borel S v
  have : Measure.IsHaarMeasure ν := sourceSLocalNormalizedSheetMeasure_isHaar K hζ S v
  let t := Real.log (sLocalNorm K S u)
  have hN : sLocalNorm K S u = sLocalNorm K S (sourceSLocalRadial hv S t) := by
    rw [sourceSLocalRadial_norm, Real.exp_log (sLocalNorm_pos K S u)]
  calc
    _ = ∫⁻ x : SNormOne K S, ‖F j ((x : SWholeUnits K S) * sourceSLocalRadial hv S t)‖ₑ ∂ν :=
      sourceSLocal_sameNorm_lintegral S ν (fun y => ‖F j y‖ₑ) u _ hN
    _ = _ := by
      unfold sourceSLocalNormalizedSheetMeasure
      rw [sourceSNormOneSheetMeasure_lintegral]
      apply lintegral_congr
      intro p
      congr 1
      change F j (sourceSLocalRadialSheet S hv p t) =
        sourceThetaLogSheetIntegrand N d.retained (d.localDeriv j) t p
      let z := sourceComplexPlaceUnitsEquiv hv ((sourceSLocalRadialSheet S hv p t).1 v)
      have hz : z = sourceComplexRadialUnit (t - Real.log (N p.2)) * Circle.toUnits p.1 := by
        apply Units.ext
        change (sourceComplexPlaceUnitsEquiv hv ((sourceSLocalRadialSheet S hv p t).1 v) : ℂ) = _
        rw [sourceSLocalRadialSheet_chosen, sourceSheetComplexCoordinate]
        rfl
      change d.localDeriv j (sourceComplexUnitAngle z) (sourceComplexUnitLogNorm z) *
        d.retained (sourceSheetOther S v (sourceSLocalRadialSheet S hv p t)) = _
      rw [hz, sourceComplexRadialUnit_mul_angle_angle, sourceComplexRadialUnit_mul_angle_logNorm,
        sourceSLocalRadialSheet_other, sourceThetaLogSheetIntegrand]

theorem scaled_tensor_mass (j : ℕ) (σ : ℝ) (hσ : -δ < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SWholeUnits K S,
      (∫⁻ x : SNormOne K S, ‖F j ((x : SWholeUnits K S) * u)‖ₑ ∂ν) ≤
        ENNReal.ofReal (C * sLocalNorm K S u ^ (-σ)) := by
  have : BorelSpace Other := sourceSheetOtherUnits_product_borel S v
  have : SigmaFinite μo := sourceSLocalOtherUnitMeasure_sigmaFinite K hζ S v
  obtain ⟨C,hC,hg⟩ := d.local_weighted j σ hσ
  obtain ⟨hI,D,hD,hbound⟩ := sourceThetaLogSheet_weighted μo N d.retained
    (measurable_sourceSheetOtherNorm S v) d.retained_measurable (d.local_measurable j)
    (sourceSheetOtherNorm_pos S v) σ C hC hg (d.retained_weighted σ hσ)
  refine ⟨D,hD,fun u => ?_⟩
  rw [d.scaled_tensor_lintegral_enorm_eq, ← ofReal_integral_norm_eq_lintegral_enorm (hI _)]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.rpow_def_of_pos (sLocalNorm_pos K S u), mul_comm (Real.log (sLocalNorm K S u))]
  exact hbound (Real.log (sLocalNorm K S u))

end
end ArtinMatthews.SourceReflection.SourceThetaRotatedTensor

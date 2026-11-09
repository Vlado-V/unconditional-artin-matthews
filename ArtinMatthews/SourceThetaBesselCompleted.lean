module

public import ArtinMatthews.SourceThetaBesselAngular
public import ArtinMatthews.SourceThetaRotatedLocalData


set_option backward.privateInPublic true
@[expose] public section

/-! Literal completion-unit factors for source03, with the complex
embedding, squared norm, and angular character all preserved. -/
namespace ArtinMatthews.SourceReflection

open NumberField NumberField.InfinitePlace
open ArtinMatthews.SourcePhysical
open scoped NumberField Classical ArtinMatthews.SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (v : InfinitePlace K)
local notation "hv" => sourceSLocalComplexPlace K hζ v

def sourceThetaBesselCompletedFactor (c : ℝ) (m : ℤ) (z : v.Completionˣ) : ℂ :=
  sourceThetaBesselComplexFactor c m (sourceComplexPlaceUnitsEquiv hv z)

theorem sourceThetaBesselCompletedFactor_eq (c : ℝ) (m : ℤ) (z : v.Completionˣ) :
    sourceThetaBesselCompletedFactor K hζ v c m z =
      (sourceComplexUnitAngle (sourceComplexPlaceUnitsEquiv hv z) : ℂ) ^ m *
        sourceThetaBesselProfile c (sourceSheetArchNorm v z) := by
  unfold sourceThetaBesselCompletedFactor sourceThetaBesselComplexFactor
  rw [sourceSheetArchNorm_eq_complex hv, sourceComplexPlaceUnitsEquiv_val]

theorem sourceThetaBesselCompletedFactor_measurable {c : ℝ} (hc : 0 < c) (m : ℤ) :
    Measurable (sourceThetaBesselCompletedFactor K hζ v c m) := by
  change Measurable (fun z : v.Completionˣ =>
    sourceThetaBesselComplexFactor c m (sourceComplexPlaceUnitsEquiv hv z))
  have he : Continuous (sourceComplexPlaceUnitsEquiv hv) := (sourceComplexPlaceUnitsEquiv hv).continuous
  have hpair : Measurable (fun z : v.Completionˣ =>
      (sourceComplexUnitAngle (sourceComplexPlaceUnitsEquiv hv z),
        sourceComplexUnitLogNorm (sourceComplexPlaceUnitsEquiv hv z))) :=
    ((sourceComplexUnitAngle_continuous.comp he).prodMk
      (sourceComplexUnitLogNorm_continuous.comp he)).measurable
  have h := (sourceThetaBesselAngularLogDerivative_measurable hc m 0).comp hpair
  simpa only [Function.comp_def, Function.uncurry_apply_pair, ← sourceThetaBesselComplexFactor_eq_log hc] using h

theorem sourceThetaBesselCompletedFactor_twoEnded {c : ℝ} (hc : 0 < c) (m : ℤ)
    {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : v.Completionˣ,
      ‖sourceThetaBesselCompletedFactor K hζ v c m z‖ ≤
        C * min ((sourceSheetArchNorm v z) ^ (5 / 6 : ℝ)) ((sourceSheetArchNorm v z) ^ (-A)) := by
  obtain ⟨C, hC, hb⟩ := sourceThetaBesselLogDerivative_twoEnded hc 0 hA
  refine ⟨C, hC, fun z => ?_⟩
  have hz := sourceSheetArchNorm_pos v z
  have h := hb (Real.log (sourceSheetArchNorm v z))
  rw [sourceThetaBesselLogDerivative_zero hc, Real.exp_log hz] at h
  rw [sourceThetaBesselCompletedFactor_eq, norm_mul, norm_zpow, Circle.norm_coe, one_zpow, one_mul]
  simpa only [Real.rpow_def_of_pos hz, mul_comm (Real.log (sourceSheetArchNorm v z))] using h

theorem sourceThetaBesselCompletedFactor_twoEnded_of_le {c : ℝ} (hc : 0 < c) (m : ℤ)
    {δ A : ℝ} (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 5 / 6) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : v.Completionˣ,
      ‖sourceThetaBesselCompletedFactor K hζ v c m z‖ ≤
        C * min ((sourceSheetArchNorm v z) ^ δ) ((sourceSheetArchNorm v z) ^ (-A)) := by
  obtain ⟨C, hC, hb⟩ := sourceThetaBesselAngularLogDerivative_twoEnded_of_le hc m 0 hδ hδ₁ hA
  refine ⟨C, hC, fun z => ?_⟩
  let w := sourceComplexPlaceUnitsEquiv hv z
  have hx : sourceComplexUnitLogNorm w = Real.log (sourceSheetArchNorm v z) := by
    rw [sourceComplexUnitLogNorm, sourceSheetArchNorm_eq_complex hv,
      sourceComplexPlaceUnitsEquiv_val, Real.log_pow]
    norm_num
  have h := hb (sourceComplexUnitAngle w) (sourceComplexUnitLogNorm w)
  rw [← sourceThetaBesselComplexFactor_eq_log hc] at h
  rw [hx] at h
  simpa only [sourceThetaBesselCompletedFactor, Real.rpow_def_of_pos (sourceSheetArchNorm_pos v z),
    mul_comm (Real.log (sourceSheetArchNorm v z))] using h

end
end ArtinMatthews.SourceReflection

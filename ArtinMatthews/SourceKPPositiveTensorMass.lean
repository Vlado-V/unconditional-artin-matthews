module

public import ArtinMatthews.SourceThetaRotatedSheetMass
public import ArtinMatthews.SourceThetaBesselTensorLiteral
public import ArtinMatthews.SourceThetaPositiveSheet


set_option backward.privateInPublic true
@[expose] public section

/-! The actual positive seed tensor has absolute mass bounds on every
scaled norm-one sheet with its original normalized Haar measure. -/
namespace ArtinMatthews.SourceReflection
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory Set SourcePhysical
open scoped NumberField Classical ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (c : InfinitePlace K → ℝ) (hc : ∀ w, 0 < c w)
variable (U : ∀ p : S, SourceThetaFiniteCutoff K p.val)
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (v : InfinitePlace K)

private theorem cutoff_continuous (p : S) : Continuous (U p).factor :=
  (show IsClopen (U p).region from ⟨(U p).isCompact.isClosed, (U p).isOpen⟩).continuous_indicator
    continuous_const

private theorem cutoff_support (p : S) (z : (p.val.adicCompletion K)ˣ)
    (hz : z ∉ sourceLocalMulBall K p.val 0) : (U p).factor z = 0 := by
  apply indicator_of_notMem
  intro h
  apply hz
  have hv : sourceLocalValuation K p.val (z : p.val.adicCompletion K) = 1 :=
    Valued.toNormedField.norm_eq_one_iff.mp ((U p).norm_eq_one z h)
  change sourceLocalValuation K p.val (z : p.val.adicCompletion K) ≤ WithZero.exp 0
  rw [hv, WithZero.exp_zero]

private theorem cutoff_small (p : S) (z : (p.val.adicCompletion K)ˣ) :
    ‖(U p).factor z‖ ≤ 1 * (sourceSheetFiniteNorm S p z) ^ (5 / 6 : ℝ) := by
  by_cases h : z ∈ (U p).region
  · rw [SourceThetaFiniteCutoff.factor, indicator_of_mem h, norm_one, sourceSheetFiniteNorm,
      (U p).norm_eq_one z h, Real.one_rpow, mul_one]
  · rw [SourceThetaFiniteCutoff.factor, indicator_of_notMem h, norm_zero]
    exact mul_nonneg zero_le_one (Real.rpow_nonneg (sourceSheetFiniteNorm_pos S p z).le _)

def sourceKPPositiveRotatedTensor : SourceThetaRotatedTensor K S hζ v (5 / 6) :=
  sourceThetaBesselTensor K S hζ v c hc (fun _ => 0) (5 / 6) (by norm_num) le_rfl
    (fun p => (U p).factor) (cutoff_continuous K S U) (fun _ => 0) (fun _ => 1)
    (fun _ => zero_le_one) (cutoff_support K S U) (fun p z _ => cutoff_small K S U p z)

theorem sourceKPPositiveRotatedTensor_literal (x : SWholeUnits K S) :
    let d := sourceKPPositiveRotatedTensor K S c hc U hζ v
    sourceThetaSLocalTensor K S hζ v (d.localDeriv 0) d.retained x =
      sourceThetaPositiveTensor K S c U x := by
  dsimp only [sourceKPPositiveRotatedTensor]
  rw [sourceThetaBesselTensor_literal,sourceThetaPositiveTensor]
  simp only [sourceThetaBesselCompletedFactor_eq,zpow_zero,one_mul,sourceThetaArchFactor]

include hc hζ v in
theorem sourceThetaPositiveTensor_scaled_measurable (u : SWholeUnits K S) :
    Measurable (fun x : SNormOne K S => sourceThetaPositiveTensor K S c U ((x : SWholeUnits K S)*u)) := by
  let d := sourceKPPositiveRotatedTensor K S c hc U hζ v
  have h := d.scaled_tensor_measurable 0 u
  change Measurable (fun x : SNormOne K S =>
    sourceThetaSLocalTensor K S hζ v (d.localDeriv 0) d.retained ((x : SWholeUnits K S)*u)) at h
  simpa only [d,sourceKPPositiveRotatedTensor_literal K S c hc U hζ v] using h

include hc in
theorem sourceThetaPositiveTensor_scaled_mass (σ : ℝ) (hσ : -(5 / 6 : ℝ) < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SWholeUnits K S,
      (∫⁻ x : SNormOne K S, ‖sourceThetaPositiveTensor K S c U ((x : SWholeUnits K S)*u)‖ₑ
        ∂sourceSLocalNormalizedSheetMeasure K hζ S v) ≤
        ENNReal.ofReal (C * sLocalNorm K S u ^ (-σ)) := by
  let d := sourceKPPositiveRotatedTensor K S c hc U hζ v
  obtain ⟨C,hC,h⟩ := d.scaled_tensor_mass 0 σ hσ
  refine ⟨C,hC,fun u => ?_⟩
  have H := h u
  change (∫⁻ x : SNormOne K S,
    ‖sourceThetaSLocalTensor K S hζ v (d.localDeriv 0) d.retained ((x : SWholeUnits K S)*u)‖ₑ
      ∂sourceSLocalNormalizedSheetMeasure K hζ S v) ≤ ENNReal.ofReal _ at H
  simpa only [d,sourceKPPositiveRotatedTensor_literal K S c hc U hζ v] using H

end
end ArtinMatthews.SourceReflection

module

public import ArtinMatthews.SourceThetaPositiveSheet
public import ArtinMatthews.SourceThetaBesselTensorLiteral


set_option backward.privateInPublic true
@[expose] public section

/-! The actual positive theta sheet is the angle-zero instance of the
Bessel tensor on its original normalized Haar sheet. Its local cutoff
factors are literal compact-open indicators at norm one. -/

namespace ArtinMatthews.SourceReflection

open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory Set SourcePhysical
open scoped NumberField Classical ContDiff ArtinMatthews.SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (c : InfinitePlace K → ℝ) (hc : ∀ w, 0 < c w)
variable (U : ∀ p : S, SourceThetaFiniteCutoff K p.val)
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (v : InfinitePlace K)

private theorem finiteCutoff_continuous (p : S) : Continuous (U p).factor :=
  (show IsClopen (U p).region from ⟨(U p).isCompact.isClosed, (U p).isOpen⟩).continuous_indicator
    continuous_const

private theorem finiteCutoff_ball_support (p : S) (z : (p.val.adicCompletion K)ˣ)
    (hz : z ∉ sourceLocalMulBall K p.val 0) : (U p).factor z = 0 := by
  apply indicator_of_notMem
  intro h
  apply hz
  have hval : sourceLocalValuation K p.val (z : p.val.adicCompletion K) = 1 :=
    Valued.toNormedField.norm_eq_one_iff.mp ((U p).norm_eq_one z h)
  change sourceLocalValuation K p.val (z : p.val.adicCompletion K) ≤ WithZero.exp 0
  rw [hval, WithZero.exp_zero]

private theorem finiteCutoff_small (p : S) (z : (p.val.adicCompletion K)ˣ) :
    ‖(U p).factor z‖ ≤ 1 * (sourceSheetFiniteNorm S p z) ^ (5 / 6 : ℝ) := by
  by_cases h : z ∈ (U p).region
  · rw [SourceThetaFiniteCutoff.factor, indicator_of_mem h, norm_one, sourceSheetFiniteNorm,
      (U p).norm_eq_one z h, Real.one_rpow, mul_one]
  · rw [SourceThetaFiniteCutoff.factor, indicator_of_notMem h, norm_zero]
    exact mul_nonneg zero_le_one (Real.rpow_nonneg (sourceSheetFiniteNorm_pos S p z).le _)

private def positiveRotatedTensor : SourceThetaRotatedTensor K S hζ v (5 / 6) :=
  sourceThetaBesselTensor K S hζ v c hc (fun _ => 0) (5 / 6) (by norm_num) le_rfl
    (fun p => (U p).factor) (finiteCutoff_continuous K S U) (fun _ => 0) (fun _ => 1)
    (fun _ => zero_le_one) (finiteCutoff_ball_support K S U)
    (fun p z _ => finiteCutoff_small K S U p z)

private theorem positiveRotatedTensor_sheet :
    (positiveRotatedTensor K S c hc U hζ v).sheet 0 = sourceThetaPositiveSheet K S c U hζ v := by
  unfold SourceThetaRotatedTensor.sheet sourceThetaSLocalSheet sourceThetaPositiveSheet
  apply congrArg (sourceSLocalSheetProfile S (sourceSLocalNormalizedSheetMeasure K hζ S v) hζ)
  funext x
  unfold positiveRotatedTensor
  rw [sourceThetaBesselTensor_literal, sourceThetaPositiveTensor]
  simp only [sourceThetaBesselCompletedFactor_eq, zpow_zero, one_mul, sourceThetaArchFactor]

include hc in
theorem sourceThetaPositiveSheet_log_measurable :
    Measurable (fun t : ℝ => sourceThetaPositiveSheet K S c U hζ v (Real.exp t)) := by
  let D := positiveRotatedTensor K S c hc U hζ v
  have he : D.logSheet 0 = fun t => sourceThetaPositiveSheet K S c U hζ v (Real.exp t) :=
    funext fun t => congrFun (positiveRotatedTensor_sheet K S c hc U hζ v) (Real.exp t)
  rw [← he]
  exact (D.logSheet_contDiff (by norm_num)).continuous.measurable

include hc in
theorem sourceThetaPositiveSheet_log_norm_bound (σ : ℝ) (hσ : -(5 / 6 : ℝ) < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖sourceThetaPositiveSheet K S c U hζ v (Real.exp t)‖ ≤ C * Real.exp (-σ * t) := by
  let D := positiveRotatedTensor K S c hc U hζ v
  obtain ⟨C, hC, hb⟩ := D.logSheetAbs_weighted 0 σ hσ
  refine ⟨C, hC, fun t => ?_⟩
  have h := (D.logSheet_norm_le_abs 0 t).trans (hb t)
  simpa only [D, SourceThetaRotatedTensor.logSheet, positiveRotatedTensor_sheet] using h

include hc in
theorem sourceThetaPositiveSheet_norm_bound (σ : ℝ) (hσ : -(5 / 6 : ℝ) < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T →
      ‖sourceThetaPositiveSheet K S c U hζ v T‖ ≤ C * T ^ (-σ) := by
  obtain ⟨C, hC, hb⟩ := sourceThetaPositiveSheet_log_norm_bound K S c hc U hζ v σ hσ
  refine ⟨C, hC, fun T hT => ?_⟩
  simpa only [Real.exp_log hT, Real.rpow_def_of_pos hT, mul_comm (-σ) (Real.log T)]
    using hb (Real.log T)

end
end ArtinMatthews.SourceReflection

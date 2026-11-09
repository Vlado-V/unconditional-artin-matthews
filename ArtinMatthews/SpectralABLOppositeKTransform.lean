module

public import ArtinMatthews.SpectralKLCompactPointwiseInverse
public import ArtinMatthews.SpectralWeylMultipliers
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Complex OAI.CubicEisenstein
open scoped ContDiff
noncomputable section

theorem spectralWeylK_synthesis_dilation (H : ℝ → ℂ) {X : ℝ} (hX : 0 < X)
    (hI : IntegrableOn (fun u : ℝ => schlafliBesselK ((u : ℂ)*I) X *
      H (u/2)*(spectralKLPlancherelWeight u : ℂ)) (Ioi (0 : ℝ))) :
    Integrable (fun t : ℝ => spectralWeylKMultiplier t X*H t) spectralKLSpectralMeasure ∧
      ((X : ℂ)/2)*(∫ t : ℝ, spectralWeylKMultiplier t X*H t ∂spectralKLSpectralMeasure) =
        (1/2 : ℂ)*spectralKLWeightedSynthesis (fun u : ℝ => H (u/2)) X := by
  let F : ℝ → ℂ := fun u => schlafliBesselK ((u : ℂ)*I) X*
    H (u/2)*(spectralKLPlancherelWeight u : ℂ)
  have hp : ∀ t : ℝ, 0 < t → 0 ≤ spectralKLPlancherelWeight t :=
    fun _ ht => (spectralKLPlancherelWeight_pos ht).le
  have he (t : ℝ) :
      (spectralKLPlancherelWeight t : ℂ)*(spectralWeylKMultiplier t X*H t) =
        (2/(X : ℂ))*F (2*t) := by
    simp only [F,spectralWeylKMultiplier,ite_eq_left hX,spectralKLPlancherelWeight]
    rw [show (2 : ℝ)*t/2 = t by ring,show Real.pi*(2*t) = 2*(Real.pi*t) by ring,Real.sinh_two_mul]
    push_cast
    ring
  have hd : IntegrableOn (fun t : ℝ => F (2*t)) (Ioi (0 : ℝ)) :=
    (integrableOn_Ioi_comp_mul_left_iff F 0 two_pos).mpr (by simpa only [mul_zero] using hI)
  refine ⟨(spectralKLPositiveWeightMeasure_complex_integrable_iff _ _
    spectralKLPlancherelWeight_continuous.measurable hp).mpr
      ((hd.const_mul (2/(X : ℂ))).congr (ae_of_all _ fun t => (he t).symm)),?_⟩
  rw [spectralKLSpectralMeasure,spectralKLPositiveWeightMeasure_complex_integral _ _
    spectralKLPlancherelWeight_continuous.measurable hp]
  have hInt : (∫ t in Ioi (0 : ℝ), (spectralKLPlancherelWeight t : ℂ)*
        (spectralWeylKMultiplier t X*H t)) = (2/(X : ℂ))*
        (∫ t in Ioi (0 : ℝ), F (2*t)) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => he t)
  rw [hInt,integral_comp_mul_left_Ioi F 0 two_pos,mul_zero,Complex.real_smul]
  unfold spectralKLWeightedSynthesis
  change ((X : ℂ)/2)*((2/(X : ℂ))*((((2 : ℝ)⁻¹ : ℝ) : ℂ)*
      (∫ u in Ioi (0 : ℝ), F u))) = (1/2 : ℂ)*(∫ u in Ioi (0 : ℝ), F u)
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hX.ne'] <;> ring

/-- The corrected weight corresponding to the literal ABL opposite-sign test. -/
def spectralABLOppositeFourierWeight (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  (2/(Real.pi : ℂ))*spectralKLCompactOrderTransform f (2*I*z)

/-- The opposite-sign test printed in ABL §6, with the actual K order and measure. -/
def spectralABLOppositeTransform (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  Complex.cosh ((Real.pi : ℂ)*z)*spectralABLOppositeFourierWeight f z

theorem spectralKLCompactOrderTransform_integral (f : ℝ → ℂ)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (ν : ℂ) :
    spectralKLCompactOrderTransform f ν =
      ∫ x in Ioi (0 : ℝ), schlafliBesselK ν x*f x/(x : ℂ) := by
  unfold spectralKLCompactOrderTransform
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) (fun x hx => ?_)]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    simp only [spectralKLCompactOrderIntegrand,spectralKLPhysicalCompactDiv,mul_div_assoc]
  · have hf0 : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hp h))
    simp [spectralKLCompactOrderIntegrand,spectralKLPhysicalCompactDiv,hf0]

theorem spectralABLOppositeTransform_source (f : ℝ → ℂ)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (z : ℂ) :
    spectralABLOppositeTransform f z =
      (2/(Real.pi : ℂ))*Complex.cosh ((Real.pi : ℂ)*z)*
        (∫ x in Ioi (0 : ℝ), schlafliBesselK (2*I*z) x*f x/(x : ℂ)) := by
  rw [spectralABLOppositeTransform,spectralABLOppositeFourierWeight,
    spectralKLCompactOrderTransform_integral f hp]
  ring

theorem spectralABLOppositeTransform_bare_inverse (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) {X : ℝ} (hX : 0 < X) :
    Integrable (fun t : ℝ => spectralWeylKMultiplier t X*spectralABLOppositeFourierWeight f (t : ℂ))
      spectralKLSpectralMeasure ∧
    ((X : ℂ)/2)*(∫ t : ℝ, spectralWeylKMultiplier t X*spectralABLOppositeFourierWeight f (t : ℂ)
      ∂spectralKLSpectralMeasure) = f X/(Real.pi : ℂ) := by
  let F : ℝ → ℂ := fun t => spectralKLCompactOrderTransform f ((t : ℂ)*I)
  let H : ℝ → ℂ := fun t => spectralABLOppositeFourierWeight f (t : ℂ)
  have hF (u : ℝ) : H (u/2) = (2/(Real.pi : ℂ))*F u := by
    dsimp only [H,spectralABLOppositeFourierWeight,F]
    rw [show 2*I*((u/2 : ℝ) : ℂ) = (u : ℂ)*I by push_cast; ring]
  have hi : IntegrableOn (fun u : ℝ => schlafliBesselK ((u : ℂ)*I) X*H (u/2)*
      (spectralKLPlancherelWeight u : ℂ)) (Ioi (0 : ℝ)) := by
    have h0 := spectralKLDirectSynthesis_integrable F
      (spectralKLCompactOrderTransform_axis_smooth f hf.continuous hc hp).continuous
      (spectralKLCompactOrderTransform_axis_rapid f hf hc hp) hX
    apply (h0.const_mul (2/(Real.pi : ℂ))).integrableOn.congr_fun _ measurableSet_Ioi
    intro u _
    dsimp only
    rw [hF]
    ring
  obtain ⟨hI,he⟩ := spectralWeylK_synthesis_dilation H hX hi
  refine ⟨hI,he.trans ?_⟩
  have hS : spectralKLWeightedSynthesis (fun u => H (u/2)) X =
      (2/(Real.pi : ℂ))*spectralKLWeightedSynthesis F X := by
    unfold spectralKLWeightedSynthesis
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp only
    rw [hF]
    ring
  rw [hS,show spectralKLWeightedSynthesis F X = f X from
    spectralKLCompactOrderTransform_pointwise_inverse f hf hc hp hX]
  ring

end
end ArtinMatthews


module

public import ArtinMatthews.SpectralKLAnalysisIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! Literal KL analysis for noncompact physical inputs with an actual
integrable K0 majorant.  No compact-support inference is made. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein
open scoped Topology

namespace ArtinMatthews

def spectralKLIntegrableMajorant (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  spectralKLRealKernel 0 x*‖spectralKLPhysicalCompactDiv f x‖

theorem spectralKLIntegrableMajorant_bound (f : ℝ → ℂ)
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0) (t x : ℝ) :
    ‖(spectralKLRealKernel t x : ℂ)*spectralKLPhysicalCompactDiv f x‖ ≤
      spectralKLIntegrableMajorant f x := by
  by_cases hx : 0 < x
  · rw [norm_mul,Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (spectralKLRealKernel_norm_le_zero t hx) (norm_nonneg _)
  · simp [spectralKLPhysicalCompactDiv,spectralKLIntegrableMajorant,hfzero x (le_of_not_gt hx)]

theorem spectralKLAnalysis_integrable_of_majorant (f : ℝ → ℂ) (hf : Measurable f)
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0) (hM : Integrable (spectralKLIntegrableMajorant f)) (t : ℝ) :
    Integrable (fun x : ℝ => (spectralKLRealKernel t x : ℂ)*spectralKLPhysicalCompactDiv f x) := by
  have hK : Measurable (fun x : ℝ => (spectralKLRealKernel t x : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp spectralKLRealKernel_stronglyMeasurable.measurable
      |>.comp (measurable_const.prodMk measurable_id)
  have hD : Measurable (spectralKLPhysicalCompactDiv f) := by
    unfold spectralKLPhysicalCompactDiv
    fun_prop
  exact hM.mono' (hK.mul hD).aestronglyMeasurable
    (Filter.Eventually.of_forall (spectralKLIntegrableMajorant_bound f hfzero t))

theorem spectralKLAnalysis_continuous_of_majorant (f : ℝ → ℂ) (hf : Measurable f)
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0) (hM : Integrable (spectralKLIntegrableMajorant f)) :
    Continuous (spectralKLPhysicalAnalysisIntegral f) := by
  unfold spectralKLPhysicalAnalysisIntegral
  apply continuous_of_dominated (bound := spectralKLIntegrableMajorant f)
  · intro t
    exact (spectralKLAnalysis_integrable_of_majorant f hf hfzero hM t).aestronglyMeasurable
  · intro t
    exact Filter.Eventually.of_forall (spectralKLIntegrableMajorant_bound f hfzero t)
  · exact hM
  · filter_upwards with x
    by_cases hx : 0 < x
    · exact (Complex.continuous_ofReal.comp (spectralKLRealKernel_order_continuous hx)).mul continuous_const
    · simpa only [spectralKLPhysicalCompactDiv,hfzero x (le_of_not_gt hx),zero_div,mul_zero] using
        (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))

theorem spectralKLAnalysis_integral_of_nonpositive_zero (f : ℝ → ℂ)
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0) (t : ℝ) :
    spectralKLPhysicalAnalysisIntegral f t =
      ∫ x in Ioi (0 : ℝ), schlafliBesselK ((t : ℂ)*Complex.I) x*f x/(x : ℂ) := by
  unfold spectralKLPhysicalAnalysisIntegral
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) (fun x hx => ?_)]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [schlafliBesselK_imaginary_eq_realKernel t hx]
    simp only [spectralKLPhysicalCompactDiv,mul_div_assoc]
  · simp [spectralKLPhysicalCompactDiv,hfzero x (le_of_not_gt hx)]

end ArtinMatthews

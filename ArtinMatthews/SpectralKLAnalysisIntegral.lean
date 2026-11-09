module

public import ArtinMatthews.SpectralKLPhysicalCompactData
public import ArtinMatthews.SpectralKLKernelOrderContinuity


set_option backward.privateInPublic true
@[expose] public section

/-! The actual inverse K integral on physical compact positive tests,
with absolute convergence and spectral continuity. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein
open scoped Topology

namespace ArtinMatthews

def spectralKLPhysicalAnalysisIntegral (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, (spectralKLRealKernel t x : ℂ)*spectralKLPhysicalCompactDiv f x

theorem spectralKLPhysicalAnalysisIntegral_majorant (f : ℝ → ℂ) (hfc : HasCompactSupport f)
    (hfp : tsupport f ⊆ Ioi (0 : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x : ℝ,
      ‖(spectralKLRealKernel t x : ℂ)*spectralKLPhysicalCompactDiv f x‖ ≤
        C*‖spectralKLPhysicalCompactDiv f x‖ := by
  obtain ⟨a,ha,hax⟩ := spectral_compact_positive_lower_bound f hfc hfp
  refine ⟨spectralKLRealKernel 0 a,spectralKLRealKernel_zero_nonneg,?_⟩
  intro t x
  by_cases hf0 : f x = 0
  · simp [spectralKLPhysicalCompactDiv,hf0]
  · rw [norm_mul,Complex.norm_real]
    exact mul_le_mul_of_nonneg_right
      (spectralKLRealKernel_norm_le_height t ha (hax x (subset_tsupport f hf0))) (norm_nonneg _)

theorem spectralKLPhysicalAnalysisIntegral_integrable (f : ℝ → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ)) (t : ℝ) :
    Integrable (fun x : ℝ => (spectralKLRealKernel t x : ℂ)*spectralKLPhysicalCompactDiv f x) := by
  obtain ⟨C,_,hbound⟩ := spectralKLPhysicalAnalysisIntegral_majorant f hfc hfp
  have hK : Measurable (fun x : ℝ => (spectralKLRealKernel t x : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (spectralKLRealKernel_stronglyMeasurable.measurable.comp
      (measurable_const.prodMk measurable_id))
  apply ((spectralKLPhysicalCompactDiv_integrable f hf hfc hfp).norm.const_mul C).mono'
    (hK.mul (spectralKLPhysicalCompactDiv_continuous f hf hfp).measurable).aestronglyMeasurable
  exact Filter.Eventually.of_forall (hbound t)

theorem spectralKLPhysicalAnalysisIntegral_continuous (f : ℝ → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ)) :
    Continuous (spectralKLPhysicalAnalysisIntegral f) := by
  obtain ⟨C,_,hbound⟩ := spectralKLPhysicalAnalysisIntegral_majorant f hfc hfp
  unfold spectralKLPhysicalAnalysisIntegral
  apply continuous_of_dominated (bound := fun x : ℝ => C*‖spectralKLPhysicalCompactDiv f x‖)
  · intro t
    exact (spectralKLPhysicalAnalysisIntegral_integrable f hf hfc hfp t).aestronglyMeasurable
  · intro t
    exact Filter.Eventually.of_forall (hbound t)
  · exact (spectralKLPhysicalCompactDiv_integrable f hf hfc hfp).norm.const_mul C
  · filter_upwards with x
    by_cases hf0 : f x = 0
    · simpa only [spectralKLPhysicalCompactDiv,hf0,zero_div,mul_zero] using
        (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
    · have hx : 0 < x := hfp (subset_tsupport f hf0)
      exact (Complex.continuous_ofReal.comp (spectralKLRealKernel_order_continuous hx)).mul continuous_const

theorem spectralKLPhysicalAnalysisIntegral_eq (f : ℝ → ℂ)
    (hfp : tsupport f ⊆ Ioi (0 : ℝ)) (t : ℝ) :
    spectralKLPhysicalAnalysisIntegral f t =
      ∫ x in Ioi (0 : ℝ), schlafliBesselK ((t : ℂ)*Complex.I) x*f x/(x : ℂ) := by
  unfold spectralKLPhysicalAnalysisIntegral
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) (fun x hx => ?_)]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [schlafliBesselK_imaginary_eq_realKernel t hx]
    simp only [spectralKLPhysicalCompactDiv,mul_div_assoc]
  · have hf0 : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hfp h))
    simp [spectralKLPhysicalCompactDiv,hf0]

end ArtinMatthews

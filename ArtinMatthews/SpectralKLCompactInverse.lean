module

public import ArtinMatthews.SpectralKLAnalysisCalibration


set_option backward.privateInPublic true
@[expose] public section

/-! Literal inverse-integral calibration and Plancherel on physical
compact positive tests, with absolute convergence proved separately. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein
open scoped Topology

namespace ArtinMatthews

theorem spectralKLAnalysis_compact_integral_integrable (f : ℝ → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ)) (t : ℝ) :
    IntegrableOn (fun x : ℝ => schlafliBesselK ((t : ℂ)*Complex.I) x*f x/(x : ℂ)) (Ioi (0 : ℝ)) := by
  apply (spectralKLPhysicalAnalysisIntegral_integrable f hf hfc hfp t).restrict.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [schlafliBesselK_imaginary_eq_realKernel t hx]
  simp only [spectralKLPhysicalCompactDiv,mul_div_assoc]

theorem spectralKLAnalysis_compact_integral_ae (f : ℝ → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ)) :
    spectralKLAnalysis ((spectralKLPhysical_compact_memLp f hf hfc hfp).toLp f) =ᵐ[spectralKLSpectralMeasure]
      (fun t : ℝ => ∫ x in Ioi (0 : ℝ), schlafliBesselK ((t : ℂ)*Complex.I) x*f x/(x : ℂ)) := by
  filter_upwards [spectralKLAnalysis_compact_ae f hf hfc hfp] with t ht
  exact ht.trans (spectralKLPhysicalAnalysisIntegral_eq f hfp t)

theorem spectralKLAnalysis_compact_plancherel (f : ℝ → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ)) :
    (∫ t in Ioi (0 : ℝ), spectralKLPlancherelWeight t*‖spectralKLPhysicalAnalysisIntegral f t‖^2) =
      ∫ x in Ioi (0 : ℝ), ‖f x‖^2/x := by
  let F : Lp ℂ 2 spectralKLPhysicalMeasure := (spectralKLPhysical_compact_memLp f hf hfc hfp).toLp f
  have h : (∫ t : ℝ, ‖spectralKLPhysicalAnalysisIntegral f t‖^2 ∂spectralKLSpectralMeasure) =
      ∫ x : ℝ, ‖f x‖^2 ∂spectralKLPhysicalMeasure := by
    calc
      _ = ∫ t : ℝ, ‖spectralKLAnalysis F t‖^2 ∂spectralKLSpectralMeasure := by
        apply integral_congr_ae
        filter_upwards [spectralKLAnalysis_compact_ae f hf hfc hfp] with t ht
        rw [ht]
      _ = ∫ x : ℝ, ‖F x‖^2 ∂spectralKLPhysicalMeasure := spectralKLAnalysis_plancherel F
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [(spectralKLPhysical_compact_memLp f hf hfc hfp).coeFn_toLp] with x hx
        rw [hx]
  have hs : (∫ t : ℝ, ‖spectralKLPhysicalAnalysisIntegral f t‖^2 ∂spectralKLSpectralMeasure) =
      ∫ t in Ioi (0 : ℝ), spectralKLPlancherelWeight t*‖spectralKLPhysicalAnalysisIntegral f t‖^2 :=
    spectralKLPositiveWeightMeasure_integral _ _ spectralKLPlancherelWeight_continuous.measurable
      (fun t ht => (spectralKLPlancherelWeight_pos ht).le)
  have hx : (∫ x : ℝ, ‖f x‖^2 ∂spectralKLPhysicalMeasure) =
      ∫ x in Ioi (0 : ℝ), x⁻¹*‖f x‖^2 :=
    spectralKLPositiveWeightMeasure_integral _ _ (by fun_prop) (fun x hx => inv_nonneg.mpr hx.le)
  rw [hs,hx] at h
  convert h using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  dsimp only
  simp only [div_eq_mul_inv]
  ring

theorem spectralKLAnalysis_compact_integral_plancherel (f : ℝ → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ)) :
    (∫ t in Ioi (0 : ℝ), spectralKLPlancherelWeight t*
      ‖∫ x in Ioi (0 : ℝ), schlafliBesselK ((t : ℂ)*Complex.I) x*f x/(x : ℂ)‖^2) =
      ∫ x in Ioi (0 : ℝ), ‖f x‖^2/x := by
  simpa only [spectralKLPhysicalAnalysisIntegral_eq f hfp] using
    spectralKLAnalysis_compact_plancherel f hf hfc hfp

end ArtinMatthews

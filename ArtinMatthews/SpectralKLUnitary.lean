module

public import ArtinMatthews.SpectralKLPhysicalRangeDensity


set_option backward.privateInPublic true
@[expose] public section

/-! The actual completed KL transform is unitary, with full L2 inverse
identities. The synthesis is calibrated by its literal integral on the
proved dense smooth positive tests. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

def spectralKLUnitary : Lp ℂ 2 spectralKLSpectralMeasure ≃ₗᵢ[ℂ] Lp ℂ 2 spectralKLPhysicalMeasure :=
  LinearIsometryEquiv.ofSurjective spectralKLCompletedSynthesis spectralKLCompletedSynthesis_surjective

def spectralKLAnalysis : Lp ℂ 2 spectralKLPhysicalMeasure ≃ₗᵢ[ℂ] Lp ℂ 2 spectralKLSpectralMeasure :=
  spectralKLUnitary.symm

theorem spectralKLUnitary_apply (g : Lp ℂ 2 spectralKLSpectralMeasure) :
    spectralKLUnitary g = spectralKLCompletedSynthesis g := rfl

theorem spectralKLAnalysis_synthesis (g : Lp ℂ 2 spectralKLSpectralMeasure) :
    spectralKLAnalysis (spectralKLCompletedSynthesis g) = g := by
  change spectralKLUnitary.symm (spectralKLUnitary g) = g
  exact spectralKLUnitary.symm_apply_apply g

theorem spectralKLSynthesis_analysis (f : Lp ℂ 2 spectralKLPhysicalMeasure) :
    spectralKLCompletedSynthesis (spectralKLAnalysis f) = f := by
  change spectralKLUnitary (spectralKLUnitary.symm f) = f
  exact spectralKLUnitary.apply_symm_apply f

theorem spectralKLAnalysis_norm (f : Lp ℂ 2 spectralKLPhysicalMeasure) :
    ‖spectralKLAnalysis f‖ = ‖f‖ := spectralKLAnalysis.norm_map f

theorem spectralKLAnalysis_plancherel (f : Lp ℂ 2 spectralKLPhysicalMeasure) :
    (∫ t : ℝ, ‖spectralKLAnalysis f t‖^2 ∂spectralKLSpectralMeasure) =
      ∫ x : ℝ, ‖f x‖^2 ∂spectralKLPhysicalMeasure := by
  rw [← spectral_Lp_norm_sq,← spectral_Lp_norm_sq,spectralKLAnalysis_norm]

theorem spectralKLAnalysis_plancherel_weighted (f : Lp ℂ 2 spectralKLPhysicalMeasure) :
    (∫ t in Ioi (0 : ℝ), spectralKLPlancherelWeight t*‖spectralKLAnalysis f t‖^2) =
      ∫ x in Ioi (0 : ℝ), ‖f x‖^2/x := by
  have h := spectralKLAnalysis_plancherel f
  have hs : (∫ t : ℝ, ‖spectralKLAnalysis f t‖^2 ∂spectralKLSpectralMeasure) =
      ∫ t in Ioi (0 : ℝ), spectralKLPlancherelWeight t*‖spectralKLAnalysis f t‖^2 :=
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

theorem spectralKLUnitary_test_ae (g : spectralKLTestSubmodule) :
    spectralKLUnitary (spectralKLTestToLp g) =ᵐ[spectralKLPhysicalMeasure] spectralKLWeightedSynthesis g := by
  rw [spectralKLUnitary_apply]
  exact spectralKLCompletedSynthesis_test_ae g

theorem spectralKLAnalysis_test_synthesis (g : spectralKLTestSubmodule) :
    spectralKLAnalysis (spectralKLTestSynthesis g) = spectralKLTestToLp g := by
  rw [← spectralKLCompletedSynthesis_test]
  exact spectralKLAnalysis_synthesis _

end ArtinMatthews

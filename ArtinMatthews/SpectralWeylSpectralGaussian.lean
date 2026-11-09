module

public import ArtinMatthews.SpectralWeylSpectralGaussianIntegrable


set_option backward.privateInPublic true
@[expose] public section

/-! Evaluated Gaussian actions of the actual compact-test J/K spectral
bilinear forms.  The swap uses proved absolute integrability. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralWeyl_gaussian_spectral_swap (M : ℝ → ℝ → ℂ) (p : ℝ) (F G : ℝ → ℂ)
    (hi : Integrable (spectralWeylGaussianSpectralIntegrand M p F G)
      ((volume.restrict (Ioi (0 : ℝ))).prod spectralKLSpectralMeasure)) :
    (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
      (∫ r : ℝ, M r X*F r*star (G r) ∂spectralKLSpectralMeasure)) =
      ∫ r : ℝ, (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*M r X)*
        F r*star (G r) ∂spectralKLSpectralMeasure := by
  calc
    _ = ∫ X in Ioi (0 : ℝ), ∫ r : ℝ,
        spectralWeylGaussianSpectralIntegrand M p F G (X,r) ∂spectralKLSpectralMeasure := by
      apply integral_congr_ae
      filter_upwards with X
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with r
      unfold spectralWeylGaussianSpectralIntegrand
      ring_nf
    _ = ∫ r : ℝ, (∫ X in Ioi (0 : ℝ),
        spectralWeylGaussianSpectralIntegrand M p F G (X,r)) ∂spectralKLSpectralMeasure :=
      integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with r
      rw [← integral_mul_const,← integral_mul_const]
      rfl

theorem spectralWeylJ_gaussian_spectral {p : ℝ} (hp : 1/4 < p)
    (F G : ℝ → ℂ) (hcF : Continuous F) (hcG : Continuous G)
    (hF : MemLp F 2 spectralKLSpectralMeasure) (hG : MemLp G 2 spectralKLSpectralMeasure) :
    (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
      (∫ r : ℝ, spectralWeylJMultiplier r X*F r*star (G r) ∂spectralKLSpectralMeasure)) =
      ∫ r : ℝ, (2*(Real.sqrt (Real.pi/p) : ℂ)*Complex.exp (-((1/(8*p) : ℝ) : ℂ))*
        schlafliBesselK ((r : ℂ)*Complex.I) (1/(8*p)))*F r*star (G r)
          ∂spectralKLSpectralMeasure := by
  rw [spectralWeyl_gaussian_spectral_swap _ p F G
    (spectralWeylJGaussianSpectralIntegrand_integrable hp F G hcF hcG hF hG)]
  apply integral_congr_ae
  filter_upwards [spectralKLPositiveWeightMeasure_ae_pos spectralKLPlancherelWeight] with r hr
  rw [spectralWeylJMultiplier_gaussian_value hr (by linarith : 0 < p)]

theorem spectralWeylK_gaussian_spectral {p : ℝ} (hp : 1/4 < p)
    (F G : ℝ → ℂ) (hcF : Continuous F) (hcG : Continuous G)
    (hF : MemLp F 2 spectralKLSpectralMeasure) (hG : MemLp G 2 spectralKLSpectralMeasure) :
    (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
      (∫ r : ℝ, spectralWeylKMultiplier r X*F r*star (G r) ∂spectralKLSpectralMeasure)) =
      ∫ r : ℝ, (2*(Real.sqrt (Real.pi/p) : ℂ)*Complex.exp ((1/(8*p) : ℝ) : ℂ)*
        schlafliBesselK ((r : ℂ)*Complex.I) (1/(8*p)))*F r*star (G r)
          ∂spectralKLSpectralMeasure := by
  rw [spectralWeyl_gaussian_spectral_swap _ p F G
    (spectralWeylKGaussianSpectralIntegrand_integrable hp F G hcF hcG hF hG)]
  apply integral_congr_ae
  filter_upwards [spectralKLPositiveWeightMeasure_ae_pos spectralKLPlancherelWeight] with r hr
  rw [spectralWeylKMultiplier_gaussian_value hr (by linarith : 0 < p)]

theorem spectralWeylJ_gaussian_compact_analysis {p : ℝ} (hp : 1/4 < p)
    (f g : ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ))
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
      (∫ r : ℝ, spectralWeylJMultiplier r X*spectralKLPhysicalAnalysisIntegral f r*
        star (spectralKLPhysicalAnalysisIntegral g r) ∂spectralKLSpectralMeasure)) =
      ∫ r : ℝ, (2*(Real.sqrt (Real.pi/p) : ℂ)*Complex.exp (-((1/(8*p) : ℝ) : ℂ))*
        schlafliBesselK ((r : ℂ)*Complex.I) (1/(8*p)))*spectralKLPhysicalAnalysisIntegral f r*
          star (spectralKLPhysicalAnalysisIntegral g r) ∂spectralKLSpectralMeasure :=
  spectralWeylJ_gaussian_spectral hp _ _
    (spectralKLPhysicalAnalysisIntegral_continuous f hf hfc hfp)
    (spectralKLPhysicalAnalysisIntegral_continuous g hg hgc hgp)
    (spectralKLPhysicalAnalysisIntegral_memLp f hf hfc hfp)
    (spectralKLPhysicalAnalysisIntegral_memLp g hg hgc hgp)

theorem spectralWeylK_gaussian_compact_analysis {p : ℝ} (hp : 1/4 < p)
    (f g : ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ))
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
      (∫ r : ℝ, spectralWeylKMultiplier r X*spectralKLPhysicalAnalysisIntegral f r*
        star (spectralKLPhysicalAnalysisIntegral g r) ∂spectralKLSpectralMeasure)) =
      ∫ r : ℝ, (2*(Real.sqrt (Real.pi/p) : ℂ)*Complex.exp ((1/(8*p) : ℝ) : ℂ)*
        schlafliBesselK ((r : ℂ)*Complex.I) (1/(8*p)))*spectralKLPhysicalAnalysisIntegral f r*
          star (spectralKLPhysicalAnalysisIntegral g r) ∂spectralKLSpectralMeasure :=
  spectralWeylK_gaussian_spectral hp _ _
    (spectralKLPhysicalAnalysisIntegral_continuous f hf hfc hfp)
    (spectralKLPhysicalAnalysisIntegral_continuous g hg hgc hgp)
    (spectralKLPhysicalAnalysisIntegral_memLp f hf hfc hfp)
    (spectralKLPhysicalAnalysisIntegral_memLp g hg hgc hgp)

end ArtinMatthews

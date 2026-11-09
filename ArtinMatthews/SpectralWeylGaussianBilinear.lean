module

public import ArtinMatthews.SpectralKLWeylGaussian
public import ArtinMatthews.SpectralKLMacdonaldBilinear
public import ArtinMatthews.SpectralWeylSpectralGaussian


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Gaussian modulus-first two-height orbital bilinear form
has the evaluated J/K spectral action on genuine compact physical tests.
No unregularized interchange or global automorphic resolution is used. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralWeylGaussian_bilinear {p : ℝ} (hp : 0 < p)
    (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1)
    (f g : ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ))
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    (∫ x : ℝ, (∫ z : ℝ,
      ((∫ X in Ioi (0 : ℝ), Real.exp (-p*X^2)*X*spectralWeylDimensionlessKernel s t X x z : ℝ) : ℂ)*
        f z ∂spectralKLPhysicalMeasure)*star (g x) ∂spectralKLPhysicalMeasure) =
      ∫ r : ℝ, (2*spectralKLWeylGaussianConstant s t p*
        schlafliBesselK ((r : ℂ)*Complex.I) (1/(8*p)))*spectralKLPhysicalAnalysisIntegral f r*
          star (spectralKLPhysicalAnalysisIntegral g r) ∂spectralKLSpectralMeasure := by
  have hy : 0 < 1/(8*p) := by positivity
  calc
    _ = spectralKLWeylGaussianConstant s t p*
        (∫ x : ℝ, (∫ z : ℝ, spectralKLMacdonaldProfile x (1/(8*p)) z*f z
          ∂spectralKLPhysicalMeasure)*star (g x) ∂spectralKLPhysicalMeasure) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx
      rw [← mul_assoc]
      congr 1
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [spectralKLPositiveWeightMeasure_ae_pos (fun z => z⁻¹)] with z hz
      have he := spectralKLWeylGaussianProfile_factor hx hp s t hs ht z
      rw [spectralKLWeylGaussianProfile,ite_eq_left hz] at he
      rw [he]
      ring_nf
    _ = spectralKLWeylGaussianConstant s t p*
        (∫ r : ℝ, (2*schlafliBesselK ((r : ℂ)*Complex.I) (1/(8*p)))*
          spectralKLPhysicalAnalysisIntegral f r*star (spectralKLPhysicalAnalysisIntegral g r)
            ∂spectralKLSpectralMeasure) := by
      rw [spectralKLMacdonald_bilinear hy f g hf hfc hfp hg hgc hgp]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with r
      ring_nf

theorem spectralWeylGaussian_same_bilinear_J {p : ℝ} (hp : 1/4 < p)
    (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) (hst : s*t = 1)
    (f g : ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ))
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    (∫ x : ℝ, (∫ z : ℝ,
      ((∫ X in Ioi (0 : ℝ), Real.exp (-p*X^2)*X*spectralWeylDimensionlessKernel s t X x z : ℝ) : ℂ)*
        f z ∂spectralKLPhysicalMeasure)*star (g x) ∂spectralKLPhysicalMeasure) =
      ∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
        (∫ r : ℝ, spectralWeylJMultiplier r X*spectralKLPhysicalAnalysisIntegral f r*
          star (spectralKLPhysicalAnalysisIntegral g r) ∂spectralKLSpectralMeasure) := by
  rw [spectralWeylGaussian_bilinear (by linarith : 0 < p) s t hs ht f g hf hfc hfp hg hgc hgp,
    spectralWeylJ_gaussian_compact_analysis hp f g hf hfc hfp hg hgc hgp]
  apply integral_congr_ae
  filter_upwards with r
  unfold spectralKLWeylGaussianConstant
  rw [hst]
  push_cast
  ring_nf

theorem spectralWeylGaussian_opposite_bilinear_K {p : ℝ} (hp : 1/4 < p)
    (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) (hst : s*t = -1)
    (f g : ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ))
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    (∫ x : ℝ, (∫ z : ℝ,
      ((∫ X in Ioi (0 : ℝ), Real.exp (-p*X^2)*X*spectralWeylDimensionlessKernel s t X x z : ℝ) : ℂ)*
        f z ∂spectralKLPhysicalMeasure)*star (g x) ∂spectralKLPhysicalMeasure) =
      ∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
        (∫ r : ℝ, spectralWeylKMultiplier r X*spectralKLPhysicalAnalysisIntegral f r*
          star (spectralKLPhysicalAnalysisIntegral g r) ∂spectralKLSpectralMeasure) := by
  rw [spectralWeylGaussian_bilinear (by linarith : 0 < p) s t hs ht f g hf hfc hfp hg hgc hgp,
    spectralWeylK_gaussian_compact_analysis hp f g hf hfc hfp hg hgc hgp]
  apply integral_congr_ae
  filter_upwards with r
  unfold spectralKLWeylGaussianConstant
  rw [hst]
  push_cast
  ring_nf

end ArtinMatthews

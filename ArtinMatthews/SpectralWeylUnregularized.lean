module

public import ArtinMatthews.SpectralWeylPhysicalContinuity
public import ArtinMatthews.SpectralWeylSpectralContinuity
public import ArtinMatthews.SpectralGaussianUniqueness


set_option backward.privateInPublic true
@[expose] public section

/-! Pointwise unregularized J/K action of the actual two-height Weyl
bilinear form at every positive modulus.  Gaussian removal uses proved
absolute Fubini, genuine Laplace uniqueness, and continuity on both
sides.  This is a model-cusp identity on compact physical tests. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

private theorem spectralWeylPhysicalBilinear_remove_gaussian
    (s t : ℝ) (f g : ℝ → ℂ)
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ))
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ))
    (M : ℝ → ℝ → ℂ) (hMm : Measurable (fun q : ℝ × ℝ => M q.1 q.2))
    (hMc : ∀ r : ℝ, 0 < r → ContinuousOn (M r) (Ioi (0 : ℝ)))
    (hMb : ∀ r X : ℝ, 0 < r → 0 < X → ‖(X : ℂ)*M r X‖ ≤
      4*Real.pi*Real.exp (X^2/4)*(1+(Real.sqrt (Real.cosh Real.pi)/Real.pi)/r))
    (hEq : ∀ p : ℝ, 1/4 < p →
      (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*spectralWeylPhysicalBilinear s t f g X) =
      ∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
        spectralWeylSpectralBilinear M (spectralKLPhysicalAnalysisIntegral f) (spectralKLPhysicalAnalysisIntegral g) X) :
    EqOn (spectralWeylPhysicalBilinear s t f g)
      (spectralWeylSpectralBilinear M (spectralKLPhysicalAnalysisIntegral f) (spectralKLPhysicalAnalysisIntegral g))
        (Ioi (0 : ℝ)) := by
  let F := spectralKLPhysicalAnalysisIntegral f
  let G := spectralKLPhysicalAnalysisIntegral g
  let C := Real.sqrt (Real.cosh Real.pi)/Real.pi
  have hC : 0 ≤ C := div_nonneg (Real.sqrt_nonneg _) Real.pi_pos.le
  have hcF : Continuous F := spectralKLPhysicalAnalysisIntegral_continuous f hf hfc hfp
  have hcG : Continuous G := spectralKLPhysicalAnalysisIntegral_continuous g hg hgc hgp
  have hF : MemLp F 2 spectralKLSpectralMeasure := spectralKLPhysicalAnalysisIntegral_memLp f hf hfc hfp
  have hG : MemLp G 2 spectralKLSpectralMeasure := spectralKLPhysicalAnalysisIntegral_memLp g hg hgc hgp
  have hfi := spectralKLPhysical_compact_integrable f hf hfc hfp
  have hgi := spectralKLPhysical_compact_integrable g hg hgc hgp
  apply spectral_eqOn_Ioi_of_gaussian_eq _ _
    (spectralWeylPhysicalBilinear_continuousOn s t f g hf hfc hfp hg hgc hgp)
    (spectralWeylSpectralBilinear_continuousOn M C hC F G hcF hcG hF hG hMm hMc hMb) (1/4)
  · intro p hp
    exact spectralWeylPhysicalBilinear_gaussian_integrable (by linarith : 0 < p) s t f g
      hf.measurable hg.measurable hfi hgi
  · intro p hp
    exact spectralWeylSpectralBilinear_gaussian_integrable M p F G
      (spectralWeylGaussianSpectralIntegrand_integrable M hp C F G hMm hMb hcF hcG hF hG)
  · exact hEq

theorem spectralWeylPhysicalBilinear_same_J {X : ℝ} (hX : 0 < X)
    (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) (hst : s*t = 1)
    (f g : ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ))
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    spectralWeylPhysicalBilinear s t f g X =
      ∫ r : ℝ, spectralWeylJMultiplier r X*spectralKLPhysicalAnalysisIntegral f r*
        star (spectralKLPhysicalAnalysisIntegral g r) ∂spectralKLSpectralMeasure := by
  have h := spectralWeylPhysicalBilinear_remove_gaussian s t f g hf hfc hfp hg hgc hgp
    spectralWeylJMultiplier spectralWeylJMultiplier_measurable
    (fun r _ => spectralWeylJMultiplier_continuousOn r)
    (fun _ _ hr hX => spectralWeylJMultiplier_order_bound hr hX)
    (fun p hp => spectralWeylPhysicalBilinear_same_gaussian_J hp s t hs ht hst f g hf hfc hfp hg hgc hgp)
  exact h (show X ∈ Ioi (0 : ℝ) from hX)

theorem spectralWeylPhysicalBilinear_opposite_K {X : ℝ} (hX : 0 < X)
    (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) (hst : s*t = -1)
    (f g : ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ))
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    spectralWeylPhysicalBilinear s t f g X =
      ∫ r : ℝ, spectralWeylKMultiplier r X*spectralKLPhysicalAnalysisIntegral f r*
        star (spectralKLPhysicalAnalysisIntegral g r) ∂spectralKLSpectralMeasure := by
  have h := spectralWeylPhysicalBilinear_remove_gaussian s t f g hf hfc hfp hg hgc hgp
    spectralWeylKMultiplier spectralWeylKMultiplier_measurable
    (fun r _ => spectralWeylKMultiplier_continuousOn r)
    (fun _ _ hr hX => spectralWeylKMultiplier_order_bound hr hX)
    (fun p hp => spectralWeylPhysicalBilinear_opposite_gaussian_K hp s t hs ht hst f g hf hfc hfp hg hgc hgp)
  exact h (show X ∈ Ioi (0 : ℝ) from hX)

end ArtinMatthews

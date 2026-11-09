module

public import ArtinMatthews.SpectralKLGaussianWeights
public import ArtinMatthews.SpectralKLDirectProperties


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Complex
open scoped ContDiff
noncomputable section

def spectralKLHeatProfile (R : ℝ) : ℝ → ℂ :=
  spectralKLDirectSynthesis (fun t : ℝ => spectralKLGaussianData R (t : ℂ))

def spectralKLWeightedHeatProfile (h : ℂ → ℂ) (R : ℝ) : ℝ → ℂ :=
  spectralKLDirectSynthesis (fun t : ℝ => spectralKLGaussianWeightedData h R (t : ℂ))

theorem spectralKLHeatProfile_properties (R : ℝ) (hR : 0 < R) :
    SpectralKLHeatRegularity (spectralKLHeatProfile R) :=
  spectralKLDirectSynthesis_regularity (spectralKLGaussianData R)
    (spectralKLGaussianData_even R) (spectralKLGaussianData_real_contDiff R)
    (fun z _ => spectralKLGaussianData_differentiable R z) (spectralKLGaussianData_direct_rapid R hR)

theorem spectralKLHeatProfile_continued_transform (R : ℝ) (hR : 0 < R)
    (ν : ℂ) (hν : |ν.re| ≤ 1 / 2) :
    spectralKLCompactOrderTransform (spectralKLHeatProfile R) ν = Complex.exp (ν ^ 2 / (R : ℂ) ^ 2) := by
  exact (spectralKLDirectSynthesis_continued_transform (spectralKLGaussianData R)
    (spectralKLGaussianData_even R) (spectralKLGaussianData_real_contDiff R)
    (fun z _ => spectralKLGaussianData_differentiable R z)
    (spectralKLGaussianData_direct_rapid R hR) ν hν).trans (spectralKLGaussianData_order R ν)

theorem spectralKLHeatProfile_transform (R : ℝ) (hR : 0 < R) (t : ℝ) :
    spectralKLPhysicalAnalysisIntegral (spectralKLHeatProfile R) t =
      (Real.exp (-((t / R) ^ 2)) : ℂ) := by
  exact (spectralKLDirectSynthesis_analysis_pointwise (spectralKLGaussianData R)
    (spectralKLGaussianData_even R) (spectralKLGaussianData_real_contDiff R)
    (fun z _ => spectralKLGaussianData_differentiable R z)
    (spectralKLGaussianData_direct_rapid R hR) t).trans (spectralKLGaussianData_real R t)

theorem spectralKLHeatProfile_real (R x : ℝ) :
    star (spectralKLHeatProfile R x) = spectralKLHeatProfile R x :=
  spectralKLDirectSynthesis_real _ (spectralKLGaussianData_real_star R) x

theorem spectralKLHeatProfile_nonpositive_zero (R x : ℝ) (hx : x ≤ 0) :
    spectralKLHeatProfile R x = 0 := spectralKLDirectSynthesis_nonpositive_zero _ x hx

theorem spectralKLWeightedHeatProfile_properties (h : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (heven : ∀ z : ℂ, h (-z) = h z)
    (hsmooth : ContDiff ℝ ∞ (fun t : ℝ => h (t : ℂ)))
    (hhol : ∀ z : ℂ, |z.im| ≤ 3 / 4 → DifferentiableAt ℂ h z)
    (H : ℝ) (hH : 0 ≤ H)
    (hbound : ∀ t y : ℝ, |y| ≤ 3 / 4 → ‖h ((t : ℂ) + (y : ℂ) * I)‖ ≤ H) :
    SpectralKLHeatRegularity (spectralKLWeightedHeatProfile h R) :=
  spectralKLDirectSynthesis_regularity (spectralKLGaussianWeightedData h R)
    (spectralKLGaussianWeightedData_even h R heven)
    (spectralKLGaussianWeightedData_real_contDiff h R hsmooth)
    (fun z hz => spectralKLGaussianWeightedData_differentiableAt h R z (hhol z hz))
    (spectralKLGaussianWeightedData_direct_rapid h R hR H hH hbound)

theorem spectralKLWeightedHeatProfile_continued_transform (h : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (heven : ∀ z : ℂ, h (-z) = h z)
    (hsmooth : ContDiff ℝ ∞ (fun t : ℝ => h (t : ℂ)))
    (hhol : ∀ z : ℂ, |z.im| ≤ 3 / 4 → DifferentiableAt ℂ h z)
    (H : ℝ) (hH : 0 ≤ H)
    (hbound : ∀ t y : ℝ, |y| ≤ 3 / 4 → ‖h ((t : ℂ) + (y : ℂ) * I)‖ ≤ H)
    (ν : ℂ) (hν : |ν.re| ≤ 1 / 2) :
    spectralKLCompactOrderTransform (spectralKLWeightedHeatProfile h R) ν =
      h (-I * ν) * Complex.exp (ν ^ 2 / (R : ℂ) ^ 2) := by
  have heq := spectralKLDirectSynthesis_continued_transform (spectralKLGaussianWeightedData h R)
    (spectralKLGaussianWeightedData_even h R heven)
    (spectralKLGaussianWeightedData_real_contDiff h R hsmooth)
    (fun z hz => spectralKLGaussianWeightedData_differentiableAt h R z (hhol z hz))
    (spectralKLGaussianWeightedData_direct_rapid h R hR H hH hbound) ν hν
  simpa only [spectralKLWeightedHeatProfile, spectralKLGaussianWeightedData, spectralKLGaussianData_order] using heq

theorem spectralKLWeightedHeatProfile_real (h : ℂ → ℂ) (R : ℝ)
    (hh : ∀ t : ℝ, star (h (t : ℂ)) = h (t : ℂ)) (x : ℝ) :
    star (spectralKLWeightedHeatProfile h R x) = spectralKLWeightedHeatProfile h R x :=
  spectralKLDirectSynthesis_real _ (spectralKLGaussianWeightedData_real_star h R hh) x

theorem spectralKLWeightedHeatProfile_nonpositive_zero (h : ℂ → ℂ) (R x : ℝ) (hx : x ≤ 0) :
    spectralKLWeightedHeatProfile h R x = 0 := spectralKLDirectSynthesis_nonpositive_zero _ x hx

end
end ArtinMatthews

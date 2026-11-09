module

public import ArtinMatthews.SourceHyperbolicEnergy
public import ArtinMatthews.SourceHyperbolicProductEnergy
public import ArtinMatthews.SourceHyperbolicProductSlices


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory Filter
open scoped Topology ContDiff BigOperators Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem product_native_tested_laplacian_integrable {f φ : ProductSpace ι → ℂ}
    (hf : ∀ p ∈ productUpper ι, ContDiffAt ℝ 2 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    Integrable (fun p => star (φ p) * SourceArchJacquet.sourceArchProductCoordinateLaplacian f p)
      (productVolume ι) := by
  apply (product_tested_laplacian_integrable_hyperbolic hf hφ hc hsupp).congr
  exact Filter.Eventually.of_forall fun p => by
    change star (φ p) * productLaplacian f p =
      star (φ p) * SourceArchJacquet.sourceArchProductCoordinateLaplacian f p
    by_cases hp : p ∈ productUpper ι
    · rw [productLaplacian_eq_native hf hp]
    · have hz : φ p=0 := image_eq_zero_of_notMem_tsupport (fun h => hp (hsupp h))
      rw [hz, star_zero, zero_mul, zero_mul]

theorem product_native_green {f φ : ProductSpace ι → ℂ}
    (hf : ∀ p ∈ productUpper ι, ContDiffAt ℝ 2 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    (∫ p, productGradientPair φ f p ∂productVolume ι) =
      ∫ p, star (φ p) * SourceArchJacquet.sourceArchProductCoordinateLaplacian f p ∂productVolume ι := by
  rw [product_green_hyperbolic hf hφ hc hsupp]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    change star (φ p) * productLaplacian f p =
      star (φ p) * SourceArchJacquet.sourceArchProductCoordinateLaplacian f p
    by_cases hp : p ∈ productUpper ι
    · rw [productLaplacian_eq_native hf hp]
    · have hz : φ p=0 := image_eq_zero_of_notMem_tsupport (fun h => hp (hsupp h))
      rw [hz, star_zero, zero_mul, zero_mul]

theorem product_native_green_on {f φ : ProductSpace ι → ℂ}
    (hf : ContDiffOn ℝ 2 f (productUpper ι))
    (hφ : ContDiffOn ℝ 2 φ (productUpper ι)) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    (∫ p, productGradientPair φ f p ∂productVolume ι) =
      ∫ p, star (φ p) * SourceArchJacquet.sourceArchProductCoordinateLaplacian f p ∂productVolume ι := by
  apply product_native_green _ (product_test_contDiff_of_contDiffOn hφ hsupp) hc hsupp
  intro p hp
  exact (hf p hp).contDiffAt ((productUpper_isOpen ι).mem_nhds hp)

theorem product_native_green_energy {φ : ProductSpace ι → ℂ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    (∫ p, star (φ p) * SourceArchJacquet.sourceArchProductCoordinateLaplacian φ p ∂productVolume ι) =
      (∫ p, productGradientEnergy φ p ∂productVolume ι : ℝ) := by
  rw [← product_native_green (fun _ _ => hφ.contDiffAt) hφ hc hsupp]
  simp only [productGradientPair_self]
  exact integral_complex_ofReal

theorem product_native_green_energy_nonneg {φ : ProductSpace ι → ℂ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    0 ≤ (∫ p, star (φ p) * SourceArchJacquet.sourceArchProductCoordinateLaplacian φ p ∂productVolume ι).re := by
  rw [product_native_green_energy hφ hc hsupp, Complex.ofReal_re]
  exact integral_nonneg (productGradientEnergy_nonneg φ)


theorem green_energy_on {φ : EuclideanSpatial → ℂ}
    (hφ : ContDiffOn ℝ 2 φ euclideanUpperHalf) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ euclideanUpperHalf) :
    (∫ p, star (φ p) * positiveEuclideanLaplacian φ p ∂hyperbolicEuclideanVolume) =
      (∫ p, gradientEnergy φ p ∂hyperbolicEuclideanVolume : ℝ) :=
  green_energy (test_contDiff_of_contDiffOn hφ hsupp) hc hsupp

theorem product_native_green_energy_on {φ : ProductSpace ι → ℂ}
    (hφ : ContDiffOn ℝ 2 φ (productUpper ι)) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    (∫ p, star (φ p) * SourceArchJacquet.sourceArchProductCoordinateLaplacian φ p ∂productVolume ι) =
      (∫ p, productGradientEnergy φ p ∂productVolume ι : ℝ) :=
  product_native_green_energy (product_test_contDiff_of_contDiffOn hφ hsupp) hc hsupp

end
end ArtinMatthews.SourceHyperbolicGreen

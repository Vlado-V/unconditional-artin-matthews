module

public import ArtinMatthews.SourceHyperbolicProductMeasureGreen


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory
open scoped Topology ContDiff BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι]

def productGradientEnergy (f : ProductSpace ι → ℂ) (p : ProductSpace ι) : ℝ :=
  ∑ i, (p i 2)^2 * ∑ j : Fin 3, ‖productPartial f i j p‖^2

theorem productGradientEnergy_nonneg (f : ProductSpace ι → ℂ) (p : ProductSpace ι) :
    0 ≤ productGradientEnergy f p := by
  unfold productGradientEnergy
  positivity

theorem productGradientPair_self (f : ProductSpace ι → ℂ) (p : ProductSpace ι) :
    productGradientPair f f p = (productGradientEnergy f p : ℂ) := by
  unfold productGradientPair productGradientEnergy
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Complex.star_def, Complex.ofReal_pow] using! RCLike.conj_mul (productPartial f i j p)

theorem productGradientEnergy_integrable {φ : ProductSpace ι → ℂ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    Integrable (productGradientEnergy φ) (productVolume ι) := by
  have h := (productGradientPair_integrable (fun _ _ => hφ.contDiffAt) hφ hc hsupp).re
  change Integrable (fun p => (productGradientPair φ φ p).re) _ at h
  simpa only [productGradientPair_self, Complex.ofReal_re] using! h

theorem product_green_energy {φ : ProductSpace ι → ℂ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    (∫ p, star (φ p) * productLaplacian φ p ∂productVolume ι) =
      (∫ p, productGradientEnergy φ p ∂productVolume ι : ℝ) := by
  calc
    _ = ∫ p, productGradientPair φ φ p ∂productVolume ι :=
      (product_green_hyperbolic (fun _ _ => hφ.contDiffAt) hφ hc hsupp).symm
    _ = _ := by
      simp only [productGradientPair_self]
      exact integral_complex_ofReal

theorem product_green_energy_nonneg {φ : ProductSpace ι → ℂ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    0 ≤ (∫ p, star (φ p) * productLaplacian φ p ∂productVolume ι).re := by
  rw [product_green_energy hφ hc hsupp, Complex.ofReal_re]
  exact integral_nonneg (productGradientEnergy_nonneg φ)

end
end ArtinMatthews.SourceHyperbolicGreen

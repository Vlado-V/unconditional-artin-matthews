module

public import ArtinMatthews.SourceHyperbolicHardyCalculus
public import ArtinMatthews.SourceHyperbolicProductGreen


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory Filter
open scoped Topology ContDiff BigOperators Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem productWeightedValue_divergence {f : ProductSpace ι → ℂ} {p : ProductSpace ι}
    (hf : ContDiffAt ℝ 1 f p) (hp : p ∈ productUpper ι) (i : ι) :
    productPartial (productWeightedValue f i) i 2 p =
      productComplexDensity p * (productVertical f i p - 2 * f p) := by
  rw [productWeightedValue_derivative hf hp i, productComplexDensity_factor p i]
  simp only [productVertical, div_eq_mul_inv]
  ring

theorem product_hardy_ibp_euclidean {f φ : ProductSpace ι → ℂ}
    (hf : ∀ p ∈ productUpper ι, ContDiffAt ℝ 1 f p)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) (i : ι) :
    (∫ p, star (productPartial φ i 2 p) * productWeightedValue f i p) =
      -(∫ p, star (φ p) * productPartial (productWeightedValue f i) i 2 p) := by
  have h₁ : Integrable (fun p => star (productPartial φ i 2 p) * productWeightedValue f i p) volume := by
    apply product_compact_star_mul_integrable (hardyPartial_continuous hφ i 2)
      (product_test_partial_compact hc i 2)
    intro p hp
    have hh := hsupp (product_test_partial_support i 2 hp)
    exact (productWeightedValue_contDiffAt (hf p hh) hh i).continuousAt
  have h₂ : Integrable (fun p => star (φ p) * productPartial (productWeightedValue f i) i 2 p) volume := by
    apply product_compact_star_mul_integrable hφ.continuous hc
    intro p hp
    have hh := hsupp hp
    exact productWeightedValue_partial_continuousAt (hf p hh) hh i
  have h₃ : Integrable (fun p => star (φ p) * productWeightedValue f i p) volume := by
    apply product_compact_star_mul_integrable hφ.continuous hc
    intro p hp
    have hh := hsupp hp
    exact (productWeightedValue_contDiffAt (hf p hh) hh i).continuousAt
  have h := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (μ := volume) (B := complexHermitianBilin) (f := φ) (g := productWeightedValue f i)
    (v := productDirection i 2) h₁ h₂ h₃
    (fun p _ => hφ.contDiffAt.differentiableAt (by norm_num))
    (fun p hp => (productWeightedValue_contDiffAt (hf p (hsupp hp)) (hsupp hp) i).differentiableAt (by norm_num))
  change (∫ p, star (φ p) * productPartial (productWeightedValue f i) i 2 p) =
    -(∫ p, star (productPartial φ i 2 p) * productWeightedValue f i p) at h
  calc
    _ = -(-(∫ p, star (productPartial φ i 2 p) * productWeightedValue f i p)) := (neg_neg _).symm
    _ = _ := congrArg Neg.neg h.symm

theorem product_hardy_left_density {f : ProductSpace ι → ℂ}
    (hsupp : tsupport f ⊆ productUpper ι) (i : ι) (p : ProductSpace ι) :
    productComplexDensity p * (star (productVertical f i p) * f p) =
      star (productPartial f i 2 p) * productWeightedValue f i p := by
  by_cases hp : p ∈ tsupport f
  · rw [productComplexDensity_factor p i]
    simp only [productVertical, productWeightedValue, map_mul, Complex.star_def, Complex.conj_ofReal]
    field_simp [Complex.ofReal_ne_zero.mpr (productUpper_pos (hsupp hp) i).ne']
  · have hz : f p = 0 := image_eq_zero_of_notMem_tsupport hp
    simp only [hz, mul_zero, productWeightedValue, zero_div]

theorem product_hardy_right_density {f : ProductSpace ι → ℂ}
    (hf : ContDiff ℝ 1 f) (hsupp : tsupport f ⊆ productUpper ι) (i : ι) (p : ProductSpace ι) :
    productComplexDensity p * (star (f p) * (productVertical f i p - 2 * f p)) =
      star (f p) * productPartial (productWeightedValue f i) i 2 p := by
  by_cases hp : p ∈ tsupport f
  · rw [productWeightedValue_divergence hf.contDiffAt (hsupp hp) i]
    ring
  · have hz : f p = 0 := image_eq_zero_of_notMem_tsupport hp
    simp only [hz, star_zero, zero_mul, mul_zero]

end
end ArtinMatthews.SourceHyperbolicGreen

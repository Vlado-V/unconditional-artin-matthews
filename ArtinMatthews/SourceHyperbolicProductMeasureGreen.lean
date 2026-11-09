module

public import ArtinMatthews.SourceHyperbolicProductGreen


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory Filter
open scoped Topology ContDiff BigOperators ENNReal Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem productDensity_lt_top (p : ProductSpace ι) : productDensity p < ⊤ :=
  ENNReal.prod_lt_top (fun _ _ => ENNReal.ofReal_lt_top)

theorem productDensity_toReal_complex {p : ProductSpace ι} (hp : p ∈ productUpper ι) :
    ((productDensity p).toReal : ℂ) = productComplexDensity p := by
  simp only [productDensity, ENNReal.toReal_prod, Complex.ofReal_prod, productComplexDensity]
  apply Finset.prod_congr rfl
  intro i _
  rw [hyperbolicDensity, ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg (productUpper_pos hp i).le 3))]
  simp only [Complex.ofReal_inv, Complex.ofReal_pow]

theorem product_density_integrable {G : ProductSpace ι → ℂ}
    (hG : Integrable (fun p => productComplexDensity p * G p) volume) :
    Integrable G (productVolume ι) := by
  rw [productVolume_eq_density]
  apply (integrable_withDensity_iff_integrable_smul' (productDensity_measurable ι)
    (Eventually.of_forall productDensity_lt_top)).2
  apply (hG.mono_measure Measure.restrict_le_self).congr
  filter_upwards [ae_restrict_mem (productUpper_isOpen ι).measurableSet] with p hp
  rw [Complex.real_smul, productDensity_toReal_complex hp]

theorem product_density_integral_restrict (G : ProductSpace ι → ℂ) :
    (∫ p, G p ∂productVolume ι) =
      ∫ p in productUpper ι, productComplexDensity p * G p := by
  rw [productVolume_eq_density,
    integral_withDensity_eq_integral_toReal_smul (productDensity_measurable ι)
      (Eventually.of_forall productDensity_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (productUpper_isOpen ι).measurableSet] with p hp
  rw [Complex.real_smul, productDensity_toReal_complex hp]

theorem product_density_integral (G : ProductSpace ι → ℂ)
    (hG : ∀ p ∉ productUpper ι, G p=0) :
    (∫ p, G p ∂productVolume ι) = ∫ p, productComplexDensity p * G p := by
  rw [product_density_integral_restrict]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  rw [hG p hp, mul_zero]

theorem productGradientPair_zero_outside {φ : ProductSpace ι → ℂ}
    (hsupp : tsupport φ ⊆ productUpper ι) (f : ProductSpace ι → ℂ)
    (p : ProductSpace ι) (hp : p ∉ productUpper ι) : productGradientPair φ f p=0 := by
  have hn : p ∉ tsupport φ := fun h => hp (hsupp h)
  have hz (i : ι) (j : Fin 3) : productPartial φ i j p=0 := by
    rw [productPartial, fderiv_of_notMem_tsupport ℝ hn]
    rfl
  simp only [productGradientPair, hz, star_zero, zero_mul, Finset.sum_const_zero, mul_zero]

theorem productPairDensity_zero_outside {φ : ProductSpace ι → ℂ}
    (hsupp : tsupport φ ⊆ productUpper ι) (f : ProductSpace ι → ℂ)
    (p : ProductSpace ι) (hp : p ∉ productUpper ι) : productPairDensity φ f p=0 := by
  have hn : p ∉ tsupport φ := fun h => hp (hsupp h)
  have hz (i : ι) (j : Fin 3) : productPartial φ i j p=0 := by
    rw [productPartial, fderiv_of_notMem_tsupport ℝ hn]
    rfl
  simp only [productPairDensity, hz, star_zero, zero_mul, Finset.sum_const_zero]

theorem productGradientPair_density_all {φ f : ProductSpace ι → ℂ}
    (hsupp : tsupport φ ⊆ productUpper ι) (p : ProductSpace ι) :
    productComplexDensity p * productGradientPair φ f p = productPairDensity φ f p := by
  by_cases hp : p ∈ productUpper ι
  · exact productGradientPair_density hp
  · rw [productGradientPair_zero_outside hsupp f p hp,
      productPairDensity_zero_outside hsupp f p hp, mul_zero]

theorem productGradientPair_integrable {f φ : ProductSpace ι → ℂ}
    (hf : ∀ p ∈ productUpper ι, ContDiffAt ℝ 2 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    Integrable (productGradientPair φ f) (productVolume ι) := by
  apply product_density_integrable
  simpa only [productGradientPair_density_all hsupp] using
    product_pairDensity_integrable hf hφ hc hsupp

theorem product_tested_laplacian_integrable_hyperbolic {f φ : ProductSpace ι → ℂ}
    (hf : ∀ p ∈ productUpper ι, ContDiffAt ℝ 2 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    Integrable (fun p => star (φ p) * productLaplacian f p) (productVolume ι) := by
  apply product_density_integrable
  convert product_tested_laplacian_integrable hf hφ hc hsupp using 1
  ext p
  ring

theorem product_green_hyperbolic {f φ : ProductSpace ι → ℂ}
    (hf : ∀ p ∈ productUpper ι, ContDiffAt ℝ 2 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    (∫ p, productGradientPair φ f p ∂productVolume ι) =
      ∫ p, star (φ p) * productLaplacian f p ∂productVolume ι := by
  rw [product_density_integral _ (productGradientPair_zero_outside hsupp f)]
  rw [product_density_integral _ (fun p hp => by
    have hz : φ p=0 := image_eq_zero_of_notMem_tsupport (fun h => hp (hsupp h))
    rw [hz, star_zero, zero_mul])]
  simp_rw [productGradientPair_density_all hsupp]
  convert product_green_euclidean hf hφ hc hsupp using 1
  congr 1
  ext p
  ring

theorem product_test_contDiff_of_contDiffOn {φ : ProductSpace ι → ℂ}
    (hφ : ContDiffOn ℝ 2 φ (productUpper ι))
    (hsupp : tsupport φ ⊆ productUpper ι) : ContDiff ℝ 2 φ := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ productUpper ι
  · exact (hφ p hp).contDiffAt ((productUpper_isOpen ι).mem_nhds hp)
  · have hn : p ∉ tsupport φ := fun h => hp (hsupp h)
    exact (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : ProductSpace ι => (0 : ℂ)) p).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hn)

theorem product_green_hyperbolic_on {f φ : ProductSpace ι → ℂ}
    (hf : ContDiffOn ℝ 2 f (productUpper ι))
    (hφ : ContDiffOn ℝ 2 φ (productUpper ι)) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    (∫ p, productGradientPair φ f p ∂productVolume ι) =
      ∫ p, star (φ p) * productLaplacian f p ∂productVolume ι := by
  apply product_green_hyperbolic _ (product_test_contDiff_of_contDiffOn hφ hsupp) hc hsupp
  intro p hp
  exact (hf p hp).contDiffAt ((productUpper_isOpen ι).mem_nhds hp)

end
end ArtinMatthews.SourceHyperbolicGreen

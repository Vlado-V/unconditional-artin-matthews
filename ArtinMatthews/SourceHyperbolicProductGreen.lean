module

public import ArtinMatthews.SourceHyperbolicProductCalculus
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory Filter
open scoped Topology ContDiff BigOperators Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

def productComplexDensity (p : ProductSpace ι) : ℂ :=
  ∏ i, ((p i 2 : ℂ)^3)⁻¹

def blockLaplacian (f : ProductSpace ι → ℂ) (i : ι) (p : ProductSpace ι) : ℂ :=
  -(p i 2 : ℂ)^2 * (∑ j : Fin 3, productPartial (productPartial f i j) i j p) +
    (p i 2 : ℂ) * productPartial f i 2 p

def productLaplacian (f : ProductSpace ι → ℂ) (p : ProductSpace ι) : ℂ :=
  ∑ i, blockLaplacian f i p

def blockWeightedDivergence (f : ProductSpace ι → ℂ) (i : ι) (p : ProductSpace ι) : ℂ :=
  -∑ j : Fin 3, productPartial (productWeightedPartial f i j) i j p

def productPairDensity (φ f : ProductSpace ι → ℂ) (p : ProductSpace ι) : ℂ :=
  ∑ i, ∑ j : Fin 3, star (productPartial φ i j p) * productWeightedPartial f i j p

def productGradientPair (φ f : ProductSpace ι → ℂ) (p : ProductSpace ι) : ℂ :=
  ∑ i, (p i 2 : ℂ)^2 * (∑ j : Fin 3, star (productPartial φ i j p) * productPartial f i j p)

theorem productComplexDensity_factor (p : ProductSpace ι) (i : ι) :
    productComplexDensity p = otherWeight i p * ((p i 2 : ℂ)^3)⁻¹ := by
  exact (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm

theorem blockWeightedDivergence_eq {f : ProductSpace ι → ℂ} {p : ProductSpace ι}
    (hf : ContDiffAt ℝ 2 f p) (hp : p ∈ productUpper ι) (i : ι) :
    blockWeightedDivergence f i p = productComplexDensity p * blockLaplacian f i p := by
  have hd (j : Fin 3) := productWeightedPartial_derivative hf hp i j
  simp only [blockWeightedDivergence, Fin.sum_univ_three]
  rw [hd 0, hd 1, hd 2, productComplexDensity_factor p i]
  simp only [blockLaplacian, Fin.sum_univ_three]
  norm_num [euclideanCoordinateVector]
  field_simp [Complex.ofReal_ne_zero.mpr (productUpper_pos hp i).ne']
  ring

theorem productGradientPair_density {φ f : ProductSpace ι → ℂ} {p : ProductSpace ι}
    (hp : p ∈ productUpper ι) :
    productComplexDensity p * productGradientPair φ f p = productPairDensity φ f p := by
  simp only [productGradientPair, productPairDensity, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [productComplexDensity_factor p i]
  simp only [productWeightedPartial]
  apply Finset.sum_congr rfl
  intro j _
  field_simp [Complex.ofReal_ne_zero.mpr (productUpper_pos hp i).ne']

theorem product_compact_mul_integrable {φ F : ProductSpace ι → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hF : ∀ p ∈ tsupport φ, ContinuousAt F p) :
    Integrable (fun p => φ p * F p) volume := by
  have hprod : Continuous (fun p => φ p * F p) := by
    apply continuous_of_tsupport
    intro p hp
    exact hφ.continuousAt.mul (hF p (tsupport_mul_subset_left hp))
  exact hprod.integrable_of_hasCompactSupport hc.mul_right

theorem product_compact_star_mul_integrable {φ F : ProductSpace ι → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hF : ∀ p ∈ tsupport φ, ContinuousAt F p) :
    Integrable (fun p => star (φ p) * F p) volume := by
  have hs : tsupport (fun p => star (φ p)) = tsupport φ := by
    unfold tsupport
    congr 1
    ext p
    simp only [Function.mem_support, star_ne_zero]
  apply product_compact_mul_integrable hφ.star
  · change IsCompact (tsupport (fun p => star (φ p)))
    rwa [hs]
  · intro p hp
    exact hF p (hs ▸ hp)

theorem product_test_partial_continuous {φ : ProductSpace ι → ℂ}
    (hφ : ContDiff ℝ 2 φ) (i : ι) (j : Fin 3) : Continuous (productPartial φ i j) :=
  ((hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).continuous

omit [Fintype ι] in
theorem product_test_partial_compact {φ : ProductSpace ι → ℂ}
    (hc : HasCompactSupport φ) (i : ι) (j : Fin 3) :
    HasCompactSupport (productPartial φ i j) := hc.fderiv_apply ℝ (productDirection i j)

omit [Fintype ι] in
theorem product_test_partial_support {φ : ProductSpace ι → ℂ} (i : ι) (j : Fin 3) :
    tsupport (productPartial φ i j) ⊆ tsupport φ :=
  tsupport_fderiv_apply_subset ℝ (productDirection i j)

theorem product_flux_derivative_continuousAt {f : ProductSpace ι → ℂ} {p : ProductSpace ι}
    (hf : ContDiffAt ℝ 2 f p) (hp : p ∈ productUpper ι) (i : ι) (j : Fin 3) :
    ContinuousAt (productPartial (productWeightedPartial f i j) i j) p :=
  (((productWeightedPartial_contDiffAt hf hp i j).fderiv_right (m := 0) (by norm_num)).clm_apply
    contDiffAt_const).continuousAt

theorem product_green_direction {f φ : ProductSpace ι → ℂ}
    (hf : ∀ p ∈ productUpper ι, ContDiffAt ℝ 2 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) (i : ι) (j : Fin 3) :
    (∫ p, star (productPartial φ i j p) * productWeightedPartial f i j p) =
      -(∫ p, star (φ p) * productPartial (productWeightedPartial f i j) i j p) := by
  have h₁ : Integrable (fun p => star (productPartial φ i j p) * productWeightedPartial f i j p) volume := by
    apply product_compact_star_mul_integrable (product_test_partial_continuous hφ i j)
      (product_test_partial_compact hc i j)
    intro p hp
    have hh := hsupp (product_test_partial_support i j hp)
    exact (productWeightedPartial_contDiffAt (hf p hh) hh i j).continuousAt
  have h₂ : Integrable (fun p => star (φ p) * productPartial (productWeightedPartial f i j) i j p) volume := by
    apply product_compact_star_mul_integrable hφ.continuous hc
    intro p hp
    have hh := hsupp hp
    exact product_flux_derivative_continuousAt (hf p hh) hh i j
  have h₃ : Integrable (fun p => star (φ p) * productWeightedPartial f i j p) volume := by
    apply product_compact_star_mul_integrable hφ.continuous hc
    intro p hp
    have hh := hsupp hp
    exact (productWeightedPartial_contDiffAt (hf p hh) hh i j).continuousAt
  have h := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (μ := volume) (B := complexHermitianBilin) (f := φ) (g := productWeightedPartial f i j)
    (v := productDirection i j) h₁ h₂ h₃
    (fun p _ => hφ.contDiffAt.differentiableAt (by norm_num))
    (fun p hp => (productWeightedPartial_contDiffAt (hf p (hsupp hp)) (hsupp hp) i j).differentiableAt (by norm_num))
  change (∫ p, star (φ p) * productPartial (productWeightedPartial f i j) i j p) =
    -(∫ p, star (productPartial φ i j p) * productWeightedPartial f i j p) at h
  calc
    _ = -(-(∫ p, star (productPartial φ i j p) * productWeightedPartial f i j p)) := (neg_neg _).symm
    _ = _ := congrArg Neg.neg h.symm

theorem product_pairDensity_integrable {f φ : ProductSpace ι → ℂ}
    (hf : ∀ p ∈ productUpper ι, ContDiffAt ℝ 2 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) : Integrable (productPairDensity φ f) volume := by
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  apply product_compact_star_mul_integrable (product_test_partial_continuous hφ i j)
    (product_test_partial_compact hc i j)
  intro p hp
  have hh := hsupp (product_test_partial_support i j hp)
  exact (productWeightedPartial_contDiffAt (hf p hh) hh i j).continuousAt

theorem product_tested_laplacian_integrable {f φ : ProductSpace ι → ℂ}
    (hf : ∀ p ∈ productUpper ι, ContDiffAt ℝ 2 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    Integrable (fun p => star (φ p) * (productComplexDensity p * productLaplacian f p)) volume := by
  have hJ (i : ι) (j : Fin 3) :
      Integrable (fun p => star (φ p) * productPartial (productWeightedPartial f i j) i j p) volume := by
    apply product_compact_star_mul_integrable hφ.continuous hc
    intro p hp
    exact product_flux_derivative_continuousAt (hf p (hsupp hp)) (hsupp hp) i j
  apply ((integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hJ i j))).neg).congr
  exact Filter.Eventually.of_forall fun p => by
    change -(∑ i, ∑ j : Fin 3, star (φ p) * productPartial (productWeightedPartial f i j) i j p) = _
    by_cases hp : p ∈ tsupport φ
    · simp only [productLaplacian, Finset.mul_sum]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← blockWeightedDivergence_eq (hf p (hsupp hp)) (hsupp hp) i]
      simp only [blockWeightedDivergence, mul_neg, Finset.mul_sum]
    · have hz : φ p=0 := image_eq_zero_of_notMem_tsupport hp
      simp only [hz, star_zero, zero_mul, Finset.sum_const_zero, neg_zero]

theorem product_green_euclidean {f φ : ProductSpace ι → ℂ}
    (hf : ∀ p ∈ productUpper ι, ContDiffAt ℝ 2 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    (∫ p, productPairDensity φ f p) =
      ∫ p, star (φ p) * (productComplexDensity p * productLaplacian f p) := by
  have hI (i : ι) (j : Fin 3) :
      Integrable (fun p => star (productPartial φ i j p) * productWeightedPartial f i j p) volume := by
    apply product_compact_star_mul_integrable (product_test_partial_continuous hφ i j)
      (product_test_partial_compact hc i j)
    intro p hp
    have hh := hsupp (product_test_partial_support i j hp)
    exact (productWeightedPartial_contDiffAt (hf p hh) hh i j).continuousAt
  have hJ (i : ι) (j : Fin 3) :
      Integrable (fun p => star (φ p) * productPartial (productWeightedPartial f i j) i j p) volume := by
    apply product_compact_star_mul_integrable hφ.continuous hc
    intro p hp
    exact product_flux_derivative_continuousAt (hf p (hsupp hp)) (hsupp hp) i j
  have he : (fun p => -(∑ i, ∑ j : Fin 3,
      star (φ p) * productPartial (productWeightedPartial f i j) i j p)) =
      fun p => star (φ p) * (productComplexDensity p * productLaplacian f p) := by
    funext p
    by_cases hp : p ∈ tsupport φ
    · simp only [productLaplacian, Finset.mul_sum]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← blockWeightedDivergence_eq (hf p (hsupp hp)) (hsupp hp) i]
      simp only [blockWeightedDivergence, mul_neg, Finset.mul_sum]
    · have hz : φ p=0 := image_eq_zero_of_notMem_tsupport hp
      simp only [hz, star_zero, zero_mul, Finset.sum_const_zero, neg_zero]
  calc
    _ = ∑ i, ∑ j : Fin 3, ∫ p, star (productPartial φ i j p) * productWeightedPartial f i j p := by
      simp only [productPairDensity]
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hI i j))]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum _ (fun j _ => hI i j)
    _ = -(∑ i, ∑ j : Fin 3, ∫ p, star (φ p) * productPartial (productWeightedPartial f i j) i j p) := by
      simp only [product_green_direction hf hφ hc hsupp, Finset.sum_neg_distrib]
    _ = ∫ p, -(∑ i, ∑ j : Fin 3, star (φ p) * productPartial (productWeightedPartial f i j) i j p) := by
      rw [integral_neg, integral_finsetSum _ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hJ i j))]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_finsetSum _ (fun j _ => hJ i j)).symm
    _ = _ := by rw [he]

end
end ArtinMatthews.SourceHyperbolicGreen

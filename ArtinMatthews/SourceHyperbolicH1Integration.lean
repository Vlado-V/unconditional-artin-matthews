module

public import ArtinMatthews.SourceHyperbolicH1AdjointCalculus
public import ArtinMatthews.SourceHyperbolicH1Gradient
public import ArtinMatthews.SourceHyperbolicProductMeasureGreen
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory Filter
open scoped Topology ContDiff BigOperators Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem h1WeightedValue_ibp (φ f : h1Tests ι 2) (i : ι) (j : Fin 3) :
    (∫ p, star (productWeightedValue φ.val i p) * productPartial f.val i j p) =
      -(∫ p, star (productPartial (productWeightedValue φ.val i) i j p) * f.val p) := by
  have hW := h1WeightedValue_contDiff φ i
  have hcW := h1WeightedValue_compact φ i
  have hDW : Continuous (productPartial (productWeightedValue φ.val i) i j) :=
    ((hW.fderiv_right (m := 0) (by norm_num)).clm_apply contDiff_const).continuous
  have h₁ : Integrable (fun p => star (productPartial (productWeightedValue φ.val i) i j p) * f.val p) volume := by
    exact product_compact_star_mul_integrable hDW (product_test_partial_compact hcW i j)
      (fun _ _ => f.prop.1.continuous.continuousAt)
  have h₂ : Integrable (fun p => star (productWeightedValue φ.val i p) * productPartial f.val i j p) volume := by
    exact product_compact_star_mul_integrable hW.continuous hcW
      (fun _ _ => (product_test_partial_continuous f.prop.1 i j).continuousAt)
  have h₃ : Integrable (fun p => star (productWeightedValue φ.val i p) * f.val p) volume := by
    exact product_compact_star_mul_integrable hW.continuous hcW
      (fun _ _ => f.prop.1.continuous.continuousAt)
  exact integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (μ := volume) (B := complexHermitianBilin) (f := productWeightedValue φ.val i) (g := f.val)
    (v := productDirection i j) h₁ h₂ h₃
    (fun _ _ => hW.contDiffAt.differentiableAt (by norm_num))
    (fun _ _ => f.prop.1.contDiffAt.differentiableAt (by norm_num))

theorem h1WeightedValue_eq_density {φ : ProductSpace ι → ℂ} {p : ProductSpace ι}
    (hp : p ∈ productUpper ι) (i : ι) :
    productWeightedValue φ i p = productComplexDensity p * (p i 2 : ℂ) * φ p := by
  rw [productComplexDensity_factor p i]
  unfold productWeightedValue
  field_simp [Complex.ofReal_ne_zero.mpr (productUpper_pos hp i).ne']

theorem h1_density_star {p : ProductSpace ι} (hp : p ∈ productUpper ι) :
    star (productComplexDensity p) = productComplexDensity p := by
  rw [← productDensity_toReal_complex hp]
  simp

theorem h1_left_density (φ f : h1Tests ι 2) (i : ι) (j : Fin 3) (p : ProductSpace ι) :
    productComplexDensity p * (star (φ.val p) * h1Coordinate f.val i j p) =
      star (productWeightedValue φ.val i p) * productPartial f.val i j p := by
  by_cases hp : p ∈ productUpper ι
  · rw [h1WeightedValue_eq_density hp i]
    have hy : star (p i 2 : ℂ) = (p i 2 : ℂ) := by simp
    simp only [h1Coordinate,star_mul,h1_density_star hp,hy]
    ring
  · have hz : φ.val p=0 := image_eq_zero_of_notMem_tsupport (fun h => hp (φ.prop.2.2 h))
    simp only [hz,star_zero,zero_mul,mul_zero,productWeightedValue,zero_div]

theorem h1_right_density (φ f : h1Tests ι 2) (i : ι) (j : Fin 3) (p : ProductSpace ι) :
    productComplexDensity p * (star (h1CoordinateAdjoint φ.val i j p) * f.val p) =
      -star (productPartial (productWeightedValue φ.val i) i j p) * f.val p := by
  by_cases hp : p ∈ productUpper ι
  · rw [h1WeightedValue_derivative (φ.prop.1.of_le (by norm_num)).contDiffAt hp i j]
    simp only [star_neg,star_mul,h1_density_star hp,neg_neg]
    ring
  · have hn : p ∉ tsupport φ.val := fun h => hp (φ.prop.2.2 h)
    have ha : h1CoordinateAdjoint φ.val i j p = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hn (h1CoordinateAdjoint_support φ.val i j h))
    have hd : productPartial (productWeightedValue φ.val i) i j p = 0 := by
      rw [productPartial,fderiv_of_notMem_tsupport ℝ (fun h => hn (h1WeightedValue_support φ.val i h))]
      rfl
    simp only [ha,hd,star_zero,zero_mul,mul_zero,neg_zero]

theorem h1_first_order_green (φ f : h1Tests ι 2) (i : ι) (j : Fin 3) :
    (∫ p, star (φ.val p) * h1Coordinate f.val i j p ∂productVolume ι) =
      ∫ p, star (h1CoordinateAdjoint φ.val i j p) * f.val p ∂productVolume ι := by
  have hL := product_density_integral (fun p => star (φ.val p) * h1Coordinate f.val i j p)
    (fun p hp => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hp (φ.prop.2.2 h)),star_zero,zero_mul])
  have hR := product_density_integral (fun p => star (h1CoordinateAdjoint φ.val i j p) * f.val p)
    (fun p hp => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hp (φ.prop.2.2 (h1CoordinateAdjoint_support φ.val i j h))),star_zero,zero_mul])
  rw [hL,hR]
  simp_rw [h1_left_density φ f i j,h1_right_density φ f i j,neg_mul]
  rw [integral_neg]
  exact h1WeightedValue_ibp φ f i j

theorem h1_first_order_inner (φ f : h1Tests ι 2) (i : ι) (j : Fin 3) :
    inner ℂ (h1TestMass φ) (h1GradientComponent (i,j) (h1TestGradient f)) =
      inner ℂ (h1TestMass (h1AdjointTest φ i j)) (h1TestMass f) := by
  rw [h1TestMass_inner,h1TestMass_inner]
  have hleft : (∫ p, star (φ.val p) * h1GradientComponent (i,j) (h1TestGradient f) p ∂productVolume ι) =
      ∫ p, star (φ.val p) * h1Coordinate f.val i j p ∂productVolume ι := by
    apply integral_congr_ae
    filter_upwards [h1GradientComponent_test f (i,j)] with p hp
    rw [hp]
    rfl
  rw [hleft,h1_first_order_green]
  apply integral_congr_ae
  filter_upwards [h1TestMass_coe f] with p hp
  rw [hp]
  rfl

end
end ArtinMatthews.SourceHyperbolicGreen

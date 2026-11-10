module

public import ArtinMatthews.SourceArchProductCasimir
public import ArtinMatthews.SourceHyperbolicProductGreen
public import ArtinMatthews.SourceHyperbolicH1Measure
public import ArtinMatthews.SourceHyperbolicProductAdjointCalculus
public import ArtinMatthews.SourceHyperbolicProductAdjointGreen
public import ArtinMatthews.SourceHyperbolicProductMeasureGreen
public import ArtinMatthews.SourceHyperbolicProductSlices
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory Filter
open scoped Topology ContDiff BigOperators Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem productPartial_continuousAt_C1 {f : ProductSpace ι → ℂ} {p : ProductSpace ι}
    (hf : ContDiffAt ℝ 1 f p) (i : ι) (j : Fin 3) :
    ContinuousAt (productPartial f i j) p :=
  ((hf.fderiv_right (m := 0) (by norm_num)).clm_apply contDiffAt_const).continuousAt

theorem product_adjoint_direction_C1 {φ f : ProductSpace ι → ℂ}
    (hf : ∀ p ∈ productUpper ι, ContDiffAt ℝ 1 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) (i : ι) (j : Fin 3) :
    (∫ p, star (productWeightedPartial φ i j p) * productPartial f i j p) =
      -(∫ p, star (productPartial (productWeightedPartial φ i j) i j p) * f p) := by
  have hW := productWeightedPartial_contDiff hφ hsupp i j
  have hcW := productWeightedPartial_compact hc i j
  have h₁ : Integrable (fun p => star (productPartial (productWeightedPartial φ i j) i j p) * f p) volume := by
    apply product_compact_star_mul_integrable (productWeightedPartial_second_continuous hφ hsupp i j)
      (product_test_partial_compact hcW i j)
    intro p hp
    exact (hf p (hsupp (productWeightedPartial_second_support i j hp))).continuousAt
  have h₂ : Integrable (fun p => star (productWeightedPartial φ i j p) * productPartial f i j p) volume := by
    apply product_compact_star_mul_integrable hW.continuous hcW
    intro p hp
    exact productPartial_continuousAt_C1 (hf p (hsupp (productWeightedPartial_support i j hp))) i j
  have h₃ : Integrable (fun p => star (productWeightedPartial φ i j p) * f p) volume := by
    apply product_compact_star_mul_integrable hW.continuous hcW
    intro p hp
    exact (hf p (hsupp (productWeightedPartial_support i j hp))).continuousAt
  exact integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (μ := volume) (B := complexHermitianBilin) (f := productWeightedPartial φ i j) (g := f)
    (v := productDirection i j) h₁ h₂ h₃
    (fun _ _ => hW.contDiffAt.differentiableAt (by norm_num))
    (fun p hp => (hf p (hsupp (productWeightedPartial_support i j hp))).differentiableAt (by norm_num))

theorem product_adjoint_euclidean_C1 {φ f : ProductSpace ι → ℂ}
    (hf : ∀ p ∈ productUpper ι, ContDiffAt ℝ 1 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    (∫ p, productPairDensity φ f p) =
      ∫ p, productComplexDensity p * (star (productLaplacian φ p) * f p) := by
  have hI (i : ι) (j : Fin 3) :
      Integrable (fun p => star (productWeightedPartial φ i j p) * productPartial f i j p) volume := by
    apply product_compact_star_mul_integrable (productWeightedPartial_contDiff hφ hsupp i j).continuous
      (productWeightedPartial_compact hc i j)
    intro p hp
    exact productPartial_continuousAt_C1 (hf p (hsupp (productWeightedPartial_support i j hp))) i j
  have hJ (i : ι) (j : Fin 3) :
      Integrable (fun p => star (productPartial (productWeightedPartial φ i j) i j p) * f p) volume := by
    apply product_compact_star_mul_integrable (productWeightedPartial_second_continuous hφ hsupp i j)
      (product_test_partial_compact (productWeightedPartial_compact hc i j) i j)
    intro p hp
    exact (hf p (hsupp (productWeightedPartial_second_support i j hp))).continuousAt
  calc
    _ = ∫ p, ∑ i, ∑ j : Fin 3, star (productWeightedPartial φ i j p) * productPartial f i j p := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by
        simp only [productPairDensity,productWeightedPartial_star_pair]
    _ = ∑ i, ∑ j : Fin 3, ∫ p, star (productWeightedPartial φ i j p) * productPartial f i j p := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hI i j))]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum _ (fun j _ => hI i j)
    _ = -(∑ i, ∑ j : Fin 3, ∫ p, star (productPartial (productWeightedPartial φ i j) i j p) * f p) := by
      simp only [product_adjoint_direction_C1 hf hφ hc hsupp,Finset.sum_neg_distrib]
    _ = ∫ p, -(∑ i, ∑ j : Fin 3, star (productPartial (productWeightedPartial φ i j) i j p) * f p) := by
      rw [integral_neg,integral_finsetSum _ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hJ i j))]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_finsetSum _ (fun j _ => hJ i j)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (product_adjoint_density_eq hφ hsupp)

theorem productGradientPair_integrable_C1 {φ f : ProductSpace ι → ℂ}
    (hf : ∀ p ∈ productUpper ι, ContDiffAt ℝ 1 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    Integrable (productGradientPair φ f) (productVolume ι) := by
  apply product_density_integrable
  simp_rw [productGradientPair_density_all hsupp]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  have h : Integrable (fun p => star (productWeightedPartial φ i j p) * productPartial f i j p) volume := by
    apply product_compact_star_mul_integrable (productWeightedPartial_contDiff hφ hsupp i j).continuous
      (productWeightedPartial_compact hc i j)
    intro p hp
    exact productPartial_continuousAt_C1 (hf p (hsupp (productWeightedPartial_support i j hp))) i j
  simpa only [productWeightedPartial_star_pair] using h

theorem product_native_adjoint_integrable_C1 {φ f : ProductSpace ι → ℂ}
    (hf : ∀ p ∈ productUpper ι, ContDiffAt ℝ 1 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    Integrable (fun p => star (SourceArchJacquet.sourceArchProductCoordinateLaplacian φ p) * f p)
      (productVolume ι) := by
  have hJ (i : ι) (j : Fin 3) :
      Integrable (fun p => star (productPartial (productWeightedPartial φ i j) i j p) * f p) volume := by
    apply product_compact_star_mul_integrable (productWeightedPartial_second_continuous hφ hsupp i j)
      (product_test_partial_compact (productWeightedPartial_compact hc i j) i j)
    intro p hp
    exact (hf p (hsupp (productWeightedPartial_second_support i j hp))).continuousAt
  have hD : Integrable (fun p => productComplexDensity p * (star (productLaplacian φ p) * f p)) volume := by
    apply ((integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hJ i j))).neg).congr
    exact Filter.Eventually.of_forall fun p => by
      change -(∑ i, ∑ j : Fin 3, star (productPartial (productWeightedPartial φ i j) i j p) * f p) = _
      exact product_adjoint_density_eq hφ hsupp p
  apply (product_density_integrable hD).congr
  filter_upwards [productVolume_ae_upper (ι := ι)] with p hp
  rw [productLaplacian_eq_native (fun _ _ => hφ.contDiffAt) hp]

theorem product_native_gradient_green_C1 {φ f : ProductSpace ι → ℂ}
    (hf : ∀ p ∈ productUpper ι, ContDiffAt ℝ 1 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    (∫ p, productGradientPair φ f p ∂productVolume ι) =
      ∫ p, star (SourceArchJacquet.sourceArchProductCoordinateLaplacian φ p) * f p ∂productVolume ι := by
  calc
    _ = ∫ p, productPairDensity φ f p := by
      rw [product_density_integral _ (productGradientPair_zero_outside hsupp f)]
      simp_rw [productGradientPair_density_all hsupp]
    _ = ∫ p, productComplexDensity p * (star (productLaplacian φ p) * f p) :=
      product_adjoint_euclidean_C1 hf hφ hc hsupp
    _ = ∫ p, star (productLaplacian φ p) * f p ∂productVolume ι := by
      symm
      apply product_density_integral
      intro p hp
      have hn : p ∉ tsupport φ := fun h => hp (hsupp h)
      rw [productLaplacian_zero_notMem_tsupport hn,star_zero,zero_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [productVolume_ae_upper (ι := ι)] with p hp
      rw [productLaplacian_eq_native (fun _ _ => hφ.contDiffAt) hp]

theorem product_native_gradient_green_C1_on {φ f : ProductSpace ι → ℂ}
    (hf : ContDiffOn ℝ 1 f (productUpper ι))
    (hφ : ContDiffOn ℝ 2 φ (productUpper ι)) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    (∫ p, productGradientPair φ f p ∂productVolume ι) =
      ∫ p, star (SourceArchJacquet.sourceArchProductCoordinateLaplacian φ p) * f p ∂productVolume ι := by
  apply product_native_gradient_green_C1 _ (product_test_contDiff_of_contDiffOn hφ hsupp) hc hsupp
  intro p hp
  exact (hf p hp).contDiffAt ((productUpper_isOpen ι).mem_nhds hp)

end
end ArtinMatthews.SourceHyperbolicGreen

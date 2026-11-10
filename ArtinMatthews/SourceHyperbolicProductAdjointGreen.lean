module

public import ArtinMatthews.SourceArchProductCasimir
public import ArtinMatthews.SourceHyperbolicProductGreen
public import ArtinMatthews.SourceHyperbolicH1Measure
public import ArtinMatthews.SourceHyperbolicProductAdjointCalculus
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory Filter
open scoped Topology ContDiff BigOperators Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem productComplexDensity_star_of_mem {p : ProductSpace ι} (hp : p ∈ productUpper ι) :
    star (productComplexDensity p) = productComplexDensity p := by
  rw [← productDensity_toReal_complex hp]
  simp

theorem product_adjoint_density_eq {φ f : ProductSpace ι → ℂ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : tsupport φ ⊆ productUpper ι) (p : ProductSpace ι) :
    -(∑ i, ∑ j : Fin 3, star (productPartial (productWeightedPartial φ i j) i j p) * f p) =
      productComplexDensity p * (star (productLaplacian φ p) * f p) := by
  by_cases hp : p ∈ productUpper ι
  · have hsum : (∑ i, blockWeightedDivergence φ i p) =
        productComplexDensity p * productLaplacian φ p := by
      simp only [productLaplacian,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => blockWeightedDivergence_eq hφ.contDiffAt hp i)
    calc
      _ = star (∑ i, blockWeightedDivergence φ i p) * f p := by
        simp [blockWeightedDivergence,Finset.sum_mul,Finset.sum_neg_distrib]
      _ = _ := by
        rw [hsum]
        simp only [star_mul,productComplexDensity_star_of_mem hp]
        ring
  · have hn : p ∉ tsupport φ := fun h => hp (hsupp h)
    have hz (i : ι) (j : Fin 3) : productPartial (productWeightedPartial φ i j) i j p=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hn (productWeightedPartial_second_support i j h))
    simp only [hz,star_zero,zero_mul,Finset.sum_const_zero,neg_zero,
      productLaplacian_zero_notMem_tsupport hn,mul_zero]

theorem product_adjoint_density_integrable {φ f : ProductSpace ι → ℂ}
    (hf : ∀ p ∈ productUpper ι, ContDiffAt ℝ 2 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    Integrable (fun p => productComplexDensity p * (star (productLaplacian φ p) * f p)) volume := by
  have hJ (i : ι) (j : Fin 3) :
      Integrable (fun p => star (productPartial (productWeightedPartial φ i j) i j p) * f p) volume := by
    apply product_compact_star_mul_integrable (productWeightedPartial_second_continuous hφ hsupp i j)
      (product_test_partial_compact (productWeightedPartial_compact hc i j) i j)
    intro p hp
    exact (hf p (hsupp (productWeightedPartial_second_support i j hp))).continuousAt
  apply ((integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hJ i j))).neg).congr
  exact Filter.Eventually.of_forall fun p => by
    change -(∑ i, ∑ j : Fin 3, star (productPartial (productWeightedPartial φ i j) i j p) * f p) = _
    exact product_adjoint_density_eq hφ hsupp p

theorem product_adjoint_tested_laplacian_integrable {φ f : ProductSpace ι → ℂ}
    (hf : ∀ p ∈ productUpper ι, ContDiffAt ℝ 2 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    Integrable (fun p => star (productLaplacian φ p) * f p) (productVolume ι) :=
  product_density_integrable (product_adjoint_density_integrable hf hφ hc hsupp)

theorem product_adjoint_green_euclidean {φ f : ProductSpace ι → ℂ}
    (hf : ∀ p ∈ productUpper ι, ContDiffAt ℝ 2 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    (∫ p, productPairDensity φ f p) =
      ∫ p, productComplexDensity p * (star (productLaplacian φ p) * f p) := by
  have hI (i : ι) (j : Fin 3) :
      Integrable (fun p => star (productWeightedPartial φ i j p) * productPartial f i j p) volume := by
    apply product_compact_star_mul_integrable (productWeightedPartial_contDiff hφ hsupp i j).continuous
      (productWeightedPartial_compact hc i j)
    intro p hp
    exact (productPartial_contDiffAt (hf p (hsupp (productWeightedPartial_support i j hp))) i j).continuousAt
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
      simp only [product_adjoint_green_direction hf hφ hc hsupp,Finset.sum_neg_distrib]
    _ = ∫ p, -(∑ i, ∑ j : Fin 3, star (productPartial (productWeightedPartial φ i j) i j p) * f p) := by
      rw [integral_neg,integral_finsetSum _ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hJ i j))]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_finsetSum _ (fun j _ => hJ i j)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (product_adjoint_density_eq hφ hsupp)

theorem product_adjoint_green_hyperbolic {φ f : ProductSpace ι → ℂ}
    (hf : ∀ p ∈ productUpper ι, ContDiffAt ℝ 2 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    (∫ p, star (productLaplacian φ p) * f p ∂productVolume ι) =
      ∫ p, star (φ p) * productLaplacian f p ∂productVolume ι := by
  calc
    _ = ∫ p, productPairDensity φ f p := by
      rw [product_density_integral _ (fun p hp => by
        have hn : p ∉ tsupport φ := fun h => hp (hsupp h)
        rw [productLaplacian_zero_notMem_tsupport hn,star_zero,zero_mul])]
      exact (product_adjoint_green_euclidean hf hφ hc hsupp).symm
    _ = ∫ p, productGradientPair φ f p ∂productVolume ι := by
      rw [product_density_integral _ (productGradientPair_zero_outside hsupp f)]
      simp_rw [productGradientPair_density_all hsupp]
    _ = _ := product_green_hyperbolic hf hφ hc hsupp

theorem product_native_adjoint_tested_laplacian_integrable {φ f : ProductSpace ι → ℂ}
    (hf : ∀ p ∈ productUpper ι, ContDiffAt ℝ 2 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    Integrable (fun p => star (SourceArchJacquet.sourceArchProductCoordinateLaplacian φ p) * f p)
      (productVolume ι) := by
  apply (product_adjoint_tested_laplacian_integrable hf hφ hc hsupp).congr
  filter_upwards [productVolume_ae_upper (ι := ι)] with p hp
  rw [productLaplacian_eq_native (fun _ _ => hφ.contDiffAt) hp]

theorem product_native_adjoint_green {φ f : ProductSpace ι → ℂ}
    (hf : ∀ p ∈ productUpper ι, ContDiffAt ℝ 2 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    (∫ p, star (SourceArchJacquet.sourceArchProductCoordinateLaplacian φ p) * f p ∂productVolume ι) =
      ∫ p, star (φ p) * SourceArchJacquet.sourceArchProductCoordinateLaplacian f p ∂productVolume ι := by
  calc
    _ = ∫ p, star (productLaplacian φ p) * f p ∂productVolume ι := by
      apply integral_congr_ae
      filter_upwards [productVolume_ae_upper (ι := ι)] with p hp
      rw [productLaplacian_eq_native (fun _ _ => hφ.contDiffAt) hp]
    _ = ∫ p, star (φ p) * productLaplacian f p ∂productVolume ι :=
      product_adjoint_green_hyperbolic hf hφ hc hsupp
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [productVolume_ae_upper (ι := ι)] with p hp
      rw [productLaplacian_eq_native hf hp]

theorem product_native_adjoint_green_on {φ f : ProductSpace ι → ℂ}
    (hf : ContDiffOn ℝ 2 f (productUpper ι))
    (hφ : ContDiffOn ℝ 2 φ (productUpper ι)) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    (∫ p, star (SourceArchJacquet.sourceArchProductCoordinateLaplacian φ p) * f p ∂productVolume ι) =
      ∫ p, star (φ p) * SourceArchJacquet.sourceArchProductCoordinateLaplacian f p ∂productVolume ι := by
  apply product_native_adjoint_green _ (product_test_contDiff_of_contDiffOn hφ hsupp) hc hsupp
  intro p hp
  exact (hf p hp).contDiffAt ((productUpper_isOpen ι).mem_nhds hp)

end
end ArtinMatthews.SourceHyperbolicGreen

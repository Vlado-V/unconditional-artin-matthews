module

public import ArtinMatthews.SourceHyperbolicProductEnergy
public import ArtinMatthews.SourceHyperbolicHardy
public import ArtinMatthews.SLocalSourceComplements
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
open OAI.CubicEisenstein MeasureTheory
open scoped Topology ContDiff BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem productVerticalEnergy_le_gradientEnergy (f : ProductSpace ι → ℂ) (p : ProductSpace ι) :
    productVerticalEnergy f p ≤ productGradientEnergy f p := by
  unfold productVerticalEnergy productGradientEnergy
  apply Finset.sum_le_sum
  intro i _
  have hn : ‖productVertical f i p‖^2 = (p i 2)^2 * ‖productPartial f i 2 p‖^2 := by
    simp only [productVertical, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hn]
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (fun j _ => sq_nonneg ‖productPartial f i j p‖) (Finset.mem_univ 2))
    (sq_nonneg (p i 2))

theorem product_hardy_gradient_inequality {f : ProductSpace ι → ℂ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ productUpper ι) :
    (Fintype.card ι : ℝ) * (∫ p, ‖f p‖^2 ∂productVolume ι) ≤
      ∫ p, productGradientEnergy f p ∂productVolume ι := by
  have h1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  exact (product_hardy_inequality h1 hc hsupp).trans
    (integral_mono (productVerticalEnergy_integrable h1 hc hsupp)
      (productGradientEnergy_integrable hf hc hsupp) (productVerticalEnergy_le_gradientEnergy f))

end
end ArtinMatthews.SourceHyperbolicGreen

namespace ArtinMatthews
open NumberField OAI.CubicEisenstein MeasureTheory SourceHyperbolicGreen
open scoped NumberField Topology ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
include hζ

theorem source_numberField_hardy_gradient_inequality
    {f : (InfinitePlace K → EuclideanSpatial) → ℂ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ productUpper (InfinitePlace K)) :
    (InfinitePlace.nrComplexPlaces K : ℝ) *
        (∫ p, ‖f p‖^2 ∂productVolume (InfinitePlace K)) ≤
      ∫ p, productGradientEnergy f p ∂productVolume (InfinitePlace K) := by
  let : IsTotallyComplex K := source_isTotallyComplex K hζ
  have hcard : Fintype.card (InfinitePlace K) = InfinitePlace.nrComplexPlaces K := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  simpa only [hcard] using product_hardy_gradient_inequality hf hc hsupp

theorem source_numberField_gradient_one_sixth_coercive
    {f : (InfinitePlace K → EuclideanSpatial) → ℂ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ productUpper (InfinitePlace K)) :
    ((InfinitePlace.nrComplexPlaces K : ℝ) / 9) *
        (∫ p, ‖f p‖^2 ∂productVolume (InfinitePlace K)) ≤
      (∫ p, productGradientEnergy f p ∂productVolume (InfinitePlace K)) -
        ((InfinitePlace.nrComplexPlaces K : ℝ) * (1 - 4 * (1 / 6 : ℝ)^2)) *
          (∫ p, ‖f p‖^2 ∂productVolume (InfinitePlace K)) := by
  have h := source_numberField_hardy_gradient_inequality K hζ hf hc hsupp
  nlinarith

end
end ArtinMatthews

module

public import ArtinMatthews.SourceHyperbolicHardy
public import ArtinMatthews.SLocalSourceComplements
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

namespace ArtinMatthews
open NumberField OAI.CubicEisenstein MeasureTheory SourceHyperbolicGreen
open scoped NumberField Topology ContDiff BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
include hζ


theorem source_numberField_hardy_gap_pos :
    0 < (InfinitePlace.nrComplexPlaces K : ℝ) / 9 := by
  let : IsTotallyComplex K := source_isTotallyComplex K hζ
  have hcard : Fintype.card (InfinitePlace K) = InfinitePlace.nrComplexPlaces K := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  have h : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
  rw [hcard] at h
  exact div_pos (Nat.cast_pos.mpr h) (by norm_num)

theorem source_numberField_hardy_identity
    {f : (InfinitePlace K → EuclideanSpatial) → ℂ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ productUpper (InfinitePlace K)) :
    (∫ p, productVerticalEnergy f p ∂productVolume (InfinitePlace K)) =
      (InfinitePlace.nrComplexPlaces K : ℝ) *
        (∫ p, ‖f p‖^2 ∂productVolume (InfinitePlace K)) +
      ∫ p, productHardyRemainder f p ∂productVolume (InfinitePlace K) := by
  let : IsTotallyComplex K := source_isTotallyComplex K hζ
  have hcard : Fintype.card (InfinitePlace K) = InfinitePlace.nrComplexPlaces K := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  simpa only [hcard] using product_hardy_identity hf hc hsupp

theorem source_numberField_hardy_inequality
    {f : (InfinitePlace K → EuclideanSpatial) → ℂ}
    (hf : ContDiffOn ℝ 1 f (productUpper (InfinitePlace K)))
    (hc : HasCompactSupport f) (hsupp : tsupport f ⊆ productUpper (InfinitePlace K)) :
    (InfinitePlace.nrComplexPlaces K : ℝ) *
        (∫ p, ‖f p‖^2 ∂productVolume (InfinitePlace K)) ≤
      ∫ p, productVerticalEnergy f p ∂productVolume (InfinitePlace K) := by
  let : IsTotallyComplex K := source_isTotallyComplex K hζ
  have hcard : Fintype.card (InfinitePlace K) = InfinitePlace.nrComplexPlaces K := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  simpa only [hcard] using product_hardy_inequality_on hf hc hsupp

theorem source_numberField_radial_cross_real
    {f : (InfinitePlace K → EuclideanSpatial) → ℂ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ productUpper (InfinitePlace K)) :
    (∫ p, (star (f p) * productRadial f p).re ∂productVolume (InfinitePlace K)) =
      (InfinitePlace.nrComplexPlaces K : ℝ) *
        (∫ p, ‖f p‖^2 ∂productVolume (InfinitePlace K)) := by
  let : IsTotallyComplex K := source_isTotallyComplex K hζ
  have hcard : Fintype.card (InfinitePlace K) = InfinitePlace.nrComplexPlaces K := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  simpa only [hcard] using product_radial_cross_real hf hc hsupp


theorem source_numberField_hardy_shifted_identity
    {f : (InfinitePlace K → EuclideanSpatial) → ℂ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ productUpper (InfinitePlace K)) (spectralValue : ℝ) :
    (∫ p, productVerticalEnergy f p ∂productVolume (InfinitePlace K)) -
        spectralValue * (∫ p, ‖f p‖^2 ∂productVolume (InfinitePlace K)) =
      ((InfinitePlace.nrComplexPlaces K : ℝ) - spectralValue) *
        (∫ p, ‖f p‖^2 ∂productVolume (InfinitePlace K)) +
      ∫ p, productHardyRemainder f p ∂productVolume (InfinitePlace K) := by
  rw [source_numberField_hardy_identity K hζ hf hc hsupp]
  ring

theorem source_numberField_one_sixth_coercive
    {f : (InfinitePlace K → EuclideanSpatial) → ℂ}
    (hf : ContDiffOn ℝ 1 f (productUpper (InfinitePlace K)))
    (hc : HasCompactSupport f) (hsupp : tsupport f ⊆ productUpper (InfinitePlace K)) :
    ((InfinitePlace.nrComplexPlaces K : ℝ) / 9) *
        (∫ p, ‖f p‖^2 ∂productVolume (InfinitePlace K)) ≤
      (∫ p, productVerticalEnergy f p ∂productVolume (InfinitePlace K)) -
        ((InfinitePlace.nrComplexPlaces K : ℝ) * (1 - 4 * (1 / 6 : ℝ)^2)) *
          (∫ p, ‖f p‖^2 ∂productVolume (InfinitePlace K)) := by
  have h := source_numberField_hardy_inequality K hζ hf hc hsupp
  nlinarith

end
end ArtinMatthews

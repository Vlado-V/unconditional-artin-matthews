module

public import ArtinMatthews.SourceKPCuspFourierFactor
public import ArtinMatthews.SourceKPCuspUnitArchMoment
public import ArtinMatthews.SourceKPCuspCompactHeightMeasure
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

/-! Holomorphic full-dimensional height moments of the actual Fourier
profile, with the fixed nonzero unit-frequency normalization. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceArchJacquet
open scoped Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0)

theorem sourceKPCuspArchFourierProfile_continuousOn (m : Kˣ) {s : ℂ} (hs : 0 < s.re)
    (B : Set (InfinitePlace K → ℝ)) (hpos : ∀ y ∈ B, ∀ v, 0 < y v) :
    ContinuousOn (sourceKPTraceJacquetArchProfile K hζ m s) B := by
  classical
  intro y hy
  have hmap : Continuous (fun y : InfinitePlace K → ℝ => (s,y)) :=
    continuous_const.prodMk continuous_id
  exact ((sourceArchWeightedProduct_continuousAt
    (fun _ : InfinitePlace K => sourceArchTraceCharacter)
    (fun _ => sourceArchTraceCharacter_continuous)
    (fun _ x => (sourceArchTraceCharacter_norm x).le)
    (sourceKPTraceJacquetProfileFrequency K hζ m) (s,y) hs (hpos y hy)).comp
      (f := fun y : InfinitePlace K → ℝ => (s,y)) hmap.continuousAt).continuousWithinAt

include d hd in
theorem sourceKPCuspArchFourierProfile_integrableOn (m : Kˣ) {s : ℂ} (hs : 0 < s.re)
    (B : Set (InfinitePlace K → ℝ)) (hB : IsCompact B)
    (hpos : ∀ y ∈ B, ∀ v, 0 < y v) :
    IntegrableOn (sourceKPTraceJacquetArchProfile K hζ m s) B (sourceKPCuspProductHeightMeasure K) :=
  (sourceKPCuspArchFourierProfile_continuousOn K hζ m hs B hpos).integrableOn_of_subset_isCompact
    hB hB.measurableSet Set.Subset.rfl
    (sourceKPCuspProductHeightMeasure_compact_lt_top K hζ d hd B hB hpos).ne

include d hd in
theorem sourceKPCuspArchFourierMoment_analyticOnNhd (m : Kˣ)
    (B : Set (InfinitePlace K → ℝ)) (hB : IsCompact B)
    (hpos : ∀ y ∈ B, ∀ v, 0 < y v) :
    AnalyticOnNhd ℂ (sourceKPCuspArchFourierMoment K hζ m B) {s : ℂ | 0 < s.re} := by
  classical
  have h := sourceArchWeightedProductMoment_analyticOnNhd
    (fun _ : InfinitePlace K => sourceArchTraceCharacter)
    (fun _ => sourceArchTraceCharacter_continuous)
    (fun _ x => (sourceArchTraceCharacter_norm x).le)
    (sourceKPTraceJacquetProfileFrequency K hζ m)
    (sourceKPCuspProductHeightMeasure K) B hB
    (sourceKPCuspProductHeightMeasure_compact_lt_top K hζ d hd B hB hpos).ne
    hpos (fun _ => 1) continuous_const
  convert h using 1
  funext z
  unfold sourceKPCuspArchFourierMoment sourceArchWeightedProductMoment
  simp only [sourceKPTraceJacquetArchProfile,one_mul]

theorem sourceKPCuspArchFourierMoment_unit_box (s : ℂ) :
    sourceKPCuspArchFourierMoment K hζ (1 : Kˣ) (sourceKPCuspHeightBox K) s =
      sourceKPCuspUnitArchMoment K s := by
  classical
  have hf : sourceKPTraceJacquetProfileFrequency K hζ (1:Kˣ) = fun _ => -1 := by
    funext v
    simp only [sourceKPTraceJacquetProfileFrequency,Units.val_one,map_one]
  unfold sourceKPCuspArchFourierMoment sourceKPTraceJacquetArchProfile
    sourceKPCuspUnitArchMoment sourceArchWeightedProductMoment
  simp only [hf,one_mul]

theorem sourceKPCuspArchFourierMoment_unit_box_ne_zero :
    sourceKPCuspArchFourierMoment K hζ (1 : Kˣ) (sourceKPCuspHeightBox K) (1/6) ≠ 0 := by
  rw [sourceKPCuspArchFourierMoment_unit_box]
  exact sourceKPCuspUnitArchMoment_oneSixth_ne_zero K

end
end ArtinMatthews

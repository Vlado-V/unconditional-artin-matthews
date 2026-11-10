module

public import ArtinMatthews.SourceKPCuspHeightBox
public import ArtinMatthews.SourceArchWeightedProductMoment
public import ArtinMatthews.SourceArchUnitFrequencyProfile
public import ArtinMatthews.SourceKPArchJacquetProfile
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! A fixed positive full-dimensional height test normalizes the actual
unit-frequency coefficient near the exceptional parameter. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceArchJacquet
open scoped Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K]

def sourceKPCuspUnitArchMoment (s : ℂ) : ℂ :=
  sourceArchWeightedProductMoment (fun _ : InfinitePlace K => sourceArchTraceCharacter)
    (fun _ => -1) (sourceKPCuspProductHeightMeasure K) (sourceKPCuspHeightBox K) (fun _ => 1) s

theorem sourceKPCuspUnitArchMoment_analyticOnNhd :
    AnalyticOnNhd ℂ (sourceKPCuspUnitArchMoment K) {s : ℂ | 0 < s.re} := by
  classical
  exact sourceArchWeightedProductMoment_analyticOnNhd
    (fun _ : InfinitePlace K => sourceArchTraceCharacter)
    (fun _ => sourceArchTraceCharacter_continuous)
    (fun _ x => (sourceArchTraceCharacter_norm x).le)
    (fun _ => -1) (sourceKPCuspProductHeightMeasure K) (sourceKPCuspHeightBox K)
    (sourceKPCuspHeightBox_isCompact K) (sourceKPCuspHeightBox_mass K).2.ne
    (sourceKPCuspHeightBox_positive K) (fun _ => 1) continuous_const

theorem sourceKPCuspUnitArchMoment_oneSixth_re_pos :
    0 < (sourceKPCuspUnitArchMoment K (1/6)).re := by
  classical
  let S := sourceKPCuspHeightBox K
  let μ := (sourceKPCuspProductHeightMeasure K).restrict S
  let F : (InfinitePlace K → ℝ) → ℂ := fun y =>
    sourceArchWeightedProduct (fun _ : InfinitePlace K => sourceArchTraceCharacter)
      (fun _ => -1) (1/6) y
  have hS : IsCompact S := sourceKPCuspHeightBox_isCompact K
  have hFc : ContinuousOn F S := by
    intro y hy
    have hmap : Continuous (fun y : InfinitePlace K → ℝ => ((1/6:ℂ),y)) :=
      continuous_const.prodMk continuous_id
    exact ((sourceArchWeightedProduct_continuousAt
      (fun _ : InfinitePlace K => sourceArchTraceCharacter)
      (fun _ => sourceArchTraceCharacter_continuous)
      (fun _ x => (sourceArchTraceCharacter_norm x).le)
      (fun _ => -1) ((1/6:ℂ),y) (by norm_num)
      (sourceKPCuspHeightBox_positive K y hy)).comp
        (f := fun y : InfinitePlace K → ℝ => ((1/6:ℂ),y)) hmap.continuousAt).continuousWithinAt
  have hi : Integrable F μ :=
    hFc.integrableOn_of_subset_isCompact hS hS.measurableSet Set.Subset.rfl
      (sourceKPCuspHeightBox_mass K).2.ne
  have hp : ∀ᵐ y ∂μ, 0 < (F y).re := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with y hy
    exact (sourceArchUnitFrequencyProduct_positive y (sourceKPCuspHeightBox_positive K y hy)).1
  have he : Function.support (fun y => (F y).re) =ᵐ[μ] Set.univ := by
    filter_upwards [hp] with y hy
    exact propext (by simp only [Function.mem_support,Set.mem_univ,iff_true]; exact hy.ne')
  have hmass : 0 < μ (Function.support (fun y => (F y).re)) := by
    rw [measure_congr he]
    change 0 < ((sourceKPCuspProductHeightMeasure K).restrict S) Set.univ
    rw [Measure.restrict_apply_univ]
    exact (sourceKPCuspHeightBox_mass K).1
  have hpos : 0 < ∫ y, (F y).re ∂μ :=
    (integral_pos_iff_support_of_nonneg_ae (hp.mono fun _ h => h.le) hi.re).mpr hmass
  have heq : sourceKPCuspUnitArchMoment K (1/6) = ∫ y, F y ∂μ := by
    unfold sourceKPCuspUnitArchMoment sourceArchWeightedProductMoment
    simp only [one_mul]
    rfl
  have hr := integral_re hi
  change (∫ y, (F y).re ∂μ) = (∫ y, F y ∂μ).re at hr
  rw [heq,← hr]
  exact hpos

theorem sourceKPCuspUnitArchMoment_oneSixth_ne_zero :
    sourceKPCuspUnitArchMoment K (1/6) ≠ 0 := by
  intro h
  have hp := sourceKPCuspUnitArchMoment_oneSixth_re_pos K
  rw [h,Complex.zero_re] at hp
  exact (lt_irrefl _ hp)

end
end ArtinMatthews

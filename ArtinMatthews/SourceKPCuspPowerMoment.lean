module

public import ArtinMatthews.SourceKPCuspHeightConstantTerm
public import ArtinMatthews.SourceKPCuspProductMeasure
public import ArtinMatthews.SourceCompactExponentialMoment
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

namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen
open scoped NumberField AdeleRing Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0)
local notation "V" => InfinitePlace K

/-- The height moment retains every independent complex-place coordinate. -/
def sourceKPCuspPowerMoment (B : Set (V → ℝ)) (s : ℂ) : ℂ :=
  ∫ y in B, sourceKPCuspArchPower K s y ∂sourceKPCuspProductHeightMeasure K

theorem sourceKPCuspArchPower_continuousOn (s : ℂ) (B : Set (V → ℝ))
    (hpos : ∀ y ∈ B, ∀ v, 0 < y v) :
    ContinuousOn (sourceKPCuspArchPower K s) B := by
  have hl : ContinuousOn (fun y => Real.log (sourceKPCuspArchHeight K y)) B :=
    (sourceKPCuspArchHeight_continuous K).continuousOn.log
      (fun y hy => (sourceKPCuspArchHeight_pos K y (hpos y hy)).ne')
  exact Complex.continuous_exp.comp_continuousOn
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hl))

include hζ d hd in
theorem sourceKPCuspArchPower_integrableOn (s : ℂ) (B : Set (V → ℝ))
    (hB : IsCompact B) (hpos : ∀ y ∈ B, ∀ v, 0 < y v) :
    IntegrableOn (sourceKPCuspArchPower K s) B (sourceKPCuspProductHeightMeasure K) :=
  (sourceKPCuspArchPower_continuousOn K s B hpos).integrableOn_of_subset_isCompact
    hB hB.measurableSet Set.Subset.rfl
    (sourceKPCuspProductHeightMeasure_compact_lt_top K hζ d hd B hB hpos).ne

include hζ d hd in
theorem sourceKPCuspPowerMoment_entire (B : Set (V → ℝ))
    (hB : IsCompact B) (hpos : ∀ y ∈ B, ∀ v, 0 < y v) :
    Differentiable ℂ (sourceKPCuspPowerMoment K B) := by
  have hl : ContinuousOn (fun y => Real.log (sourceKPCuspArchHeight K y)) B :=
    (sourceKPCuspArchHeight_continuous K).continuousOn.log
      (fun y hy => (sourceKPCuspArchHeight_pos K y (hpos y hy)).ne')
  have h := sourceCompactExponentialMoment_entire (sourceKPCuspProductHeightMeasure K)
    B hB hB.measurableSet
    (sourceKPCuspProductHeightMeasure_compact_lt_top K hζ d hd B hB hpos).ne
    (fun y => Real.log (sourceKPCuspArchHeight K y)) hl
  change Differentiable ℂ (fun s : ℂ => ∫ y in B,
    Complex.exp ((s+1/2)*(Real.log (sourceKPCuspArchHeight K y):ℂ))
      ∂sourceKPCuspProductHeightMeasure K)
  simpa only [Function.comp_def,id_eq] using
    h.comp (differentiable_id.add_const (1/2:ℂ))

include hζ d hd in
theorem sourceKPCuspPowerMoment_analyticAt (B : Set (V → ℝ))
    (hB : IsCompact B) (hpos : ∀ y ∈ B, ∀ v, 0 < y v) (s : ℂ) :
    AnalyticAt ℂ (sourceKPCuspPowerMoment K B) s :=
  (sourceKPCuspPowerMoment_entire K hζ d hd B hB hpos).analyticAt s

end
end ArtinMatthews

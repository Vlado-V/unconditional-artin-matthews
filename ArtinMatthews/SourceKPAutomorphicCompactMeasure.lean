module

public import ArtinMatthews.SourceKPAutomorphicL2
public import ArtinMatthews.SourceKPAutomorphicCompactTopology
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
open NumberField Matrix Topology MeasureTheory
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

instance sourceKPAutomorphicCompactMeasure_finiteOnCompacts
    (μ : Measure (PGL(2, InfiniteAdeleRing K)))
    [IsFiniteMeasureOnCompacts (sourceKPAutomorphicMeasure K hζ μ)] :
    IsFiniteMeasureOnCompacts (sourceKPAutomorphicCompactMeasure K hζ μ) where
  lt_top_of_isCompact C hC := by
    rw [sourceKPAutomorphicCompactMeasure,
      Measure.map_apply (sourceKPAutomorphicCompactMk_measurable K hζ) hC.isClosed.measurableSet]
    exact (sourceKPAutomorphicCompactMk_isCompact_preimage K hζ hC).measure_lt_top

instance sourceKPAutomorphicCompactMeasure_sigmaFinite
    (μ : Measure (PGL(2, InfiniteAdeleRing K)))
    [IsFiniteMeasureOnCompacts (sourceKPAutomorphicMeasure K hζ μ)] :
    SigmaFinite (sourceKPAutomorphicCompactMeasure K hζ μ) := by
  infer_instance

instance sourceKPAutomorphicCompactMeasure_openPositive
    (μ : Measure (PGL(2, InfiniteAdeleRing K)))
    [(sourceKPAutomorphicMeasure K hζ μ).IsOpenPosMeasure] :
    (sourceKPAutomorphicCompactMeasure K hζ μ).IsOpenPosMeasure :=
  (sourceKPAutomorphicCompactMk_isOpenQuotientMap K hζ).continuous.isOpenPosMeasure_map
    (sourceKPAutomorphicCompactMk_isOpenQuotientMap K hζ).surjective

end
end ArtinMatthews

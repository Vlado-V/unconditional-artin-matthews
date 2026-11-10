module

public import ArtinMatthews.SourceKPAutomorphicBorel
public import ArtinMatthews.SourceKPArchComponentMeasure
public import ArtinMatthews.SourceKPFiniteOrbit
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

/-! The actual finite-component automorphic measure for a specified
archimedean measure. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPFiniteOrbitRepresentative (i : SourceKPFiniteOrbit K hζ) : SourceKPFiniteLevelFiber K hζ :=
  Quotient.out i

theorem sourceKPFiniteOrbitRepresentative_spec (i : SourceKPFiniteOrbit K hζ) :
    sourceKPFiniteOrbitMk K hζ (sourceKPFiniteOrbitRepresentative K hζ i) = i :=
  Quotient.out_eq' i

def sourceKPAutomorphicComponentMeasure
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) (i : SourceKPFiniteOrbit K hζ) :
    Measure (SourceKPAutomorphicLevel K hζ) :=
  Measure.map (sourceKPArchComponentEmbedding K hζ (sourceKPFiniteOrbitRepresentative K hζ i))
    (sourceKPArchComponentQuotientMeasure K hζ (sourceKPFiniteOrbitRepresentative K hζ i) μ)

def sourceKPAutomorphicMeasure (μ : Measure (PGL(2, InfiniteAdeleRing K))) :
    Measure (SourceKPAutomorphicLevel K hζ) :=
  Measure.sum (sourceKPAutomorphicComponentMeasure K hζ μ)

theorem sourceKPAutomorphicComponentMeasure_apply
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) (i : SourceKPFiniteOrbit K hζ)
    (U : Set (SourceKPAutomorphicLevel K hζ)) (hU : MeasurableSet U) :
    sourceKPAutomorphicComponentMeasure K hζ μ i U =
      sourceKPArchComponentQuotientMeasure K hζ (sourceKPFiniteOrbitRepresentative K hζ i) μ
        ((sourceKPArchComponentEmbedding K hζ (sourceKPFiniteOrbitRepresentative K hζ i)) ⁻¹' U) :=
  Measure.map_apply (sourceKPArchComponentEmbedding_measurable K hζ _) hU

theorem sourceKPAutomorphicMeasure_apply
    (μ : Measure (PGL(2, InfiniteAdeleRing K)))
    (U : Set (SourceKPAutomorphicLevel K hζ)) (hU : MeasurableSet U) :
    sourceKPAutomorphicMeasure K hζ μ U =
      ∑' i : SourceKPFiniteOrbit K hζ,
        sourceKPArchComponentQuotientMeasure K hζ (sourceKPFiniteOrbitRepresentative K hζ i) μ
          ((sourceKPArchComponentEmbedding K hζ (sourceKPFiniteOrbitRepresentative K hζ i)) ⁻¹' U) := by
  rw [sourceKPAutomorphicMeasure,Measure.sum_apply _ hU]
  apply tsum_congr
  intro i
  exact sourceKPAutomorphicComponentMeasure_apply K hζ μ i U hU

end
end ArtinMatthews

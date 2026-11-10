module

public import ArtinMatthews.SourceKPAutomorphicMeasure
public import ArtinMatthews.SourceKPArchDoubleQuotient
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

instance sourceKPAutomorphicCompactLevel_measurableSpace :
    MeasurableSpace (SourceKPAutomorphicCompactLevel K hζ) := borel _

instance sourceKPAutomorphicCompactLevel_borelSpace :
    BorelSpace (SourceKPAutomorphicCompactLevel K hζ) := ⟨rfl⟩

theorem sourceKPAutomorphicCompactMk_measurable : Measurable (sourceKPAutomorphicCompactMk K hζ) :=
  (sourceKPAutomorphicCompactMk_isOpenQuotientMap K hζ).continuous.measurable

def sourceKPAutomorphicCompactMeasure (μ : Measure (PGL(2, InfiniteAdeleRing K))) :
    Measure (SourceKPAutomorphicCompactLevel K hζ) :=
  Measure.map (sourceKPAutomorphicCompactMk K hζ) (sourceKPAutomorphicMeasure K hζ μ)

theorem sourceKPAutomorphicCompactMk_measurePreserving
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) :
    MeasurePreserving (sourceKPAutomorphicCompactMk K hζ)
      (sourceKPAutomorphicMeasure K hζ μ) (sourceKPAutomorphicCompactMeasure K hζ μ) :=
  ⟨sourceKPAutomorphicCompactMk_measurable K hζ,rfl⟩

abbrev SourceKPAutomorphicL2 (μ : Measure (PGL(2, InfiniteAdeleRing K))) :=
  Lp ℂ 2 (sourceKPAutomorphicCompactMeasure K hζ μ)

def sourceKPAutomorphicL2Pullback (μ : Measure (PGL(2, InfiniteAdeleRing K))) :
    SourceKPAutomorphicL2 K hζ μ →ₗᵢ[ℂ] Lp ℂ 2 (sourceKPAutomorphicMeasure K hζ μ) :=
  Lp.compMeasurePreservingₗᵢ ℂ (sourceKPAutomorphicCompactMk K hζ)
    (sourceKPAutomorphicCompactMk_measurePreserving K hζ μ)

theorem sourceKPAutomorphicL2Pullback_norm (μ : Measure (PGL(2, InfiniteAdeleRing K)))
    (f : SourceKPAutomorphicL2 K hζ μ) : ‖sourceKPAutomorphicL2Pullback K hζ μ f‖ = ‖f‖ :=
  (sourceKPAutomorphicL2Pullback K hζ μ).norm_map f

end
end ArtinMatthews

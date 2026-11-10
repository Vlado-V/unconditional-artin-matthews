module

public import ArtinMatthews.SourceKPAutomorphicComponentMeasure
public import ArtinMatthews.SourceKPAutomorphicL2
public import ArtinMatthews.SourceKPAutomorphicMeasureChoice
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
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAutomorphicCompactComponentSet (i : SourceKPFiniteOrbit K hζ) :
    Set (SourceKPAutomorphicCompactLevel K hζ) :=
  (sourceKPAutomorphicCompactFiniteOrbit K hζ) ⁻¹' {i}

theorem sourceKPAutomorphicCompactComponentSet_measurable (i : SourceKPFiniteOrbit K hζ) :
    MeasurableSet (sourceKPAutomorphicCompactComponentSet K hζ i) :=
  ((isOpen_discrete ({i} : Set (SourceKPFiniteOrbit K hζ))).preimage
    (sourceKPAutomorphicCompactFiniteOrbit_continuous K hζ)).measurableSet

theorem sourceKPAutomorphicCompactComponentSet_preimage (i : SourceKPFiniteOrbit K hζ) :
    (sourceKPAutomorphicCompactMk K hζ) ⁻¹' sourceKPAutomorphicCompactComponentSet K hζ i =
      sourceKPAutomorphicComponentSet K hζ i := rfl

theorem sourceKPAutomorphicCompactMeasure_restrict_component
    (b : SourceKPFiniteLevelFiber K hζ)
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) [μ.IsMulLeftInvariant] :
    (sourceKPAutomorphicCompactMeasure K hζ μ).restrict
        (sourceKPAutomorphicCompactComponentSet K hζ (sourceKPFiniteOrbitMk K hζ b)) =
      Measure.map (fun q : SourceKPArchComponentQuotient K hζ b =>
        sourceKPAutomorphicCompactMk K hζ (sourceKPArchComponentEmbedding K hζ b q))
        (sourceKPArchComponentQuotientMeasure K hζ b μ) := by
  unfold sourceKPAutomorphicCompactMeasure
  rw [Measure.restrict_map (sourceKPAutomorphicCompactMk_measurable K hζ)
      (sourceKPAutomorphicCompactComponentSet_measurable K hζ _),
    sourceKPAutomorphicCompactComponentSet_preimage,
    sourceKPAutomorphicMeasure_restrict_component,
    ← sourceKPArchComponentPushMeasure_eq_component K hζ b μ]
  exact Measure.map_map (sourceKPAutomorphicCompactMk_measurable K hζ)
    (sourceKPArchComponentEmbedding_measurable K hζ b)

end
end ArtinMatthews

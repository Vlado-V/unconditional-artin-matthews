module

public import ArtinMatthews.SourceKPArchMeasureTopology
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

namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

instance sourceKPAutomorphicLevel_measurableSpace :
    MeasurableSpace (SourceKPAutomorphicLevel K hζ) := borel _

instance sourceKPAutomorphicLevel_borelSpace :
    BorelSpace (SourceKPAutomorphicLevel K hζ) := ⟨rfl⟩

theorem sourceKPArchComponentPoint_measurable (b : SourceKPFiniteLevelFiber K hζ) :
    Measurable (sourceKPArchComponentPoint K hζ b) :=
  (sourceKPArchComponentPoint_continuous K hζ b).measurable

theorem sourceKPArchComponentEmbedding_measurable (b : SourceKPFiniteLevelFiber K hζ) :
    Measurable (sourceKPArchComponentEmbedding K hζ b) := by
  intro U hU
  change MeasurableSet ((Quotient.mk (QuotientGroup.rightRel
    (sourceKPArchComponentSubgroup K hζ b))) ⁻¹'
      ((sourceKPArchComponentEmbedding K hζ b) ⁻¹' U))
  change MeasurableSet ((sourceKPArchComponentPoint K hζ b) ⁻¹' U)
  exact sourceKPArchComponentPoint_measurable K hζ b hU

end
end ArtinMatthews

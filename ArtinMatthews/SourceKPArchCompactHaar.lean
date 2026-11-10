module

public import ArtinMatthews.SourceKPArchCompactOrbifold
public import ArtinMatthews.SourceKPArchMeasureTopology
public import ArtinMatthews.SourceKPArithmeticDiscreteness
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
open NumberField Matrix Topology TopologicalSpace MeasureTheory
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

instance sourceKPArchCompactGroup_compactSpace :
    CompactSpace (sourceKPArchBaseCompactSubgroup K hζ) :=
  isCompact_iff_compactSpace.mp (sourceKPArchBaseCompactSubgroup_isCompact K hζ)

def sourceKPArchCompactPositive : PositiveCompacts (sourceKPArchBaseCompactSubgroup K hζ) :=
  ⟨⟨Set.univ,isCompact_univ⟩,by simp⟩

def sourceKPArchCompactHaar : Measure (sourceKPArchBaseCompactSubgroup K hζ) :=
  Measure.haarMeasure (sourceKPArchCompactPositive K hζ)

instance sourceKPArchCompactHaar_isHaar : (sourceKPArchCompactHaar K hζ).IsHaarMeasure := by
  unfold sourceKPArchCompactHaar
  infer_instance

theorem sourceKPArchCompactHaar_univ : sourceKPArchCompactHaar K hζ Set.univ = 1 := by
  exact Measure.haarMeasure_self

instance sourceKPArchCompactHaar_isProbability : IsProbabilityMeasure (sourceKPArchCompactHaar K hζ) :=
  ⟨sourceKPArchCompactHaar_univ K hζ⟩

instance sourceKPArchCompactHaar_rightInvariant : (sourceKPArchCompactHaar K hζ).IsMulRightInvariant := by
  constructor
  intro k
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure
    (Measure.map (fun h : sourceKPArchBaseCompactSubgroup K hζ => h*k)
      (sourceKPArchCompactHaar K hζ)) (sourceKPArchCompactHaar K hζ)

end
end ArtinMatthews

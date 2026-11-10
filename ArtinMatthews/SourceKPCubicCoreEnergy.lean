module

public import ArtinMatthews.SourceKPCubicCoreAction
public import ArtinMatthews.SourceKPCompactCoreEnergy
public import ArtinMatthews.SourceKPCubicUpperAction
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

/-! Actual center pullback preserves the global native Dirichlet integral. -/
namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField MatrixGroups AdeleRing ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCubicCoreEnergy_covariant (z : rootsOfUnity 3 K)
    (f : sourceKPCompactC2Core K hζ) (y : SourceKPAutomorphicCompactLevel K hζ) :
    sourceKPCompactCoreEnergy K hζ (sourceKPCubicCorePullback K hζ 2 z f) y =
      sourceKPCompactCoreEnergy K hζ f (z⁻¹ • y) := by
  obtain ⟨b, p, rfl⟩ := sourceKPUpperToCompact_cover K hζ y
  rw [sourceKPCubicCenter_upperToCompact, sourceKPCompactCoreEnergy_chart,
    sourceKPCompactCoreEnergy_chart, sourceKPCubicCorePullback_energy]

theorem sourceKPCubicCoreEnergy_integral (z : rootsOfUnity 3 K)
    (f : sourceKPCompactC2Core K hζ) :
    (∫ y, sourceKPCompactCoreEnergy K hζ (sourceKPCubicCorePullback K hζ 2 z f) y
      ∂sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) =
      ∫ y, sourceKPCompactCoreEnergy K hζ f y
        ∂sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ) := by
  simp_rw [sourceKPCubicCoreEnergy_covariant]
  exact (sourceKPAutomorphicCompactMeasure_center_preserving K hζ z⁻¹
    (sourceKPArchHaar K hζ)).integral_comp
      (sourceKPCubicCenterCompactHomeomorph K hζ z⁻¹).measurableEmbedding
      (sourceKPCompactCoreEnergy K hζ f)

end
end ArtinMatthews
